"""Decode the AAT-02 vector suite into the Lean model's input format.

The model treats signatures and SHA-256 as ideal (assumptions 1, 5). This
decoder computes, for each token, the set of keys under which its Ed25519
signature actually verifies (OpenSSL), and the SHA-256 of its JWS Signing
Input; the model consumes those. Keys are identified by their JWK thumbprint
URI (RFC 7638 / 9278). Each token is read from its `compact` serialization
only. For each vector we extract:
  - params (suite defaults overridden by the vector) and `now`,
  - trust anchors as (issuer, key thumbprint),
  - per token: the payload as written (a JSON tree that keeps repeated member
    names and number literals; the Lean model parses claims itself, steps
    3b-3m, 4b-4n), the thumbprint URI of cnf.jwk, the signing-input hash, the
    signing keys, and the constraint maps of the attenuating_agent_token entry,
  - the PoP payload as written, its signing keys and `hta` as arguments,
  - the invocation: tool and args.

A vector is IN SCOPE when its expected verdict is decided by steps the model
implements: every PERMIT, and every DENY whose expected first failing step is
in MODELED_STEPS. Vectors that use constraint types of the second pass, or
cannot be decoded, are out of scope.

Usage:
    python3 -I vectors/decode.py vectors/upstream/aat-jws-vectors.json vectors/out/model-input.json
"""
import base64
import concurrent.futures
import hashlib
import json
import pathlib
import sys
import threading
from decimal import Decimal
from fractions import Fraction

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import ed25519  # noqa: E402

MODELED_STEPS = {
    "1", "2a", "2b", "2c", "3a", "4a", "7a",
    "3b", "3c", "3d", "3e", "3f", "3g", "3h", "3i", "3j", "3k", "3l", "3m",
    "4b", "4b1", "4b2", "4b3", "4b4", "4b5", "4n", "4c", "4d", "4e", "4f", "4g", "4h", "4i", "4j", "4k", "4l", "4m",
    "3n", "4o",
    "4p1", "4p2", "4p3", "4p4", "4q",
    "5", "6b", "6c",
    "7b", "7c", "7d", "7e", "7f", "7g", "7h", "7i",
}


class OutOfScope(Exception):
    pass


class _Obj(list):
    """A JSON object as its member list, before duplicate names are resolved."""


def load_args(s):
    """Top-level argument pairs. Duplicate top-level names are kept: step 6b
    must see them. Nested objects become dicts recursively (a repeated nested
    name: the last value; the model denies such a call from the tree as
    written, `call.tree`, before it reads any value)."""
    def nested(x):
        if isinstance(x, _Obj):
            return {k: nested(v) for k, v in x}
        if isinstance(x, list):
            return [nested(e) for e in x]
        return x
    top = json.loads(s, parse_float=Decimal, parse_int=int, object_pairs_hook=_Obj)
    if not isinstance(top, _Obj):
        raise OutOfScope("precondition: arguments are not a JSON object")
    return [(k, nested(v)) for k, v in top]


class _Num(str):
    """A JSON number as written (its literal)."""


def _no_constant(c):
    raise OutOfScope(f"precondition: {c} is not JSON (byte level)")


def tree(text):
    """JSON as written: objects keep repeated names (_Obj), numbers keep their literal (_Num)."""
    return json.loads(text, object_pairs_hook=_Obj, parse_int=_Num, parse_float=_Num,
                      parse_constant=_no_constant)


def no_dup(x):
    if isinstance(x, _Obj):
        return len({k for k, _ in x}) == len(x) and all(no_dup(v) for _, v in x)
    if isinstance(x, list):
        return all(no_dup(e) for e in x)
    return True


def plain(x):
    """Tree -> Python values (only used where the tree has no repeated names)."""
    if isinstance(x, _Obj):
        return {k: plain(v) for k, v in x}
    if isinstance(x, list):
        return [plain(e) for e in x]
    if isinstance(x, _Num):
        return Decimal(x) if any(c in x for c in ".eE") else int(x)
    return x


def enc(x):
    """Tree -> the Lean `JVal` encoding read by Runner.lean."""
    if isinstance(x, _Obj):
        return {"o": [[k, enc(v)] for k, v in x]}
    if isinstance(x, list):
        return {"a": [enc(e) for e in x]}
    if isinstance(x, _Num):
        return {"n": str(x)}
    if isinstance(x, bool):
        return {"b": x}
    if x is None:
        return {"z": True}
    return {"s": x}


def field(x, k):
    """Member `k` of an object tree (the first one; repeated names make the model deny)."""
    if isinstance(x, _Obj):
        for a, v in x:
            if a == k:
                return v
    return None


def segment(s):
    """A base64url JSON segment as written. Any JSON value is passed to the
    model as is — an array or a string carries no claims and the model denies
    (2c, 3a). A segment that is not base64url, UTF-8 or JSON is passed as
    null, which the model treats the same way."""
    try:
        return tree(ed25519.b64u_decode(s).decode("utf-8"))
    except (ValueError, UnicodeDecodeError, OutOfScope):
        return None


def jws(token):
    """Payload tree, signing input and signature, all from the one compact
    serialization: the other fields of the vector are not trusted to agree."""
    parts = token["compact"].split(".")
    if len(parts) != 3:
        raise OutOfScope("precondition: compact JWS is not three segments (byte level)")
    try:
        sig = ed25519.b64u_decode(parts[2])
    except ValueError:
        sig = b""
    return segment(parts[1]), (parts[0] + "." + parts[1]).encode(), sig


def jws_header(token):
    """The JWS Protected Header as written (a tree, like the payload)."""
    return segment(token["compact"].split(".")[0])


def cnf_jwk(p):
    """cnf.jwk as a dict, if it is an object."""
    j = field(field(p, "cnf"), "jwk")
    return plain(j) if isinstance(j, _Obj) else None


_POOL = concurrent.futures.ThreadPoolExecutor(16)


def signed_by(keys, msg, sig):
    """Thumbprint URIs of the Ed25519 keys under which `sig` verifies over `msg`.
    Only a key with crv Ed25519 can verify an Ed25519 signature (3a, 4a, 7a:
    alg consistent with the key): the x of any other key is not tried.
    Each check is an independent OpenSSL process; they run in parallel."""
    keys = [k for k in keys if thumb(k) is not None and k.get("crv") == "Ed25519"]
    ok = _POOL.map(lambda k: ed25519.verify(k["x"], msg, sig), keys)
    return sorted({thumbprint_uri(k) for k, good in zip(keys, ok) if good})


def admissible(x):
    """§3.4: the JCS serialization of the number's double denotes the same value.
    A number beyond the double range has no such serialization: inadmissible."""
    try:
        f = float(x)
    except OverflowError:
        return False
    if f in (float("inf"), float("-inf")):
        return False
    return Fraction(Decimal(repr(f))) == Fraction(x)


def check_admissible(x):
    if isinstance(x, bool) or x is None or isinstance(x, str):
        return
    if isinstance(x, (int, Decimal)):
        if not admissible(x):
            raise OutOfScope("precondition: inadmissible number inside a nested value (assumption 6)")
    elif isinstance(x, list):
        for e in x:
            check_admissible(e)
    elif isinstance(x, dict):
        for e in x.values():
            check_admissible(e)


def num(x):
    f = Fraction(x)
    return {"n": f.numerator, "d": f.denominator}


def jcs(x):
    """JCS (RFC 8785) for compound values used in equality only."""
    if isinstance(x, bool) or x is None:
        return json.dumps(x)
    if isinstance(x, (int, Decimal)):
        f = Fraction(x)
        if f.denominator == 1:
            return str(f.numerator)
        return repr(float(x))  # ES6 shortest form coincides for admissible numbers in practice
    if isinstance(x, str):
        return json.dumps(x, ensure_ascii=False)
    if isinstance(x, list):
        return "[" + ",".join(jcs(e) for e in x) + "]"
    if isinstance(x, dict):
        keys = sorted(x.keys(), key=lambda k: k.encode("utf-16-be"))
        return "{" + ",".join(json.dumps(k, ensure_ascii=False) + ":" + jcs(x[k]) for k in keys) + "}"
    raise OutOfScope(f"unknown JSON value {type(x)}")


def is_num(x):
    return isinstance(x, (int, Decimal)) and not isinstance(x, bool)


def scalar(x):
    """An array element: scalar, or a nested array/object in JCS form."""
    if isinstance(x, bool):
        return {"bool": x}
    if x is None:
        return {"null": True}
    if is_num(x):
        return {"num": num(x)}  # exact value; the model checks admissibility (§3.4)
    if isinstance(x, str):
        return {"str": x}
    check_admissible(x)  # numbers inside a JCS string are invisible to the model (assumption 6)
    return {"compound": jcs(x)}


def value(x):
    if isinstance(x, list):
        return {"arr": [scalar(e) for e in x]}
    if isinstance(x, dict):
        check_admissible(x)
        return {"compound": jcs(x)}
    return scalar(x)


MALFORMED = {"malformed": True}
MEMBERS = {
    "wildcard": set(), "exact": {"value"}, "one_of": {"values"}, "not_one_of": {"excluded"},
    "range": {"min", "max", "min_inclusive", "max_inclusive"}, "contains": {"required"},
    "subset": {"allowed"}, "all": {"constraints"}, "any": {"constraints"},
}


def constraint(c, nested=False):
    """§3.4 well-formedness at the representation level; what the Lean `wf`
    checks (non-empty one_of/all/any, min <= max, depth) is left to the model."""
    if not isinstance(c, dict):
        return MALFORMED
    t = c.get("constraint_type")
    if not isinstance(t, str) or t not in MEMBERS:
        return MALFORMED  # unknown type: fail-closed
    allowed = MEMBERS[t] | {"constraint_type"} | (set() if nested else {"optional"})
    if set(c) - allowed:
        return MALFORMED  # «no members other than ...»; optional nested in all/any
    if "optional" in c and not isinstance(c["optional"], bool):
        return MALFORMED
    if t == "wildcard":
        return {"wildcard": True}
    if t == "exact":
        v = c.get("value", ...)
        if not (v is None or isinstance(v, (str, bool)) or is_num(v)):
            return MALFORMED
        return {"exact": value(v)}
    if t in ("one_of", "not_one_of", "contains", "subset"):
        key = {"one_of": "values", "not_one_of": "excluded", "contains": "required", "subset": "allowed"}[t]
        arr = c.get(key)
        if not isinstance(arr, list):
            return MALFORMED
        if t in ("one_of", "not_one_of"):
            return {{"one_of": "oneOf", "not_one_of": "notOneOf"}[t]: [value(x) for x in arr]}
        return {t: [scalar(x) for x in arr]}
    if t == "range":
        out = {}
        for side in ("min", "max"):
            flag = side + "_inclusive"
            if flag in c and (side not in c or not isinstance(c[flag], bool)):
                return MALFORMED
            if side in c:
                if not is_num(c[side]):
                    return MALFORMED
                out[side] = {"val": num(c[side]), "incl": bool(c.get(flag, True))}
            else:
                out[side] = None
        return {"range": {"lo": out["min"], "hi": out["max"]}}
    cs = c.get("constraints")
    if not isinstance(cs, list):
        return MALFORMED
    return {t: [constraint(x, nested=True) for x in cs]}


def cmap(m):
    if not isinstance(m, dict):
        raise OutOfScope("precondition: constraint map is not an object")
    named, star = [], False
    for k, entry in m.items():
        if k == "*":
            if isinstance(entry, dict) and set(entry) == {"constraint_type"} and \
                    entry["constraint_type"] == "wildcard":
                star = True
            else:  # «a "*" entry is a wildcard constraint with no optional member»
                named.append([k, {"c": MALFORMED, "optional": False}])
            continue
        opt = entry.get("optional", False) if isinstance(entry, dict) else False
        named.append([k, {"c": constraint(entry), "optional": opt is True}])
    return {"named": named, "star": star}


def b64u(b):
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode()


def thumbprint_uri(jwk):
    canon = json.dumps({"crv": jwk["crv"], "kty": jwk["kty"], "x": jwk["x"]},
                       separators=(",", ":"), sort_keys=True)
    return "urn:ietf:params:oauth:jwk-thumbprint:sha-256:" + b64u(hashlib.sha256(canon.encode()).digest())


def thumb(jwk):
    """jwk_thumbprint_uri for an OKP key with string members (assumption 5);
    for anything else None — the model rejects such a key (3l, 4b2) first."""
    if not isinstance(jwk, dict) or jwk.get("kty") != "OKP" or \
            not all(isinstance(jwk.get(k), str) for k in ("crv", "x")):
        return None
    return thumbprint_uri(jwk)


def maps(p):
    """Constraint maps of the single AAT entry, by tool name. Empty when the
    payload repeats a name or the entry is malformed: the model denies those
    itself (3b/4b, 3m/4n) before it reads any map."""
    if not no_dup(p):
        return []
    ad = field(p, "authorization_details")
    if not isinstance(ad, list) or isinstance(ad, _Obj):
        return []
    entries = [e for e in ad if field(e, "type") == "attenuating_agent_token"]
    if len(entries) != 1 or not isinstance(field(entries[0], "tools"), _Obj):
        return []
    return [[t, cmap(plain(m))] for t, m in field(entries[0], "tools") if isinstance(m, _Obj)]


def link(token, candidates):
    p, msg, sig = jws(token)
    jwk = cnf_jwk(p)
    keys = candidates + ([jwk] if jwk else [])
    return {
        "header": enc(jws_header(token)),
        "size": len(token["compact"].encode()),
        "payload": enc(p),
        "thumb": thumb(jwk),
        "maps": maps(p),
        "selfHash": b64u(hashlib.sha256(msg).digest()),
        "sigBy": signed_by(keys, msg, sig),
    }


def pop_of(v, candidates, args_pairs):
    pop = v.get("pop")
    if not pop:
        raise OutOfScope("no PoP JWT")
    p, msg, sig = jws(pop)
    hta = field(p, "hta")
    hta = [[k, value(plain(x))] for k, x in hta] if isinstance(hta, _Obj) and no_dup(p) else None
    return {"header": enc(jws_header(pop)), "payload": enc(p), "hta": hta,
            "sigBy": signed_by(candidates, msg, sig)}


def deep(f):
    """Runs f() in a thread with a 512 MiB stack and a high recursion limit, and
    restores the limit after. A signed token may nest JSON as deep as
    MAX_TOKEN_SIZE allows, and every pass over such a tree (parse, encode,
    load, dump) recurses: all of them go through here. The limit is raised
    only while f runs, so elsewhere deep nesting is a RecursionError, not a
    stack overflow."""
    out = {}

    def body():
        try:
            out["v"] = f()
        except BaseException as e:  # re-raised in the caller's thread
            out["e"] = e
    old_limit = sys.getrecursionlimit()
    old_stack = threading.stack_size(1 << 29)
    sys.setrecursionlimit(1_000_000)
    try:
        t = threading.Thread(target=body)
        t.start()
        t.join()
    finally:
        sys.setrecursionlimit(old_limit)
        threading.stack_size(old_stack)
    if "e" in out:
        raise out["e"]
    return out["v"]


def decode(suite):
    return deep(lambda: _decode(suite))


def _decode(suite):
    anchors = [{"iss": a["iss"], "key": thumbprint_uri(a["jwk"])} for a in suite["trust_anchors"]]
    known = [k["jwk"] for k in suite["keys"].values()] + [a["jwk"] for a in suite["trust_anchors"]]
    out = []
    for v in suite["vectors"]:
        # a vector without `expected` (sent blind to an implementation) is decided by the model
        exp = v.get("expected") or {"verdict": None, "step": None}
        rec = {"id": v["id"], "expected": exp["verdict"], "step": exp.get("step"), "title": v.get("title", "")}
        modeled = exp["verdict"] in ("PERMIT", None) or exp.get("step") in MODELED_STEPS
        try:
            if not modeled:
                raise OutOfScope(f"expected step {exp.get('step')} not modeled")
            params = dict(suite["params"]); params.update(v.get("params") or {})
            now = v.get("now", params["now"])
            args = load_args(v["args_json"])
            chain, cands = [], list(known)
            for t in v["chain"]:
                l = link(t, cands)
                jwk = cnf_jwk(jws(t)[0])
                cands = cands + ([jwk] if jwk else [])
                chain.append(l)
            pol = v.get("policy") or {}
            rs = v.get("replay_state") or {}
            endpoint = {"audience": params["audience"], "popWindow": params["pop_window"],
                        "requireChainAud": bool(pol.get("require_chain_aud", False)),
                        "requirePopAud": bool(pol.get("require_pop_aud", False)),
                        "nonce": pol.get("nonce"), "trackJti": bool(pol.get("track_pop_jti", False))}
            if "after" in rs:
                rec["expected_state"] = rs["after"]
            rec["input"] = {
                "endpoint": endpoint,
                "seen": rs.get("before", []),
                "pop": pop_of(v, cands, args),
                "params": {"now": now, "maxIatSkew": params["max_iat_skew"],
                           "maxTokenLifetime": params["max_token_lifetime"],
                           "maxDelegationDepth": params["max_delegation_depth"],
                           "maxConstraintDepth": params["max_constraint_depth"],
                           "maxTokenSize": params["max_token_size"],
                           "maxChainSize": params["max_chain_size"]},
                "anchors": anchors,
                "chain": chain,
                "call": {"tool": v["tool"], "args": [[k, value(x)] for k, x in args],
                         "tree": enc(tree(v["args_json"]))},
            }
            rec["scope"] = "in"
        except OutOfScope as e:
            rec["scope"] = "out"
            rec["reason"] = str(e)
        except (KeyError, TypeError, ValueError, AttributeError) as e:
            # not a stated assumption: a coverage loss, reported as an error
            rec["scope"] = "error"
            rec["reason"] = f"undecodable: {type(e).__name__}: {e}"
        out.append(rec)
    return out


def dump(obj, path):
    deep(lambda: pathlib.Path(path).write_text(json.dumps(obj, ensure_ascii=False)))


def load(path):
    return deep(lambda: json.loads(pathlib.Path(path).read_text()))


def main():
    suite = json.load(open(sys.argv[1]))
    recs = decode(suite)
    dump(recs, sys.argv[2])
    inn = [r for r in recs if r["scope"] == "in"]
    print(f"{len(recs)} vectors, {len(inn)} in scope "
          f"({sum(r['expected'] == 'PERMIT' for r in inn)} PERMIT, "
          f"{sum(r['expected'] == 'DENY' for r in inn)} DENY)")
    reasons = {}
    errs = [r for r in recs if r["scope"] == "error"]
    for r in errs:
        print(f"  ERROR {r['id']}: {r['reason']}")
    for r in recs:
        if r["scope"] == "out":
            key = r["reason"].split(":")[0] if r["reason"].startswith("undecodable") else r["reason"]
            reasons[key] = reasons.get(key, 0) + 1
    for k, n in sorted(reasons.items(), key=lambda kv: -kv[1])[:15]:
        print(f"  out: {n:3d}  {k}")
    return 1 if errs else 0


if __name__ == "__main__":
    sys.exit(main())
