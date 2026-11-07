"""Decode the AAT-02 vector suite into the Lean model's input format.

The model treats signatures and SHA-256 as ideal (assumptions 1, 5). This
decoder computes, for each token, the set of keys under which its Ed25519
signature actually verifies (OpenSSL), and the SHA-256 of its JWS Signing
Input; the model consumes those. Keys are identified by their JWK thumbprint
URI (RFC 7638 / 9278). Each token is read from its `compact` serialization
only. For each vector we extract, losslessly:
  - params (suite defaults overridden by the vector) and `now`,
  - trust anchors as (issuer, key thumbprint),
  - per token: iss, holder = thumbprint URI of cnf.jwk, jti, iat, exp,
    del_depth, del_max_depth, par_hash, own signing-input hash, signing keys,
    and the constraint maps of the attenuating_agent_token entry,
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
from decimal import Decimal
from fractions import Fraction

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import ed25519  # noqa: E402

MODELED_STEPS = {
    "1", "2c",
    "3b", "3c", "3d", "3e", "3f", "3g", "3h", "3i", "3k",
    "4b", "4c", "4d", "4e", "4f", "4g", "4h", "4i", "4j", "4k", "4l", "4m",
    "3n", "4o",
    "4p1", "4p2", "4p3", "4p4", "4q",
    "5", "6b", "6c",
    "7b", "7c", "7d", "7e", "7f", "7g", "7h", "7i",
}


class OutOfScope(Exception):
    pass


def _no_dups(pairs):
    keys = [k for k, _ in pairs]
    if len(keys) != len(set(keys)):
        raise OutOfScope("precondition: duplicate JSON member names in claims (assumption 7)")
    return dict(pairs)


def loads(s):
    return json.loads(s, parse_float=Decimal, parse_int=int, object_pairs_hook=_no_dups)


class _Obj(list):
    """A JSON object as its member list, before duplicate names are resolved."""


def load_args(s):
    """Top-level argument pairs. Duplicate top-level names are kept: step 6b
    must see them. Nested objects become dicts recursively; a duplicate name
    inside a nested object is outside the model (assumption 7)."""
    def nested(x):
        if isinstance(x, _Obj):
            if len({k for k, _ in x}) != len(x):
                raise OutOfScope("precondition: duplicate JSON member names in a nested argument (assumption 7)")
            return {k: nested(v) for k, v in x}
        if isinstance(x, list):
            return [nested(e) for e in x]
        return x
    top = json.loads(s, parse_float=Decimal, parse_int=int, object_pairs_hook=_Obj)
    if not isinstance(top, _Obj):
        raise OutOfScope("precondition: arguments are not a JSON object")
    return [(k, nested(v)) for k, v in top]


def jws(token):
    """Payload, signing input and signature, all from the one compact
    serialization: the other fields of the vector are not trusted to agree."""
    parts = token["compact"].split(".")
    if len(parts) != 3:
        raise OutOfScope("precondition: compact JWS is not three segments (byte level)")
    payload = loads(ed25519.b64u_decode(parts[1]).decode("utf-8"))
    if not isinstance(payload, dict):
        raise OutOfScope("precondition: JWS payload is not a JSON object")
    return payload, (parts[0] + "." + parts[1]).encode(), ed25519.b64u_decode(parts[2])


_POOL = concurrent.futures.ThreadPoolExecutor(16)


def signed_by(keys, msg, sig):
    """Thumbprint URIs of the OKP keys under which `sig` verifies over `msg`.
    Each check is an independent OpenSSL process; they run in parallel."""
    keys = [k for k in keys if k.get("kty") == "OKP"]
    ok = _POOL.map(lambda k: ed25519.verify(k["x"], msg, sig), keys)
    return sorted({thumbprint_uri(k) for k, good in zip(keys, ok) if good})


def admissible(x):
    """§3.4: the JCS serialization of the number's double denotes the same value."""
    return Fraction(Decimal(repr(float(x)))) == Fraction(x)


def check_admissible(x):
    if isinstance(x, bool) or x is None or isinstance(x, str):
        return
    if isinstance(x, (int, Decimal)):
        if not admissible(x):
            raise OutOfScope("precondition: inadmissible number (assumption 6)")
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
        check_admissible(x)
        return {"num": num(x)}
    if isinstance(x, str):
        return {"str": x}
    check_admissible(x)
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
    if t not in MEMBERS:
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
                check_admissible(c[side])
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
    if jwk.get("kty") != "OKP":
        raise OutOfScope("non-OKP cnf.jwk")
    canon = json.dumps({"crv": jwk["crv"], "kty": jwk["kty"], "x": jwk["x"]},
                       separators=(",", ":"), sort_keys=True)
    return "urn:ietf:params:oauth:jwk-thumbprint:sha-256:" + b64u(hashlib.sha256(canon.encode()).digest())


def intclaim(p, k):
    if k not in p:
        raise OutOfScope(f"precondition: {k} missing (parsing, 3b/4b)")
    x = p[k]
    if isinstance(x, bool) or not isinstance(x, int):
        raise OutOfScope(f"precondition: {k} is not an integer (parsing, 3b/4b)")
    return x


def link(token, candidates):
    p, msg, sig = jws(token)
    entries = [e for e in p.get("authorization_details", []) if e.get("type") == "attenuating_agent_token"]
    if len(entries) != 1:
        raise OutOfScope("not exactly one attenuating_agent_token entry")
    tools = entries[0].get("tools")
    if not isinstance(tools, dict):
        raise OutOfScope("tools is not an object")
    if not isinstance(p.get("jti"), str):
        raise OutOfScope("precondition: jti missing (3j/4b1)")
    jwk = p["cnf"]["jwk"]
    sig_by = signed_by(candidates + [jwk], msg, sig)
    ph = p.get("par_hash")
    aud = p.get("aud", None)
    if "aud" not in p:
        aud = None
    elif isinstance(aud, str):
        aud = [aud]
    elif isinstance(aud, list) and all(isinstance(a, str) for a in aud):
        pass
    else:
        aud = []  # not a string or an array of strings: step 6c denies
    return {
        "aud": aud,
        "issuer": p["iss"],
        "holder": thumbprint_uri(jwk),
        "tools": [[t, cmap(m)] for t, m in tools.items()],
        "jti": p["jti"],
        "delDepth": intclaim(p, "del_depth"),
        "delMaxDepth": intclaim(p, "del_max_depth"),
        "iat": intclaim(p, "iat"),
        "exp": intclaim(p, "exp"),
        "parHash": ph,
        "selfHash": b64u(hashlib.sha256(msg).digest()),
        "sigBy": sig_by,
    }


def strfield(p, k):
    x = p.get(k)
    return x if isinstance(x, str) else ""


def pop_of(v, candidates, args_pairs):
    pop = v.get("pop")
    if not pop:
        raise OutOfScope("no PoP JWT")
    p, msg, sig = jws(pop)
    if not isinstance(p.get("iat"), int) or isinstance(p.get("iat"), bool):
        raise OutOfScope("precondition: PoP iat is not a NumericDate (parsing, 7c)")
    hta = p.get("hta")
    hta = [[k, value(x)] for k, x in hta.items()] if isinstance(hta, dict) else None
    aud = p["aat_aud"] if isinstance(p.get("aat_aud"), str) else ("" if "aat_aud" in p else None)
    nonce = p["nonce"] if isinstance(p.get("nonce"), str) else ("" if "nonce" in p else None)
    sig_by = signed_by(candidates, msg, sig)
    return {"jti": strfield(p, "jti"), "aatId": strfield(p, "aat_id"), "aatHash": strfield(p, "aat_hash"),
            "aatTool": strfield(p, "aat_tool"), "iat": p["iat"], "hta": hta, "aatAud": aud,
            "nonce": nonce, "sigBy": sig_by}


def decode(suite):
    anchors = [{"iss": a["iss"], "key": thumbprint_uri(a["jwk"])} for a in suite["trust_anchors"]]
    known = [k["jwk"] for k in suite["keys"].values()] + [a["jwk"] for a in suite["trust_anchors"]]
    out = []
    for v in suite["vectors"]:
        exp = v["expected"]
        rec = {"id": v["id"], "expected": exp["verdict"], "step": exp.get("step"), "title": v["title"]}
        modeled = exp["verdict"] == "PERMIT" or exp.get("step") in MODELED_STEPS
        try:
            if not modeled:
                raise OutOfScope(f"expected step {exp.get('step')} not modeled")
            params = dict(suite["params"]); params.update(v.get("params") or {})
            now = v.get("now", params["now"])
            args = load_args(v["args_json"])
            chain, cands = [], list(known)
            for t in v["chain"]:
                l = link(t, cands)
                cands = cands + [jws(t)[0]["cnf"]["jwk"]]
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
                           "maxConstraintDepth": params["max_constraint_depth"]},
                "anchors": anchors,
                "chain": chain,
                "call": {"tool": v["tool"], "args": [[k, value(x)] for k, x in args]},
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


def main():
    suite = json.load(open(sys.argv[1]))
    recs = decode(suite)
    with open(sys.argv[2], "w") as f:
        json.dump(recs, f, indent=1, ensure_ascii=False)
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
