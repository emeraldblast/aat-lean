"""Decode the AAT-02 vector suite into the Lean model's input format.

The model treats signatures and SHA-256 as ideal (assumptions 1, 5). This
decoder computes, for each token, the set of keys under which its Ed25519
signature actually verifies (OpenSSL), and the SHA-256 of its JWS Signing
Input; the model consumes those. Keys are identified by their JWK thumbprint
URI (RFC 7638 / 9278). For each vector we extract, losslessly:
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
    "4p1", "4p2", "4p3", "4p4", "4q",
    "5", "6b",
}
FIRST_PASS = {"wildcard", "exact", "one_of", "range"}


class OutOfScope(Exception):
    pass


def _no_dups(pairs):
    keys = [k for k, _ in pairs]
    if len(keys) != len(set(keys)):
        raise OutOfScope("precondition: duplicate JSON member names in claims (assumption 7)")
    return dict(pairs)


def loads(s):
    return json.loads(s, parse_float=Decimal, parse_int=int, object_pairs_hook=_no_dups)


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


def value(x):
    if isinstance(x, bool):
        return {"bool": x}
    if x is None:
        return {"null": True}
    if isinstance(x, (int, Decimal)):
        check_admissible(x)
        return {"num": num(x)}
    if isinstance(x, str):
        return {"str": x}
    check_admissible(x)
    return {"compound": jcs(x)}


def bound(c, side):
    if side not in c:
        return None
    return {"val": num(c[side]), "incl": bool(c.get(side + "_inclusive", True))}


def constraint(c):
    t = c.get("constraint_type")
    if t not in FIRST_PASS:
        raise OutOfScope(f"constraint type {t}")
    if t == "wildcard":
        return {"wildcard": True}
    if t == "exact":
        return {"exact": value(c["value"])}
    if t == "one_of":
        return {"oneOf": [value(v) for v in c["values"]]}
    return {"range": {"lo": bound(c, "min"), "hi": bound(c, "max")}}


def cmap(m):
    if not isinstance(m, dict):
        raise OutOfScope("constraint map is not an object")
    named, star = [], False
    for k, entry in m.items():
        if k == "*":
            if entry.get("constraint_type") != "wildcard":
                raise OutOfScope("'*' is not a wildcard")
            star = True
            continue
        named.append([k, {"c": constraint(entry), "optional": bool(entry.get("optional", False))}])
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
    x = p[k]
    if isinstance(x, bool) or not isinstance(x, int):
        raise OutOfScope(f"precondition: {k} is not an integer (parsing, 3b/4b)")
    return x


def link(token, candidates):
    p = loads(token["payload_json"])
    entries = [e for e in p.get("authorization_details", []) if e.get("type") == "attenuating_agent_token"]
    if len(entries) != 1:
        raise OutOfScope("not exactly one attenuating_agent_token entry")
    tools = entries[0].get("tools")
    if not isinstance(tools, dict):
        raise OutOfScope("tools is not an object")
    if not isinstance(p.get("jti"), str):
        raise OutOfScope("precondition: jti missing (3j/4b1)")
    jwk = p["cnf"]["jwk"]
    msg = token["signing_input"].encode()
    sig = ed25519.b64u_decode(token["signature_b64"])
    sig_by = sorted({thumbprint_uri(k) for k in candidates + [jwk]
                     if k.get("kty") == "OKP" and ed25519.verify(k["x"], msg, sig)})
    ph = p.get("par_hash")
    return {
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
            # keep duplicate top-level argument names: step 6b must see them
            args = json.loads(v["args_json"], parse_float=Decimal, parse_int=int,
                              object_pairs_hook=lambda kv: kv)
            args = [(k, x if not isinstance(x, list) or not x or not isinstance(x[0], tuple)
                     else dict(x)) for k, x in args]
            chain, cands = [], list(known)
            for t in v["chain"]:
                l = link(t, cands)
                cands = cands + [loads(t["payload_json"])["cnf"]["jwk"]]
                chain.append(l)
            rec["input"] = {
                "params": {"now": now, "maxIatSkew": params["max_iat_skew"],
                           "maxTokenLifetime": params["max_token_lifetime"],
                           "maxDelegationDepth": params["max_delegation_depth"]},
                "anchors": anchors,
                "chain": chain,
                "call": {"tool": v["tool"], "args": [[k, value(x)] for k, x in args]},
            }
            rec["scope"] = "in"
        except OutOfScope as e:
            rec["scope"] = "out"
            rec["reason"] = str(e)
        except (KeyError, TypeError, ValueError, AttributeError) as e:
            rec["scope"] = "out"
            rec["reason"] = f"undecodable: {type(e).__name__}"
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
    for r in recs:
        if r["scope"] == "out":
            key = r["reason"].split(":")[0] if r["reason"].startswith("undecodable") else r["reason"]
            reasons[key] = reasons.get(key, 0) + 1
    for k, n in sorted(reasons.items(), key=lambda kv: -kv[1])[:15]:
        print(f"  out: {n:3d}  {k}")


if __name__ == "__main__":
    main()
