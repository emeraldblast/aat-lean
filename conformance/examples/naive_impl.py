"""TEST FIXTURE ONLY: a naive AAT-02 verifier with three deliberate bugs, to show what
the conformance report finds. Not a reference implementation.

  BUG 1  range bounds are always treated as inclusive (min_inclusive / max_inclusive ignored)
  BUG 2  par_hash is not checked (step 4q)
  BUG 3  chain aud is not checked (step 6c)

Speaks the conformance JSON-lines protocol (see conformance/check.py).
"""
import json
import pathlib
import sys
from fractions import Fraction

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "vectors"))
import decode  # noqa: E402  (base64, signature check, thumbprints, constraint maps)


class Malformed(Exception):
    """The presentation is malformed: the verifier denies."""


# ---------- parsing: the decoder hands over JSON as written; this verifier parses it itself ----------

def no_dup(j):
    if "o" in j:
        ks = [k for k, _ in j["o"]]
        return len(ks) == len(set(ks)) and all(no_dup(v) for _, v in j["o"])
    if "a" in j:
        return all(no_dup(e) for e in j["a"])
    return True


def py(j):
    """JSON tree -> Python; numbers: int only for integer literals, else a float marker."""
    if "o" in j: return {k: py(v) for k, v in j["o"]}
    if "a" in j: return [py(e) for e in j["a"]]
    if "n" in j: return int(j["n"]) if not any(c in j["n"] for c in ".eE") else ("float", j["n"])
    if "s" in j: return j["s"]
    if "b" in j: return j["b"]
    return None


def is_int(x): return isinstance(x, int) and not isinstance(x, bool)


def header_ok(h, typ):
    if not no_dup(h): return False
    h = py(h)
    return isinstance(h, dict) and h.get("alg") == "Ed25519" and h.get("typ") == typ and "crit" not in h


def jwk_ok(j):
    x = j.get("x") if isinstance(j, dict) else None
    return (isinstance(j, dict) and j.get("kty") == "OKP" and j.get("crv") == "Ed25519" and "d" not in j
            and isinstance(x, str) and len(x) == 43 and all(c.isalnum() or c in "-_" for c in x))


def aat_tools(ad):
    if not isinstance(ad, list): return None
    es = [e for e in ad if isinstance(e, dict) and e.get("type") == "attenuating_agent_token"]
    if len(es) != 1 or not isinstance(es[0].get("tools"), dict): return None
    if not all(isinstance(m, dict) for m in es[0]["tools"].values()): return None
    return list(es[0]["tools"])


def is_uri(x):
    """3k: RFC 3986 scheme, then ':', and only URI characters."""
    ok = set("-._~:/?#[]@!$&'()*+,;=%")
    if not x or not all(c.isascii() and (c.isalnum() or c in ok) for c in x): return False
    i = x.find(":")
    return i > 0 and x[0].isalpha() and all(c.isalnum() or c in "+-." for c in x[1:i])


def parse_link(t, root):
    if not no_dup(t["payload"]): raise Malformed("duplicate names")
    p = py(t["payload"])
    if not isinstance(p.get("jti"), str) or not p["jti"]: raise Malformed("jti")
    if not jwk_ok((p.get("cnf") or {}).get("jwk") if isinstance(p.get("cnf"), dict) else None):
        raise Malformed("cnf.jwk")
    names = aat_tools(p.get("authorization_details"))
    maps = dict(t["maps"])
    if names is None or any(n not in maps for n in names): raise Malformed("authorization_details")
    for k in ("iat", "exp", "del_depth", "del_max_depth"):
        if not is_int(p.get(k)): raise Malformed(k)
    if p["del_depth"] < 0 or p["del_max_depth"] < 0: raise Malformed("depth")
    if not isinstance(p.get("iss"), str): raise Malformed("iss")
    if root and not is_uri(p["iss"]): raise Malformed("iss is not a URI")
    if not root and not isinstance(p.get("par_hash"), str): raise Malformed("par_hash")
    if not isinstance(t.get("thumb"), str): raise Malformed("thumb")
    return {"issuer": p["iss"], "holder": t["thumb"], "tools": [[n, maps[n]] for n in names], "jti": p["jti"],
            "delDepth": p["del_depth"], "delMaxDepth": p["del_max_depth"], "iat": p["iat"], "exp": p["exp"],
            "parHash": p.get("par_hash") if "par_hash" in p else None, "selfHash": t["selfHash"],
            "sigBy": t["sigBy"]}


def parse_pop(q):
    if not no_dup(q["payload"]): raise Malformed("PoP duplicate names")
    p = py(q["payload"])
    if not is_int(p.get("iat")): raise Malformed("PoP iat")
    s = lambda k: p[k] if isinstance(p.get(k), str) else ""
    opt = lambda k: (p[k] if isinstance(p[k], str) else "") if k in p else None
    return {"sigBy": q["sigBy"], "jti": s("jti"), "aatId": s("aat_id"), "aatHash": s("aat_hash"),
            "aatTool": s("aat_tool"), "iat": p["iat"], "aatAud": opt("aat_aud"), "nonce": opt("nonce"),
            "hta": q["hta"] if isinstance(p.get("hta"), dict) else None}


def num(v):
    return Fraction(v["num"]["n"], v["num"]["d"])


def eq(a, b):
    if "num" in a and "num" in b:
        return num(a) == num(b)
    return a == b


def contains(xs, x):
    return any(eq(e, x) for e in xs)


def check(c, x):
    if "wildcard" in c: return True
    if "malformed" in c: return False
    if "exact" in c: return eq(x, c["exact"])
    if "oneOf" in c: return contains(c["oneOf"], x)
    if "notOneOf" in c: return not contains(c["notOneOf"], x)
    if "range" in c:
        if "num" not in x: return False
        lo, hi, v = c["range"]["lo"], c["range"]["hi"], num(x)
        # BUG 1: inclusive flags ignored
        return (lo is None or Fraction(lo["val"]["n"], lo["val"]["d"]) <= v) and \
               (hi is None or v <= Fraction(hi["val"]["n"], hi["val"]["d"]))
    if "contains" in c:
        return "arr" in x and all(contains(x["arr"], e) for e in c["contains"])
    if "subset" in c:
        return "arr" in x and all(contains(c["subset"], e) for e in x["arr"])
    if "all" in c: return all(check(d, x) for d in c["all"])
    if "any" in c: return any(check(d, x) for d in c["any"])
    return False


def bval(b): return Fraction(b["val"]["n"], b["val"]["d"])


def subsumes(p, c):
    if "wildcard" in p: return True
    if "exact" in p: return "exact" in c and eq(c["exact"], p["exact"])
    if "range" in p:
        if "range" in c:
            return (tighter(p["range"]["lo"], c["range"]["lo"], True)
                    and tighter(p["range"]["hi"], c["range"]["hi"], False))
        return "exact" in c and "num" in c["exact"] and check(p, c["exact"])
    if "oneOf" in p:
        if "oneOf" in c: return bool(c["oneOf"]) and all(contains(p["oneOf"], e) for e in c["oneOf"])
        return "exact" in c and contains(p["oneOf"], c["exact"])
    if "notOneOf" in p: return "notOneOf" in c and all(contains(c["notOneOf"], e) for e in p["notOneOf"])
    if "contains" in p: return "contains" in c and all(contains(c["contains"], e) for e in p["contains"])
    if "subset" in p: return "subset" in c and all(contains(p["subset"], e) for e in c["subset"])
    if "all" in p: return "all" in c and all(any(subsumes(pc, dc) for dc in c["all"]) for pc in p["all"])
    if "any" in p: return "any" in c and all(any(subsumes(pc, dc) for pc in p["any"]) for dc in c["any"])
    return False


def tighter(p, c, lower):
    if p is None: return True
    if c is None: return False
    pv, cv = bval(p), bval(c)
    return (pv <= cv) if lower else (cv <= pv)   # BUG 1: an inclusive child bound under an exclusive parent passes


def wf(n, c):
    if n == 0 or "malformed" in c: return False
    if "oneOf" in c: return bool(c["oneOf"])
    if "range" in c:
        lo, hi = c["range"]["lo"], c["range"]["hi"]
        return lo is None or hi is None or bval(lo) <= bval(hi)
    if "all" in c or "any" in c:
        cs = c.get("all", c.get("any"))
        return bool(cs) and all(wf(n - 1, d) for d in cs)
    return True


def norm(m):
    return {"named": m["named"], "star": True} if not m["named"] and not m["star"] else m


def get(m, k):
    for kk, e in m["named"]:
        if kk == k: return e
    return None


def permits_args(m, args):
    for k, v in args:
        e = get(m, k)
        if (e is not None and not check(e["c"], v)) or (e is None and not m["star"]): return False
    return all(get(m, k)["optional"] or any(a == k for a, _ in args) for k, _ in m["named"])


def narrows_map(p, c):
    for k, ce in c["named"]:
        pe = get(p, k)
        if pe is None and not p["star"]: return False
        if pe is not None and not pe["optional"] and ce["optional"]: return False
        if not subsumes(pe["c"] if pe else {"wildcard": True}, ce["c"]): return False
    for k, pe in p["named"]:
        if get(c, k) is None and not (pe["optional"] and not c["star"]): return False
    return not c["star"] or p["star"]


def tool(link, t):
    for tt, m in link["tools"]:
        if tt == t: return m
    return None


def narrows(p, c):
    return all(tool(p, t) is not None and narrows_map(norm(tool(p, t)), norm(m)) for t, m in c["tools"])


def verify(P, anchors, chain):
    if not chain: return False
    if not all(wf(P["maxConstraintDepth"], e["c"]) for l in chain for _, m in l["tools"] for _, e in m["named"]):
        return False
    if len({l["jti"] for l in chain}) != len(chain): return False
    r = chain[0]
    if not (any(a["iss"] == r["issuer"] and a["key"] in r["sigBy"] for a in anchors) and r["delDepth"] == 0
            and r["parHash"] is None and P["now"] < r["exp"] and r["iat"] <= P["now"] + P["maxIatSkew"]
            and r["iat"] < r["exp"] and r["exp"] <= r["iat"] + P["maxTokenLifetime"]
            and r["delMaxDepth"] <= P["maxDelegationDepth"]):
        return False
    for p, c in zip(chain, chain[1:]):
        if not (p["holder"] in c["sigBy"] and c["issuer"] == p["holder"] and c["delDepth"] == p["delDepth"] + 1
                and c["delMaxDepth"] <= p["delMaxDepth"] and c["exp"] <= p["exp"] and P["now"] < c["exp"]
                and p["iat"] <= c["iat"] and c["iat"] <= P["now"] + P["maxIatSkew"] and c["iat"] < c["exp"]
                and c["delDepth"] <= c["delMaxDepth"] and narrows(p, c)):
            return False
        # BUG 2: c["parHash"] == p["selfHash"] is not checked
    return len(chain) == chain[-1]["delDepth"] + 1


def invoke(x):
    P, E, raw, call = x["params"], x["endpoint"], x["chain"], x["call"]
    sizes = [t["size"] for t in raw]
    if any(n > P["maxTokenSize"] for n in sizes) or sum(sizes) > P["maxChainSize"]: return False
    if not all(header_ok(t["header"], "aat+jwt") for t in raw) or not header_ok(x["pop"]["header"], "aat-pop+jwt"):
        return False
    try:
        chain = [parse_link(t, i == 0) for i, t in enumerate(raw)]
        pop = parse_pop(x["pop"])
    except Malformed:
        return False
    if not verify(P, x["anchors"], chain): return False
    leaf, args = chain[-1], call["args"]
    if len({k for k, _ in args}) != len(args): return False
    m = tool(leaf, call["tool"])
    if m is None or not permits_args(norm(m), args): return False
    # BUG 3: chain aud (step 6c) is not checked
    if not (leaf["holder"] in pop["sigBy"] and pop["jti"] and pop["aatId"] == leaf["jti"]
            and pop["aatHash"] == leaf["selfHash"] and pop["aatTool"] == call["tool"]): return False
    if pop["aatAud"] is not None and pop["aatAud"] != E["audience"]: return False
    if pop["aatAud"] is None and E["requirePopAud"]: return False
    h = pop["hta"]
    if h is None or len(h) != len(args) or not all(any(k == a and eq(v, w) for a, w in args) for k, v in h):
        return False
    if not (P["now"] - E["popWindow"] <= pop["iat"] <= P["now"] + E["popWindow"]): return False
    if E["nonce"] is not None and pop["nonce"] != E["nonce"]: return False
    if E["trackJti"] and pop["jti"] in x["seen"]: return False
    return True


def main():
    for line in sys.stdin:
        if not line.strip(): continue
        req = json.loads(line)
        suite = {"params": req["params"], "trust_anchors": req["trust_anchors"], "keys": {}, "vectors": [req["vector"]]}
        # only a stated precondition of the decoder (byte level, inadmissible numbers) denies here;
        # any other exception is a bug in this fixture and must crash it, not turn into DENY
        rec = decode.decode(suite)[0]
        if rec["scope"] == "error":
            raise SystemExit(f"decoder error on {req['id']}: {rec['reason']}")
        ok = rec["scope"] == "in" and invoke(rec["input"])
        print(json.dumps({"id": req["id"], "verdict": "PERMIT" if ok else "DENY"}), flush=True)


if __name__ == "__main__":
    decode.deep(main)  # payload trees may nest deeply
