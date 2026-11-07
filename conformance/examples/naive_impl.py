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
import decode  # noqa: E402  (token parsing, signature check, thumbprints)


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
    P, E, chain, call, pop = x["params"], x["endpoint"], x["chain"], x["call"], x["pop"]
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
        try:
            rec = decode.decode(suite)[0]
            ok = rec["scope"] == "in" and invoke(rec["input"])
        except Exception:
            ok = False
        print(json.dumps({"id": req["id"], "verdict": "PERMIT" if ok else "DENY"}), flush=True)


if __name__ == "__main__":
    main()
