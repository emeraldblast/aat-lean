"""Shrink a disagreement to a smaller reproducible vector (greedy, not necessarily minimal).

Given a vector on which the implementation and the Lean model disagree, try
smaller variants (fewer links, tools, constraint entries, list members and call
arguments; constraints replaced by `wildcard`) and keep a variant whenever the
same disagreement (model verdict, implementation verdict) survives. Variants are
re-signed with each token's original signer, so a deliberate fault (wrong
signer, wrong `par_hash`, wrong PoP binding) is kept as it was: a `par_hash` or
`aat_hash` that named the real parent / leaf is recomputed, any other value is
left unchanged.

Used by conformance/check.py (--shrink); standalone:
    python3 -I conformance/shrink.py SUITE.json VECTOR_ID --impl "COMMAND" OUT.json
"""
import copy
import json
import pathlib
import sys


sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import mint  # noqa: E402

MAX_ROUNDS = 40


def _hash(tok):
    return tok["signing_input_sha256_b64u"]


def rebuild(suite, v, payloads, pop_payload, n=None):
    """Re-sign a vector from edited payloads, keeping the original signers and
    the original binding pattern (par_hash / aat_hash / aat_id)."""
    keys = suite["keys"]
    old = v["chain"]
    n = len(payloads) if n is None else n
    chain = []
    for i in range(n):
        p = copy.deepcopy(payloads[i])
        if i > 0 and old[i]["payload"].get("par_hash") == _hash(old[i - 1]):
            p["par_hash"] = _hash(chain[i - 1])
        signer = old[i]["signer"]
        chain.append(mint.jws(old[i]["header"], p, keys[signer]["seed_hex"], signer))
    pop_old = v["pop"]
    q = copy.deepcopy(pop_payload)
    leaf_old, leaf = old[-1], chain[-1]
    if pop_old["payload"].get("aat_hash") == _hash(leaf_old):
        q["aat_hash"] = _hash(leaf)
    if pop_old["payload"].get("aat_id") == leaf_old["payload"].get("jti"):
        q["aat_id"] = leaf["payload"].get("jti")
    pop_signer = pop_old["signer"]
    # the PoP was signed by the old leaf's holder: the new leaf's holder signs it
    holder = {json.dumps(k["jwk"], sort_keys=True): name for name, k in keys.items()}
    if pop_signer == holder.get(json.dumps(leaf_old["payload"]["cnf"]["jwk"], sort_keys=True)):
        pop_signer = holder.get(json.dumps(leaf["payload"]["cnf"]["jwk"], sort_keys=True), pop_signer)
    pop = mint.jws(pop_old["header"], q, keys[pop_signer]["seed_hex"], pop_signer)
    w = copy.deepcopy(v)
    w["chain"], w["pop"] = chain, pop
    w["chain_compact"] = [t["compact"] for t in chain]
    w["presentation"] = {"aat_chain": w["chain_compact"], "aat_pop": pop["compact"]}
    return w


def _tools(p):
    for e in p.get("authorization_details", []):
        if isinstance(e, dict) and e.get("type") == "attenuating_agent_token" and isinstance(e.get("tools"), dict):
            return e["tools"]
    return None


LISTS = ("values", "excluded", "required", "allowed", "constraints")


def _constraint_edits(c):
    """Smaller variants of one constraint."""
    if not isinstance(c, dict):
        return
    if c.get("constraint_type") != "wildcard":
        w = {"constraint_type": "wildcard"}
        if "optional" in c:
            w["optional"] = c["optional"]
        yield w
    if "optional" in c:
        d = dict(c); d.pop("optional"); yield d
    for k in LISTS:
        if isinstance(c.get(k), list) and len(c[k]) > 1:
            for j in range(len(c[k])):
                d = copy.deepcopy(c); d[k].pop(j); yield d
    if isinstance(c.get("constraints"), list):
        for j, sub in enumerate(c["constraints"]):
            for e in _constraint_edits(sub):
                d = copy.deepcopy(c); d["constraints"][j] = e; yield d


def candidates(v):
    """(description, payloads, pop_payload, n_links, args) for smaller variants."""
    payloads = [t["payload"] for t in v["chain"]]
    pop = v["pop"]["payload"]
    args = v["args"] if isinstance(v.get("args"), dict) else None
    n = len(payloads)
    for k in range(1, n):
        yield f"keep first {k} link(s)", payloads[:k], pop, k, args
    for i, p in enumerate(payloads):
        tools = _tools(p)
        if tools is None:
            continue
        for t in list(tools):
            if len(tools) > 1:
                q = copy.deepcopy(payloads); del _tools(q[i])[t]
                yield f"link {i}: drop tool {t}", q, pop, n, args
            m = tools[t]
            if not isinstance(m, dict):
                continue
            for a in list(m):
                q = copy.deepcopy(payloads); del _tools(q[i])[t][a]
                yield f"link {i}: drop {t}.{a}", q, pop, n, args
                for e in _constraint_edits(m[a]):
                    q = copy.deepcopy(payloads); _tools(q[i])[t][a] = e
                    yield f"link {i}: simplify {t}.{a}", q, pop, n, args
        if "aud" in p:
            q = copy.deepcopy(payloads); del q[i]["aud"]
            yield f"link {i}: drop aud", q, pop, n, args
    if args:
        for a in list(args):
            new = {k: x for k, x in args.items() if k != a}
            q = dict(pop)
            if pop.get("hta") == args:
                q["hta"] = new
            yield f"call: drop argument {a}", payloads, q, n, new


def variant(suite, v, cand):
    desc, payloads, pop, n, args = cand
    w = rebuild(suite, v, payloads, pop, n)
    if args is not v.get("args") and args is not None:
        if v.get("args_json") != mint.compact_json(v["args"]):
            return None  # hand-written args_json (e.g. duplicate names): keep the call as is
        w["args"], w["args_json"] = args, mint.compact_json(args)
    w["id"] = f"{v['id']}~{desc}"
    return w


def size(v):
    return sum(len(t["payload_json"]) for t in v["chain"]) + len(v["pop"]["payload_json"]) + len(v["args_json"])


def shrink(suite, v, judge, log=print):
    """judge(suite, vectors) -> {id: (model verdict, impl verdict)}. Returns the
    smallest vector found with the same pair as `v`, and the steps taken."""
    target = judge(suite, [v]).get(v["id"])
    steps = []
    if target is None:
        # the original disagreement does not reproduce cleanly: nothing to shrink against
        return v, None, steps
    for _ in range(MAX_ROUNDS):
        ws = []
        for c in candidates(v):
            try:
                w = variant(suite, v, c)
            except (KeyError, TypeError, ValueError):
                w = None
            if w is not None and size(w) < size(v):
                ws.append(w)
        if not ws:
            break
        got = judge(suite, ws)
        keep = [w for w in ws if got.get(w["id"]) is not None and got[w["id"]] == target]
        if not keep:
            break
        best = min(keep, key=size)
        steps.append(best["id"].split("~", 1)[1])
        log(f"  shrink {v['id'].split('~')[0]}: {best['id'].split('~', 1)[1]} ({size(v)} -> {size(best)} bytes)")
        best = dict(best, id=v["id"].split("~")[0])
        v = best
    return v, target, steps


def main():
    import argparse
    import check
    ap = argparse.ArgumentParser()
    ap.add_argument("suite"); ap.add_argument("vector_id"); ap.add_argument("out")
    ap.add_argument("--impl", required=True)
    a = ap.parse_args()
    suite = json.load(open(a.suite))
    v = next(x for x in suite["vectors"] if x["id"] == a.vector_id)
    small, target, steps = shrink(suite, v, check.judge(a.impl))
    out = {k: suite[k] for k in suite if k != "vectors"}
    out["vectors"] = [small]
    json.dump(out, open(a.out, "w"), indent=1, ensure_ascii=False)
    print(f"{a.vector_id}: model {target[0]}, implementation {target[1]}; "
          f"{len(steps)} step(s), {size(v)} -> {size(small)} bytes -> {a.out}")


if __name__ == "__main__":
    main()
