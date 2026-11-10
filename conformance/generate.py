"""Generate signed AAT-02 chains beyond the author's suite.

Chains of 1..MAX_DELEGATION_DEPTH+1 tokens (9 with the suite's parameters) over all
nine constraint types: children usually narrow
their parent, sometimes deliberately widen it; one mutation per vector breaks a
§8 step (signature, par_hash, depth, time, jti, aud, PoP) or the call. The
generator does not decide the verdict: the Lean model does (conformance/check.py).
Output uses the upstream suite's schema, so vectors/decode.py reads it as is.

    python3 -I conformance/generate.py SEED COUNT OUT.json
"""
import copy
import hashlib
import json
import pathlib
import random
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import mint  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
SUITE = json.load(open(ROOT / "vectors/upstream/aat-jws-vectors.json"))
KEYS = SUITE["keys"]
ANCHOR_ISS = SUITE["trust_anchors"][0]["iss"]   # key: control_plane
# Holder keys cycle along the chain: a key may hold several tokens of one chain
# (notes to §8), but never its own parent's token.
CYCLE = ["orchestrator", "worker", "worker2"]


def holders_for(n):
    return [CYCLE[i % len(CYCLE)] for i in range(n)]
TOOLS = ["read_file", "search_index", "pay"]
ARGS = ["path", "query", "limit", "amount", "tags"]
STRS = ["a", "b", "c", "d", "/data/q3.pdf", "/data/q4.pdf"]
HDR = {"alg": "Ed25519", "typ": "aat+jwt"}
POP_HDR = {"alg": "Ed25519", "typ": "aat-pop+jwt"}
P = SUITE["params"]
MAXD = P["max_delegation_depth"]
NOW = P["now"]

MUTATIONS = [
    None, None, None, None,              # most vectors: only random narrowing/widening
    "child-widens-tool", "child-widens-constraint", "child-adds-arg", "child-adds-star",
    "child-drops-required", "required-to-optional",
    "sig-attacker", "root-sig-attacker", "iss-mismatch", "par-hash-wrong", "par-hash-other-parent",
    "depth-skip", "max-depth-raised", "root-depth-1", "dup-jti",
    "child-outlives-parent", "expired", "iat-future", "child-iat-before-parent",
    "aud-other", "pop-tool", "pop-hta", "pop-sig-attacker", "pop-iat-old", "pop-aat-id",
    "call-violates", "call-unknown-tool", "call-extra-arg", "call-missing-arg", "call-dup-arg",
    "range-edge-child", "call-at-exclusive-bound", "chain-too-deep",
]

# exclusive-bound edge cases: what a verifier that ignores min_inclusive/max_inclusive gets wrong
EDGE_PARENT = {"pay": {"amount": {"constraint_type": "range", "min": 10, "max": 100,
                                  "min_inclusive": False, "max_inclusive": False}}}


# ---------- constraints ----------

def rnd_value(r):
    return r.choice([r.choice(STRS), r.randint(0, 200), round(r.uniform(0, 100), 1)])


def rnd_constraint(r, depth=0):
    t = r.choice(["wildcard", "exact", "one_of", "not_one_of", "range", "contains", "subset"]
                 + (["all", "any"] if depth < 2 else []))
    if t == "wildcard":
        return {"constraint_type": "wildcard"}
    if t == "exact":
        return {"constraint_type": "exact", "value": rnd_value(r)}
    if t in ("one_of", "not_one_of"):
        k = "values" if t == "one_of" else "excluded"
        return {"constraint_type": t, k: r.sample(STRS, r.randint(1, 4))}
    if t == "range":
        lo = r.randint(0, 50); c = {"constraint_type": "range"}
        if r.random() < 0.8: c["min"] = lo
        if r.random() < 0.8: c["max"] = lo + r.randint(0, 150)
        if "min" in c and r.random() < 0.3: c["min_inclusive"] = False
        if "max" in c and r.random() < 0.3: c["max_inclusive"] = False
        return c
    if t in ("contains", "subset"):
        k = "required" if t == "contains" else "allowed"
        return {"constraint_type": t, k: r.sample(STRS[:4], r.randint(1, 3))}
    return {"constraint_type": t, "constraints": [rnd_constraint(r, depth + 1) for _ in range(r.randint(1, 3))]}


def narrow(r, c):
    """A child constraint that Table 4 accepts under c (most of the time)."""
    t = c["constraint_type"]
    if t == "wildcard":
        return rnd_constraint(r)
    if t == "exact":
        return copy.deepcopy(c)
    if t == "one_of":
        vs = c["values"]
        return ({"constraint_type": "exact", "value": r.choice(vs)} if r.random() < 0.3
                else {"constraint_type": "one_of", "values": r.sample(vs, r.randint(1, len(vs)))})
    if t == "not_one_of":
        return {"constraint_type": "not_one_of", "excluded": sorted(set(c["excluded"]) | set(r.sample(STRS, 1)))}
    if t == "range":
        d = copy.deepcopy(c)
        if "min" in d and r.random() < 0.5: d["min"] += r.randint(0, 5)
        if "max" in d and r.random() < 0.5: d["max"] -= r.randint(0, 5)
        if r.random() < 0.2 and "min" in c and "max" in c and c["max"] >= c["min"] + 2:
            return {"constraint_type": "exact", "value": c["min"] + 1}
        if "min" in d and "max" in d and d["min"] > d["max"]:
            d["max"] = d["min"]
        return d
    if t == "contains":
        return {"constraint_type": "contains", "required": sorted(set(c["required"]) | set(r.sample(STRS[:4], 1)))}
    if t == "subset":
        al = c["allowed"]
        return {"constraint_type": "subset", "allowed": r.sample(al, r.randint(1, len(al)))}
    if t == "all":
        return {"constraint_type": "all", "constraints": [narrow(r, x) for x in c["constraints"]]}
    cs = c["constraints"]
    return {"constraint_type": "any", "constraints": [narrow(r, x) for x in r.sample(cs, r.randint(1, len(cs)))]}


def widen(r, c):
    """A child constraint that is usually NOT a valid narrowing of c."""
    t = c["constraint_type"]
    if t == "one_of":
        return {"constraint_type": "one_of", "values": c["values"] + [x for x in STRS if x not in c["values"]][:1]}
    if t == "range" and "max" in c:
        d = copy.deepcopy(c); d["max"] += r.randint(1, 50); return d
    if t == "range" and "min" in c:
        d = copy.deepcopy(c); d["min"] -= r.randint(1, 50); return d
    if t == "subset":
        return {"constraint_type": "subset", "allowed": sorted(set(c["allowed"]) | set(STRS[:4]))}
    if t == "contains" and len(c["required"]) > 1:
        return {"constraint_type": "contains", "required": c["required"][:-1]}
    if t == "not_one_of" and len(c["excluded"]) > 1:
        return {"constraint_type": "not_one_of", "excluded": c["excluded"][:-1]}
    return {"constraint_type": "wildcard"} if t != "wildcard" else {"constraint_type": "exact", "value": "a"}


def rnd_map(r):
    m = {}
    for a in r.sample(ARGS, r.randint(0, 3)):
        e = rnd_constraint(r)
        if r.random() < 0.25: e["optional"] = True
        m[a] = e
    if r.random() < 0.25: m["*"] = {"constraint_type": "wildcard"}
    return m


def narrow_map(r, pm):
    pm = pm or {"*": {"constraint_type": "wildcard"}}
    star = "*" in pm
    cm = {}
    for k, e in pm.items():
        if k == "*": continue
        if e.get("optional") and not star and r.random() < 0.2:
            continue  # omitted optional argument becomes forbidden
        ce = narrow(r, {kk: vv for kk, vv in e.items() if kk != "optional"})
        if e.get("optional") and r.random() < 0.6: ce["optional"] = True
        cm[k] = ce
    if star:
        if r.random() < 0.3:
            extra = [a for a in ARGS if a not in cm]
            if extra: cm[r.choice(extra)] = rnd_constraint(r)
        if r.random() < 0.6: cm["*"] = {"constraint_type": "wildcard"}
    return cm


def rnd_args(r, m):
    args = {}
    for k, e in (m or {}).items():
        if k == "*": continue
        if e.get("optional") and r.random() < 0.4: continue
        args[k] = sample_value(r, e)
    if (not m or "*" in m) and r.random() < 0.3:
        args.setdefault("extra", r.choice(STRS))
    return args


def sample_value(r, c):
    """A value that usually satisfies c."""
    t = c["constraint_type"]
    if t == "exact": return c["value"]
    if t == "one_of": return r.choice(c["values"])
    if t == "not_one_of": return r.choice([x for x in STRS if x not in c["excluded"]] or ["z"])
    if t == "range":
        lo = c.get("min", 0) + (1 if not c.get("min_inclusive", True) else 0)
        hi = c.get("max", lo + 100) - (1 if not c.get("max_inclusive", True) else 0)
        return r.randint(int(lo), int(max(lo, hi)))
    if t == "contains": return sorted(set(c["required"]) | set(r.sample(STRS[:4], r.randint(0, 2))))
    if t == "subset": return r.sample(c["allowed"], r.randint(0, len(c["allowed"])))
    if t == "all":
        return sample_value(r, c["constraints"][0])
    if t == "any":
        return sample_value(r, r.choice(c["constraints"]))
    return rnd_value(r)


# ---------- tokens ----------

def jti(seed, n):
    return f"019471f8-0000-7000-8000-{hashlib.sha256(f'{seed}-{n}'.encode()).hexdigest()[:12]}"


def aat(tools):
    return [{"type": "attenuating_agent_token", "tools": tools}]


def build(r, seed, n_links, mutation):
    holders = holders_for(n_links)
    # del_max_depth: non-increasing (4g), never below the leaf depth (4m, step 5), at most MAX (3i)
    floor = min(max(n_links - 1, 3), MAXD)
    dmds = [r.randint(floor, MAXD)]
    for _ in range(1, n_links):
        dmds.append(r.randint(floor, dmds[-1]))
    root_tools = ({t: rnd_map(r) for t in r.sample(TOOLS, r.randint(1, 3))}
                  if mutation not in ("range-edge-child", "call-at-exclusive-bound") else copy.deepcopy(EDGE_PARENT))
    toolsets = [root_tools]
    for _ in range(1, n_links):
        parent = toolsets[-1]
        child = {}
        for t, pm in parent.items():
            if r.random() < 0.2 and len(parent) > 1: continue
            child[t] = narrow_map(r, pm)
        if not child: child = {next(iter(parent)): narrow_map(r, next(iter(parent.values())))}
        toolsets.append(child)
    if mutation == "range-edge-child":
        # same bound, inclusive under an exclusive parent: widens by exactly one value
        side = r.choice(["min", "max"])
        toolsets[-1] = {"pay": {"amount": {"constraint_type": "range", "min": 10, "max": 100,
                                           "min_inclusive": side != "min", "max_inclusive": side != "max"}}}
    li = n_links - 1  # index of the link a structural mutation hits
    if mutation and n_links >= 2 and mutation.startswith("child-") or mutation == "required-to-optional":
        c, p = toolsets[li], toolsets[li - 1] if li else None
        if p is not None:
            t = next(iter(c))
            if mutation == "child-widens-tool":
                extra = [x for x in TOOLS if x not in p]
                if extra: c[extra[0]] = {}
            elif mutation == "child-widens-constraint":
                named = [k for k in c[t] if k != "*"]
                if named: c[t][named[0]] = widen(r, c[t][named[0]])
            elif mutation == "child-adds-arg":
                extra = [a for a in ARGS if a not in c[t]]
                if extra: c[t][extra[0]] = {"constraint_type": "wildcard"}
            elif mutation == "child-adds-star":
                c[t]["*"] = {"constraint_type": "wildcard"}
            elif mutation == "child-drops-required":
                req = [k for k, e in (p.get(t) or {}).items() if k != "*" and not e.get("optional")]
                if req: c[t].pop(req[0], None)
            elif mutation == "required-to-optional":
                req = [k for k, e in c[t].items() if k != "*" and not e.get("optional")]
                if req: c[t][req[0]]["optional"] = True

    iat0, exp0 = NOW - 300, NOW + 3000
    chain, payloads = [], []
    for i in range(n_links):
        holder = holders[i]
        p = {"jti": jti(seed, i), "iat": iat0 + 10 * i, "exp": exp0 - 100 * i,
             "del_depth": i, "del_max_depth": dmds[i],
             "cnf": {"jwk": KEYS[holder]["jwk"]}, "authorization_details": aat(toolsets[i])}
        if i == 0:
            p["iss"] = ANCHOR_ISS
            signer = "control_plane"
        else:
            p["iss"] = mint.thumbprint_uri(KEYS[holders[i - 1]]["jwk"])
            p["par_hash"] = chain[i - 1]["signing_input_sha256_b64u"]
            signer = holders[i - 1]
        k = li if n_links > 1 else 0
        if i == k:
            if mutation == "sig-attacker" and i > 0: signer = "attacker"
            if mutation == "iss-mismatch" and i > 0: p["iss"] = mint.thumbprint_uri(KEYS["attacker"]["jwk"])
            if mutation == "par-hash-wrong" and i > 0: p["par_hash"] = "A" * 43
            if mutation == "depth-skip" and i > 0: p["del_depth"] = i + 1
            if mutation == "max-depth-raised" and i > 0: p["del_max_depth"] = payloads[i - 1]["del_max_depth"] + 1
            if mutation == "dup-jti" and i > 0: p["jti"] = payloads[0]["jti"]
            if mutation == "child-outlives-parent" and i > 0: p["exp"] = payloads[i - 1]["exp"] + 50
            if mutation == "child-iat-before-parent" and i > 0: p["iat"] = payloads[i - 1]["iat"] - 5
            if mutation == "aud-other": p["aud"] = "https://other.example.com"
        if i == 0:
            if mutation == "root-sig-attacker": signer = "attacker"
            if mutation == "root-depth-1": p["del_depth"] = 1
            if mutation == "expired": p["exp"] = NOW - 1
            if mutation == "iat-future": p["iat"] = NOW + P["max_iat_skew"] + 60
        if mutation == "aud-other" and r.random() < 0.3:
            p["aud"] = [SUITE["params"]["audience"], "https://other.example.com"]  # still names us: allowed
        t = mint.jws(HDR, p, KEYS[signer]["seed_hex"], signer)
        chain.append(t); payloads.append(p)
    if mutation == "par-hash-other-parent" and n_links >= 2:
        # a sibling parent with the same holder: the child's par_hash names the sibling
        sib = copy.deepcopy(payloads[-2]); sib["jti"] = jti(seed, 99)
        sib_tok = mint.jws(HDR, sib, KEYS[chain[-2]["signer"]]["seed_hex"], chain[-2]["signer"])
        p = copy.deepcopy(payloads[-1]); p["par_hash"] = sib_tok["signing_input_sha256_b64u"]
        chain[-1] = mint.jws(HDR, p, KEYS[holders[-2]]["seed_hex"], holders[-2]); payloads[-1] = p
    return chain, payloads, toolsets


NEEDS_CHILD = {"range-edge-child", "child-widens-tool", "child-widens-constraint", "child-adds-arg", "child-adds-star",
               "child-drops-required", "required-to-optional", "sig-attacker", "iss-mismatch",
               "par-hash-wrong", "par-hash-other-parent", "depth-skip", "max-depth-raised", "dup-jti",
               "child-outlives-parent", "child-iat-before-parent"}


def make_vector(r, seed, idx):
    mutation = r.choice(MUTATIONS)
    if mutation == "chain-too-deep":
        n_links = MAXD + 2  # leaf depth MAX + 1: exceeds every del_max_depth (4m) and MAX (4f)
    else:
        n_links = r.randint(2 if mutation in NEEDS_CHILD else 1, MAXD + 1)
    chain, payloads, toolsets = build(r, seed, n_links, mutation)
    leaf_tools = toolsets[-1]
    tool = r.choice(list(leaf_tools))
    args = rnd_args(r, leaf_tools[tool])
    args_json = None
    if mutation == "call-violates":
        named = [k for k in leaf_tools[tool] if k != "*"]
        if named: args[named[0]] = "zzz" if not isinstance(args.get(named[0]), str) else 999
    elif mutation == "call-unknown-tool":
        tool = next((t for t in TOOLS if t not in leaf_tools), tool + "_x")
    elif mutation == "call-extra-arg":
        args["unexpected"] = "x"
    elif mutation == "call-at-exclusive-bound":
        args = {"amount": r.choice([10, 100])}
    elif mutation == "range-edge-child":
        args = {"amount": 50}
    elif mutation == "call-missing-arg":
        req = [k for k, e in leaf_tools[tool].items() if k != "*" and not e.get("optional")]
        if req: args.pop(req[0], None)
    if mutation == "call-dup-arg" and args:
        k0 = next(iter(args))
        body = mint.compact_json(args)[1:-1]
        args_json = "{" + body + "," + json.dumps(k0) + ":" + json.dumps(args[k0]) + "}"
    if args_json is None:
        args_json = mint.compact_json(args)
    leaf = chain[-1]
    pop = {"jti": jti(seed, 1000), "iat": NOW, "aat_id": payloads[-1]["jti"],
           "aat_hash": leaf["signing_input_sha256_b64u"], "aat_tool": tool, "hta": args,
           "aat_aud": SUITE["params"]["audience"]}
    pop_signer = holders_for(n_links)[-1]
    if mutation == "pop-tool": pop["aat_tool"] = tool + "_other"
    if mutation == "pop-hta": pop["hta"] = dict(args, extra_pop="x")
    if mutation == "pop-iat-old": pop["iat"] = NOW - P["pop_window"] - 10
    if mutation == "pop-aat-id": pop["aat_id"] = payloads[0]["jti"] if n_links > 1 else jti(seed, 7)
    if mutation == "pop-sig-attacker": pop_signer = "attacker"
    pop_tok = mint.jws(POP_HDR, pop, KEYS[pop_signer]["seed_hex"], pop_signer)
    return {
        "id": f"G.{seed}.{idx}", "title": f"generated, {n_links} links, mutation: {mutation or 'none'}",
        "mutation": mutation or "none", "description": "", "notes": [], "now": NOW,
        "tool": tool, "args": args, "args_json": args_json, "policy": {}, "params": {}, "replay_state": None,
        "chain": chain, "chain_compact": [t["compact"] for t in chain], "pop": pop_tok,
        "presentation": {"aat_chain": [t["compact"] for t in chain], "aat_pop": pop_tok["compact"]},
        # placeholder: the Lean model decides the verdict (check.py)
        "expected": {"verdict": "PERMIT", "step": None},
    }


def main():
    seed, count, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    r = random.Random(seed)
    suite = {k: SUITE[k] for k in ("spec", "conventions", "params", "keys", "trust_anchors")}
    suite["vectors"] = [make_vector(r, seed, i) for i in range(count)]
    json.dump(suite, open(out, "w"), indent=1, ensure_ascii=False)
    print(f"{count} vectors -> {out}")


if __name__ == "__main__":
    main()
