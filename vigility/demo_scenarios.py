"""Scenarios for the Vigility demo page: real signed chains, verdicts from the Lean model.

    python3 -I vigility/demo_scenarios.py OUT.json
"""
import copy
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "vigility"))
sys.path.insert(0, str(ROOT / "vectors"))
import mint  # noqa: E402
import decode  # noqa: E402

SUITE = json.load(open(ROOT / "vectors/upstream/aat-jws-vectors.json"))
K, P = SUITE["keys"], SUITE["params"]
NOW, ANCHOR_ISS = P["now"], SUITE["trust_anchors"][0]["iss"]
HDR, POP_HDR = {"alg": "Ed25519", "typ": "aat+jwt"}, {"alg": "Ed25519", "typ": "aat-pop+jwt"}
NAMES = {"control_plane": "Сервер авторизации", "orchestrator": "Агент-оркестратор",
         "worker": "Агент-исполнитель", "worker2": "Под-агент платежей", "attacker": "Злоумышленник"}


def cap(limit):
    return {"pay": {"amount": {"constraint_type": "range", "min": 0, "max": limit}},
            **({"read_file": {"path": {"constraint_type": "one_of",
                                       "values": ["/data/q3.pdf", "/data/q4.pdf"]}}} if limit >= 1000 else {})}


def chain_of(tools, holders=("orchestrator", "worker", "worker2"), tweak=None):
    toks, pays = [], []
    for i, (h, t) in enumerate(zip(holders, tools)):
        p = {"jti": f"019471f8-0000-7000-8000-00000000d{i:03d}", "iat": NOW - 300 + 10 * i,
             "exp": NOW + 3000 - 100 * i, "del_depth": i, "del_max_depth": 3,
             "cnf": {"jwk": K[h]["jwk"]},
             "authorization_details": [{"type": "attenuating_agent_token", "tools": t}]}
        signer = "control_plane" if i == 0 else holders[i - 1]
        if i == 0:
            p["iss"] = ANCHOR_ISS
        else:
            p["iss"] = mint.thumbprint_uri(K[holders[i - 1]]["jwk"])
            p["par_hash"] = toks[i - 1]["signing_input_sha256_b64u"]
        if tweak:
            signer = tweak(i, p, toks) or signer
        toks.append(mint.jws(HDR, p, K[signer]["seed_hex"], signer)); pays.append(p)
    return toks, pays


def vector(sid, toks, pays, tool, args, pop_signer="worker2", policy=None, seen=None, pop_tweak=None):
    leaf = toks[-1]
    pop = {"jti": f"019471f8-0000-7000-8000-0000000p{sid[:4]}", "iat": NOW, "aat_id": pays[-1]["jti"],
           "aat_hash": leaf["signing_input_sha256_b64u"], "aat_tool": tool, "hta": args, "aat_aud": P["audience"]}
    if pop_tweak: pop_tweak(pop)
    pt = mint.jws(POP_HDR, pop, K[pop_signer]["seed_hex"], pop_signer)
    return {"id": sid, "title": sid, "now": NOW, "tool": tool, "args": args, "args_json": mint.compact_json(args),
            "policy": policy or {}, "params": {}, "replay_state": {"before": seen or []} if seen is not None else None,
            "chain": toks, "pop": pt, "expected": {"verdict": "PERMIT", "step": None}}


BASE = [cap(1000), cap(100), cap(50)]
PAY40 = {"amount": 40}


def sc_ok():
    t, p = chain_of(BASE); return vector("ok", t, p, "pay", PAY40)


def sc_widen():
    t, p = chain_of([cap(1000), cap(100), cap(500)]); return vector("widen", t, p, "pay", PAY40)


def sc_tool():
    tools = copy.deepcopy(BASE); tools[2]["delete_records"] = {}
    t, p = chain_of(tools); return vector("tool", t, p, "pay", PAY40)


def sc_over():
    t, p = chain_of(BASE); return vector("over", t, p, "pay", {"amount": 80})


def sc_splice():
    # a second token for the executor with a wider limit; the sub-agent's par_hash points at it
    t, p = chain_of(BASE)
    sib = copy.deepcopy(p[1]); sib["jti"] = "019471f8-0000-7000-8000-00000000d999"
    sib["authorization_details"] = [{"type": "attenuating_agent_token", "tools": cap(1000)}]
    sib_tok = mint.jws(HDR, sib, K["orchestrator"]["seed_hex"], "orchestrator")
    q = copy.deepcopy(p[2]); q["par_hash"] = sib_tok["signing_input_sha256_b64u"]
    t[2] = mint.jws(HDR, q, K["worker"]["seed_hex"], "worker"); p[2] = q
    return vector("splice", t, p, "pay", PAY40)


def sc_forged():
    t, p = chain_of(BASE, tweak=lambda i, p, toks: "attacker" if i == 2 else None)
    return vector("forged", t, p, "pay", PAY40)


def sc_expired():
    def tw(i, p, toks):
        if i == 2: p["exp"] = NOW - 60
    t, p = chain_of(BASE, tweak=tw); return vector("expired", t, p, "pay", PAY40)


def sc_root():
    t, p = chain_of(BASE, tweak=lambda i, p, toks: "attacker" if i == 0 else None)
    return vector("root", t, p, "pay", PAY40)


def sc_stolen():
    t, p = chain_of(BASE); return vector("stolen", t, p, "pay", PAY40, pop_signer="attacker")


def sc_replay():
    t, p = chain_of(BASE)
    v = vector("replay", t, p, "pay", PAY40, policy={"track_pop_jti": True}, seen=[])
    v["replay_state"]["before"] = [v["pop"]["payload"]["jti"]]
    return v


SCENARIOS = [
    ("ok", sc_ok, "Всё в порядке", "Человек выдал оркестратору право платить до 1000, тот передал исполнителю до 100, исполнитель — под-агенту до 50. Под-агент платит 40.",
     None, "—", "Т1, Т2, Т9"),
    ("widen", sc_widen, "Под-агент расширил лимит", "Исполнителю разрешено до 100, а он выдал под-агенту токен на 500.",
     "Лимит последнего звена 500 при лимите родителя 100", "4p4", "Т1 — права звена не шире прав родителя"),
    ("tool", sc_tool, "Добавлен чужой инструмент", "Исполнитель выдал под-агенту право удалять записи, которого у него самого не было.",
     "В последнем звене появился инструмент delete_records", "4p1", "Т1"),
    ("over", sc_over, "Платёж сверх лимита листа", "Под-агент платит 80: в пределах лимита исполнителя (100), но больше своего (50).",
     "Сумма вызова 80 при лимите листа 50", "6b", "Т2 — вызов допускает каждое звено, а проверяется по листу"),
    ("splice", sc_splice, "Подмена родителя", "У исполнителя есть второй, более широкий токен. Под-агент ссылается на него через par_hash, чтобы унаследовать лишние права.",
     "par_hash указывает на другой токен того же держателя", "4q", "I5 — звено привязано к экземпляру родителя"),
    ("forged", sc_forged, "Подпись не того ключа", "Токен под-агента подписан ключом злоумышленника, а не исполнителя.",
     "Подпись последнего звена — ключом злоумышленника", "4b", "I1 — каждое звено подписано держателем родителя"),
    ("expired", sc_expired, "Просроченный токен", "Срок токена под-агента истёк минуту назад.",
     "exp последнего звена в прошлом", "4i", "Т4 — каждое звено действительно в момент проверки"),
    ("root", sc_root, "Поддельный корень", "Корневой токен называет настоящий сервер авторизации, но подписан чужим ключом.",
     "Подпись корня — ключом злоумышленника", "3b", "Т3 — корень подписан доверенным ключом"),
    ("stolen", sc_stolen, "Украденная цепочка", "Злоумышленник перехватил всю цепочку и предъявляет её со своим доказательством владения.",
     "PoP подписан не ключом держателя листа", "7b", "Т9 — PoP подписан ключом листа"),
    ("replay", sc_replay, "Повтор запроса", "Тот же самый запрос с тем же PoP отправлен второй раз.",
     "PoP jti уже принимался этой точкой проверки", "7i", "Т9′ — повторный PoP отклоняется"),
]


def summarize(tok):
    p = tok["payload"]
    tools = p["authorization_details"][0]["tools"]
    out = []
    for t, m in tools.items():
        parts = []
        for k, c in m.items():
            if c.get("constraint_type") == "range": parts.append(f"{k} ≤ {c['max']}")
            elif c.get("constraint_type") == "one_of": parts.append(f"{k} ∈ {{{', '.join(c['values'])}}}")
            else: parts.append(k)
        out.append(t + (" (" + ", ".join(parts) + ")" if parts else ""))
    return out


def main():
    vectors, meta = [], []
    for sid, fn, title, story, changed, step, thm in SCENARIOS:
        v = fn(); v["id"] = sid; vectors.append(v)
        meta.append((sid, title, story, changed, step, thm, v))
    suite = {k: SUITE[k] for k in ("spec", "conventions", "params", "keys", "trust_anchors")}
    suite["vectors"] = vectors
    tmp = ROOT / "vigility/out"; tmp.mkdir(exist_ok=True)
    recs = decode.decode(suite)
    json.dump(recs, open(tmp / "demo-input.json", "w"))
    res = subprocess.run([str(pathlib.Path.home() / ".elan/bin/lake"), "exe", "aat-run", str(tmp / "demo-input.json")],
                         cwd=ROOT, capture_output=True, text=True, check=True).stdout
    verdict = {l.split("\t")[0]: l.split("\t")[1] for l in res.splitlines() if "\t" in l}
    out = []
    for sid, title, story, changed, step, thm, v in meta:
        holders = [t["payload"]["cnf"]["jwk"]["x"] for t in v["chain"]]
        names = [next(n for k, n in NAMES.items() if K[k]["jwk"]["x"] == x) for x in holders]
        out.append({
            "id": sid, "title": title, "story": story, "changed": changed, "step": step, "theorem": thm,
            "verdict": verdict[sid],
            "issuers": [NAMES[t["signer"]] for t in v["chain"]],
            "links": [{"holder": n, "signedBy": NAMES[t["signer"]], "rights": summarize(t),
                       "token": t["compact"]} for n, t in zip(names, v["chain"])],
            "call": {"tool": v["tool"], "args": v["args"]},
            "pop": {"signedBy": NAMES[v["pop"]["signer"]], "token": v["pop"]["compact"]},
        })
    json.dump(out, open(sys.argv[1], "w"), ensure_ascii=False, indent=1)
    for s in out: print(f"{s['id']:8s} {s['verdict']:7s} {s['title']}")


if __name__ == "__main__":
    main()
