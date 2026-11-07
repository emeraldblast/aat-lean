"""Vigility: check an AAT-02 verifier against the proved Lean model.

    python3 -I vigility/check.py --impl "COMMAND" [--seed 1] [--count 300] [--out report.md]

Inputs: the author's 229 vectors plus COUNT generated chains (vigility/generate.py).
Oracle: the Lean model (`lake exe aat-run`) — the same function T1–T9 are proved
about. For author vectors outside the model's scope (byte-level checks), the
author's expected verdict is the reference.

Protocol: COMMAND is started once. It reads JSON lines on stdin, one per vector:
    {"id": ..., "vector": <vector, upstream suite schema>, "params": {...}, "trust_anchors": [...]}
and writes one JSON line per vector on stdout:
    {"id": ..., "verdict": "PERMIT" | "DENY", "step": "<optional §8 step>"}
"""
import argparse
import collections
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LAKE = pathlib.Path.home() / ".elan/bin/lake"
OUT = ROOT / "vigility/out"
UPSTREAM = ROOT / "vectors/upstream/aat-jws-vectors.json"


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, check=True, capture_output=True, text=True, **kw)


def oracle(suite_path, tag):
    """Decode a suite and run the Lean model; returns {id: verdict} for in-scope vectors, and the records."""
    inp = OUT / f"{tag}-input.json"
    run([sys.executable, "-I", str(ROOT / "vectors/decode.py"), str(suite_path), str(inp)])
    res = run([str(LAKE), "exe", "aat-run", str(inp)])
    verdicts = {}
    for line in res.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) >= 2 and parts[1] in ("PERMIT", "DENY"):
            verdicts[parts[0]] = parts[1]
    return verdicts, {r["id"]: r for r in json.load(open(inp))}


def run_impl(cmd, suite, vectors):
    lines = [json.dumps({"id": v["id"], "vector": v, "params": suite["params"],
                         "trust_anchors": suite["trust_anchors"]}, ensure_ascii=False) for v in vectors]
    res = subprocess.run(cmd, shell=True, input="\n".join(lines) + "\n", capture_output=True, text=True)
    got = {}
    for line in res.stdout.splitlines():
        try:
            o = json.loads(line)
            got[o["id"]] = o
        except (ValueError, KeyError):
            continue
    return got, res.returncode, res.stderr[-2000:]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--impl", required=True, help="command implementing the JSON-lines protocol")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--count", type=int, default=300)
    ap.add_argument("--out", default=str(OUT / "report.md"))
    a = ap.parse_args()
    OUT.mkdir(exist_ok=True)
    run([str(LAKE), "build", "aat-run"])

    up = json.load(open(UPSTREAM))
    gen_path = OUT / f"gen-{a.seed}.json"
    run([sys.executable, "-I", str(ROOT / "vigility/generate.py"), str(a.seed), str(a.count), str(gen_path)])
    gen = json.load(open(gen_path))

    o_up, rec_up = oracle(UPSTREAM, "upstream")
    o_gen, _ = oracle(gen_path, f"gen-{a.seed}")

    # reference verdict: Lean model where in scope; the author's verdict for the rest of the author's suite
    ref, source, meta = {}, {}, {}
    for v in up["vectors"]:
        i = v["id"]
        ref[i] = o_up.get(i, v["expected"]["verdict"])
        source[i] = "model" if i in o_up else "author"
        meta[i] = ("author", v["expected"].get("step") or "—", v["title"])
    for v in gen["vectors"]:
        i = v["id"]
        if i in o_gen:
            ref[i], source[i], meta[i] = o_gen[i], "model", ("generated", v["mutation"], v["title"])

    got_up, rc1, err1 = run_impl(a.impl, up, up["vectors"])
    got_gen, rc2, err2 = run_impl(a.impl, gen, [v for v in gen["vectors"] if v["id"] in ref])
    got = {**got_up, **got_gen}

    rows = []
    for i in ref:
        g = got.get(i, {}).get("verdict", "NO ANSWER")
        rows.append((i, meta[i][0], meta[i][1], ref[i], source[i], g, meta[i][2]))
    dis = [r for r in rows if r[5] != r[3]]
    by_kind = collections.Counter((r[1], r[2]) for r in dis)
    too_lax = [r for r in dis if r[3] == "DENY" and r[5] == "PERMIT"]
    too_strict = [r for r in dis if r[3] == "PERMIT" and r[5] == "DENY"]

    L = [
        "# Vigility — отчёт о проверке соответствия AAT-02",
        "",
        f"Реализация: `{a.impl}`",
        f"Входы: {len(up['vectors'])} авторских векторов + {sum(1 for r in rows if r[1] == 'generated')} "
        f"сгенерированных цепочек (seed {a.seed}).",
        "Эталон: Lean-модель с доказанными Т1–Т9 (для авторских векторов вне зоны модели — вердикт автора).",
        "",
        "## Итог",
        "",
        "| | Векторов |",
        "|---|---|",
        f"| Проверено | {len(rows)} |",
        f"| Совпало с эталоном | {len(rows) - len(dis)} |",
        f"| **Пропущено опасное** (эталон DENY, реализация PERMIT) | **{len(too_lax)}** |",
        f"| Лишний отказ (эталон PERMIT, реализация DENY) | {len(too_strict)} |",
        f"| Нет ответа | {sum(1 for r in dis if r[5] not in ('PERMIT', 'DENY'))} |",
        "",
    ]
    if dis:
        L += ["## Расхождения по виду", "", "| Набор | Шаг §8 / порча | Расхождений |", "|---|---|---|"]
        for (kind, what), n in by_kind.most_common():
            L.append(f"| {kind} | {what} | {n} |")
        L += ["", "## Расхождения (первые 60)", "",
              "| Вектор | Набор | Шаг / порча | Эталон | Реализация | Описание |", "|---|---|---|---|---|---|"]
        for r in sorted(dis, key=lambda r: (r[3] != "DENY", r[0]))[:60]:
            L.append(f"| {r[0]} | {r[1]} | {r[2]} | {r[3]} ({r[4]}) | {r[5]} | {r[6]} |")
    else:
        L += ["Расхождений нет."]
    L += ["", "## Как воспроизвести", "",
          f"`python3 -I vigility/check.py --impl \"{a.impl}\" --seed {a.seed} --count {a.count}`"]
    if rc1 or rc2:
        L += ["", f"**Реализация завершилась с ошибкой** (код {rc1 or rc2}): проверка не пройдена. "
              "Последние строки stderr:", "", "```", err1 if rc1 else err2, "```"]
    pathlib.Path(a.out).write_text("\n".join(L) + "\n", encoding="utf-8")
    print("\n".join(L[:17]))
    if rc1 or rc2:
        print(f"\nimplementation exited with code {rc1 or rc2}: check failed")
    print(f"\nreport: {a.out}")
    return 1 if dis or rc1 or rc2 else 0


if __name__ == "__main__":
    sys.exit(main())
