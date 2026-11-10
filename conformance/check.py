"""Differential conformance check of an AAT-02 verifier against the proved Lean model.

    python3 -I conformance/check.py --impl "COMMAND" [--seed 1] [--count 300] [--out report.md]
                                    [--json summary.json] [--shrink 3]

Exit status 0 only when every verdict agrees, every vector got a model verdict
(no coverage loss) and the implementation exited cleanly. Disagreements on which
the model is the reference are shrunk to minimal vectors (conformance/shrink.py).

Inputs: the author's 229 vectors plus COUNT generated chains (conformance/generate.py).
Oracle: the Lean model (`lake exe aat-run`) — the same function T1–T9 are proved
about. For author vectors outside the model's scope (byte-level checks), the
author's expected verdict is the reference.

Protocol: COMMAND is started twice (author vectors, then generated chains). Each time it
reads JSON lines on stdin, one per vector:
    {"id": ..., "vector": <vector, upstream suite schema without expected, title,
                            description, notes, mutation>, "params": {...}, "trust_anchors": [...]}
and writes one JSON line per vector on stdout:
    {"id": ..., "verdict": "PERMIT" | "DENY", "step": "<optional §8 step>"}
Each asked id is answered once; any other line on stdout fails the check.
"""
import argparse
import collections
import hashlib
import itertools
import json
import pathlib
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))  # shrink, mint, check under -I

ROOT = pathlib.Path(__file__).resolve().parent.parent
LAKE = pathlib.Path.home() / ".elan/bin/lake"
OUT = ROOT / "conformance/out"
UPSTREAM = ROOT / "vectors/upstream/aat-jws-vectors.json"
SCOPE = ROOT / "vectors/scope.json"


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, check=True, capture_output=True, text=True, **kw)


def oracle(suite_path, tag):
    """Decode a suite and run the Lean model; returns {id: verdict} for in-scope vectors, and the records."""
    inp = OUT / f"{tag}-input.json"
    run([sys.executable, "-I", str(ROOT / "vectors/decode.py"), str(suite_path), str(inp)])
    res = subprocess.run([str(LAKE), "exe", "aat-run", str(inp)], cwd=ROOT, capture_output=True, text=True)
    verdicts = {}
    for line in res.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) >= 2:
            verdicts[parts[0]] = parts[1]
    recs = {r["id"]: r for r in json.load(open(inp))}
    # every in-scope vector must get a verdict; anything else is a coverage loss
    lost = [f"{i}: {r['reason']}" for i, r in recs.items() if r["scope"] == "error"]
    lost += [f"{i}: model answered {verdicts.get(i)!r}" for i, r in recs.items()
             if r["scope"] == "in" and verdicts.get(i) not in ("PERMIT", "DENY")]
    if res.returncode:
        lost.append(f"model runner exited with code {res.returncode}")
    verdicts = {i: v for i, v in verdicts.items() if v in ("PERMIT", "DENY") and recs[i]["scope"] == "in"}
    return verdicts, recs, lost


# Fields that state or hint at the expected verdict: never sent to the implementation.
HIDDEN = ("expected", "title", "description", "notes", "mutation")


def blind(v):
    return {k: x for k, x in v.items() if k not in HIDDEN}


def run_impl(cmd, suite, vectors):
    """Answers of the implementation for exactly these vectors. Anything else on
    stdout — a line that is not a JSON object with a string id and verdict, an
    id not asked in this run, an id answered twice — is a protocol error."""
    lines = [json.dumps({"id": v["id"], "vector": blind(v), "params": suite["params"],
                         "trust_anchors": suite["trust_anchors"]}, ensure_ascii=False) for v in vectors]
    res = subprocess.run(cmd, shell=True, input="\n".join(lines) + "\n", capture_output=True, text=True)
    asked = {v["id"] for v in vectors}
    got, errors = {}, []
    for n, line in enumerate(res.stdout.splitlines(), 1):
        if not line.strip():
            continue
        try:
            o = json.loads(line)
        except ValueError:
            errors.append(f"line {n}: not JSON"); continue
        if not isinstance(o, dict) or not isinstance(o.get("id"), str) or not isinstance(o.get("verdict"), str):
            errors.append(f"line {n}: not an object with string id and verdict"); continue
        if o["id"] not in asked:
            errors.append(f"line {n}: id {o['id']!r} was not asked in this run"); continue
        if o["id"] in got:
            errors.append(f"line {n}: id {o['id']!r} answered twice"); continue
        got[o["id"]] = o
    return got, res.returncode, res.stderr[-2000:], errors


_tags = itertools.count()


def judge(cmd):
    """For shrinking: (model verdict, implementation verdict) for each vector.
    A run with any error the main check counts — model coverage loss, a
    non-zero exit of the implementation, a protocol error — decides nothing:
    every vector of that batch gets None, so no candidate is kept on it."""
    def f(suite, vectors):
        path = OUT / "shrink-suite.json"
        doc = {k: suite[k] for k in suite if k != "vectors"}
        doc["vectors"] = vectors
        path.write_text(json.dumps(doc, ensure_ascii=False))
        model, _, lost = oracle(path, f"shrink-{next(_tags)}")
        impl, rc, _, protocol = run_impl(cmd, suite, vectors)
        if lost or rc or protocol:
            return {v["id"]: None for v in vectors}
        return {v["id"]: (model.get(v["id"]), impl.get(v["id"], {}).get("verdict", "NO ANSWER")) for v in vectors}
    return f


def git_head():
    try:
        return run(["git", "rev-parse", "--short", "HEAD"]).stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        return "unknown"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--impl", required=True, help="command implementing the JSON-lines protocol")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--count", type=int, default=300)
    ap.add_argument("--out", default=str(OUT / "report.md"))
    ap.add_argument("--json", help="also write a machine-readable summary here")
    ap.add_argument("--shrink", type=int, default=3, help="shrink up to N disagreements (0: off)")
    a = ap.parse_args()
    OUT.mkdir(exist_ok=True)
    run([str(LAKE), "build", "aat-run"])

    up = json.load(open(UPSTREAM))
    gen_path = OUT / f"gen-{a.seed}.json"
    run([sys.executable, "-I", str(ROOT / "conformance/generate.py"), str(a.seed), str(a.count), str(gen_path)])
    gen = json.load(open(gen_path))

    o_up, rec_up, lost_up = oracle(UPSTREAM, "upstream")
    o_gen, rec_gen, lost_gen = oracle(gen_path, f"gen-{a.seed}")
    # coverage: the author vectors outside the model are exactly the pinned ones,
    # and every generated vector is decided by the model
    pinned = json.load(open(SCOPE))["out"]
    lost = lost_up + lost_gen
    lost += [f"{i}: outside the model but not pinned in vectors/scope.json ({r['reason']})"
             for i, r in rec_up.items() if r["scope"] == "out" and i not in pinned]
    lost += [f"{i}: pinned as out of scope but now in scope" for i in pinned if rec_up.get(i, {}).get("scope") == "in"]
    lost += [f"{i}: generated vector outside the model ({r.get('reason')})"
             for i, r in rec_gen.items() if r["scope"] == "out"]

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

    got_up, rc1, err1, perr1 = run_impl(a.impl, up, up["vectors"])
    got_gen, rc2, err2, perr2 = run_impl(a.impl, gen, [v for v in gen["vectors"] if v["id"] in ref])
    protocol = [f"author run, {e}" for e in perr1] + [f"generated run, {e}" for e in perr2]
    if set(got_up) & set(got_gen):
        protocol.append("an id is in both runs")  # cannot happen: ids are checked per run
    got = {**got_up, **got_gen}

    rows = []
    for i in ref:
        g = got.get(i, {}).get("verdict", "NO ANSWER")
        rows.append((i, meta[i][0], meta[i][1], ref[i], source[i], g, meta[i][2]))
    dis = [r for r in rows if r[5] != r[3]]
    by_kind = collections.Counter((r[1], r[2]) for r in dis)
    too_lax = [r for r in dis if r[3] == "DENY" and r[5] == "PERMIT"]
    too_strict = [r for r in dis if r[3] == "PERMIT" and r[5] == "DENY"]

    # minimal reproducers for disagreements the model decides, dangerous ones first
    import shrink as shr
    shrunk, shrink_failed = [], []
    vec = {v["id"]: (up, v) for v in up["vectors"]}
    vec.update({v["id"]: (gen, v) for v in gen["vectors"]})
    for r in sorted((r for r in dis if r[4] == "model"), key=lambda r: (r[3] != "DENY", r[0]))[:a.shrink]:
        suite, v = vec[r[0]]
        small, target, steps = shr.shrink(suite, v, judge(a.impl))
        if target is None:
            shrink_failed.append(r[0])
            continue
        path = OUT / f"min-{r[0]}.json"
        doc = {k: suite[k] for k in suite if k != "vectors"}
        doc["vectors"] = [small]
        path.write_text(json.dumps(doc, indent=1, ensure_ascii=False))
        shrunk.append((r[0], target, shr.size(v), shr.size(small), len(small["chain"]), steps, path))

    suite_sha = hashlib.sha256(UPSTREAM.read_bytes()).hexdigest()
    L = [
        "# Отчёт о проверке соответствия AAT-02",
        "",
        f"Реализация: `{a.impl}`",
        f"Модель: коммит `{git_head()}`; набор векторов SHA-256 `{suite_sha[:16]}…`.",
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
    if shrunk or shrink_failed:
        L += ["", "## Минимальные воспроизводимые случаи", ""]
    if shrunk:
        L += ["| Вектор | Модель | Реализация | Звеньев | Байт: было → стало | Файл |", "|---|---|---|---|---|---|"]
        for i, t, b0, b1, nl, steps, path in shrunk:
            L.append(f"| {i} | {t[0]} | {t[1]} | {nl} | {b0} → {b1} | `{path.relative_to(ROOT)}` |")
        L += ["", "Каждый файл — набор в схеме авторских векторов из одного вектора; "
              "`python3 -I conformance/check.py` его не читает, но любой декодер набора — да."]
    if shrink_failed:
        L += ["", "Не уменьшены (повторный прогон дал ошибку модели или реализации): "
              + ", ".join(shrink_failed)]
    L += ["", "## Как воспроизвести", "",
          f"`python3 -I conformance/check.py --impl \"{a.impl}\" --seed {a.seed} --count {a.count}`"]
    if lost:
        L += ["", f"## Потеря покрытия: {len(lost)}", "",
              "Проверка не пройдена: эти векторы не получили вердикта модели.", ""]
        L += [f"- {x}" for x in lost[:60]]
    if protocol:
        L += ["", f"## Нарушения протокола: {len(protocol)}", "",
              "Проверка не пройдена: ответ реализации не соответствует протоколу.", ""]
        L += [f"- {x}" for x in protocol[:60]]
    if rc1 or rc2:
        L += ["", f"**Реализация завершилась с ошибкой** (код {rc1 or rc2}): проверка не пройдена. "
              "Последние строки stderr:", "", "```", err1 if rc1 else err2, "```"]
    pathlib.Path(a.out).write_text("\n".join(L) + "\n", encoding="utf-8")
    ok = not (dis or rc1 or rc2 or lost or protocol)
    if a.json:
        pathlib.Path(a.json).write_text(json.dumps({
            "ok": ok, "impl": a.impl, "seed": a.seed, "count": a.count, "model_commit": git_head(),
            "suite_sha256": suite_sha, "checked": len(rows), "agree": len(rows) - len(dis),
            "dangerous": [r[0] for r in too_lax], "spurious_denials": [r[0] for r in too_strict],
            "no_answer": [r[0] for r in dis if r[5] not in ("PERMIT", "DENY")],
            "coverage_loss": lost, "protocol_errors": protocol, "impl_exit": rc1 or rc2,
            "minimal": [{"id": i, "model": t[0], "impl": t[1], "links": nl, "file": str(path.relative_to(ROOT)),
                         "steps": steps} for i, t, b0, b1, nl, steps, path in shrunk],
        }, indent=1, ensure_ascii=False))
    print("\n".join(L[:17]))
    if protocol:
        print(f"\nprotocol errors: {len(protocol)}: check failed")
    if lost:
        print(f"\ncoverage loss: {len(lost)} vector(s) without a model verdict: check failed")
    if rc1 or rc2:
        print(f"\nimplementation exited with code {rc1 or rc2}: check failed")
    print(f"\nreport: {a.out}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
