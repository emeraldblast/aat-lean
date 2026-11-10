"""Run the Lean model on the AAT-02 vector suite and compare verdicts.

    python3 -I vectors/run.py                 # decode, build, run, compare
    python3 -I vectors/run.py --update-scope  # accept a deliberate change of scope
Writes vectors/out/report.md. Exit status 1 on any disagreement in scope, on a
decoder or model error, or when the set of out-of-scope vectors differs from
vectors/scope.json (a coverage change must be deliberate, never silent).
"""
import collections
import json
import pathlib
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import decode  # noqa: E402  (deep: decoder output may nest JSON deeply)

ROOT = pathlib.Path(__file__).resolve().parent.parent
LAKE = pathlib.Path.home() / ".elan/bin/lake"
SUITE = ROOT / "vectors/upstream/aat-jws-vectors.json"
OUT = ROOT / "vectors/out"
SCOPE = ROOT / "vectors/scope.json"


def scope_diff(recs, pinned):
    """Differences between the decoder's out-of-scope set and the pinned one."""
    now = {r["id"]: r["reason"] for r in recs if r["scope"] != "in"}
    diff = []
    for i in sorted(set(now) | set(pinned)):
        if now.get(i) != pinned.get(i):
            diff.append(f"{i}: pinned {pinned.get(i, 'in scope')!r}, now {now.get(i, 'in scope')!r}")
    return diff


def main():
    OUT.mkdir(exist_ok=True)
    dec = subprocess.run([sys.executable, "-I", str(ROOT / "vectors/decode.py"), str(SUITE),
                          str(OUT / "model-input.json")])
    subprocess.run([str(LAKE), "build", "aat-run"], cwd=ROOT, check=True, capture_output=True)
    res = subprocess.run([str(LAKE), "exe", "aat-run", str(OUT / "model-input.json")],
                         cwd=ROOT, capture_output=True, text=True)
    rows = [l.split("\t") for l in res.stdout.splitlines() if l]
    got = {r[0]: r[1] for r in rows}
    state = {r[0]: [x for x in r[2].split(",") if x] if len(r) > 2 else [] for r in rows}
    recs = decode.load(OUT / "model-input.json")
    if "--update-scope" in sys.argv[1:]:
        doc = json.load(open(SCOPE))
        doc["out"] = {r["id"]: r["reason"] for r in recs if r["scope"] == "out"}
        SCOPE.write_text(json.dumps(doc, indent=1, ensure_ascii=False) + "\n")
    sdiff = scope_diff(recs, json.load(open(SCOPE))["out"])
    errors = [r for r in recs if r["scope"] == "error"]
    model_err = [r for r in recs if r["scope"] == "in" and got.get(r["id"]) not in ("PERMIT", "DENY")]

    inn = [r for r in recs if r["scope"] == "in"]
    agree = [r for r in inn if got.get(r["id"]) == r["expected"]]
    dis = [r for r in inn if got.get(r["id"]) != r["expected"]]
    st_checked = [r for r in inn if "expected_state" in r]
    st_bad = [r for r in st_checked if state.get(r["id"]) != r["expected_state"]]
    out_reasons = collections.Counter(r["reason"] for r in recs if r["scope"] == "out")
    by_step = collections.Counter((r["expected"], r["step"]) for r in inn)

    lines = [
        "# Прогон Lean-модели на векторах AAT-02",
        "",
        f"Набор: `vectors/upstream/aat-jws-vectors.json` ({len(recs)} векторов).",
        f"В зоне модели: **{len(inn)}**; совпало **{len(agree)} из {len(inn)}**.",
        f"Состояние σ после вызова (PoP `jti`) сверено на {len(st_checked)} векторах: "
        f"совпало {len(st_checked) - len(st_bad)}.",
        "",
        "## В зоне модели по ожидаемому шагу",
        "",
        "| Ожидается | Шаг | Векторов |",
        "|---|---|---|",
    ]
    for (v, s), n in sorted(by_step.items(), key=lambda kv: (kv[0][0], str(kv[0][1]))):
        lines.append(f"| {v} | {s or '—'} | {n} |")
    lines += ["", "## Расхождения", ""]
    if dis:
        for r in dis:
            lines.append(f"- {r['id']}: модель {got.get(r['id'])}, ожидается {r['expected']} "
                         f"на шаге {r['step']} — {r['title']}")
    else:
        lines.append("Нет.")
    if sdiff or errors or model_err:
        lines += ["", "## Потеря покрытия", ""]
        lines += [f"- зона изменилась: {d}" for d in sdiff]
        lines += [f"- ошибка декодера: {r['id']}: {r['reason']}" for r in errors]
        lines += [f"- нет вердикта модели: {r['id']}: {got.get(r['id'])}" for r in model_err]
    lines += ["", "## Вне зоны модели", "", "| Причина | Векторов |", "|---|---|"]
    for reason, n in out_reasons.most_common():
        lines.append(f"| {reason} | {n} |")
    (OUT / "report.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines[:6]))
    for r in dis:
        print(f"  DISAGREE {r['id']}: model {got.get(r['id'])}, expected {r['expected']} at {r['step']}")
    for r in st_bad:
        print(f"  STATE {r['id']}: model {state.get(r['id'])}, expected {r['expected_state']}")
    for d in sdiff:
        print(f"  SCOPE {d}")
    for r in errors:
        print(f"  DECODER ERROR {r['id']}: {r['reason']}")
    for r in model_err:
        print(f"  NO MODEL VERDICT {r['id']}: {got.get(r['id'])}")
    if res.returncode:
        print(f"  MODEL RUNNER exited with code {res.returncode}")
    return 1 if dis or st_bad or sdiff or errors or model_err or dec.returncode or res.returncode else 0


if __name__ == "__main__":
    sys.exit(main())
