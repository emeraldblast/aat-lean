"""Run the Lean model on the AAT-02 vector suite and compare verdicts.

    python3 -I vectors/run.py            # decode, build, run, compare
Writes vectors/out/report.md. Exit status 1 on any disagreement in scope.
"""
import collections
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LAKE = pathlib.Path.home() / ".elan/bin/lake"
SUITE = ROOT / "vectors/upstream/aat-jws-vectors.json"
OUT = ROOT / "vectors/out"


def main():
    OUT.mkdir(exist_ok=True)
    subprocess.run([sys.executable, "-I", str(ROOT / "vectors/decode.py"), str(SUITE),
                    str(OUT / "model-input.json")], check=True)
    subprocess.run([str(LAKE), "build", "aat-run"], cwd=ROOT, check=True, capture_output=True)
    res = subprocess.run([str(LAKE), "exe", "aat-run", str(OUT / "model-input.json")],
                         cwd=ROOT, check=True, capture_output=True, text=True)
    got = dict(l.split("\t", 1) for l in res.stdout.splitlines() if l)
    recs = json.load(open(OUT / "model-input.json"))

    inn = [r for r in recs if r["scope"] == "in"]
    agree = [r for r in inn if got.get(r["id"]) == r["expected"]]
    dis = [r for r in inn if got.get(r["id"]) != r["expected"]]
    out_reasons = collections.Counter(r["reason"] for r in recs if r["scope"] == "out")
    by_step = collections.Counter((r["expected"], r["step"]) for r in inn)

    lines = [
        "# Прогон Lean-модели на векторах AAT-02",
        "",
        f"Набор: `vectors/upstream/aat-jws-vectors.json` ({len(recs)} векторов).",
        f"В зоне модели: **{len(inn)}**; совпало **{len(agree)} из {len(inn)}**.",
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
    lines += ["", "## Вне зоны модели", "", "| Причина | Векторов |", "|---|---|"]
    for reason, n in out_reasons.most_common():
        lines.append(f"| {reason} | {n} |")
    (OUT / "report.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines[:6]))
    for r in dis:
        print(f"  DISAGREE {r['id']}: model {got.get(r['id'])}, expected {r['expected']} at {r['step']}")
    return 1 if dis else 0


if __name__ == "__main__":
    sys.exit(main())
