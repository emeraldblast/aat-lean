"""Self-test of the conformance harness: it must pass a correct verifier and
catch a broken one.

    python3 -I conformance/selftest.py [--count 100]

1. examples/model_impl.py (the model itself) must agree on every vector.
2. examples/naive_impl.py (three deliberate bugs: range inclusivity, no
   par_hash check, no chain aud check) must be reported with dangerous
   disagreements, and with no spurious denial, missing answer, protocol error,
   coverage loss or crash — a fixture that silently denies everything (as
   happened when its input format changed) fails here.
Exit status 0 only if both hold.
"""
import argparse
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "conformance/out"


def run(impl, count, tag):
    summary = OUT / f"selftest-{tag}.json"
    res = subprocess.run([sys.executable, "-I", str(ROOT / "conformance/check.py"),
                          "--impl", f"python3 -I {impl}", "--count", str(count), "--shrink", "0",
                          "--json", str(summary), "--out", str(OUT / f"selftest-{tag}.md")],
                         cwd=ROOT, capture_output=True, text=True)
    if not summary.exists():
        print(res.stdout[-2000:], res.stderr[-2000:])
        return res.returncode, None
    return res.returncode, json.load(open(summary))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=100)
    a = ap.parse_args()
    OUT.mkdir(exist_ok=True)
    failures = []

    rc, s = run("conformance/examples/model_impl.py", a.count, "model")
    if rc != 0 or not s or not s["ok"]:
        failures.append(f"model adapter: exit {rc}, summary {s and {k: s[k] for k in ('agree', 'checked')}}")
    else:
        print(f"model adapter: {s['agree']} of {s['checked']} agree")

    rc, s = run("conformance/examples/naive_impl.py", a.count, "naive")
    if s is None:
        failures.append(f"naive fixture: no summary (exit {rc})")
    else:
        bad = {k: s[k] for k in ("spurious_denials", "no_answer", "protocol_errors", "coverage_loss") if s[k]}
        if rc != 1 or s["ok"] or not s["dangerous"] or bad or s["impl_exit"]:
            failures.append(f"naive fixture: exit {rc}, dangerous {len(s['dangerous'])}, "
                            f"impl exit {s['impl_exit']}, {bad}")
        else:
            print(f"naive fixture: {len(s['dangerous'])} dangerous disagreements, no spurious denial")

    for f in failures:
        print("FAIL", f)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
