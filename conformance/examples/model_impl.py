"""Reference adapter: answers with the Lean model itself. Must agree 100% on the
model's scope; outside it (byte-level checks) it answers DENY. Used to check that
the conformance harness itself is honest."""
import json
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "vectors"))
import decode  # noqa: E402

reqs = [json.loads(l) for l in sys.stdin if l.strip()]
recs = []
for q in reqs:
    suite = {"params": q["params"], "trust_anchors": q["trust_anchors"], "keys": {}, "vectors": [q["vector"]]}
    recs.append(decode.decode(suite)[0])
with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
    name = f.name
decode.dump(recs, name)
res = subprocess.run([str(pathlib.Path.home() / ".elan/bin/lake"), "exe", "aat-run", name], cwd=ROOT,
                     capture_output=True, text=True)
got = {l.split("\t")[0]: l.split("\t")[1] for l in res.stdout.splitlines() if "\t" in l}
for q, r in zip(reqs, recs):
    if r["scope"] == "in" and got.get(q["id"]) not in ("PERMIT", "DENY"):
        # the model must decide every vector in its scope: never fall back to DENY
        sys.exit(f"no model verdict for {q['id']}: {got.get(q['id'])!r} (runner exit {res.returncode})")
    print(json.dumps({"id": q["id"], "verdict": got.get(q["id"], "DENY")}))
