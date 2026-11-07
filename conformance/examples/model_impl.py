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
    json.dump(recs, f)
out = subprocess.run([str(pathlib.Path.home() / ".elan/bin/lake"), "exe", "aat-run", f.name], cwd=ROOT,
                     capture_output=True, text=True).stdout
got = {l.split("\t")[0]: l.split("\t")[1] for l in out.splitlines() if "\t" in l}
for q in reqs:
    print(json.dumps({"id": q["id"], "verdict": got.get(q["id"], "DENY")}))
