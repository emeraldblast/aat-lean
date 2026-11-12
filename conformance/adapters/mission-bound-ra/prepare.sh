#!/bin/sh
# Copy Mission-Bound RA's AAT-02 verifier from a checkout and make it runnable
# by Node's type stripping. Only mechanical edits: import suffixes .js -> .ts,
# and two TypeScript parameter properties written as explicit fields.
#   sh prepare.sh /path/to/mission-bound-authorization [COMMIT]
set -e
RA=${1:?path to a mission-bound-authorization checkout}
REV=${2:-HEAD}
HERE=$(cd "$(dirname "$0")" && pwd)
SRC=src/packages/mission-core/src
for f in aat-constraints aat-json aat-jws aat-verify; do
  git -C "$RA" show "$REV:$SRC/$f.ts" | sed -E 's#from "\./(aat-[a-z]+)\.js";#from "./\1.ts";#' > "$HERE/$f.ts"
done
python3 - "$HERE/aat-json.ts" <<'PY'
import sys, pathlib
p = pathlib.Path(sys.argv[1]); s = p.read_text()
for a, b in [("  constructor(readonly raw: string) {}", "  readonly raw: string;\n  constructor(raw: string) { this.raw = raw; }"),
             ("  constructor(private readonly s: string) {}", "  private readonly s: string;\n  constructor(s: string) { this.s = s; }")]:
    assert s.count(a) == 1, a
    s = s.replace(a, b)
p.write_text(s)
PY
echo "prepared from $(git -C "$RA" rev-parse --short "$REV")"
