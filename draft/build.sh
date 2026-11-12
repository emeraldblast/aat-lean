#!/bin/sh
# Build the Internet-Draft: markdown -> XML v3 -> txt/html, then idnits.
#   sh draft/build.sh            (from the repository root)
# Tools (isolated, see ~/.local/aat-tools): kramdown-rfc (Ruby 3 gem),
# xml2rfc (Python venv), idnits v3 (npx).
set -e
T=$HOME/.local/aat-tools
OUT=${OUT:-draft/out}
NAME=draft-mussa-oauth-aat-mechanized-model-00
mkdir -p "$OUT"
export GEM_HOME=$T/gems KRAMDOWN_REFCACHEDIR=$T/refcache
PATH=/opt/homebrew/opt/ruby/bin:$T/gems/bin:$PATH kramdown-rfc --v3 draft/draft-mussa-oauth-aat-mechanized-model.md \
  | grep -v '^<?line ' | sed 's/<?line [0-9]*?>//g' > "$OUT/$NAME.v2.xml"
"$T/venv/bin/xml2rfc" -q --v2v3 "$OUT/$NAME.v2.xml" -o "$OUT/$NAME.xml"
rm "$OUT/$NAME.v2.xml"
(cd "$OUT" && "$T/venv/bin/xml2rfc" -q --text --html "$NAME.xml")
npx --yes @ietf-tools/idnits@3 "$OUT/$NAME.xml"
