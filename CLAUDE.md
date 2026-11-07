# CLAUDE.md

Executable Lean 4 model of the AAT-02 chain verifier
(draft-niyikiza-oauth-attenuating-agent-tokens-02) with kernel-checked proofs
and a conformance run against the author's 229 vectors.

The user (Yerassyl) writes in Russian; answer in Russian. README is in English;
`spec/` and code comments are in Russian.

## Private context — read first, never commit

`CONTEXT.md` and `PLAN.md` are gitignored, local only (copies in
`~/aat-lean-private/`). They hold decisions, approvals and the plan. Read
`CONTEXT.md` at the start of a session. Nothing from them goes into tracked
files: the repository is public (github.com/emeraldblast/aat-lean).

## Commands

```
~/.elan/bin/lake build                 # all proofs (elan is not on PATH)
python3 review/mutate.py               # mutation test, must report 0 surviving
python3 -I vectors/run.py              # vectors: decode, run lake exe aat-run, compare
python3 -I conformance/selftest.py     # harness: model agrees on all, buggy fixture caught
```

After changing any checker (`check`, `subsumes`, `permitsArgs`, `narrowsMapB`,
`narrowsB`, `verify`, `authorize`, `invoke`), run the build, the mutation test
and the vectors. Add a mutation to `review/mutate.py` for every new check.
`EXPECTED_SURVIVORS` (3c, 4e, 4f, step 5, 4b5) must survive: T7/T7′/T7″ prove
they are redundant. Copy `vectors/out/report.md` to `vectors/REPORT.md` when it changes.
`vectors/scope.json` pins which author vectors are outside the model; a change of
scope fails `vectors/run.py` until accepted with `--update-scope` — only for a
deliberate change, with a stated assumption for every out-of-scope vector.

## Rules for proofs

- No `sorry`, `admit`, `native_decide`. Concrete traps use `decide +kernel`.
- Only standard axioms (`propext`, `Classical.choice`, `Quot.sound`); check with
  `#print axioms` from a scratch file.
- Denotation before structure: define what a constraint/map/link permits
  (`check`, `permitsArgs`, `Permits`) independently of the structural rule
  (`subsumes`, `narrowsMapB`, `narrowsB`), then prove `structural → semantic`.
  Never define the semantics through the checker — that makes T1 a tautology.
- The link is one-directional by design (§4.1: rules are conservative);
  `incompleteness_witness` and `exactPdf_structurally_rejected` must stay true.
- Every theorem statement is approved by the user before it counts. Show the
  statement, wait for approval, record it in `CONTEXT.md`. Do not change the
  text of approved statements (`t1_monotone`, `Narrows`, T2–T9) without
  re-approval. `t1_core` carries T1 independently of `verify`'s parameters.
- `verify` takes the §8 inputs (`Params`, anchors, chain). State σ (PoP jti)
  lives in `invokeWithState`, revocation R in `Extension/Revocation.lean` —
  never in `verify`.
- Lean core has no `swap`/`tauto` (Mathlib); use `rotate_left`, explicit cases.

## Vectors

`vectors/upstream/aat-jws-vectors.json` is byte-identical to tenuo-ai/tenuo at
`99fb009` (SHA-256 `b7a42e9d…209b`); never edit it. Out-of-scope vectors must be
explained by a stated assumption (byte level, duplicates, inadmissible numbers),
never by skipping a modelled step. Ed25519 is checked with OpenSSL ≥ 3
(`vectors/ed25519.py`; macOS needs Homebrew OpenSSL).

## External reviews

Adversarial reviews come from DeepSeek (`review/`). Do not compile or run Lean or
Python files produced by another model; check each claim with your own code
(own mutant, own counterexample) and report which claims held.

## Gotchas

- System Python 3.9 fails on very long lines with Cyrillic in heredocs
  ("Non-UTF-8 code"): put long Russian text in a file and read it.
- Commit messages end with the co-author line from the session instructions.
  Push only when the user asks.
