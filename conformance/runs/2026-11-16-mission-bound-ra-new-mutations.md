# Mission-Bound RA against the Lean model, new mutations — 2026-11-16

A second run of Mission-Bound RA, with eight mutations the generator gained
after the 13 November run (`2026-11-13-mission-bound-ra.md`). **Result: no
dangerous disagreement; 42 spurious denials, all from one mutation
(`deep-ignored-claim`), all at step 2c, all from RA's JSON nesting limit.**

## What was run

| | |
|---|---|
| Implementation | Mission-Bound RA `e456a5fbb`, prepared by `conformance/adapters/mission-bound-ra/prepare.sh` (as on 13 November) |
| Model | aat-lean model as at `9d940b9` (unchanged since `e0baa09`); generator as committed with this record |
| Author suite | `vectors/upstream/aat-jws-vectors.json`, SHA-256 `b7a42e9d…209b`, 229 vectors |
| Generated chains | seeds 21, 22, 23; 1 000 chains each; generator with the new mutations below |
| Comparison | verdict only; vectors sent without `expected`, `title`, `description`, `notes`, `mutation` |
| Versions | as in the 13 November record (Lean 4.35.0, Node.js v26.12.0, Python 3.9.6, OpenSSL 4.0.3, macOS 26.6.1 arm64) |

New mutations, and the model's verdict on each (checked on 400 chains of seed 21):

| Mutation | What it does | Model |
|---|---|---|
| `arg-inadmissible` | argument `2^53 + 1`, `hta` `2^53` (equal by JCS) | DENY at 6b |
| `hta-inadmissible` | argument `2^53`, `hta` `2^53 + 1` | DENY at 7f |
| `arg-admissible-big` | argument and `hta` `2^53 + 2` (admissible) | PERMIT |
| `constraint-inadmissible` | `exact` `2^53 + 1`, argument `2^53` | DENY at 3n |
| `nested-dup-arg` | arguments `{"amount":5,"meta":{"a":1,"a":2}}` | DENY at 6b |
| `root-iss-not-uri` | root `iss` `not a URI`, trust anchor with the same issuer | DENY at 3k |
| `anchor-x25519` | trust anchor JWK with `crv` `X25519` and the `x` of the signing Ed25519 key | DENY (root not anchored) |
| `deep-ignored-claim` | root payload carries an unrecognised claim nested 5 000 deep, within `MAX_TOKEN_SIZE` | PERMIT |

Generated suites carry two extra trust anchors for the anchor mutations, since
the vector schema has no per-vector anchors.

## Results

| Seed | Checked | Agree | Dangerous | Spurious denial | No answer | Protocol errors | Coverage loss | RA exit |
|---|---|---|---|---|---|---|---|---|
| 21 | 1 229 | 1 212 | 0 | 17 | 0 | 0 | 0 | 0 |
| 22 | 1 229 | 1 219 | 0 | 10 | 0 | 0 | 0 | 0 |
| 23 | 1 229 | 1 214 | 0 | 15 | 0 | 0 | 0 | 0 |

All 42 spurious denials are `deep-ignored-claim` chains; RA denies each at step
2c ("a string-valued jti cannot be extracted"). On every other new mutation RA
and the model agree, including the non-URI issuer, the X25519 anchor, nested
duplicate arguments and all four number cases.

## The disagreement

RA's JSON reader (`aat-json.ts`) has `MAX_NESTING = 512`: "Nesting deeper than
this refuses rather than risk the stack." Its minimal reader for step 2c
refuses the payload, so no `jti` is extracted and the chain is denied.

AAT-02 sets no nesting limit. Unrecognised claims are ignored, and the only
bound on a token is `MAX_TOKEN_SIZE`; a 5 000-deep array fits well inside
65 536 bytes. Read literally, such a token is permitted, and the model permits
it. RA's denial is fail-closed and a reasonable resource limit, but it is not
in the specification, so two conforming verifiers can disagree on it.

This is a question for the specification rather than a bug in either
implementation. Suggestion for the next revision: either define a maximum JSON
nesting depth for tokens (as `MAX_TOKEN_SIZE` bounds their size), or state that
an enforcement point MAY deny a token whose nesting exceeds an
implementation-defined limit.

## Reproducing

```
sh conformance/adapters/mission-bound-ra/prepare.sh <ra-checkout> e456a5fbb
python3 -I conformance/check.py --impl conformance/adapters/mission-bound-ra/run.sh --seed 21 --count 1000
```

Adding mutations changes the chains a seed produces: the suites of the
13 November run (seeds 11-13) reproduce with the generator at `9d940b9`.
