# Mission-Bound RA against the Lean model — 2026-11-13

An independent AAT-02 verifier, run through `conformance/check.py` against the
Lean model. **Result: no disagreement on 3 229 distinct inputs** (the 229
author vectors, checked in each of three runs, and 3 000 generated signed
chains).

## What was run

| | |
|---|---|
| Implementation | Mission-Bound RA, `verifyAatPresentation` (TypeScript), github.com/mcguinness/mission-bound-authorization |
| RA commit | `e456a5fbb3c391a2f9b5577cde9faab9d63bcd5a` (`origin/main`). The four verifier files are unchanged since `eaf7b97`, the commit of the 5 November run. |
| RA files | `src/packages/mission-core/src/aat-{constraints,json,jws,verify}.ts`, prepared by `conformance/adapters/mission-bound-ra/prepare.sh`: import suffixes `.js` → `.ts` and two parameter properties written as fields, so that Node's type stripping runs them. No other change. |
| Adapter | `conformance/adapters/mission-bound-ra/adapter.ts`, the input mapping of RA's own `test/aat-vectors.test.ts`; `run.sh` runs it under `sandbox-exec` with network denied. The runs used this adapter with a different first comment line. |
| Model | aat-lean `f834a5d` (model identical to `e0baa09`): all 229 author vectors in the model's scope |
| Author suite | `vectors/upstream/aat-jws-vectors.json`, SHA-256 `b7a42e9dfdce7fbc1f623670bf060f90e6d6b25f64384cbab1bd79363e82209b` (tenuo-ai/tenuo `99fb009`), 229 vectors: 54 PERMIT, 175 DENY |
| Generated chains | `conformance/generate.py`, seeds 11, 12, 13, 1 000 chains each, 1 to 10 tokens (`MAX_DELEGATION_DEPTH` + 2), one mutation per chain against a §8 step |
| Comparison | verdict only (PERMIT / DENY); the implementation receives vectors without `expected`, `title`, `description`, `notes`, `mutation` |

Generated suites (byte-reproducible from the seed at this commit):

| Seed | SHA-256 of `gen-<seed>.json` | Model PERMIT / DENY | No mutation | One token too deep |
|---|---|---|---|---|
| 11 | `bc0bc264b980c7470f4f7df0c10c1deb14b21cd6e2d174108a13a7dc6da7931c` | 131 / 869 | 104 | 36 |
| 12 | `077d2d7a27c4466c8970b8b36a2ea1347baa7f6cff338c3a2035a44b3e182b43` | 137 / 863 | 106 | 27 |
| 13 | `8a3a951c4d89a0d5ab21a6f87ad04d6cbf9e8fadad4bd499836cfb477f0a0e30` | 120 / 880 | 101 | 32 |

## Results

| Seed | Checked | Agree | Dangerous (model DENY, RA PERMIT) | Spurious denial (model PERMIT, RA DENY) | No answer | Protocol errors | Coverage loss | RA exit | Exceptions in RA |
|---|---|---|---|---|---|---|---|---|---|
| 11 | 1 229 | 1 229 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| 12 | 1 229 | 1 229 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| 13 | 1 229 | 1 229 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

"Exceptions in RA" counts answers the adapter produced from an exception thrown
by the verifier (the adapter turns those into DENY, which `check.py` cannot tell
from a deliberate denial). It was counted separately by running the adapter
again on the same blind inputs: none of the 3 229 answers came from an exception.

The 229 author vectors are the same in all three runs; the 3 000 generated
chains are distinct.

## Versions

| | |
|---|---|
| Lean | 4.35.0 (`leanprover/lean4:v4.35.0`, commit `eb6cafb7`), Lake 5.0.0 |
| Node.js | v26.12.0 |
| Python | 3.9.6 (macOS system) |
| OpenSSL | 4.0.3 (Homebrew), for Ed25519 in the decoder and the generator |
| OS | macOS 26.6.1, arm64 |

## How to reproduce

```
git clone https://github.com/mcguinness/mission-bound-authorization ra
sh conformance/adapters/mission-bound-ra/prepare.sh ra e456a5fbb
for seed in 11 12 13; do
  python3 -I conformance/check.py --impl "conformance/adapters/mission-bound-ra/run.sh" \
    --seed $seed --count 1000 --json summary-$seed.json
done
```

`run.sh` uses macOS `sandbox-exec`; elsewhere run `node --no-warnings adapter.ts`.

## What this does and does not show

Two independent implementations, the Lean model and RA, agree on every input
tried, including chains longer than the author's suite covers and all five
inadmissible-number vectors. Agreement raises confidence in both; it does not
prove either correct, and it does not show that the model matches Section 8.
That is the subject of `spec/MAPPING.md` and of external review. Inputs not
generated here (for example a non-URI root issuer, or a trust anchor with a
non-Ed25519 curve) are not covered by this run.
