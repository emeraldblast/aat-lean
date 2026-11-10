# aat-lean

An executable Lean 4 model of the chain verifier of
[draft-niyikiza-oauth-attenuating-agent-tokens-02](https://www.ietf.org/archive/id/draft-niyikiza-oauth-attenuating-agent-tokens-02.txt)
(Attenuating Agent Tokens, "AAT-02"), with machine-checked proofs of its
security properties and a conformance run against the author's 229 test vectors.

It answers one question for a recipient of an AI agent's action: if the
verifier accepts a delegation chain, what does that guarantee?

The proofs were written with AI assistance and are checked by the Lean kernel.
The link between this model and any production verifier is by testing (the
vectors), not by proof.

## What is proved

All theorems hold for chains of any length. No `sorry`, `admit` or
`native_decide`; every theorem depends only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

| | Statement | Where |
|---|---|---|
| T1 | In an accepted chain every link permits only calls its parent permits (C(child) ⊆ C(parent), §4.1) | `t1_monotone`, `t1_core` |
| — | The structural rules of §4.5 (Table 4 and the key rules 4p2–4p4) are **sound** w.r.t. the denotation of §3.4, for all nine core constraint types | `subsumes_sound`, `narrowsMapB_sound`, `narrowsB_sound` |
| — | They are **not complete**, as §4.1 intends: `one_of` inside `range`, and `exact` under `any` (the §4.1 example), are semantically narrower but rejected | `incompleteness_witness`, `exactPdf_structurally_rejected` |
| T2 | An authorised call is permitted by every link, not only the leaf (step 6b) | `t2_coverage` |
| T3 | The root is signed by a trust anchor's key and names that anchor's issuer (3b, 3k) | `t3_root` |
| I1, I5 | Each link is signed by its parent's holder and bound to that parent instance by `par_hash` | `i1_signed`, `i5_bound` |
| T4 | Every link is valid at `now`, outlives no parent, and is issued no earlier than the root (I3) | `t4_ttl` |
| T6 | Depth equals position; chain length ≤ `MAX_DELEGATION_DEPTH` + 1 (I2) | `t6_depth`, `t6_length` |
| **T7** | Steps 4e, 4f and 5 never change a verdict: `verify` equals the algorithm without them, on all inputs | `t7_redundant` |
| **T7′** | The value check of step 3c (root `del_depth` = 0) is redundant too, given step 5 and 4d: it and step 5 are mutually redundant. The integer check of 3c is not: in the model it is part of parsing (J.21.9, `del_depth: false`, is denied there) | `t7_3c_redundant` |
| **T7″** | The `iss`/`par_hash` check of step 4b5 (a derived token's `iss` and `par_hash` present and strings; the `iat`/`exp` NumericDate check of 4b5 is not covered) never changes a verdict: 4c and 4q reject what it rejects, given non-empty key thumbprints | `t7_4b5_redundant` |
| — | Claims parsing in the model (3b–3m, 4b–4n, 7b–7c): an accepted presentation parses into a chain and PoP that `invokeWithState` accepts, so T1–T9 apply to tokens as written | `invokeTokens_allow` |
| T8 | Every `aud` in the chain names this enforcement point (6c) | `t8_aud` |
| T9 | The PoP is signed by the leaf holder's key and binds the leaf, tool, arguments and time window (step 7, I6); a replayed PoP is rejected | `t9_pop`, `t9_replay` |
| T5 | Extension per §9.8: revoking a root rejects every chain that starts at it | `t5_revocation`, `t5_revokes_descendants` |

T7 is a machine-checked confirmation of findings B9 and B10 in
[Davliatshin's implementation report](https://datatracker.ietf.org/doc/draft-davliatshin-oauth-attenuation-chains-report/)
and of the notes to §8. T7′ is the converse direction, not stated there; the
suite's generator already records the redundancy of 4b5 that T7″ proves.

## Conformance with the author's vectors

`python3 -I vectors/run.py` decodes the suite (`vectors/upstream`, byte-identical
to tenuo-ai/tenuo at `99fb009`), checks Ed25519 signatures with OpenSSL, and runs
`invokeTokens` (`lake exe aat-run`): the model checks token and chain sizes
and every JWS header (steps 2a, 2b, 3a, 4a, 7a: `alg`, `typ`, `crit`), reads
each signed payload as written — a JSON tree with repeated member names and
number literals — parses the claims itself (steps 3b–3m, 4b–4n, 7b–7c:
duplicate names, NumericDate and integer claims, `jti`, `cnf.jwk`,
`authorization_details`), and then runs the
**same `invokeWithState` function the theorems are about**. Result
([vectors/REPORT.md](vectors/REPORT.md)):

- 224 of 229 vectors are in the model's scope; **224 of 224 agree**, including
  all 54 PERMIT vectors; the PoP replay state matches on 3 of 3. Each of the 15
  header and size vectors is denied by those checks, each of the 32 parsing
  vectors at parsing, and each of the other 177 passes both.
- The remaining 5 test inadmissible numbers (§3.4), left to assumption 6; the
  list is pinned in `vectors/scope.json`.

## Differential conformance testing

`conformance/` uses the model as a test oracle for other AAT-02 verifiers:

```
python3 -I conformance/check.py --impl "COMMAND" --seed 1 --count 300
```

It runs `COMMAND` (a JSON-lines protocol, see `conformance/check.py`) on the 229
author vectors plus generated signed chains (`conformance/generate.py`: 1 to
`MAX_DELEGATION_DEPTH` + 1 tokens, plus chains one token too deep; all nine
constraint types; one mutation per vector against a §8 step), and
compares every verdict with the Lean model. The report groups disagreements by
§8 step and separates the dangerous ones (model DENY, implementation PERMIT).

- **Smaller reproducers.** Disagreements on which the model is the reference
  (the first `--shrink N`, default 3, dangerous ones first) are shrunk
  greedily (`conformance/shrink.py`, at most 40 rounds): links, tools,
  constraint entries, list members and call arguments are removed,
  constraints replaced by `wildcard`, and the chain re-signed with the
  original signers, for as long as the same disagreement survives. The
  result is a smaller one-vector suite in the author's schema, not
  necessarily a minimal one.
- **No silent coverage loss.** The check fails if any vector does not get a
  model verdict, if the implementation exits with an error, or if the set of
  author vectors outside the model differs from `vectors/scope.json`.
- **CI.** One command; exit status 0 only on full agreement. `--json` writes a
  machine-readable summary; the report records the model commit, the suite's
  SHA-256 and the seed, so every run is reproducible.

- `conformance/examples/model_impl.py` answers with the model itself: 529 of 529
  agree, which checks the harness.
- `conformance/examples/naive_impl.py` is a verifier with three deliberate bugs
  (range inclusivity, no `par_hash` check, no chain `aud` check). The check finds
  all three, from the author vectors and independently from the generated chains,
  with no false alarms.

## Assumptions

The numbers are the ones used in the code, `vectors/scope.json` and
`vectors/REPORT.md`.

1. Signatures cannot be forged.
2. The key of a trust anchor belongs to its stated issuer.
3. The recipient executes exactly the bytes that were verified.
4. A revocation snapshot is fresher than Δ (T5 only).
5. SHA-256 and `jwk_thumbprint_uri` are injective.
6. All values are compared by JCS and every number is admissible (§3.4).
7. Enforcement-point profile and byte level: only `alg` `Ed25519` and only
   Ed25519 keys (`cnf.jwk` "encodes a public key" when `kty` is `OKP`, `crv`
   is `Ed25519`, `x` is 43 base64url characters and there is no `d`; steps
   3l, 4b2; an Ed25519 signature is attributed only to keys with `crv`
   `Ed25519`), the root `iss` a URI in a minimal sense (an RFC 3986 scheme,
   `:`, only URI characters; step 3k), no `crit` parameter understood, a JWS header with a repeated
   member name rejected (RFC 7515 §4 permits it); a repeated member name
   inside a nested call argument is left out of the model.

## Mutation test

`python3 review/mutate.py` mutates each check of the verifier and confirms that
some kernel-checked `example` fails. 129 mutations are caught. Exactly five
survive — steps 3c, 4e, 4f, 5 and 4b5 — which is what T7, T7′ and T7″ predict:
no input can distinguish them.

## Layout

| File | Contents |
|---|---|
| `AatLean/Constraint.lean` | Constraint denotation (§3.4), Table 4 (§4.5), soundness, well-formedness |
| `AatLean/CMap.lean` | Constraint maps: step 6b and key rules 4p2–4p4 |
| `AatLean/Chain.lean` | Tokens, `Permits`, `Narrows`, step 4p, T1 core |
| `AatLean/Verify.lean` | §8 steps 1–6b, T1–T4, T6, T7 |
| `AatLean/Invoke.lean` | Steps 6c and 7 with state, T8, T9 |
| `AatLean/Parse.lean` | Claims parsing (3b–3m, 4b–4n, 7b–7c) over JSON as written; `invokeTokens` |
| `AatLean/Extension/Revocation.lean` | T5 |
| `Runner.lean`, `vectors/` | Vector decoder, runner, report |
| `conformance/` | Differential conformance testing of other verifiers |
| `spec/` | Mapping of AAT-02 to the model; position relative to Davliatshin's report |

## Build

```
lake build                 # all proofs
python3 review/mutate.py   # mutation test
python3 -I vectors/run.py  # vectors (needs OpenSSL >= 3 with Ed25519)
```

## License

Apache License 2.0. The vector suite is from tenuo-ai/tenuo, Apache-2.0; see
`NOTICE`.
