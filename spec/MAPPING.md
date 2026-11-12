# AAT-02 Section 8 ↔ the Lean model: traceability

For reviewers who want to check that the model is Section 8 of
[draft-niyikiza-oauth-attenuating-agent-tokens-02](https://www.ietf.org/archive/id/draft-niyikiza-oauth-attenuating-agent-tokens-02.txt)
and not something nearby. Each row gives the requirement, where it is
implemented, which reading of the text was taken, and what tests it: test vectors,
mutations (`review/mutate.py`) and theorems. As of commit `f834a5d` (model
unchanged since `e0baa09`). Definitions are named by file and identifier; line
numbers drift.

The older `spec/AAT-02-mapping.md` (in Russian, 4 November) records the first
reading of Sections 4 and 8 and the decisions taken then. It is kept for history.
This document describes the current model.

## 1. What runs where

A vector goes through three layers. Only the first is covered by the proofs.

| Layer | What it does | Trusted how |
|---|---|---|
| **Lean model** (`AatLean/`) | Every check listed in §3 below, on JSON as written: sizes, headers, claim parsing, chain and invocation checks, number admissibility, JCS comparison of `hta`. `lake exe aat-run` runs `invokeCall`. | Kernel-checked theorems (§4); kernel-checked traps; mutation test (146 caught; 5 survivors, each proved redundant). |
| **Python decoder** (`vectors/decode.py`) | base64url decoding of the compact JWS; JSON parsing into a tree that keeps repeated names and number literals (`tree`, `enc`); **representation-level well-formedness of constraints** (`constraint`, `cmap`: known type, no extra members, member types, `"*"` entry form) producing parsed constraint maps; exact numeric values (`num`); JCS strings for values nested inside arrays and objects (`jcs`); argument pairs (`load_args`). | Not proved. Tested by the 229 vectors, the harness self-test, and several adversarial reviews (findings and fixes are in the git history). |
| **OpenSSL / hashlib** | Ed25519 signature verification under each candidate key (`signed_by`, only keys with `crv` `Ed25519`); SHA-256 of the signing input (`selfHash`); JWK thumbprint URI (`thumb`, RFC 7638/9278). | Standard implementations; the model takes their outputs as given (assumptions 1 and 5). |

The model receives, per token: the protected header and the payload as JSON
trees, the compact length, the thumbprint of `cnf.jwk`, the SHA-256 of the
signing input, the set of keys under which the signature verifies, and the
parsed constraint maps by tool name. Per PoP: header and payload trees, its
signing keys, and `hta` as parsed argument values. Per call: the tool, the
top-level argument pairs with exact values, and the arguments as a JSON tree.
When the decoder's maps or `hta` disagree with the tree it also supplies (a tool
named in the tree has no map, `hta` is an object without parsed values), the
runner reports `ERROR` and the run fails; it is never turned into a verdict.

## 2. Assumptions

Numbered as in the code, `vectors/scope.json` and `vectors/REPORT.md`.

1. Signatures cannot be forged.
2. The key of a trust anchor belongs to its stated issuer.
3. The recipient executes exactly the bytes that were verified.
4. A revocation snapshot is fresh (revocation extension only).
5. SHA-256 and `jwk_thumbprint_uri` are injective.
6. Numbers nested inside array or object values reach the model as a JCS string
   computed by the decoder, and are assumed admissible. Every other number is
   checked in the model.
7. Enforcement-point profile: `alg` `Ed25519` only, Ed25519 keys only, no `crit`
   parameter understood, a JWS header with a repeated member name rejected.

No test vector is outside the model's scope (`vectors/scope.json` lists none).

## 3. Step by step

Columns: **Where** names the Lean definition (all in `AatLean/`) unless marked
*Python*. **Vectors** counts the author's DENY vectors whose expected first
failing step is this one (`vectors/REPORT.md`); all 54 PERMIT vectors exercise
every step. **Mutations** are named as in `review/mutate.py`; each is caught by a
kernel-checked trap unless marked *survives*.

The model does not run the steps in Section 8's order: sizes and headers come
first (`framesOk`), then claim parsing (`parseChain`, `parsePoP`), then the
chain checks (`verify`) and the invocation checks (`authorize`, `invoke`). Every
check is a conjunct of one Boolean decision, and replay state is recorded only
after all others pass (`invokeWithState`), so the order cannot change a verdict.
Steps that Section 8 places after signature verification (claim parsing) run on
the same bytes; the signature is a separate input (`sigBy`).

### Step 1, 2: chain

| Step | Requirement | Where | Reading | Vectors | Mutations | Theorems |
|---|---|---|---|---|---|---|
| 1 | empty chain → DENY | `Verify.verify` | — | 1 | empty chain allowed | `verify_allow_iff` |
| 2a | each token ≤ `MAX_TOKEN_SIZE` | `Parse.sizesOk` (size from *Python*: compact length in bytes) | size = length of the compact serialization | 1 | 2a: token size not checked | — |
| 2b | chain ≤ `MAX_CHAIN_SIZE` | `Parse.sizesOk` | sum of the tokens' compact lengths, PoP excluded | 1 | 2b: chain size not checked | — |
| 2c | string `jti` extractable; no repeated `jti` | `Parse.parseFields` (string, non-empty), `Verify.jtiNoDup` | — | 2 | 2c: jti duplicates allowed; 3j/4b1: empty jti accepted | `jti_nodup` |

### Step 3: root

| Step | Requirement | Where | Reading | Vectors | Mutations | Theorems |
|---|---|---|---|---|---|---|
| 3a | `alg` allowed and consistent with the anchor key; `typ` `aat+jwt`; `crit` | `Parse.headerOk`; key curve in *Python* `signed_by` | profile (assumption 7) | 6 | 3a/4a: chain headers not checked; alg, typ, crit (3), header duplicates | — |
| 3b | signature under a trust anchor key; claims parsed, no repeated names; `iat`, `exp` NumericDate | `Verify.rootOk` (anchor), `Parse.parseFields`, `JVal.noDup`, `intLit` | NumericDate = JSON number with no fraction or exponent (§3.2) | 4 | 3b: root signature not checked; 3b/4b: duplicate names ignored; noDup (2); NumericDate: non-digits skipped | `t3_root` |
| 3c | `del_depth` integer, = 0 | integer: `Parse.parseFields` (`JVal.asNat`); value: `Verify.rootOk` | — | 2 | 3c/4b4: negative integers accepted; 3c value *survives* | `t7_3c_redundant` (value check redundant given 5 and 4d) |
| 3d | `par_hash` absent | `Verify.rootOk`; `Parse.parHashOf` | a non-string `par_hash` counts as present | 1 | 3d | — |
| 3e–3h | `exp > now`; `iat ≤ now + skew`; `exp > iat`; `exp ≤ iat + MAX_TOKEN_LIFETIME` | `Verify.rootOk` | `now` is an explicit parameter | 4 | 3e, 3f, 3g, 3h | `t4_ttl` |
| 3i | `del_max_depth` non-negative integer ≤ `MAX_DELEGATION_DEPTH` | `Parse.parseFields`, `Verify.rootOk` | — | 4 | 3i; 3i: missing del_max_depth defaults | `t6_length` |
| 3j | `jti` non-empty string | `Parse.parseFields` | — | 1 | 3j/4b1: empty jti accepted | — |
| 3k | `iss` a URI, equal to the issuer of the anchor whose key verified | `Parse.isUri`, `Verify.rootOk` | URI = RFC 3986 scheme, `:`, only URI characters (authority, percent-encoding not parsed); an anchor is trusted per (issuer, key) pair | 2 | 3k: root iss not compared; 3k: root iss need not be a URI; isUri (2); 3b/3k: root not anchored | `t3_root` |
| 3l | `cnf.jwk` a public key | `Parse.jwkOk` | `kty` OKP, `crv` Ed25519, `x` 43 base64url characters, no `d` | 2 | 3l/4b2 (6) | — |
| 3m | exactly one AAT entry; `tools` an object of objects | `Parse.aatTools` | entries of other types are ignored | 4 | 3m/4n (3) | — |
| 3n | each constraint well-formed, known type, depth ≤ `MAX_CONSTRAINT_DEPTH`, non-empty `all`/`any`, admissible numbers | representation (types, members): *Python* `constraint`; depth, emptiness, `min ≤ max`: `Constraint.wf`, `Verify.allWF`; numbers: `Number.admissible` via `Parse.parseFields` | malformed or unknown → `Constraint.malformed`, which `wf` rejects | 18 | 3n/4o: well-formedness not checked; wf (5); malformed accepted; 3n/4o: constraint numbers not checked | — |

### Step 4: each (parent, child)

| Step | Requirement | Where | Reading | Vectors | Mutations | Theorems |
|---|---|---|---|---|---|---|
| 4a | as 3a, key = `parent.cnf.jwk` | `Parse.headerOk` | profile | 3 | as 3a | — |
| 4b | signature under `parent.cnf.jwk`; claims parsed | `Verify.pairCore`, `Parse.parseFields` | — | 3 | 4b; 3b/4b: duplicate names ignored | `i1_signed` |
| 4b1 | `jti` non-empty string | `Parse.parseFields` | — | 1 | 3j/4b1 | — |
| 4b2 | `cnf.jwk` a public key | `Parse.jwkOk` | as 3l | 3 | 3l/4b2 | — |
| 4b3 | `authorization_details` an array | `Parse.aatTools` | — | 1 | 3m/4n | — |
| 4b4 | `del_depth`, `del_max_depth` non-negative integers | `Parse.parseFields` | — | 2 | 3c/4b4 | — |
| 4b5 | `iss`, `par_hash` strings; `iat`, `exp` NumericDate | `iss`/`par_hash`: `Parse.check4b5`; dates: `Parse.parseFields` | — | 3 | 4b5 *survives* | `t7_4b5_redundant` (`iss`/`par_hash` part redundant given 4c, 4q, non-empty thumbprints) |
| 4c | `iss` = thumbprint of `parent.cnf.jwk` (I1) | `Chain.linkedB` | exact string comparison | 1 | linkedB (2) | `i1_signed` |
| 4d–4g, 4m | depth = parent + 1; ≤ parent's and global maximum; `del_max_depth` non-increasing; ≤ own maximum (I2) | `Verify.pairCore`, `Verify.pairRedundant` | — | 5 | 4d, 4g, 4m; 4e, 4f *survive* | `t6_depth`, `t7_redundant` (4e, 4f redundant) |
| 4h–4l | TTL monotone, valid now (I3) | `Verify.pairCore` | — | 5 | 4h–4l | `t4_ttl` |
| 4n | exactly one AAT entry; `tools` an object of objects | `Parse.aatTools` | — | 5 | 3m/4n | — |
| 4o | as 3n for the child | as 3n | — | 2 | as 3n | — |
| 4p1 | every child tool in the parent | `Chain.narrowsB` | — | 1 | 4p1 | `t1_monotone`, `t1_core` |
| 4p2–4p3 | key rules after normalization (§3.3, §4.5) | `CMap.narrowsMapB`, `CMap.norm` | — | 7 | 4p2 (4), 4p3, norm | `narrowsMapB_sound` |
| 4p4 | each constraint structurally narrower (Table 4) | `Constraint.subsumes` | Table 4 as an exhaustive list; anything else rejected | 24 | 4p4: constraint not compared; the 31 mutations of `Constraint.lean` (denotation `check`, Table 4 `subsumes`, `wf`) | `subsumes_sound`; `incompleteness_witness`, `exactPdf_structurally_rejected` (intended incompleteness) |
| 4q | `par_hash` = SHA-256 of parent's signing input (I5) | `Verify.pairCore` (hash from *hashlib*) | — | 2 | 4q | `i5_bound` |

### Step 5

| Step | Requirement | Where | Reading | Vectors | Mutations | Theorems |
|---|---|---|---|---|---|---|
| 5 | `len(chain) = leaf.del_depth + 1` | `Verify.step5` | — | 0 | step 5 *survives* | `t7_redundant` |

### Step 6: leaf and call

| Step | Requirement | Where | Reading | Vectors | Mutations | Theorems |
|---|---|---|---|---|---|---|
| 6a | leaf has exactly one AAT entry | `Parse.aatTools` (as 4n for the leaf) | — | — | 3m/4n | — |
| 6b | tool in leaf; admissible numbers; no repeated names in any argument object; closed world, `"*"`, required arguments, each value satisfies its constraint | `Parse.invokeCall` (repeated names at any depth, admissibility), `Verify.authorize`, `Verify.argsNoDup`, `Chain.permitsB`, `CMap.permitsArgs`, `Constraint.check`; top-level pairs from *Python* `load_args` | — | 27 | 6b (4 in CMap); authorize (4); 6b: nested duplicate argument names ignored; 6b: argument numbers not checked | `t2_coverage` (every link permits the call), `invokeCall_allow` |
| 6c | every `aud` in the chain names this point; required audience | `Invoke.audOk` | `aud` a string or array of strings; anything else matches nothing | 4 | 6c (2) | `t8_aud` |

### Step 7: proof of possession

| Step | Requirement | Where | Reading | Vectors | Mutations | Theorems |
|---|---|---|---|---|---|---|
| 7a | PoP header: `alg`, `typ` `aat-pop+jwt`, `crit` | `Parse.headerOk` | profile | 4 | 7a: PoP header not checked | — |
| 7b | signature under `leaf.cnf.jwk`; no repeated names | `Invoke.popOk`, `Parse.parsePoP` | — | 2 | 7b: PoP signature not checked; 7b: PoP duplicate names ignored | `t9_pop` |
| 7c | `jti`, `aat_id`, `aat_hash`, `aat_tool` non-empty strings; `iat` NumericDate; `hta` an object; `aat_id`, `aat_hash` bind the leaf | `Parse.parsePoP`, `Invoke.popOk` | — | 5 | 7c (5) | `t9_pop` |
| 7d | `aat_aud` names this point; required binding | `Invoke.popOk` | `aat_aud` a single string (author's reading of C5) | 3 | 7d (2) | `t9_pop` |
| 7e | `aat_tool` = tool | `Invoke.popOk` | exact string | 1 | 7e | `t9_pop` |
| 7f | admissible numbers in `hta`; `hta` = args by JCS | `Parse.parsePoP` (admissibility), `Invoke.htaEq` with `Value.jcs` | numbers compared by the value of their JCS form | 3 | 7f (3); 7f: hta numbers not checked | `t9_pop` |
| 7g | `iat` within the window | `Invoke.popOk` | inclusive at both ends (confirmed by the author) | 2 | 7g (3) | `t9_pop` |
| 7h | nonce, when required | `Invoke.popOk` | — | 2 | 7h | — |
| 7i | PoP `jti` not replayed; record on success | `Invoke.invokeWithState` | state outside `verify`; recorded only after every other check | 1 | 7i (3) | `t9_replay` |

### Section 3.4: number admissibility

| Requirement | Where | Validation |
|---|---|---|
| "the JCS serialization of its double-precision value denotes the same mathematical value" | `Number.toDouble` (round to nearest, ties to even, subnormals, overflow → none), `Number.shortest` (shortest decimal in the rounding interval, as ECMAScript `Number::toString`), `Number.admissible` | Equal to Python's correctly rounded `float` and shortest `repr` on 194 860 numbers (random, and targeted at powers of 2 and 10). Ten mutations, each caught by a trap found by that comparison. Not reached by any tested input: the tie rule of `Number::toString` (two equally close shortest forms) and the `log10` corrections, which the three-exponent window tolerates. |

### Extension: revocation (§9.8)

Section 9.8 defines no revocation. `Extension/Revocation.verifyWithStatus` adds a
root-revocation check outside `verify`; `t5_revocation`, `t5_revokes_descendants`.

## 4. Theorems that carry the properties to tokens as written

`invokeTokens_allow`: an allowed presentation parses into a chain and PoP that
`invokeWithState` allows. `invokeCall_allow`: an allowed call has no repeated
argument names at any depth, and `invokeTokens` allows it. T1–T9 are stated
about `verify`, `authorize`, `invoke` and `invokeWithState`; these two theorems
connect them to what the runner executes. All theorems depend only on Lean's
three standard axioms; no `sorry`, `admit` or `native_decide`.

## 5. Known limits of this mapping

- **Python is part of the trusted path.** It covers base64url and JSON parsing,
  the representation-level form of constraints (3n, 4o), the argument pairs (6b)
  and JCS strings of nested values. A decoder bug can feed the model the wrong
  input; the runner's consistency checks catch some cases, not all.
- **Readings.** The URI reading in 3k is weaker than the full RFC 3986 grammar:
  `https://a%zz` is a URI to the model. The enforcement-point profile
  (assumption 7) fixes choices Section 8 leaves to the implementation.
- **Order.** Steps are regrouped (§3); the step at which a vector is denied may
  differ from Section 8's first failing step. Verdicts do not.
- **Redundant checks.** Five mutations survive because the corresponding checks
  cannot change a verdict (T7, T7′, T7″). No test vector can detect an
  implementation that omits exactly one of them.
