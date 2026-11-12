// JSON-lines adapter (conformance/check.py protocol) for Mission-Bound RA's verifyAatPresentation.
// Mapping copied from their test/aat-vectors.test.ts.
import { createInterface } from "node:readline";
import { verifyAatPresentation, type AatPolicy } from "./aat-verify.ts";

const rl = createInterface({ input: process.stdin });
for await (const line of rl) {
  if (!line.trim()) continue;
  const req = JSON.parse(line);
  const v = req.vector;
  const s = { ...req.params, ...(v.params ?? {}) };
  const pol = v.policy ?? {};
  const accepted = new Set<string>(v.replay_state?.before ?? []);
  const policy: AatPolicy = {
    audiences: [req.params.audience],
    ...(pol.require_pop_aud ? { requirePopAud: true } : {}),
    ...(pol.require_chain_aud ? { requireChainAud: true } : {}),
    ...(pol.nonce !== undefined ? { acceptNonce: (n: string) => n === pol.nonce } : {}),
    ...(pol.track_pop_jti
      ? { replay: { trackJti: true, admit: (jti: string) => { if (accepted.has(jti)) return false; accepted.add(jti); return true; } } }
      : {}),
  };
  let out: { verdict: string; step?: string };
  try {
    const r = verifyAatPresentation({
      chain: v.presentation.aat_chain, pop: v.presentation.aat_pop, tool: v.tool, argsJson: v.args_json,
      trustAnchors: req.trust_anchors.map((a: any) => ({ issuer: a.iss, jwk: a.jwk })),
      now: v.now,
      params: { maxIatSkew: s.max_iat_skew, maxTokenLifetime: s.max_token_lifetime,
                maxDelegationDepth: s.max_delegation_depth, maxConstraintDepth: s.max_constraint_depth,
                maxTokenSize: s.max_token_size, maxChainSize: s.max_chain_size, popWindow: s.pop_window },
      policy,
    });
    out = { verdict: r.verdict, ...(r.verdict === "DENY" ? { step: (r as any).step } : {}) };
  } catch (e) {
    out = { verdict: "DENY", step: "exception: " + String(e).slice(0, 80) };
  }
  process.stdout.write(JSON.stringify({ id: req.id, ...out }) + "\n");
}
