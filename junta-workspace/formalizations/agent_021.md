# Agent 021 — Boolean degree-d on the slice ⇒ junta (statement only)

*Note reconstructed from `agent_021.lean`; the agent's session ended before it saved
this file. The `.lean` formalization itself was written by the agent and is complete
(3 theorems, all `:= by sorry`).*

**Parts stated.** All three: positive (`boolean_degree_junta`, with `1 ≤ d`,
`m(d)` existential), converse (`not_junta_of_small_k`, for `1 ≤ k < 2d`), and the
explicit family with its junta lower bound (`blockForm_not_junta`).

**Encoding.**
- Slice: `abbrev Slice (n k) := {S : Finset (Fin n) // S.card = k}`.
- `indicator S` / `evalAt p S` = evaluate `p : MvPolynomial (Fin n) ℝ` at the `0/1`
  indicator vector of `S : Finset (Fin n)` (`noncomputable`).
- Boolean: `IsBooleanValued (f : α → ℝ)` = `∀ x, f x = 0 ∨ f x = 1` (generic).
- Degree ≤ d: `HasDegreeLE f d` = `∃ p, totalDegree p ≤ d ∧ ∀ S : Slice n k, f S = evalAt p S.1`
  (multilinearity not separately imposed — the slice makes it moot).
- `m`-junta: `IsJunta f m` = `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`.
- Explicit family: `blockForm n e ℓ = ∏_{i<ℓ} (∑_{j<e} X_{i·e+j})` (literal
  product-of-sums transcription, `e = min d k`); the converse produces an
  `f : Slice n k → ℝ` equal to `evalAt (blockForm …)` that is Boolean, degree ≤ d,
  and not an `(ℓ·min d k − 1)`-junta, under `n ≥ 2ℓe`, `n ≥ 2k`.

**Uncertainties.** `MvPolynomial.eval` signature / coercions for `evalAt`; whether
the literal `∏(Σ)` `blockForm` is genuinely Boolean on the slice (agent transcribed
it as given).
