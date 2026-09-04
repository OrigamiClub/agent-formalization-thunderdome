# Agent 008 — Boolean degree-d on the slice ⇒ junta (statement only)

*Note reconstructed from `agent_008.lean`; the agent's session ended before it saved
this file. The `.lean` formalization itself was written by the agent and is complete
(3 theorems, all `:= by sorry`).*

**Parts stated.** All three: positive direction (`boolean_degree_junta_pos`),
plain converse (`boolean_degree_junta_converse`), and converse witnessed by the
explicit family (`boolean_degree_junta_converse_explicit`).

**Encoding.**
- Slice: `abbrev Slice (n k) := {S : Finset (Fin n) // S.card = k}`.
- Boolean functions: `Slice n k → ℝ` plus a separate `IsBooleanValued` predicate
  (`∀ S, f S = 0 ∨ f S = 1`).
- Degree ≤ d: `BooleanDegreeLE f d` = there is a `p : MvPolynomial (Fin n) ℝ` that
  `IsMultilinear` (`degreeOf i ≤ 1` for all `i`) with `totalDegree ≤ d`, agreeing
  with `f` at the real `{0,1}` `indicator` vector on every slice point.
- `m`-junta: `IsJunta f m` = `∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T`.
- `m(d)`: existential inside the positive statement (`∃ M : ℕ, …`).
- Explicit family: `familyFun n k e ℓ` with `e = min d k`, a `noncomputable def`
  transcribing the product-of-block-sums; the explicit converse asserts, for
  `n ≥ 2k`, `n ≥ 2ℓe`, that it is Boolean, degree ≤ d, and not an `m`-junta.

**Uncertainties.** Multilinearity spelled via `MvPolynomial.degreeOf`; exact
Mathlib lemma names for evaluating `MvPolynomial` at a function were guessed.
