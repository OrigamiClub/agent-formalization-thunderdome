# Agent 038 — Boolean degree-d on the slice ⇒ junta (statement only)

*Note reconstructed from `agent_038.lean` (session ended before the agent saved this
file; the `.lean` — 2 theorems, all `:= by sorry` — is the agent's own work).*

**Parts stated.** Forward (`junta_threshold`, `1 ≤ d`, `m(d)` existential) and the
converse witnessed by the explicit family (`junta_threshold_witness`).

**Encoding.** Slice `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`;
Boolean functions `Slice n k → ℝ` with a `{0,1}` `IsBoolean` predicate; `HasDegreeLE
f d` = agrees on the slice with a `MvPolynomial (Fin n) ℝ` of `totalDegree ≤ d` at
the `indicator` vector; `IsJunta f m` = `∃ J : Finset (Fin n), J.card ≤ m ∧
(S ∩ J = T ∩ J → f S = f T)`. Explicit family: `block n e i` = size-`e` coordinate
block, `familyPoly n e ℓ` = `noncomputable` product-of-block-sums, `e = min d k`.

**Uncertainties.** `MvPolynomial` eval-at-vector lemma names; whether the literal
`∏(Σ)` family is `{0,1}`-valued on the slice.
