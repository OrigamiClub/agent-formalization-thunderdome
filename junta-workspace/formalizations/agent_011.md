# Agent 011 — Boolean degree-d on the slice ⇒ junta (statement only)

*Note reconstructed from `agent_011.lean`; the agent's session ended before it saved
this file. The `.lean` formalization itself was written by the agent and is complete
(3 theorems, all `:= by sorry`).*

**Parts stated.** All three: positive (`boolean_degree_le_d_isJunta`, with `1 ≤ d`),
plain converse (`exists_boolean_degree_le_d_not_isJunta`), and an explicit-witness
theorem (`explicitFn_boolean_degree_not_junta`).

**Encoding.**
- Slice: `abbrev Slice (n k) := {S : Finset (Fin n) // S.card = k}`.
- Boolean: `IsBoolean f` = values in `{0,1}` (real-valued `f`).
- Degree ≤ d: `HasSliceDegreeLE d f` = agrees at every slice point with a
  `p : MvPolynomial (Fin n) ℝ` that `IsMultilinearPoly` and has `totalDegree ≤ d`,
  evaluated at the `{0,1}` `indicator` vector.
- `m`-junta: `IsJunta m f` = `∃ J : Finset (Fin n), J.card ≤ m ∧ (S ∩ J = T ∩ J → f S = f T)`.
- `m(d)`: existential inside the positive statement.
- Explicit family: `block n e i` = coordinates `{i·e, …, i·e+e−1}`; `explicitPoly n e ℓ`
  `= ∑_{i<ℓ} ∏_{j∈block i} X_j` (the sum-of-block-monomials reading of the informal
  "∏(Σ)"); `explicitFn` is its restriction to the slice. Lower bound rendered as
  "not an `(ℓ·min d k − 1)`-junta" given `1 ≤ ℓ·min d k`, `n ≥ 2ℓe`, `n ≥ 2k`.

**Uncertainties.** `MvPolynomial` multilinearity predicate and eval-at-vector lemma
names guessed; `Finset.sum`/`Finset.prod` over `Fin`-blocks may need index massaging.
