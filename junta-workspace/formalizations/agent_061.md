# Agent 061 — Boolean degree-d on the slice ⇒ junta (statement only)

*Note reconstructed from `agent_061.lean` (session ended before the agent saved this
file; the `.lean` — 3 theorems, all `:= by sorry` — is the agent's own work).*

**Parts stated.** Forward (`junta_threshold_upper`, `m(d)` existential), converse
(`junta_threshold_converse`), and converse with the explicit family
(`junta_threshold_converse_explicit`).

**Encoding.** Slice `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`;
`Slice.ind : Fin n → ℝ` indicator; `IsBoolean` (`{0,1}`); `HasDegreeLE d f` =
agreement on the slice with a `totalDegree ≤ d` `MvPolynomial (Fin n) ℝ` at `ind`;
`IsJunta m f` = `∃ J, J.card ≤ m ∧ (S ∩ J = T ∩ J → f S = f T)`. Explicit family:
`blockMonomial n e i`, `FIpoly n d k ℓ` (`noncomputable`, product-of-block-sums),
`FIfun` its restriction to the slice, `e = min d k`.

**Uncertainties.** `MvPolynomial` eval/degree API; literal `∏(Σ)` family
Boolean/degree properties.
