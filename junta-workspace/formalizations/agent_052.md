# Agent 052 — Boolean degree-d on the slice ⇒ junta (statement only)

*Note reconstructed from `agent_052.lean` (session ended before the agent saved this
file; the `.lean` — 2 theorems, all `:= by sorry` — is the agent's own work).*

**Parts stated.** Forward (`filmus_ihringer`, `1 ≤ d`, `m(d)` existential) and the
converse witnessed by the explicit family (`filmus_ihringer_witness`, `1 ≤ k`).

**Encoding.** Slice `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`;
`indicator S : Fin n → ℝ`; `IsBoolean` (`{0,1}`); `HasDegreeLE f d` = agreement with
a `totalDegree ≤ d` `MvPolynomial (Fin n) ℝ` at the indicator; `IsJunta f m` =
coordinate set of card `≤ m` determining the value. Explicit family via `blk d k =
min d k`, `coordVal S c` (value of coordinate `c` as a real, `0` if out of range),
`fam d k ℓ n S` = product-of-block-sums built from `coordVal`.

**Uncertainties.** `MvPolynomial` eval API; `coordVal` out-of-range handling;
family Boolean/degree claims transcribed, not verified.
