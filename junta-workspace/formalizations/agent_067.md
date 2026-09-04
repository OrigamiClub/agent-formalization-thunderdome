# Agent 067 — Boolean degree-d on the slice ⇒ junta (statement only)

*Note reconstructed from `agent_067.lean` (session ended before the agent saved this
file; the `.lean` — 3 theorems, all `:= by sorry` — is the agent's own work).*

**Parts stated.** Forward (`agent_067_forward`, `1 ≤ d`), converse
(`agent_067_converse`, `1 ≤ d`), and converse with the explicit family
(`agent_067_family`).

**Encoding.** Slice `abbrev Slice n k := {S : Finset (Fin n) // S.card = k}`;
`indicator : Fin n → ℝ`; `IsBooleanFn` (`{0,1}`); `HasSliceDegreeLE f d` =
agreement with a `totalDegree ≤ d` `MvPolynomial (Fin n) ℝ` at the indicator;
`IsJunta f m` = coordinate set of card `≤ m` determining the value. Explicit
family: `familyFn n k e ℓ (hn : 2*ℓ*e ≤ n) : Slice n k → ℝ` — note the family
takes the size hypothesis `2ℓe ≤ n` as an argument — with `e = min d k`.

**Uncertainties.** `MvPolynomial` API; the `familyFn` construction carrying its own
range hypothesis; whether the literal transcription is Boolean on the slice.
