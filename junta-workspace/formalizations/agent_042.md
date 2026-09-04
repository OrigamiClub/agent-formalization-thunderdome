# Agent 042 — Boolean degree-d on the slice ⇒ junta (statement only)

*Note reconstructed from `agent_042.lean` (session ended before the agent saved this
file; the `.lean` — 2 theorems, all `:= by sorry` — is the agent's own work).*

**Parts stated.** Forward (`filmus_junta_threshold`, `1 ≤ d`, `m(d)` existential)
and the converse witnessed by the explicit family (`filmus_junta_threshold_witness`).

**Encoding.** Slice points carried as bare `S : Finset (Fin n)` with `S.card = k`
side conditions (no subtype); functions `Finset (Fin n) → ℝ`; `BooleanOnSlice n k f`,
`HasDegreeAtMostOnSlice n k d f` (agreement with a `totalDegree ≤ d`
`MvPolynomial (Fin n) ℝ` at the `indicator` vector), and `IsJuntaOnSlice n k m f`
(coordinate set `J`, `J.card ≤ m`, value depends on `S ∩ J`) each take `n k` as
explicit parameters. Explicit family: `block n e i`, `witnessFn n e ℓ`,
`e = min d k`.

**Uncertainties.** Guessed `MvPolynomial` API; family Boolean/degree claims are
transcriptions, not checked.
