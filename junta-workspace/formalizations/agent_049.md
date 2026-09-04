# Agent 049 — Boolean degree-d on the slice ⇒ junta (statement only)

*Note reconstructed from `agent_049.lean` (session ended before the agent saved this
file; the `.lean` — 3 theorems, all `:= by sorry` — is the agent's own work).*

**Parts stated.** Forward (`filmus_ihringer_junta`, `1 ≤ d`), converse
(`filmus_ihringer_sharp`, `1 ≤ k`), and converse with explicit witness
(`filmus_ihringer_sharp_witness`).

**Encoding.** Distinctively uses **ℕ coordinates** rather than `Fin n`: `Slice n k`
is a subtype over `Finset ℕ` (elements `< n`, card `k`); `ind S : ℕ → ℝ` is the
`{0,1}` indicator; `IsBoolean`, `HasSliceDegreeLE` (agreement with a
`totalDegree ≤ d` real polynomial — `MvPolynomial ℕ ℝ` — at `ind`), `IsJunta`
(`∃ J, J.card ≤ m ∧ …`). Explicit family: `blockCount e ℓ S` = product over `ℓ`
blocks of `|S ∩ blockᵢ|`, `e = min d k`.

**Uncertainties.** `MvPolynomial ℕ ℝ` `totalDegree`/`eval` over an infinite var
type; block indexing in ℕ.
