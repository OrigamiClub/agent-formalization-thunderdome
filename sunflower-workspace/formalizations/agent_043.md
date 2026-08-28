# Agent 043 — improved sunflower lemma (statement only)

*Note reconstructed from `agent_043.lean` after the agent's session was cut short
before it saved this file; the `.lean` formalization itself was written by the
agent and is complete.*

**Form chosen.** The "large family ⇒ contains a sunflower" direction, with an
absolute constant existentially quantified out front.

**Encoding decisions.**
- Sets are `Finset α` over an arbitrary ambient type `α` with `[DecidableEq α]`;
  the family `W` is `Finset (Finset α)`, so member distinctness (and petal
  distinctness) is automatic.
- Own `IsSunflower r Y P` predicate: `P.card = r` together with "every pairwise
  intersection of two distinct members of `P` equals the core `Y`". No
  requirement that petals `S \ Y` be nonempty; `Y ⊆ S` is left implicit (it
  follows for `r ≥ 2`).
- Logarithm: `Real.log` (natural log); base is immaterial since it only rescales
  `C`.
- Degenerate range: hypothesis `2 ≤ k` excludes `k = 0, 1` (where `Real.log k = 0`
  collapses the bound; `f(1,r) = r`).
- `C` is `∃ C : ℝ, 0 < C ∧ …`, quantified before `α, k, r, W`, so it is genuinely
  absolute.
- Bound stated in `ℝ` after coercion: `(C * r * Real.log k) ^ k < (W.card : ℝ)`.
- Conclusion exhibits both the core `Y` and the petal subfamily `P ⊆ W`.

**Uncertainties.** Mathlib identifier for a sunflower predicate — the agent
assumed none exists in the checkout and defined its own. `Real.log` on `ℕ`-casts
and the coercion sites are best-effort without a compiler.
