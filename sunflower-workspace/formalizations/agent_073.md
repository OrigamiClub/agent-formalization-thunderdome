# agent_073 — improved sunflower lemma (statement only)

## Form chosen

Single `theorem improved_sunflower_lemma : ∃ C : ℝ, 0 < C ∧ ∀ k r, 2 ≤ k → 1 ≤ r → ∀ (α) [DecidableEq α] (W : Finset (Finset α)), (∀ S ∈ W, S.card = k) → (C * r * Real.log k)^k < W.card → ∃ Y 𝒮, 𝒮 ⊆ W ∧ IsSunflower r Y 𝒮`, ending `:= by sorry`.

Plus one auxiliary definition `IsSunflower`.

## Encoding decisions

- **Set representation.** Ambient type `α`; individual sets are `Finset α`; the family `W` is
  `Finset (Finset α)`. A `Finset` family gives finiteness for free and makes `|W|` just
  `W.card : ℕ`. Distinctness of the `r` sunflower members is automatic (elements of a `Finset`).
- **Sunflower predicate.** Defined locally as
  `𝒮.card = r ∧ ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ≠ T → S ∩ T = Y`.
  This is the explicit-core formulation. It forces exactly `r` petals via `𝒮.card = r`, and the
  pairwise-intersection-equals-core condition yields the usual consequences (`Y ⊆ S`; petals
  `S \ Y` pairwise disjoint). The result is returned as a subfamily `𝒮 ⊆ W`.
- **Petals nonempty.** Not imposed. For `r ≥ 2` it is anyway forced: distinct equicardinal
  members cannot equal the common core. For `r = 1` the condition is vacuous, the standard
  degenerate reading.
- **Logarithm.** `Real.log` (natural log). Base is irrelevant since it is absorbed into `C`.
  The threshold is `(C * (r:ℝ) * Real.log (k:ℝ)) ^ k` compared with `(W.card : ℝ)`.
- **k = 0, 1.** Excluded by hypothesis `2 ≤ k`. Rationale: `Real.log 1 = 0` makes the threshold
  `0`, and "`|W| > 0` ⇒ sunflower with `r` petals" is false (need `|W| ≥ r`). `k ≥ 2` is the
  standard convention for this bound (e.g. Tao's exposition).
- **The constant `C`.** Existentially quantified as the outermost binder, with `0 < C`, so it is
  a single absolute constant. The ambient type `α` is quantified inside, so `C` cannot depend on
  it.
- **`r`.** Required `1 ≤ r` (positive integer, as in the statement).
- **Cardinality.** `Finset.card` throughout; coerced to `ℝ` only for the comparison with the
  real-valued threshold.

## Uncertainties

- Mathlib is believed to contain `Finset.IsSunflower` in
  `Mathlib.Combinatorics.SetFamily.Sunflower` with signature roughly
  `IsSunflower (r : ℕ) (t : Finset α) (𝒜 : Finset (Finset α))` (only the classical
  Erdős–Rado bound is formalized there, not this improved one). Exact name / argument order not
  verified, so a self-contained local definition is used instead. If the Mathlib predicate is
  present and matches, `ImprovedSunflower.IsSunflower` could be replaced by it.
- `import Mathlib` used for safety; the minimal import is essentially
  `Mathlib.Analysis.SpecialFunctions.Log.Basic` plus `Mathlib.Data.Finset.Card`.
- Instance binder `[DecidableEq α]` inside the `∀`-telescope is expected to elaborate; if a
  particular Mathlib/Lean version objects, move `α` and its `DecidableEq` instance to
  `variable`s and keep `∃ C` at the top (C still independent of `α`).
- Not fully certain whether the canonical modern statement uses `Real.log k` or `Real.log (r*k)`
  inside the base; the `log k` form (ALWZ / Rao / Tao exposition) is used here.
