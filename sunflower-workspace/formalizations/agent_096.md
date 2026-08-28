# agent_096 — improved sunflower lemma (statement only)

## Form chosen

A single existential over the absolute constant, then a universal statement:

```
∃ C : ℝ, 0 < C ∧ ∀ (α) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
  2 ≤ k → 1 ≤ r → (∀ S ∈ W, S.card = k) →
  (C * r * Real.log k) ^ k < (W.card : ℝ) →
  ∃ P ⊆ W, P.card = r ∧ ∃ Y, IsSunflower Y P
```

## Encoding decisions

- **Set family**: `W : Finset (Finset α)` over an ambient type `α` with `[DecidableEq α]`
  (needed for `Finset` intersection). This makes "finite family" and "distinct members"
  automatic; `α` is not required finite.
- **Sunflower**: custom `IsSunflower Y P` with an explicit core `Y`, defined as
  (i) `∀ S ∈ P, Y ⊆ S` and (ii) `∀ S₁ S₂ ∈ P, S₁ ≠ S₂ → S₁ ∩ S₂ = Y`.
  This is the "all pairwise intersections coincide (with `Y`)" formulation. Pairwise-disjoint
  petals and the "≥2 ⇒ all" property are consequences, noted in the docstring.
- **Number of petals / distinctness**: encoded as `P.card = r` together with `P ⊆ W`.
  `P` being a `Finset` gives distinctness for free, so no separate injectivity hypothesis.
- **Petals nonempty**: not required (standard). With `r ≥ 2` distinct members at most one petal
  `S \ Y` can be empty anyway.
- **Cardinality**: `Finset.card` throughout; sets have card exactly `k` via `∀ S ∈ W, S.card = k`.
- **Logarithm**: `Real.log` (natural log). Base choice only rescales the absolute constant `C`.
- **`k = 0, 1` handling**: guarded by `2 ≤ k`. For `k = 1`, `Real.log 1 = 0` collapses the RHS to
  `0`, so the bound could not force `r ≥ 2` petals; the usual fixes (`log k + 1`,
  `max (log k) 1`, `log (k+1)`) are all absorbable into `C`. `r` kept at `1 ≤ r` to match
  "all positive integers `r`"; `r ≥ 2`/`3` is the meaningful regime.
- **Constant `C`**: existentially quantified inside the theorem ("there is an absolute constant"),
  with `0 < C`.
- **Inequality**: strict, `(C * r * log k) ^ k < |W|`, matching the task's `|W| > (C r log k)^k`.
  `^ k` is the natural-number power (`Monoid.npow`); the base is positive under the hypotheses.

## Uncertainties / guessed identifiers

- Mathlib does have a sunflower development (I believe `Mathlib.Combinatorics.SetFamily.Sunflower`
  with a predicate spelled roughly `Finset.IsSunflower` / `IsSunflower`, plus a proof of the
  classical `f(k,r) ≤ k! (r-1)^k` bound). Exact name/argument order is guessed, so a
  self-contained `IsSunflower` is defined here instead of importing one. The improved
  (ALWZ/Rao/BCW) bound is, to my knowledge, not yet in Mathlib.
- `import Mathlib` used for a self-contained file rather than a minimal import list.
- `Real.log` applied to a `Nat` cast: written `Real.log (k : ℝ)` explicitly.
- Syntax `∀ (α : Type*) [DecidableEq α] ...` inside the existential body is believed valid Lean 4.
