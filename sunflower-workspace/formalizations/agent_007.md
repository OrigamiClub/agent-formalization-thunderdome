# agent_007 — improved sunflower lemma (statement only)

## Form chosen

One `def` (`IsSunflower`) plus one `theorem improved_sunflower_lemma := by sorry`.

- `IsSunflower r Y 𝒮` for `𝒮 : Finset (Finset α)`, `Y : Finset α`, `r : ℕ`:
  `𝒮.card = r ∧ ∀ s ∈ 𝒮, ∀ t ∈ 𝒮, s ≠ t → s ∩ t = Y`.
- The theorem: `∃ C : ℝ, 0 < C ∧ ∀ α [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
  2 ≤ k → 1 ≤ r → (∀ s ∈ W, s.card = k) →
  (C * r * Real.log k) ^ k < (W.card : ℝ) →
  ∃ Y 𝒮, 𝒮 ⊆ W ∧ IsSunflower r Y 𝒮`.

## Encoding decisions and why

- **Set representation.** Ambient type `α : Type*` with `[DecidableEq α]`; a set is a
  `Finset α`; the family `W` is a `Finset (Finset α)`. This makes finiteness, size
  (`Finset.card`), and distinctness of members all automatic, with no side hypotheses.
  The sunflower is exhibited as a subfamily `𝒮 ⊆ W` rather than an indexed family,
  which is the lightest way to also get "distinct" and "exactly `r`" for free
  (`𝒮.card = r`).
- **Sunflower definition.** Explicit core `Y` with all pairwise intersections of
  distinct members equal to `Y`. I did not assume a Mathlib predicate exists (see
  uncertainties). Petal disjointness, `Y ⊆ s`, and the "element in ≥ 2 sets ⇒ in all"
  property are consequences for `r ≥ 2`, so they are left out of the definition.
- **Petals nonempty:** not required. The improved sunflower lemma does not need it,
  and for `r ≥ 2` it is essentially forced anyway (distinct `k`-sets with common
  intersection `Y`).
- **`r` count:** exact (`𝒮.card = r`), matching "a sunflower with `r` petals". A larger
  sunflower yields an `r`-sunflower by taking a subset, so this is not a loss.
- **Logarithm:** `Real.log` (natural log). The bound is scale-insensitive in the base
  up to absorbing the constant into `C`, so the base choice is immaterial; `Real.log`
  is the most standard in Mathlib. `(k : ℝ)` coercion inside `Real.log`.
- **Small `k`:** handled by the hypothesis `2 ≤ k`. For `k = 0` there is no
  `0`-uniform family issue but `log 0 = 0` makes the RHS `0`/degenerate; for `k = 1`,
  `log 1 = 0` gives RHS `0` and the statement would claim an `r`-sunflower whenever
  `|W| ≥ 1`, which is false unless `|W| ≥ r` — but the `k = 1` case is trivial anyway
  (any `r` distinct singletons are a sunflower with core `∅`). Restricting to `k ≥ 2`
  matches how Rao / Bell–Chueluecha–Warnke phrase the clean bound.
- **Constant `C`:** existentially quantified inside the theorem, with `0 < C`,
  matching "there is an absolute constant `C`".
- **Comparison `|W| > RHS`:** written as `(RHS : ℝ) < (W.card : ℝ)` with `W.card : ℕ`
  cast to `ℝ`.

## Uncertainties

- **Mathlib sunflower predicate.** I am not confident Mathlib currently has a
  sunflower / `Δ`-system definition or the sunflower lemma. Candidate names I would
  have looked for: `Finset.IsSunflower`, `SetFamily.Sunflower`,
  `Mathlib.Combinatorics.SetFamily.Sunflower`. To be safe I define `IsSunflower`
  locally. If a Mathlib predicate exists it may differ (e.g. indexed family, core as
  a `Set`, or "pairwise intersections all coincide" without naming `Y`).
- **`∀ (α : Type*) [DecidableEq α]` under an `∃`.** I believe instance binders in a
  `∀` telescope inside the statement are accepted; if not, `α` and its `DecidableEq`
  instance could be lifted to `variable`s / section arguments outside the `∃ C`.
- **Coercions.** `Real.log (k : ℝ)`, `(r : ℝ)`, `(W.card : ℝ)` should elaborate, but
  exact insertion points of `Nat.cast` were not machine-checked (no compiler used).
- **Exact constant form in the literature.** Some sources write `(C r log(rk))^k` or
  `(C log k)^{k}` times `r^k`, or use `log(k+1)`. These are equivalent up to the
  absolute constant; I used the `(C · r · log k)^k` form from the task statement.
