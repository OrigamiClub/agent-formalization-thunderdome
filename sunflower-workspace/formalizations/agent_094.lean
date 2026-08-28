/-
Agent 094 — Formalization of the *statement* of the improved sunflower lemma.

Improved sunflower lemma (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
Bell–Chueluecha–Warnke): there is an absolute constant `C` such that for all
positive integers `k` and `r`, every finite family `W` of `k`-element sets with
`|W| > (C · r · log k)^k` contains a sunflower with `r` petals.

Statement only: the theorem ends with `:= by sorry`.
-/

import Mathlib

open scoped Classical

namespace Agent094

/-- `IsSunflower r Y 𝓢` says that the finite family of finsets `𝓢` is a
*sunflower with `r` petals* and *core* `Y`:

* `𝓢` has exactly `r` members, and
* any two distinct members meet in exactly `Y`.

Members of `𝓢` are automatically pairwise distinct, being elements of a `Finset`.
Given the pairwise-intersection condition, every element lying in `≥ 2` members
lies in all of them, and the petals `S \ Y` (for `S ∈ 𝓢`) are pairwise disjoint.
For a family whose members all have the same size and with `r ≥ 2`, the petals
are moreover automatically nonempty, so this predicate is not weakened by
omitting an explicit nonemptiness clause. -/
def IsSunflower {α : Type*} (r : ℕ) (Y : Finset α) (𝓢 : Finset (Finset α)) : Prop :=
  𝓢.card = r ∧
    ∀ ⦃S₁⦄, S₁ ∈ 𝓢 → ∀ ⦃S₂⦄, S₂ ∈ 𝓢 → S₁ ≠ S₂ → S₁ ∩ S₂ = Y

/-- **Improved sunflower lemma** (statement only).

There is an absolute positive constant `C` such that, for every type `α`, all
positive integers `k` and `r`, and every finite family `W` of finite subsets of
`α`:

* if every member of `W` has exactly `k` elements, and
* `W` has more than `(C · r · log (k+1))^k` members,

then `W` contains a sunflower with `r` petals (a subfamily `𝓢 ⊆ W` that is an
`r`-petal sunflower for some core `Y`).

Encoding notes:
* Sets are `Finset α`; the family `W` is a `Finset (Finset α)`, so its members
  are automatically distinct and `W` is automatically finite.
* Cardinalities are `Finset.card`.
* The logarithm is `Real.log`, applied to `(k + 1 : ℝ)` rather than `(k : ℝ)`.
  Using `k + 1` keeps the bound meaningful (nonzero) at `k = 1`, where
  `Real.log 1 = 0` would otherwise make the hypothesis vacuously strong; this
  changes the statement only by an absolute constant factor for large `k`, since
  `log (k+1) = Θ(log k)`.
* `C` is existentially quantified inside the theorem.
* `≤` vs `=` on the number of petals: we ask for exactly `r` petals, matching
  "a sunflower with `r` petals"; a sunflower with more petals yields one with
  exactly `r` by discarding petals. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} (k r : ℕ) (W : Finset (Finset α)),
        0 < k → 0 < r →
        (∀ S ∈ W, S.card = k) →
        (C * (r : ℝ) * Real.log (k + 1 : ℝ)) ^ k < (W.card : ℝ) →
        ∃ Y : Finset α, ∃ 𝓢 : Finset (Finset α), 𝓢 ⊆ W ∧ IsSunflower r Y 𝓢 := by
  sorry

/-- Equivalent phrasing via the *sunflower function* `sunflowerFn k r`, the least
`N` such that every family of `N` sets of size `k` contains an `r`-petal
sunflower.  The improved lemma bounds it by `(C · r · log (k+1))^k`.  (Here
`sunflowerFn` is left abstract; only its defining property is used.) -/
theorem improved_sunflower_bound
    (sunflowerFn : ℕ → ℕ → ℕ)
    (hspec : ∀ {α : Type*} (k r : ℕ) (W : Finset (Finset α)),
      (∀ S ∈ W, S.card = k) → sunflowerFn k r ≤ W.card →
        ∃ Y : Finset α, ∃ 𝓢 : Finset (Finset α), 𝓢 ⊆ W ∧ IsSunflower r Y 𝓢) :
    ∃ C : ℝ, 0 < C ∧ ∀ k r : ℕ, 0 < k → 0 < r →
      (sunflowerFn k r : ℝ) ≤ (C * (r : ℝ) * Real.log (k + 1 : ℝ)) ^ k := by
  sorry

end Agent094
