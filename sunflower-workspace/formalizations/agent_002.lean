/-
Improved sunflower lemma — statement only.

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file states the theorem and ends with `:= by sorry`; nothing is proved.
-/
import Mathlib

namespace ImprovedSunflower

open Real

/-- A **sunflower with `r` petals and core `Y`**: a family `S` of exactly `r` sets
(distinct, since `S : Finset _` and `S.card = r`) whose pairwise intersections are all
equal to `Y`.

`Set.Pairwise` here says: for `s t ∈ S` with `s ≠ t`, `s ∩ t = Y`.

Facts that follow from this definition and are therefore *not* stated separately:
* every element lying in at least two members of `S` lies in all of them;
* the petals `s \ Y`, for `s ∈ S`, are pairwise disjoint;
* if in addition all members of `S` have the same cardinality and `r ≥ 2`, then every
  petal `s \ Y` is nonempty (`Y ⊊ s`). -/
def IsSunflower {α : Type*} [DecidableEq α]
    (r : ℕ) (Y : Finset α) (S : Finset (Finset α)) : Prop :=
  S.card = r ∧ (↑S : Set (Finset α)).Pairwise (fun s t => s ∩ t = Y)

/-- **Improved sunflower lemma.**

There is an absolute constant `C` such that for all integers `k ≥ 2` and `r ≥ 1`, and every
ambient type `α`, every finite family `W` of subsets of `α` each of cardinality exactly `k`
with
`|W| > (C · r · log k) ^ k`
contains a sunflower with `r` petals (a subfamily `S ⊆ W` with `IsSunflower r Y S` for some
core `Y`).

Equivalently, if `f k r` denotes the least `N` such that every family of `N` distinct
`k`-element sets contains a sunflower with `r` petals, then `f k r ≤ (C · r · log k) ^ k`.

Encoding notes:
* `k` is restricted to `k ≥ 2` so that `Real.log k ≥ Real.log 2 > 0`; the cases `k = 0, 1`
  are degenerate (`log k ≤ 0`) and are not covered by this phrasing.
* `C` is existentially bound *outside* the quantifier over `α, k, r`, so it is genuinely
  absolute.
* The count `|W|` is `Finset.card`; the strict inequality `... < (W.card : ℝ)` is the
  Lean rendering of `|W| > (C r log k)^k`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ Y : Finset α, ∃ S ⊆ W, IsSunflower r Y S := by
  sorry

end ImprovedSunflower
