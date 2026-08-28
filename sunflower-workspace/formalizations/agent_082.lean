/-
  Improved sunflower lemma (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
  Bell–Chueluecha–Warnke).  STATEMENT ONLY.

  Informal statement being formalized:
  There is an absolute constant `C` such that for all positive integers `k` and `r`,
  every finite family `W` of sets, each of cardinality exactly `k`, with
  `|W| > (C · r · log k)^k`, contains a sunflower with `r` petals — i.e. `r` distinct
  members with a common core `Y` such that any two of them meet exactly in `Y`.
-/

import Mathlib

namespace ImprovedSunflower

variable {α : Type*}

/-- `IsSunflower core petals` says that the finite family `petals` of finsets is a
sunflower with the given `core`: any two distinct members intersect in exactly `core`.

Consequences (not part of the definition): if `petals` has at least two members then
`core` is forced to be their common pairwise intersection, `core ⊆ S` for every
`S ∈ petals`, and the "petals" `S \ core` are pairwise disjoint.

Mathlib has an essentially identical predicate `Finset.IsSunflower` in
`Mathlib.Combinatorics.SetFamily.Sunflower` (argument order / exact name not relied
on here); this local copy keeps the file self-contained. -/
def IsSunflower [DecidableEq α] (core : Finset α) (petals : Finset (Finset α)) : Prop :=
  (petals : Set (Finset α)).Pairwise fun S T => S ∩ T = core

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` (independent of everything, in particular of the
ambient type `α`) such that: for every type `α` with decidable equality, all naturals
`k, r` with `1 ≤ r` and `2 ≤ k` (for `k ≤ 1` the quantity `log k` degenerates), and
every finite family `W : Finset (Finset α)` all of whose members have cardinality
exactly `k`, if

  `(C * r * Real.log k) ^ k < (W.card : ℝ)`

then `W` contains a sunflower with `r` petals: there is a `core` and a subfamily
`T ⊆ W` with `r ≤ T.card` that is a sunflower with that `core`.

Equivalently, for the sunflower function `f k r` (least `N` forcing a sunflower with
`r` petals among `k`-sets), `f k r ≤ (C * r * Real.log k) ^ k`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type) [DecidableEq α] (k r : ℕ), 1 ≤ r → 2 ≤ k →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ (core : Finset α) (T : Finset (Finset α)),
            T ⊆ W ∧ r ≤ T.card ∧ IsSunflower core T := by
  sorry

end ImprovedSunflower
