import Mathlib

/-!
# The improved sunflower lemma (statement only)

Alweiss–Lovett–Wu–Zhang (2019), with the polynomial-in-`r log k` bound due to
Rao and to Bell–Chueluecha–Warnke.

This file states only the theorem.  Nothing is proved: the theorem ends with
`:= by sorry`.
-/

namespace ImprovedSunflower

/-- A family `B` of finite sets is a **sunflower with core `Y`** when every
pairwise intersection of two *distinct* members of `B` is exactly `Y`.

This "all pairwise intersections coincide" formulation already encodes the usual
picture, given the ambient hypotheses of the lemma:

* if `2 ≤ B.card` then `Y ⊆ s` for every `s ∈ B` (take any other `t ∈ B`);
* the *petals* `s \ Y`, for `s ∈ B`, are pairwise disjoint, since
  `(s \ Y) ∩ (t \ Y) = (s ∩ t) \ Y = ∅` for `s ≠ t`;
* if in addition all members of `B` have the same cardinality `k` and
  `2 ≤ B.card`, then `Y ⊊ s`, so every petal `s \ Y` is nonempty.

The number of **petals** is `B.card`. -/
def IsSunflower {α : Type*} [DecidableEq α] (Y : Finset α) (B : Finset (Finset α)) :
    Prop :=
  ∀ ⦃s⦄, s ∈ B → ∀ ⦃t⦄, t ∈ B → s ≠ t → s ∩ t = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for every integer `k ≥ 2`, every
integer `r ≥ 1`, and every finite family `W` of sets each of cardinality exactly
`k`, if
`|W| > (C * r * log k) ^ k`
then `W` contains a sunflower with `r` petals: there are a core `Y` and a
subfamily `B ⊆ W` with `B.card = r` and `IsSunflower Y B`.

Encoding notes.
* Sets are `Finset α` and the family is a `Finset (Finset α)`; `|W|` is
  `W.card`.  Distinctness of the `r` members of the sunflower is automatic from
  `B.card = r` together with `B : Finset _`.
* `log` is the natural logarithm `Real.log`; changing the base only rescales the
  absolute constant `C`, so the choice is immaterial.
* The hypothesis `2 ≤ k` makes `Real.log k > 0`, so the right–hand side is a
  positive real.  For `k ≤ 1` one has `log k ≤ 0` and the inequality has to be
  stated separately (for `k = 1` the sunflower-free families are exactly those
  with fewer than `r` singletons).
* `C` is existentially quantified *outside* the quantifier over the ambient type
  `α`, so it is a genuine absolute constant, independent of everything.

Equivalently, in terms of the sunflower function `f(k, r)` (the least `N` such
that every family of `N` distinct `k`-sets has an `r`-petal sunflower):
`f(k, r) ≤ (C * r * log k) ^ k`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ (W : Finset (Finset α)),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ (Y : Finset α) (B : Finset (Finset α)),
            B ⊆ W ∧ B.card = r ∧ IsSunflower Y B := by
  sorry

end ImprovedSunflower
