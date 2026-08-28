import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by Bell–Chueluecha–Warnke.

This file contains the *statement only*.  Every theorem ends with `:= by sorry`.
-/

namespace ImprovedSunflower

variable {α : Type*} [DecidableEq α]

/-- `IsSunflower r Y P` says that the finite family of finite sets `P` is a
*sunflower with `r` petals* and *core* `Y`:

* `P` has exactly `r` members (which, being elements of a `Finset`, are automatically
  distinct);
* the core `Y` is contained in every member;
* any two distinct members meet in exactly `Y`.

Consequently the petals `S \ Y` for `S ∈ P` are pairwise disjoint, and every element
lying in two or more members of `P` lies in all of them.  Petals are allowed to be
empty (this can happen for at most one member, namely one equal to `Y`). -/
def IsSunflower (r : ℕ) (Y : Finset α) (P : Finset (Finset α)) : Prop :=
  P.card = r ∧
  (∀ S ∈ P, Y ⊆ S) ∧
  (∀ S ∈ P, ∀ T ∈ P, S ≠ T → S ∩ T = Y)

/-- **Improved sunflower lemma.**
There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and `r ≥ 1`,
every finite family `W` of sets each of cardinality exactly `k` with
`|W| > (C * r * Real.log k) ^ k`
contains a sunflower with `r` petals, i.e. some subfamily `P ⊆ W` with core `Y` such
that `IsSunflower r Y P`.

Encoding notes:
* Sets are `Finset α` over an ambient type `α`; the family `W` is a `Finset (Finset α)`.
* `Real.log` is the natural logarithm; the choice of base only rescales the absolute
  constant `C`, so it is immaterial.
* `k ≥ 2` avoids the degenerate cases `k = 0` (no bound) and `k = 1` (`Real.log 1 = 0`
  collapses the right-hand side); the `k = 1` case is elementary anyway.
* `C` is existentially quantified inside the statement. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ (W : Finset (Finset α)),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ (Y : Finset α) (P : Finset (Finset α)), P ⊆ W ∧ IsSunflower r Y P := by
  sorry

/-- Equivalent packaging in terms of the *sunflower function* `f`, characterised (via `sSup`)
as the largest cardinality of a family of `k`-sets containing no sunflower with `r` petals.
The improved bound reads `f k r ≤ (C * r * Real.log k) ^ k`. -/
theorem improved_sunflower_lemma_function
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ k r : ℕ,
      IsGreatest
        {n : ℕ | ∃ (W : Finset (Finset α)),
          W.card = n ∧ (∀ S ∈ W, S.card = k) ∧
          ¬ ∃ (Y : Finset α) (P : Finset (Finset α)), P ⊆ W ∧ IsSunflower r Y P}
        (f k r)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r →
        (f k r : ℝ) ≤ (C * (r : ℝ) * Real.log (k : ℝ)) ^ k := by
  sorry

end ImprovedSunflower
