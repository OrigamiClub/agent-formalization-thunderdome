import Mathlib

/-!
# Improved sunflower lemma — statement only

Alweiss–Lovett–Wu–Zhang (2019), with the bound refined by Rao and by
Bell–Chueluecha–Warnke.  This file contains only the *statement*; the proof is `sorry`.
-/

namespace ImprovedSunflower

variable {α : Type*}

/-- `IsSunflower S Y` says the finsets in the family `S` pairwise intersect in exactly the
*core* `Y`: for all distinct `s, t ∈ S` we have `s ∩ t = Y`.

Consequences of this predicate (not needed for the statement): every element lying in at
least two members of `S` lies in all of them, and the *petals* `s \ Y` (`s ∈ S`) are
pairwise disjoint.  A *sunflower with `r` petals* is such a family `S` with `S.card = r`;
because `S : Finset (Finset α)`, its `r` members are automatically distinct. -/
def IsSunflower [DecidableEq α] (S : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃s : Finset α⦄, s ∈ S → ∀ ⦃t : Finset α⦄, t ∈ S → s ≠ t → s ∩ t = Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
Bell–Chueluecha–Warnke).

There is an absolute constant `C` such that for every ambient type `α`, all integers
`k ≥ 2` and `r ≥ 1`, and every finite family `W` of sets each of cardinality exactly `k`,
if
`|W| > (C · r · log k) ^ k`
then `W` contains a sunflower with `r` petals: an `r`-element subfamily `S ⊆ W` together
with a core `Y` such that `s ∩ t = Y` for all distinct `s, t ∈ S`.

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C · r · log k) ^ k`.

Encoding notes:
* Sets are `Finset α` and a family is a `Finset (Finset α)`; `Real.log` is the natural
  logarithm (its base is immaterial, being absorbed into `C`).
* The hypothesis `2 ≤ k` avoids the degeneracy `Real.log 1 = 0` (for `k = 1` the intended
  reading needs `log k` replaced by something `≥ 1`).
* `α`, `k`, `r` are quantified *inside* the existential, so `C` is one constant independent
  of the ambient type and of `k, r`.
* Petals are not required to be nonempty. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α), (∀ s ∈ W, s.card = k) →
          (W.card : ℝ) > (C * r * Real.log k) ^ k →
            ∃ S : Finset (Finset α), S ⊆ W ∧ S.card = r ∧ ∃ Y : Finset α, IsSunflower S Y := by
  sorry

end ImprovedSunflower
