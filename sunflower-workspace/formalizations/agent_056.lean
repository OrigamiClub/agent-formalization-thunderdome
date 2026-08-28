import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with the bound refined by Rao and by
Bell–Chueluecha–Warnke.  This file states the theorem only; the proof is `sorry`.
-/

namespace ImprovedSunflower

/-- A *sunflower with `r` petals* and *core* `Y`.

`IsSunflower r Y P` states that the finite family of sets `P` (a `Finset (Finset α)`,
so its members are automatically distinct) consists of exactly `r` sets, each of which
contains the core `Y`, and such that any two distinct members meet **exactly** in `Y`.

Equivalently: every element lying in at least two members of `P` lies in `Y` (hence in
all of them), and the petals `S \ Y` for `S ∈ P` are pairwise disjoint.  In the
`k`-uniform setting of the lemma below the petals are automatically nonempty, so that
is not imposed here. -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (Y : Finset α)
    (P : Finset (Finset α)) : Prop :=
  P.card = r ∧
  (∀ S ∈ P, Y ⊆ S) ∧
  (∀ S ∈ P, ∀ T ∈ P, S ≠ T → S ∩ T = Y)

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
Bell–Chueluecha–Warnke).

There is an absolute constant `C` such that for every `r ≥ 1` and every `k ≥ 2`, any
finite family `W` of sets, each of cardinality exactly `k`, with
`(C * r * Real.log k) ^ k < |W|`
contains a sunflower with `r` petals.

Encoding notes:
* Sets are `Finset α` over an arbitrary ambient type `α`; the family `W` is a
  `Finset (Finset α)`, so distinctness of its members is automatic and its size is
  `W.card`.
* `log` is the natural logarithm `Real.log`; the choice of base only changes the
  absolute constant `C`.
* The displayed bound is false when `k = 1` (there `Real.log 1 = 0`, but
  `f(1, r) = r`), and `log 0` is not meaningful, so we require `2 ≤ k`.
* `C` is existentially quantified *outside* the quantifier over the ambient type `α`,
  so it is a genuine absolute constant independent of everything.
* The conclusion produces the core `Y` and the subfamily `P ⊆ W` of petals. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ S ∈ W, S.card = k) →
        (C * (r : ℝ) * Real.log k) ^ k < (W.card : ℝ) →
        ∃ (Y : Finset α) (P : Finset (Finset α)), P ⊆ W ∧ IsSunflower r Y P := by
  sorry

end ImprovedSunflower
