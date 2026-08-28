import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file states the theorem only; every proof is `by sorry`.

Mathlib already contains a sunflower API in `Mathlib/Combinatorics/SetFamily/Sunflower.lean`
(a predicate `Finset.IsSunflower` on a family together with a core, plus the classical
Erdős–Rado bound `(r - 1) ^ k * k !`). The *improved* quasi-polynomial bound
`(C · r · log k) ^ k` is, to the author's knowledge, not yet in Mathlib. To keep this
file self-contained and independent of the exact spelling of Mathlib's identifiers, a
local `IsSunflower` predicate is defined below.
-/

namespace ImprovedSunflower

/-- `IsSunflower P Y` means that the finite family of finite sets `P` forms a
*sunflower* with *core* `Y`: any two distinct members of `P` meet in exactly `Y`.

The *petals* are the sets `S \ Y` for `S ∈ P`; the number of petals is `P.card`
(members of a `Finset` are automatically distinct). Petals are **not** required to be
nonempty. When `2 ≤ P.card` this condition forces `Y = ⋂ S ∈ P, S`, forces `Y ⊆ S`
for every `S ∈ P`, and makes the petals pairwise disjoint; equivalently, every element
lying in `≥ 2` members of `P` lies in all of them. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (P : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃S : Finset α⦄, S ∈ P → ∀ ⦃T : Finset α⦄, T ∈ P → S ≠ T → S ∩ T = Y

/-- **Improved sunflower lemma**
(Alweiss–Lovett–Wu–Zhang; Rao; Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for every `k ≥ 2`, every `r ≥ 1`,
every ambient type `α`, and every finite family `W` of `k`-element subsets of `α`
with strictly more than `(C · r · log k) ^ k` members, the family `W` contains a
sunflower with `r` petals: an `r`-element subfamily `P ⊆ W` whose pairwise
intersections all coincide with some common core `Y`.

Encoding notes:
* Sets are `Finset α` for an arbitrary type `α`; the family is `W : Finset (Finset α)`,
  so `W.card` is `Finset.card` and members of the sunflower `P` are automatically
  distinct.
* `log` is the natural logarithm `Real.log`; any other fixed base only rescales `C`.
* `C` is existentially quantified *outside* the quantifier over `α, k, r, W`, so it is
  genuinely absolute (independent of the ambient type and of `k, r`).
* The hypothesis `2 ≤ k` sidesteps the degenerate case `log 1 = 0` (for `k = 1` a
  family of singletons is already a sunflower as soon as it has `r` members, which the
  bound `(C · r · log 1) ^ 1 = 0` would not detect). -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ S ∈ W, S.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ P : Finset (Finset α),
          P ⊆ W ∧ P.card = r ∧ ∃ Y : Finset α, IsSunflower P Y := by
  sorry

/-- Reformulation as an upper bound on the *sunflower function* `f(k, r)`
(`f(k, r) ≤ (C · r · log k) ^ k`).

Contrapositive of `improved_sunflower_lemma`: if the `k`-uniform family `W` contains
no `r`-petal sunflower at all, then `|W| ≤ (C · r · log k) ^ k`. -/
theorem improved_sunflower_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ S ∈ W, S.card = k) →
        (∀ P : Finset (Finset α), P ⊆ W → P.card = r →
            ∀ Y : Finset α, ¬ IsSunflower P Y) →
        (W.card : ℝ) ≤ (C * (r : ℝ) * Real.log (k : ℝ)) ^ k := by
  sorry

end ImprovedSunflower
