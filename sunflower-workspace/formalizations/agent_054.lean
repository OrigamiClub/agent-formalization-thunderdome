import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains the *statement only*.  The single theorem ends in `:= by sorry`;
nothing is proved.
-/

open scoped BigOperators

/-- A *sunflower with `r` petals and core `Y`*.

`F` is a family of exactly `r` (distinct, since `F : Finset _`) finite sets, any
two distinct members of which meet exactly in `Y`.  Equivalently the petals
`A \ Y` (`A ∈ F`) are pairwise disjoint, and every point contained in at least
two members of `F` is contained in all of them.

This mirrors `Finset.IsSunflower` from Mathlib
(`Mathlib/Combinatorics/SetFamily/Sunflower.lean`), which records the pairwise
condition `(F : Set (Finset α)).Pairwise (fun a b => a ∩ b = Y)` and tracks the
petal count separately through `F.card`; here the count `r` is bundled in. -/
def IsSunflower {α : Type*} [DecidableEq α] (r : ℕ) (Y : Finset α)
    (F : Finset (Finset α)) : Prop :=
  F.card = r ∧ (F : Set (Finset α)).Pairwise fun A B => A ∩ B = Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for every ambient type `α`, all
integers `k ≥ 2` and `r ≥ 1`, and every finite family `W` of sets each of
cardinality exactly `k`, if
`(C · r · log k) ^ k < |W|`
then `W` contains a sunflower with `r` petals (a subfamily `F ⊆ W` and a core `Y`
with `IsSunflower r Y F`).

Equivalently, the sunflower function obeys `f(k, r) ≤ (C · r · log k) ^ k`.

Conventions:
* Sets are `Finset α` over an arbitrary type; the family `W : Finset (Finset α)`
  carries distinctness of its members for free.
* `log` is the natural logarithm `Real.log`; changing the base only rescales `C`.
* `2 ≤ k` sidesteps the degenerate `k = 1` case, in which `log k = 0` and the
  right-hand side collapses to `0`.  Replacing `Real.log (k : ℝ)` by
  `max (Real.log (k : ℝ)) 1` would readmit `k = 1` at the cost of a less
  standard-looking bound; `C` absorbs the difference. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 1 ≤ r → 2 ≤ k →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ F ⊆ W, ∃ Y : Finset α, IsSunflower r Y F := by
  sorry
