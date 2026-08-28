import Mathlib

namespace ImprovedSunflower

/-- A *sunflower with `r` petals and core `Y`* is a family `𝒮` of finitely many sets with
exactly `r` members such that any two distinct members meet in exactly `Y`.

Consequences of this definition (not part of it):
* every element lying in two members lies in every member (`Y ⊆ S` for each `S ∈ 𝒮`);
* the petals `S \ Y`, for `S ∈ 𝒮`, are pairwise disjoint;
* for `r ≥ 2`, if in addition all members are equicardinal then every petal is nonempty
  (members are distinct, so no member can equal the core).

Mathlib has an essentially identical predicate `Finset.IsSunflower`
(in `Mathlib.Combinatorics.SetFamily.Sunflower`); it is restated here so that this file is
self-contained and the intended reading is explicit.  Distinctness of the `r` members is
automatic, since `𝒮 : Finset (Finset α)`. -/
def IsSunflower {α : Type*} [DecidableEq α]
    (r : ℕ) (Y : Finset α) (𝒮 : Finset (Finset α)) : Prop :=
  𝒮.card = r ∧ ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ≠ T → S ∩ T = Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang, 2019; with the refinements of
Rao and of Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and `r ≥ 1`, every
finite family `W` of sets, each of cardinality exactly `k`, with
`(C * r * Real.log k) ^ k < |W|`, contains a sunflower with `r` petals: a subfamily
`𝒮 ⊆ W` that is a sunflower with `r` petals for some core `Y`.

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C * r * Real.log k) ^ k`.

Encoding notes:
* `log` is the natural logarithm `Real.log`; the base only changes `C`.
* The restriction `k ≥ 2` avoids the degeneracy `Real.log 1 = 0`: for `k = 1` the correct
  threshold is `≈ r`, not `0`, so the unrestricted statement would be false.
* `C` is an explicit existential, hence genuinely absolute — in particular independent of
  the ambient type `α`, which is universally quantified *inside* the existential. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ (α : Type*) [DecidableEq α] (W : Finset (Finset α)),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ∃ (Y : Finset α) (𝒮 : Finset (Finset α)), 𝒮 ⊆ W ∧ IsSunflower r Y 𝒮 := by
  sorry

end ImprovedSunflower
