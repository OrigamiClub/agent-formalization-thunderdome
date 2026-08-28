import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains only the *statement*; the proof is `sorry`.
-/

namespace ImprovedSunflower

variable {α : Type*}

/-- A **sunflower with `r` petals** and **core** `Y` is a family `S` of exactly `r` sets
(automatically distinct, since `S : Finset (Finset α)`) whose pairwise intersections are all
equal to `Y`.

`Set.Pairwise` only constrains *distinct* members, so this says exactly
`S₁ ∩ S₂ = Y` for every `S₁ ≠ S₂` in `S`. Consequences (not part of the definition): every
element lying in at least two members of `S` lies in all of them, and the petals `s \ Y`
(`s ∈ S`) are pairwise disjoint. When the members of `S` all have the same cardinality
`k` and `2 ≤ r`, the petals are automatically nonempty (a member equal to `Y` would force,
by distinctness, another member to strictly contain `Y`, impossible at equal cardinality). -/
def IsSunflower [DecidableEq α] (r : ℕ) (Y : Finset α) (S : Finset (Finset α)) : Prop :=
  S.card = r ∧ (S : Set (Finset α)).Pairwise (fun s₁ s₂ => s₁ ∩ s₂ = Y)

/-- **Improved sunflower lemma.**
There is an absolute constant `C` such that for all integers `k ≥ 2` and `r ≥ 1`, every finite
family `W` of sets each of cardinality exactly `k` with
`#W > (C · r · log k) ^ k`
contains a sunflower with `r` petals (equivalently, the sunflower function satisfies
`f(k, r) ≤ (C · r · log k) ^ k`).

Encoding notes:
* Sets are `Finset α` over an arbitrary ambient type with decidable equality; the family is a
  `Finset (Finset α)`.
* `Real.log` is the natural logarithm. The hypothesis `2 ≤ k` excludes the degenerate case
  `k = 1` (where `Real.log 1 = 0` makes the displayed bound false) and `k = 0`.
* `C` is quantified existentially, and the quantification over the ambient type `α` sits inside
  the existential, expressing that `C` is genuinely absolute: independent of `α`, `k`, and `r`.
* Distinctness of the `r` members of the sunflower is automatic (`Finset`). -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ s ∈ W, s.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ (Y : Finset α) (S : Finset (Finset α)), S ⊆ W ∧ IsSunflower r Y S := by
  sorry

end ImprovedSunflower
