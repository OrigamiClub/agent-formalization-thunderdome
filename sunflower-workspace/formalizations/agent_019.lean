import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with the bound refined by Rao and by
Bell–Chueluecha–Warnke:

There is an absolute constant `C` such that for all positive integers `k` and `r`,
every finite family `W` of sets, each of cardinality exactly `k`, with
`|W| > (C * r * log k) ^ k` contains a sunflower with `r` petals.

This file states the theorem only.  The single `theorem` ends in `:= by sorry`;
nothing is proved.
-/

namespace ImprovedSunflower

variable {α : Type*} [DecidableEq α]

/-- A *sunflower with `r` petals* and *core* `Y`, realized as a finite family `𝒮`
of finsets over `α`:

* `𝒮` has exactly `r` members (its members are automatically distinct, being a
  `Finset`);
* the core `Y` is contained in every member;
* any two distinct members intersect in exactly `Y`.

The last condition is equivalent to saying that the petals `S \ Y` (`S ∈ 𝒮`) are
pairwise disjoint, and — for `r ≥ 2` — that every element lying in at least two
members lies in all of them. Petals are **not** required to be nonempty. -/
def IsSunflower (r : ℕ) (Y : Finset α) (𝒮 : Finset (Finset α)) : Prop :=
  𝒮.card = r ∧
  (∀ S ∈ 𝒮, Y ⊆ S) ∧
  (∀ S₁ ∈ 𝒮, ∀ S₂ ∈ 𝒮, S₁ ≠ S₂ → S₁ ∩ S₂ = Y)

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang 2019; Rao;
Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for every ambient type `α`, all
integers `k ≥ 2` and `r ≥ 1`, and every `k`-uniform finite family `W` of finsets
over `α`, if
`(C * r * Real.log k) ^ k < W.card`
then `W` contains a subfamily `𝒮` that is a sunflower with `r` petals (with some
core `Y`).

Encoding notes:
* Sets are `Finset α` over an arbitrary ambient type `α`; the family is
  `W : Finset (Finset α)`.  `α` is bound *inside* the existential for `C`, so `C`
  is genuinely one absolute constant, independent of `α`, `k`, `r`, `W`.
* `Real.log` is the natural logarithm; the choice of base only rescales `C`.
* `k = 1` is excluded (`2 ≤ k`) because `Real.log 1 = 0` makes the literal bound
  degenerate; `k = 1` is trivial anyway.  An alternative that keeps all positive
  `k` is to replace `Real.log k` by `Real.log k + 1` or `Real.log (k + 1)`.
* The conclusion asks for *exactly* `r` petals; a family with more can always be
  thinned. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ S ∈ W, S.card = k) →
        (C * (r : ℝ) * Real.log k) ^ k < (W.card : ℝ) →
        ∃ (Y : Finset α) (𝒮 : Finset (Finset α)),
          𝒮 ⊆ W ∧ IsSunflower r Y 𝒮 := by
  sorry

end ImprovedSunflower
