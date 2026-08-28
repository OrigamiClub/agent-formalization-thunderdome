import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with refinements by Rao and by
Bell–Chueluecha–Warnke: there is an absolute constant `C` such that every finite
family of `k`-element sets with more than `(C · r · log k) ^ k` members contains a
sunflower with `r` petals.

Statement only: the theorem ends with `:= by sorry`.
-/

namespace ImprovedSunflower

variable {α : Type*}

/-- A **sunflower with `r` petals** and core `core`, living in an ambient type `α`.

`petals` is a `Finset` of set-valued members, so its `r` elements are automatically
distinct.  Any two distinct petals meet *exactly* in `core`, and `core` is contained
in every petal.

For `r ≥ 2` the field `core_subset_petals` is redundant (it follows from
`pairwise_inter_eq_core`), each difference `S \ core` is nonempty, and the
differences `S \ core` are pairwise disjoint — i.e. this is the usual notion. -/
structure IsSunflower [DecidableEq α] (r : ℕ) (core : Finset α)
    (petals : Finset (Finset α)) : Prop where
  /-- there are exactly `r` petals (distinct, since `petals` is a `Finset`) -/
  card_petals : petals.card = r
  /-- any two distinct petals intersect exactly in the core -/
  pairwise_inter_eq_core : ∀ S ∈ petals, ∀ T ∈ petals, S ≠ T → S ∩ T = core
  /-- the core is contained in every petal -/
  core_subset_petals : ∀ S ∈ petals, core ⊆ S

/-- **Improved sunflower lemma.**
There is an absolute constant `C > 0` such that for every `k ≥ 2`, every `r ≥ 1`,
and every finite family `W` of sets each of cardinality exactly `k`, if
`|W| > (C · r · log k) ^ k` then some sub-family of `W` is a sunflower with `r`
petals.

Equivalently: the sunflower function satisfies `f (k, r) ≤ (C · r · log k) ^ k`.

Encoding notes:
* Sets are `Finset α`; a family is a `Finset (Finset α)` over an arbitrary ambient
  type `α`, quantified *inside* the existential so that `C` is genuinely absolute
  (independent of `α`, `k`, `r`).
* `Real.log` is the natural logarithm; the base is irrelevant, being absorbed into
  `C`.
* `k ≥ 2` is assumed so that `Real.log k > 0`.  At `k = 1` the right-hand side is
  `0`, and the statement would be false there (any `r` distinct singletons already
  form a sunflower with `r` petals), so the `k = 1` "positive integer" case is
  deliberately excluded. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α), (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
            ∃ (core : Finset α) (petals : Finset (Finset α)),
              petals ⊆ W ∧ IsSunflower r core petals := by
  sorry

end ImprovedSunflower
