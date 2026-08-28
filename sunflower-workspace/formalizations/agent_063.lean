import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with the constant/exponent refinements of Rao and of
Bell–Chueluecha–Warnke:

There is an absolute constant `C` such that for every `k ≥ 2` and every `r ≥ 1`, any finite
family `W` of sets each of cardinality exactly `k` with `|W| > (C · r · log k) ^ k` contains a
sunflower with `r` petals.

Statement only: the theorem ends in `:= by sorry`.
-/

open scoped BigOperators

variable {α : Type*}

/-- `S` is a *sunflower with core `Y`* : any two distinct members of `S` meet exactly in `Y`.
Equivalently, every element lying in `≥ 2` members of `S` lies in all of them, and the petals
`s \ Y` for `s ∈ S` are pairwise disjoint. The number of petals is `S.card`.

(Mathlib may carry an essentially identical predicate, e.g. `Finset.IsSunflower`, with signature
`(𝒮 : Finset (Finset α)) (t : Finset α) : Prop`; this local definition is used to keep the file
self-contained and independent of that identifier.) -/
def IsSunflowerWith [DecidableEq α] (S : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ S → s ≠ t → s ∩ t = Y

/-- `W` *contains a sunflower with `r` petals* : some `r`-element subfamily of `W` is a sunflower
for some core `Y`. Distinctness of the `r` petals is automatic from `S.card = r` (`S` a `Finset`). -/
def ContainsSunflower [DecidableEq α] (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ S : Finset (Finset α), S ⊆ W ∧ S.card = r ∧ ∃ Y : Finset α, IsSunflowerWith S Y

/-- **Improved sunflower lemma** (ALWZ 2019; Rao; Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for all integers `k ≥ 2` and `r ≥ 1`, over any
ambient type `α`, every finite family `W : Finset (Finset α)` whose members all have cardinality
exactly `k` and with `(C · r · log k) ^ k < |W|` contains a sunflower with `r` petals.

Encoding notes:
* `Real.log` is the natural logarithm; the choice of base is absorbed into `C`.
* The hypothesis `2 ≤ k` is imposed because at `k = 1` one has `Real.log 1 = 0`, making the RHS
  `0` and the literal statement false (a family of `< r` distinct singletons has no `r`-petal
  sunflower). Rao and BCW likewise state the bound for `k ≥ 2`.
* `C` is existentially quantified inside the statement (an absolute constant, independent of
  `α, k, r, W`).
* Equivalent "sunflower function" phrasing: with `f k r` the least `N` forcing an `r`-petal
  sunflower among `k`-sets, this says `f k r ≤ (C * r * Real.log k) ^ k` for `k ≥ 2`.
-/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ), 2 ≤ k → 1 ≤ r →
        ∀ W : Finset (Finset α),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ContainsSunflower W r := by
  sorry
