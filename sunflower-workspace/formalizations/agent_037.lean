import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), with subsequent refinements by Rao and by
Bell–Chueluecha–Warnke:

There is an absolute constant `C` such that for all `k ≥ 2` and `r ≥ 1`, every
finite family `W` of `k`-element sets with `|W| > (C * r * log k) ^ k` contains a
sunflower with `r` petals.

This file states the theorem only; the proof is `by sorry`.
-/

namespace ImprovedSunflower

variable {α : Type*}

/-- A finite family `P` of finite sets is a *sunflower with core `Y`* when any two
distinct members of `P` intersect exactly in `Y`.

Equivalently: every element lying in at least two members of `P` lies in all of
them, and the "petals" `S \ Y` for `S ∈ P` are pairwise disjoint.  When `P` has at
least two members the core is forced to satisfy `Y ⊆ S` for every `S ∈ P`; when in
addition all members have the same cardinality `k ≥ 1`, each petal `S \ Y` is
nonempty, so no separate nonemptiness hypothesis is needed. -/
def IsSunflower [DecidableEq α] (P : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃S⦄, S ∈ P → ∀ ⦃T⦄, T ∈ P → S ≠ T → S ∩ T = Y

/-- `W` *contains a sunflower with `r` petals* when some `r`-element subfamily `P`
of `W` is a sunflower for some core `Y`.

Collecting the petals in a `Finset` already encodes that the `r` petals are
pairwise distinct, so `P.card = r` says exactly "`r` distinct petals". -/
def ContainsSunflower [DecidableEq α] (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ P : Finset (Finset α), P ⊆ W ∧ P.card = r ∧ ∃ Y : Finset α, IsSunflower P Y

/-- **Improved sunflower lemma** (statement only).

There is an absolute constant `C > 0` such that, for every ambient type `α` with
decidable equality, all integers `k ≥ 2` and `r ≥ 1`, and every finite family `W`
of finite subsets of `α` each of cardinality exactly `k`:
if `|W| > (C * r * Real.log k) ^ k` then `W` contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C * r * log k) ^ k`.

Encoding notes:
* `C` is existentially quantified *outside* the quantifier over `α`, `k`, `r`, so
  it is genuinely an absolute constant.
* The logarithm is the natural logarithm `Real.log`; the base only affects `C`.
* The hypothesis `2 ≤ k` avoids the degenerate cases `k = 0` (empty sets) and
  `k = 1` (where `Real.log k = 0` collapses the bound to `0` and the statement
  would be false). -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (W : Finset (Finset α)) (k r : ℕ),
        2 ≤ k → 0 < r →
        (∀ S ∈ W, S.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ContainsSunflower W r := by
  sorry

end ImprovedSunflower
