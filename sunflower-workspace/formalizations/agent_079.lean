import Mathlib

/-!
# The improved sunflower lemma (statement only)

Alweiss–Lovett–Wu–Zhang (2019), with the bound refined by Rao and by
Bell–Chueluecha–Warnke:

> There is an absolute constant `C` such that for all positive integers `k` and
> `r`, every finite family `W` of sets, each of cardinality exactly `k`, with
> `|W| > (C · r · log k)^k` contains a sunflower with `r` petals.

This file contains the *statement* only. The single theorem ends in `:= by sorry`.
-/

namespace Agent079

variable {α : Type*} [DecidableEq α]

/-- `IsSunflower r Y T` says that `T` is a *sunflower with `r` petals and core
`Y`*: it is a family of `r` sets (as a `Finset (Finset α)` of cardinality `r`
its members are automatically pairwise distinct), each containing the core `Y`,
and such that the intersection of any two distinct members is exactly `Y`.

Consequences (not part of the definition, but implied):
* the petals `s \ Y` for `s ∈ T` are pairwise disjoint, since for distinct
  `s t ∈ T` we have `(s \ Y) ∩ (t \ Y) = (s ∩ t) \ Y = Y \ Y = ∅`;
* for `r ≥ 3`, every element lying in at least two members of `T` lies in `Y`,
  hence in every member (`Y = s ∩ t ⊆ u` for any third member `u`).

The clause `∀ s ∈ T, Y ⊆ s` is redundant once `r ≥ 2` (then `Y = s ∩ t ⊆ s`);
it is kept so that the predicate also behaves sensibly for `r ≤ 1`. -/
def IsSunflower (r : ℕ) (Y : Finset α) (T : Finset (Finset α)) : Prop :=
  T.card = r ∧
  (∀ s ∈ T, Y ⊆ s) ∧
  (∀ ⦃s⦄, s ∈ T → ∀ ⦃t⦄, t ∈ T → s ≠ t → s ∩ t = Y)

/-- **The improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang 2019; bound refined
by Rao and by Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that: for every type `α` with
decidable equality, all naturals `k ≥ 2` and `r ≥ 1`, and every finite family
`W : Finset (Finset α)` all of whose members have cardinality exactly `k`, if

`(C * r * Real.log k) ^ k < |W|`

then `W` contains a sunflower with `r` petals (a subfamily `T ⊆ W` and a core `Y`
with `IsSunflower r Y T`).

Encoding notes:
* `C` is existentially quantified *outside* the quantifier over `α, k, r, W`, so
  it is genuinely absolute (independent of everything else).
* The logarithm is `Real.log` (natural log); the base only changes `C`.
* `k ≥ 2` is assumed so that `Real.log k > 0` and the bound is meaningful
  (for `k ≤ 1` one has `log k ≤ 0` and the displayed bound degenerates).
* `r ≥ 1` matches "positive integers `r`".
* Equivalently: the sunflower function satisfies `f(k, r) ≤ (C r log k)^k`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [inst : DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ s ∈ W, s.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ (Y : Finset α) (T : Finset (Finset α)),
          T ⊆ W ∧ IsSunflower r Y T := by
  sorry

end Agent079
