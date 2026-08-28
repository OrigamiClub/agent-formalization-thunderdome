/-
Agent 077 — Formalization of the *statement* of the improved sunflower lemma
(Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by Bell–Chueluecha–Warnke).

Statement only. Every theorem ends in `:= by sorry`. Nothing is proved.
-/

import Mathlib

open scoped BigOperators

namespace Agent077

/-- A family `𝒮` of finite subsets of `α` forms a **sunflower with core `Y`** if

* `Y` is contained in every member of `𝒮`, and
* any two distinct members of `𝒮` intersect in exactly `Y`.

Consequences of this definition (not needed for the statement):
the petals `S \ Y` for `S ∈ 𝒮` are pairwise disjoint, and every element of `α`
lying in at least two members of `𝒮` lies in all of them (namely in `Y`). -/
def IsSunflower {α : Type*} [DecidableEq α]
    (𝒮 : Finset (Finset α)) (Y : Finset α) : Prop :=
  (∀ S ∈ 𝒮, Y ⊆ S) ∧
  (∀ S ∈ 𝒮, ∀ T ∈ 𝒮, S ≠ T → S ∩ T = Y)

/-- `W` **contains a sunflower with `r` petals** if some `r`-element subfamily of `W`
is a sunflower (for some core `Y`).  Because `𝒮 : Finset (Finset α)`, its members are
automatically distinct, so `𝒮.card = r` really encodes `r` distinct petals. -/
def HasSunflower {α : Type*} [DecidableEq α]
    (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ 𝒮 : Finset (Finset α), 𝒮 ⊆ W ∧ 𝒮.card = r ∧ ∃ Y : Finset α, IsSunflower 𝒮 Y

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for every ambient type `α`, all
integers `k ≥ 2` and `r ≥ 1`, and every finite family `W` of subsets of `α` each of
cardinality exactly `k`, if
`|W| > (C · r · log k)^k`
then `W` contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C · r · log k)^k`.

Here `log` is the natural logarithm (`Real.log`); the hypothesis `2 ≤ k` guarantees
`Real.log k > 0` so the bound is a positive real raised to the `k`-th power. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (k r : ℕ),
        2 ≤ k → 0 < r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          HasSunflower W r := by
  sorry

end Agent077
