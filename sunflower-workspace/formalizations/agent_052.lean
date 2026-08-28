import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao and by Bell–Chueluecha–Warnke.

This file contains the *statement only*.  The single theorem is closed with `:= by sorry`.
-/

namespace ImprovedSunflower

/-- A finite family `𝒮` of finsets is a **sunflower with `r` petals** and **core** `Y`
if it has exactly `r` (necessarily distinct) members and every two distinct members meet
exactly in `Y`.

The petals are the sets `S \ Y` for `S ∈ 𝒮`.  The condition `S ∩ T = Y` for `S ≠ T`
forces the petals to be pairwise disjoint and forces every point that lies in at least two
members to lie in all of them, matching the informal description in the problem statement.

For `r ≥ 2` the core `Y` is uniquely determined by `𝒮`; we nevertheless carry `Y`
explicitly and quantify it existentially in the theorem below. -/
structure IsSunflower {α : Type*} (r : ℕ) (Y : Finset α) (𝒮 : Finset (Finset α)) : Prop where
  /-- the family has exactly `r` petals -/
  card_eq : 𝒮.card = r
  /-- any two distinct members of the family intersect exactly in the core `Y` -/
  pairwise_inter_eq :
    ∀ ⦃S : Finset α⦄, S ∈ 𝒮 → ∀ ⦃T : Finset α⦄, T ∈ 𝒮 → S ≠ T → S ∩ T = Y

/-- **Improved sunflower lemma.**

There is an absolute positive constant `C` such that for all positive integers `k` and `r`,
every finite family `W` of sets, each of cardinality exactly `k`, with
`|W| > (C * r * (log k + 1)) ^ k`, contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f(k, r) ≤ (C * r * (log k + 1)) ^ k`.

Encoding choices (see the accompanying `.md` note for rationale):
* Sets are `Finset α` over an ambient type `α`; a family is a `Finset (Finset α)`, so its
  members are automatically distinct and its cardinality is `Finset.card`.
* `α` is bound *inside* the existential for `C`, so that `C` is genuinely absolute
  (independent of the ambient type).
* `Real.log` is the natural logarithm.  The `+ 1` inside the base makes the bound
  meaningful and the statement true also at `k = 1` (where `Real.log 1 = 0`) without
  affecting the asymptotics for large `k`.
* `C` is existentially quantified and required to be positive.
* The sunflower sub-family `𝒮 ⊆ W`, together with its core `Y`, is existentially
  quantified via the predicate `IsSunflower`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} (k r : ℕ), 0 < k → 0 < r →
        ∀ W : Finset (Finset α),
          (∀ S ∈ W, S.card = k) →
          (C * (r : ℝ) * (Real.log (k : ℝ) + 1)) ^ k < (W.card : ℝ) →
          ∃ (Y : Finset α) (𝒮 : Finset (Finset α)), 𝒮 ⊆ W ∧ IsSunflower r Y 𝒮 := by
  sorry

end ImprovedSunflower
