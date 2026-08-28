import Mathlib

open Finset

variable {α : Type*}

/-- `IsSunflower r Y 𝒮` states that the finite family of finite sets `𝒮`
is a *sunflower with `r` petals* and *core* `Y`: it has exactly `r`
(necessarily distinct) members, and any two distinct members intersect
exactly in `Y`.

Consequences that follow from the definition (so they are not stated
separately): for `r ≥ 2` one has `Y ⊆ s` for every `s ∈ 𝒮`, the petals
`s \ Y` for `s ∈ 𝒮` are pairwise disjoint, and every element lying in at
least two members of `𝒮` lies in all of them. -/
def IsSunflower [DecidableEq α]
    (r : ℕ) (Y : Finset α) (𝒮 : Finset (Finset α)) : Prop :=
  𝒮.card = r ∧ ∀ s ∈ 𝒮, ∀ t ∈ 𝒮, s ≠ t → s ∩ t = Y

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang 2019; refined by
Rao and by Bell–Chueluecha–Warnke).

There is an absolute constant `C > 0` such that for every `k ≥ 2`, every
`r ≥ 1`, and every finite family `W` of sets, each of cardinality exactly
`k`, if `|W| > (C · r · log k) ^ k` then `W` contains a sunflower with
`r` petals (i.e. some subfamily `𝒮 ⊆ W` is a sunflower with `r` petals
for a suitable core `Y`).

Equivalently, writing `f(k, r)` for the sunflower function (the largest
size of a `k`-uniform family with no `r`-sunflower), this says
`f(k, r) ≤ (C · r · log k) ^ k`.

Encoding notes: `log` is the natural logarithm `Real.log`; the family `W`
is a `Finset (Finset α)` so its members are automatically distinct and
`W.card` is its size; the hypothesis `2 ≤ k` avoids the degenerate cases
`k = 0, 1` where `log k ≤ 0` makes the bound vacuous or false (for
`k = 1` the lemma is trivial since any `r` distinct singletons form a
sunflower with empty core). The constant `C` is existentially quantified
inside the statement, matching "there is an absolute constant `C`". -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
        2 ≤ k → 1 ≤ r →
        (∀ s ∈ W, s.card = k) →
        (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
        ∃ Y : Finset α, ∃ 𝒮 : Finset (Finset α), 𝒮 ⊆ W ∧ IsSunflower r Y 𝒮 := by
  sorry
