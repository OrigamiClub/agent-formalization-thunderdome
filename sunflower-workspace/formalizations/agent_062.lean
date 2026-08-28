import Mathlib

/-!
# Statement of the improved sunflower lemma

Alweiss–Lovett–Wu–Zhang (2019), refined by Rao ("Coding for sunflowers") and by
Bell–Chueluecha–Warnke.

This file contains the *statement* only. Every theorem ends in `:= by sorry`.
-/

namespace Agent062

variable {α : Type*} [DecidableEq α]

/-- `petals` is a **sunflower with `r` petals and core `core`** if it has exactly `r`
members and any two distinct members meet in exactly `core`.

Equivalent informal content: the `r` sets are distinct (automatic, since `petals` is a
`Finset`), there is a common "core" `core` with `Sᵢ ∩ Sⱼ = core` for all `i ≠ j`, hence
every element contained in `≥ 2` of the sets is contained in all of them and the petals
`Sᵢ \ core` are pairwise disjoint.

For `r ≥ 2` the core is forced to satisfy `core ⊆ s` for every `s ∈ petals`; we do not
add that clause explicitly (it matches the usual, and Mathlib's, convention for the
pairwise-intersection formulation). -/
def IsSunflower (r : ℕ) (core : Finset α) (petals : Finset (Finset α)) : Prop :=
  petals.card = r ∧
    ∀ ⦃s : Finset α⦄, s ∈ petals → ∀ ⦃t : Finset α⦄, t ∈ petals → s ≠ t → s ∩ t = core

/-- `W` **contains a sunflower with `r` petals** if some subfamily of `W` is a sunflower
with `r` petals, for some core. -/
def ContainsSunflower (r : ℕ) (W : Finset (Finset α)) : Prop :=
  ∃ (core : Finset α) (petals : Finset (Finset α)),
    petals ⊆ W ∧ IsSunflower r core petals

/-- **Improved sunflower lemma.**

There is an absolute constant `C > 0` such that for all positive integers `k` and `r`,
every finite family `W` of sets each of cardinality exactly `k` with
`|W| > (C * r * log k) ^ k` contains a sunflower with `r` petals.

Equivalently, the sunflower function satisfies `f (k, r) ≤ (C * r * log k) ^ k`.

Encoding notes:
* Sets are `Finset α` over an ambient type; the family `W` is a `Finset (Finset α)`, so
  `W` is automatically finite and its members are automatically distinct.
* `C` is existentially quantified inside the statement ("there is an absolute constant").
* `Real.log` is the natural logarithm; the base is irrelevant since a change of base is
  absorbed into `C`.
* The bound is compared against `(W.card : ℝ)` with a strict inequality.
* Caveat at `k = 1`: `Real.log 1 = 0`, so the hypothesis degenerates to `0 < |W|`, and
  the conclusion can fail when `0 < |W| < r`. Faithful to the literature, the intended
  regime is `k ≥ 2`; a variant that is unconditionally true replaces `Real.log k` by
  `Real.log (k + 1)` (or `max 1 (Real.log k)`), which `C` again absorbs for `k ≥ 2`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (k r : ℕ), 0 < k → 0 < r →
        ∀ (W : Finset (Finset α)),
          (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
          ContainsSunflower r W := by
  sorry

/-- Restatement in terms of a sunflower/threshold *function* `f : ℕ → ℕ → ℕ`
(`f k r` = least `N` forcing an `r`-petal sunflower among `N` sets of size `k`):
its value is bounded by `(C * r * log k) ^ k`. Here `f` and its defining property are
taken as hypotheses. -/
theorem improved_sunflower_lemma_function
    (f : ℕ → ℕ → ℕ)
    (hf : ∀ (α : Type*) [DecidableEq α] (k r : ℕ) (W : Finset (Finset α)),
      (∀ s ∈ W, s.card = k) → f k r ≤ W.card → ContainsSunflower r W) :
    ∃ C : ℝ, 0 < C ∧
      ∀ k r : ℕ, 0 < k → 0 < r → (f k r : ℝ) ≤ (C * (r : ℝ) * Real.log (k : ℝ)) ^ k := by
  sorry

end Agent062
