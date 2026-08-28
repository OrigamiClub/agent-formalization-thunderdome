/-
Agent 010 — Formalization of the *statement* of the improved sunflower lemma.

Improved sunflower lemma (Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by
Bell–Chueluecha–Warnke): there is an absolute constant `C` such that for every
`k ≥ 2`, every `r ≥ 1`, and every finite family `W` of `k`-element sets, if
`|W| > (C · r · log k) ^ k` then `W` contains a sunflower with `r` petals.

Statement only — the proof is `sorry`.
-/
import Mathlib

open scoped BigOperators

namespace Agent010

variable {α : Type*} [DecidableEq α]

/-- `IsSunflowerWith 𝒮 r Y` says that `𝒮` is a *sunflower with `r` petals and core `Y`*:
it consists of exactly `r` (necessarily distinct, since `𝒮` is a `Finset`) sets, and
every pairwise intersection of two different members equals the core `Y`.

Consequences that need not be stated separately: any element lying in `≥ 2` members
lies in all of them, and the petals `S \ Y` for `S ∈ 𝒮` are pairwise disjoint. -/
def IsSunflowerWith (𝒮 : Finset (Finset α)) (r : ℕ) (Y : Finset α) : Prop :=
  𝒮.card = r ∧ ∀ ⦃s : Finset α⦄, s ∈ 𝒮 → ∀ ⦃t : Finset α⦄, t ∈ 𝒮 → s ≠ t → s ∩ t = Y

/-- **Improved sunflower lemma (statement).**

There is an absolute constant `C > 0` such that for all naturals `k, r` with `2 ≤ k`
and `0 < r`, and every finite family `W : Finset (Finset α)` whose members all have
cardinality exactly `k`, if `|W| > (C * r * Real.log k) ^ k` then `W` contains a
sub-family `𝒮 ⊆ W` that is a sunflower with `r` petals (with some core `Y`).

Equivalently: the sunflower function satisfies `f(k, r) ≤ (C * r * Real.log k) ^ k`
for `k ≥ 2`.

The restriction `2 ≤ k` is deliberate: for `k = 1` one has `Real.log 1 = 0`, so the
right-hand side would be `0`, while `f(1, r) = r`; the classical `k = 0, 1` cases are
not interesting and are excluded here. `Real.log` is the natural logarithm; the choice
of base is irrelevant since it can be absorbed into `C`. -/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k r : ℕ), 2 ≤ k → 0 < r →
        ∀ W : Finset (Finset α), (∀ s ∈ W, s.card = k) →
          (C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ) →
            ∃ 𝒮 ⊆ W, ∃ Y : Finset α, IsSunflowerWith 𝒮 r Y := by
  sorry

end Agent010
