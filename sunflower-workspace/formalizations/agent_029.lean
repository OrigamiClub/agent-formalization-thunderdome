/-
Improved sunflower lemma
(Alweiss–Lovett–Wu–Zhang 2019; refined by Rao and by Bell–Chueluecha–Warnke).

STATEMENT ONLY.  Nothing is proved: the single theorem ends in `:= by sorry`.

Agent 029 — independent formalization diversity study (context-isolated).
-/
import Mathlib

namespace ImprovedSunflower

variable {α : Type*} [DecidableEq α]

/-- `IsSunflower T Y` says that the finite family of finsets `T` is a *sunflower*
with *core* `Y`: any two distinct members of `T` meet in exactly `Y`.

This is the "all pairwise intersections coincide" formulation, with the common
value named explicitly as `Y`.  It implies the usual equivalent descriptions: the
petals `A \ Y` (`A ∈ T`) are pairwise disjoint, and any element lying in two
members of `T` lies in every member. -/
def IsSunflower (T : Finset (Finset α)) (Y : Finset α) : Prop :=
  ∀ ⦃A⦄, A ∈ T → ∀ ⦃B⦄, B ∈ T → A ≠ B → A ∩ B = Y

/-- `HasSunflower W r` says that the family `W` contains a sunflower with `r`
petals: a subfamily `T ⊆ W` consisting of exactly `r` sets (necessarily
distinct, since `T : Finset _`) that forms a sunflower for some core `Y`. -/
def HasSunflower (W : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ T ⊆ W, T.card = r ∧ ∃ Y, IsSunflower T Y

end ImprovedSunflower

/-- **Improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang; Rao;
Bell–Chueluecha–Warnke).

There is an absolute constant `C` such that for all positive integers `k` and
`r`, every finite family `W` of sets each of cardinality exactly `k` with
`|W| > (C · r · log k) ^ k` contains a sunflower with `r` petals.  Equivalently,
the sunflower function satisfies `f(k, r) ≤ (C · r · log k) ^ k`.

Encoding decisions:
* Sets are `Finset`s over an arbitrary type `α` with decidable equality; the
  family `W` is a `Finset (Finset α)` (so its members are automatically
  distinct, and `W` is finite by construction).
* The absolute constant `C : ℝ` is existentially quantified, together with
  `0 < C`.
* `log` is the natural logarithm `Real.log`.  Its base is immaterial here since a
  change of base is absorbed into `C`.
* To keep the statement total and correct for the small cases `k ∈ {1, 2}` (where
  `Real.log k < 1`) the multiplicative factor is `max 1 (Real.log k)`.  For
  `k ≥ 3` this equals `Real.log k` exactly, so the asymptotic content — and the
  content of the ALWZ/Rao/BCW theorem — is unchanged.  The case `k = 0` is
  excluded by the hypothesis `0 < k`.
* Cardinalities are `Finset.card`.  Distinctness of the `r` petals is automatic
  from `T.card = r`.  Petals are not required to be nonempty, and the core `Y` is
  not required to be a proper subset of the petals.
-/
theorem improved_sunflower_lemma :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type*) [DecidableEq α] (W : Finset (Finset α)) (k r : ℕ),
        0 < k → 0 < r →
        (∀ A ∈ W, A.card = k) →
        ((W.card : ℝ) > (C * (r : ℝ) * max 1 (Real.log (k : ℝ))) ^ k) →
        ImprovedSunflower.HasSunflower W r := by
  sorry
