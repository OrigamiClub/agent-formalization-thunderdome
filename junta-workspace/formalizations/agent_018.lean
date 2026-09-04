/-
Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas.

Formalization of the STATEMENT only. Every theorem ends in `:= by sorry`.

This file states:
  * the positive direction  (`filmus_ihringer_junta_bound`),
  * the converse direction   (`filmus_ihringer_no_junta_bound`),
  * the explicit witnessing family (`filmus_ihringer_explicit_family`).

See `agent_018.md` for the encoding rationale and the list of uncertainties.
-/
import Mathlib

open Finset MvPolynomial

namespace FilmusIhringer

/-- The `k`-slice of the `n`-cube: subsets of `Fin n` of cardinality exactly `k`,
i.e. `binom([n], k) = {S ⊆ {1,…,n} : |S| = k}`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- Real `0/1` indicator vector of a subset `S ⊆ Fin n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- `p : MvPolynomial (Fin n) ℝ` is multilinear: every monomial occurring in `p`
uses each variable at most once. -/
def Multilinear {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ c ∈ p.support, ∀ i, c i ≤ 1

/-- A real-valued function on the slice is a *Boolean function of degree ≤ d* if

  * it is `{0,1}`-valued, and
  * it agrees, at every point of the slice, with the evaluation at the indicator
    vector of some multilinear real polynomial of total degree ≤ `d`.

The polynomial is existentially quantified (only its restriction to the slice is
pinned down), which matches the intended notion of "degree on the slice". -/
def BooleanDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  (∀ S : Slice n k, f S = 0 ∨ f S = 1) ∧
    ∃ p : MvPolynomial (Fin n) ℝ,
      p.totalDegree ≤ d ∧ Multilinear p ∧
        ∀ S : Slice n k, f S = eval (indicator S.val) p

/-- `f` is an `m`-junta: there is a set `J` of at most `m` coordinates such that
`f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.val ∩ J = T.val ∩ J → f S = f T

/-- **Filmus–Ihringer, positive direction.**

For every `d ≥ 1` there is a bound `m = m(d)`, depending on `d` only, such that
for all `k ≥ 2d` and all `n ≥ 2k`, every Boolean degree-`d` function on the slice
`binom([n], k)` is an `m`-junta.

(`m(d)` is encoded as an existential `∃ m : ℕ` placed after `d` and before `k`,
`n`, `f`, so that it cannot depend on `k`, `n` or `f`.) -/
theorem filmus_ihringer_junta_bound :
    ∀ d : ℕ, 1 ≤ d →
      ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, BooleanDegreeLE d f → IsJunta m f := by
  sorry

/-- **Filmus–Ihringer, converse direction.**

If `1 ≤ k < 2d` then there is no uniform junta bound: for every `m` there exist
`n ≥ 2k` and a Boolean degree-`d` function on `binom([n], k)` that is not an
`m`-junta. -/
theorem filmus_ihringer_no_junta_bound :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d →
      ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ, BooleanDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-- The explicit witnessing family
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e + j})`, written here `0`-indexed.
Variables whose index would exceed `n` (which never happens once `n ≥ ℓ·e`) are
replaced by `0`, so the definition is total. -/
noncomputable def familyPoly (n e ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then (X (⟨i * e + j, h⟩ : Fin n)) else 0)

/-- The slice function induced by `familyPoly` through evaluation at indicator
vectors. -/
noncomputable def familyFun (n e ℓ k : ℕ) : Slice n k → ℝ :=
  fun S => eval (indicator S.val) (familyPoly n e ℓ)

/-- **Filmus–Ihringer, explicit family.**

With `e = min d k`, for `1 ≤ k < 2d` and every target `m`, choosing enough
blocks `ℓ` makes the function induced by `familyPoly` a Boolean degree-`d`
function on `binom([n], k)`, for every `n ≥ 2ℓe`, which is not an `ℓe`-junta and
hence not an `m`-junta. -/
theorem filmus_ihringer_explicit_family :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
      ∃ ℓ : ℕ, ∀ n : ℕ, 2 * (ℓ * min d k) ≤ n →
        BooleanDegreeLE d (familyFun n (min d k) ℓ k) ∧
        ¬ IsJunta (ℓ * min d k) (familyFun n (min d k) ℓ k) ∧
        ¬ IsJunta m (familyFun n (min d k) ℓ k) := by
  sorry

end FilmusIhringer
