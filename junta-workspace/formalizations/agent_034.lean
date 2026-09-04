import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (every theorem ends in `sorry`; nothing is proved).

See `agent_034.md` for the encoding notes and uncertainties.
-/

namespace FilmusIhringer

open Finset

/-- The slice `binom([n], k)`: the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector of a subset of `Fin n`, viewed as a real point of the
cube `{0,1}^n ⊆ ℝ^n`. -/
def indicatorVec {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it only takes the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree at most `d`* on the slice: it agrees, at every point of the slice,
with the evaluation on `0/1` indicator vectors of some multilinear real polynomial
(`p.degreeOf i ≤ 1` for every variable `i`) whose total degree is at most `d`. -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ i : Fin n, p.degreeOf i ≤ 1) ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicatorVec S.1) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that the
value of `f` at `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Filmus–Ihringer, main (junta) direction.**
For every `d ≥ 1` there is a constant `m` (depending only on `d`) such that:
if `k ≥ 2 * d`, then for every `n ≥ 2 * k`, every Boolean degree-`≤ d` function on the
slice `binom([n], k)` is an `m`-junta. -/
theorem filmus_ihringer_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta m f := by
  sorry

/-- **Filmus–Ihringer, tightness of the hypothesis `k ≥ 2 * d`.**
If `1 ≤ k < 2 * d`, then there is no uniform junta bound: for every `m` there exist
`n ≥ 2 * k` and a Boolean degree-`≤ d` function on `binom([n], k)` that is *not* an
`m`-junta. -/
theorem filmus_ihringer_tight (d k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-- The explicit lower-bound construction described in the paper, given here *for
reference only* — no property of it is asserted in this file (see `agent_034.md`
for why the literal family is not asserted to be `{0,1}`-valued on the slice).
With `e = min d k` it is the real polynomial `∏_{i=0}^{ℓ-1} (∑_{j=0}^{e-1} x_{i*e+j})`. -/
noncomputable def lowerConstruction (n e ℓ : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    if h : i * e + j < n then x ⟨i * e + j, h⟩ else 0

end FilmusIhringer
