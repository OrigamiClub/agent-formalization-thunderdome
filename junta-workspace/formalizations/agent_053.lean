import Mathlib

open scoped BigOperators
open Finset

namespace FilmusIhringer

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas — statement only.

All theorems are stated and closed with `:= by sorry`.  Nothing is proved.

Encoding summary (see `agent_053.md`):
* the slice `binom([n],k)` is carried implicitly: a function on the slice is a total
  function `Finset (Fin n) → ℝ`, and every statement only ever constrains it on
  `{S : Finset (Fin n) // S.card = k}`;
* Boolean codomain: real values, "Boolean" means "equals `0` or `1` on the slice";
* degree `≤ d`: agrees on the slice with the evaluation of a multilinear real
  `MvPolynomial (Fin n) ℝ` of `totalDegree ≤ d` at the 0/1 indicator vector;
* `m`-junta: `∃ J, J.card ≤ m` and the value only depends on `S ∩ J`;
* the bound `m(d)` is an existential `∃ M : ℕ → ℕ` at the head of the forward statement;
* the explicit witnessing family is included as a third theorem.
-/

/-- The 0/1 indicator vector of a subset `S ⊆ Fin n`, as a real point of the cube. -/
def indicatorVec (n : ℕ) (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- `f` (a total function on `Finset (Fin n)`) is Boolean-valued on the slice `binom([n],k)`. -/
def IsBooleanOnSlice (n k : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → f S = 0 ∨ f S = 1

/-- `f` has degree `≤ d` on the slice `binom([n],k)`: it agrees on the slice with the
evaluation, at the indicator vector, of some real polynomial that is multilinear
(`degreeOf i ≤ 1` for every variable `i`) and has `totalDegree ≤ d`. -/
def HasSliceDegreeLE (n k d : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ (∀ i, MvPolynomial.degreeOf i p ≤ 1) ∧
    ∀ S : Finset (Fin n), S.card = k →
      f S = MvPolynomial.eval (indicatorVec n S) p

/-- `f` is an `m`-junta on the slice `binom([n],k)`: there is a set `J` of at most `m`
coordinates such that, for slice inputs, `f S` depends only on `S ∩ J`. -/
def IsSliceJunta (n k m : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Finset (Fin n), S.card = k → T.card = k →
      S ∩ J = T ∩ J → f S = f T

/-- The explicit Filmus–Ihringer witness polynomial
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`.  The `ℓ · e` variables are placed on the first
`ℓ · e` coordinates of `Fin n`, via `finProdFinEquiv : Fin ℓ × Fin e ≃ Fin (ℓ * e)`
followed by `Fin.castLE h : Fin (ℓ * e) → Fin n`. -/
noncomputable def witnessPoly (n ℓ e : ℕ) (h : ℓ * e ≤ n) : MvPolynomial (Fin n) ℝ :=
  ∏ i : Fin ℓ, ∑ j : Fin e,
    MvPolynomial.X (Fin.castLE h (finProdFinEquiv (i, j)))

/-- The function on the slice obtained by evaluating `witnessPoly` at indicator vectors. -/
noncomputable def witnessFun (n ℓ e : ℕ) (h : ℓ * e ≤ n) : Finset (Fin n) → ℝ :=
  fun S => MvPolynomial.eval (indicatorVec n S) (witnessPoly n ℓ e h)

/-- **Forward direction (Filmus–Ihringer).**  For every `d ≥ 1` there is a bound `M d` such
that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on the slice
`binom([n],k)` is an `M d`-junta. -/
theorem slice_degree_junta :
    ∃ M : ℕ → ℕ, ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Finset (Fin n) → ℝ,
        IsBooleanOnSlice n k f → HasSliceDegreeLE n k d f →
        IsSliceJunta n k (M d) f := by
  sorry

/-- **Converse direction (Filmus–Ihringer).**  If `1 ≤ k < 2d` then no uniform junta bound
holds: for every `m` there are `n ≥ 2k` and a Boolean degree-`d` function on the slice
`binom([n],k)` that is not an `m`-junta. -/
theorem slice_degree_not_junta :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
      ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Finset (Fin n) → ℝ,
        IsBooleanOnSlice n k f ∧ HasSliceDegreeLE n k d f ∧
        ¬ IsSliceJunta n k m f := by
  sorry

/-- **Explicit witnessing family (Filmus–Ihringer).**  With `e = min d k` and `1 ≤ k < 2d`,
for every `ℓ` and every `n` with `n ≥ 2·ℓ·e` and `n ≥ 2k`, the function
`witnessFun n ℓ e = ∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` (evaluated at indicators) is a
Boolean degree-`d` function on the slice `binom([n],k)` that is not an `(ℓ·e)`-junta. -/
theorem witness_not_junta
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hkd : k < 2 * d)
    (ℓ n : ℕ) (hle : ℓ * min d k ≤ n)
    (hn2k : 2 * k ≤ n) (hn : 2 * (ℓ * min d k) ≤ n) :
    IsBooleanOnSlice n k (witnessFun n ℓ (min d k) hle) ∧
    HasSliceDegreeLE n k d (witnessFun n ℓ (min d k) hle) ∧
    ¬ IsSliceJunta n k (ℓ * min d k) (witnessFun n ℓ (min d k) hle) := by
  sorry

end FilmusIhringer
