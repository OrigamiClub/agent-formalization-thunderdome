import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (every theorem ends in `:= by sorry`).

We formalize three parts of the theorem:

* `boolean_degree_d_junta_upper`  — the junta upper bound for `k ≥ 2d`;
* `boolean_degree_d_junta_lower`  — the converse, in pure existence form, for `1 ≤ k < 2d`;
* `boolean_degree_d_junta_lower_witness` — the converse with the explicit
  witnessing family `∏_{i=1}^{ℓ} ( Σ_{j=1}^{e} x_{(i-1)e+j} )`, `e = min d k`.
-/

open Finset

namespace FilmusIhringer

/-- The slice `binom([n],k)`: subsets of `Fin n` of cardinality exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` real indicator vector of a slice point. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.1 then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `p` is *multilinear* (squarefree): every monomial in its support uses each
variable with exponent at most `1`. -/
def IsMultilinearPoly {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ m ∈ p.support, ∀ i, m i ≤ 1

/-- `f` has *degree ≤ d* on the slice: it agrees, at every slice point, with the
evaluation at the `0/1` indicator vector of some multilinear real polynomial of
total degree `≤ d`. -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    IsMultilinearPoly p ∧ p.totalDegree ≤ d ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that
the value `f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Filmus–Ihringer, upper bound.**
There is a function `m : ℕ → ℕ` such that for every `d ≥ 1`, every `k ≥ 2d` and
every `n ≥ 2k`, every Boolean function of degree `≤ d` on the slice `binom([n],k)`
is an `m d`-junta. -/
theorem boolean_degree_d_junta_upper :
    ∃ m : ℕ → ℕ, ∀ d k n : ℕ, 1 ≤ d → 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta (m d) f := by
  sorry

/-- **Filmus–Ihringer, lower bound (existence form).**
If `1 ≤ k < 2d` then for every `m` there is an `n ≥ 2k` and a Boolean function of
degree `≤ d` on `binom([n],k)` that is not an `m`-junta. -/
theorem boolean_degree_d_junta_lower (d k : ℕ)
    (hd : 1 ≤ d) (hk : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-- The explicit witness polynomial in `n` variables:
`∏_{i=0}^{ℓ-1} ( Σ_{j=0}^{e-1} X_{i*e + j} )`, i.e. the product over `ℓ` consecutive
blocks of width `e` of the sum of the block's variables.  Indices `≥ n` are clamped
away (this branch is never taken once `ℓ * e ≤ n`). -/
noncomputable def witnessPoly (n ℓ e : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) else 0)

/-- **Filmus–Ihringer, lower bound (explicit witnesses).**
For `1 ≤ k < 2d`, `e = min d k`, any `ℓ ≥ 1` and any `n ≥ 2ℓe`, the function on the
slice `binom([n],k)` represented by `∏_{i=1}^{ℓ} ( Σ_{j=1}^{e} x_{(i-1)e+j} )` is
Boolean, has degree `≤ d`, and is not an `ℓe`-junta. -/
theorem boolean_degree_d_junta_lower_witness (d k ℓ n : ℕ)
    (hd : 1 ≤ d) (hk : 1 ≤ k) (hk2 : k < 2 * d) (hℓ : 1 ≤ ℓ)
    (hn : 2 * (ℓ * min d k) ≤ n) :
    ∃ f : Slice n k → ℝ,
      (∀ S, f S = MvPolynomial.eval (indicator S) (witnessPoly n ℓ (min d k))) ∧
      IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta (ℓ * min d k) f := by
  sorry

end FilmusIhringer
