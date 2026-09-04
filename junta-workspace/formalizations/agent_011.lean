/-
  Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas.

  Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.

  What is stated here (see agent_011.md for discussion):
    * `boolean_degree_le_d_isJunta`            -- positive direction (existential `m(d)`)
    * `exists_boolean_degree_le_d_not_isJunta` -- converse direction, pure existence
    * `explicitFn_boolean_degree_not_junta`    -- converse direction, explicit witnessing family
-/
import Mathlib

open scoped BigOperators Classical

namespace FilmusIhringer

/-! ## Basic objects -/

/-- The slice `binom([n], k)`: the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-indicator vector in `ℝ^n` of a point of the slice. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ (S : Finset (Fin n)) then (1 : ℝ) else 0

/-- A real polynomial in `Fin n` variables is *multilinear* if every monomial in its
support is squarefree (each exponent is `≤ 1`). -/
def IsMultilinearPoly {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ mono ∈ p.support, ∀ i, mono i ≤ 1

/-- A real function on the slice is *Boolean* if all its values lie in `{0,1}`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree ≤ d on the slice*: it agrees, at every point of the slice, with the
evaluation at the indicator vector of some multilinear real polynomial of total
degree `≤ d`. -/
def HasSliceDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    IsMultilinearPoly p ∧ p.totalDegree ≤ d ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S) p

/-- `f` is an *m-junta*: there is a set `J` of at most `m` coordinates such that the
value `f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k,
      (S : Finset (Fin n)) ∩ J = (T : Finset (Fin n)) ∩ J → f S = f T

/-! ## Positive direction

For each `d ≥ 1` there is a constant `m(d)` (packaged here as an existential `m`) such
that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on the slice
`binom([n], k)` is an `m`-junta. -/
theorem boolean_degree_le_d_isJunta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasSliceDegreeLE d f → IsJunta m f := by
  sorry

/-! ## Converse direction (pure existence)

If `1 ≤ k < 2d` then the junta size cannot be bounded: for every `m` there is an
`n ≥ 2k` and a Boolean degree-`d` function on `binom([n], k)` that is not an
`m`-junta. -/
theorem exists_boolean_degree_le_d_not_isJunta
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk₀ : 1 ≤ k) (hk₁ : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasSliceDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-! ## Converse direction (explicit witnessing family)

`e := min d k`.  Block `i` (0-indexed) is the set of coordinates `{i·e, …, i·e+e-1}`;
this matches the 1-indexed description `x_{(i-1)e+j}`, `1 ≤ j ≤ e`, of the statement.

The witness is `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` (a *sum of products*; see
agent_011.md for why this rather than the literal product of sums).  It is multilinear
of total degree `e ≤ d`; on the slice with `k < 2d` at most one block can lie entirely
inside a given `k`-set, so it is Boolean; and its minimal junta size is at least `ℓ·e`,
which is unbounded in `ℓ`. -/

/-- Block `i` (0-indexed): the coordinates `{i·e, …, i·e + e − 1}` of `Fin n`. -/
def block (n e i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n => i * e ≤ (x : ℕ) ∧ (x : ℕ) < i * e + e)

/-- The witnessing polynomial `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`. -/
noncomputable def explicitPoly (n e ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ i ∈ Finset.range ℓ, ∏ x ∈ block n e i, MvPolynomial.X x

/-- The witnessing family, as a function on the slice. -/
noncomputable def explicitFn (n k e ℓ : ℕ) (S : Slice n k) : ℝ :=
  MvPolynomial.eval (indicator S) (explicitPoly n e ℓ)

/-- **Explicit witnesses for the converse.**
With `e = min d k` and `ℓ` arbitrary, each member of the family `explicitFn` is a
Boolean degree-`d` function on the slice, and (for `n ≥ 2ℓe`) it is not an
`(ℓ·e − 1)`-junta; taking `ℓ` large gives functions with unbounded junta size. -/
theorem explicitFn_boolean_degree_not_junta
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk₀ : 1 ≤ k) (hk₁ : k < 2 * d)
    (ℓ n : ℕ) (hn : 2 * (ℓ * min d k) ≤ n) (hnk : 2 * k ≤ n) :
    IsBoolean (explicitFn n k (min d k) ℓ) ∧
      HasSliceDegreeLE d (explicitFn n k (min d k) ℓ) ∧
      (1 ≤ ℓ * min d k →
        ¬ IsJunta (ℓ * min d k - 1) (explicitFn n k (min d k) ℓ)) := by
  sorry

end FilmusIhringer
