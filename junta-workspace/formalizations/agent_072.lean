import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-!
# Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer)

Statement-only formalization. Every `theorem` ends in `:= by sorry`.

The slice `binom([n],k)` is modelled as `S : Finset (Fin n)` carrying the side condition
`S.card = k`, threaded through every definition and theorem.  Boolean values are `{0,1} ⊆ ℝ`.
-/

/-- The 0/1 real indicator vector of a finite set `S ⊆ Fin n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- A real-valued function on the slice `binom([n],k)` is **Boolean** if it takes only the
values `0` and `1` on sets of cardinality `k`. -/
def IsBooleanOnSlice {n : ℕ} (f : Finset (Fin n) → ℝ) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → f S = 0 ∨ f S = 1

/-- `f` has **degree ≤ d on the slice** `binom([n],k)` if it agrees, on every set of
cardinality `k`, with the evaluation at the 0/1 indicator vector of some *multilinear*
(`degreeOf i ≤ 1` in every variable) real polynomial of total degree `≤ d`. -/
def HasSliceDegreeLE {n : ℕ} (f : Finset (Fin n) → ℝ) (k d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ i, MvPolynomial.degreeOf i p ≤ 1) ∧
    MvPolynomial.totalDegree p ≤ d ∧
    ∀ S : Finset (Fin n), S.card = k →
      f S = MvPolynomial.eval (indicator S) p

/-- `f` is an **m-junta on the slice** `binom([n],k)` if there is a set `J` of at most `m`
coordinates such that, on sets of cardinality `k`, the value of `f` depends only on
`S ∩ J`. -/
def IsSliceJunta {n : ℕ} (f : Finset (Fin n) → ℝ) (k m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Finset (Fin n), S.card = k → T.card = k → S ∩ J = T ∩ J → f S = f T

/-- The explicit witnessing family
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, evaluated at the 0/1 indicator of `S`.
Coordinates are named in `ℕ` through `Fin.valEmbedding`, so `x_t` reads as `1` iff the
element of `Fin n` with value `t` lies in `S`. -/
noncomputable def blockProdSlice (n e ℓ : ℕ) (S : Finset (Fin n)) : ℝ :=
  ∏ i ∈ Finset.range ℓ,
    (∑ j ∈ Finset.range e,
      (if (i * e + j) ∈ S.map Fin.valEmbedding then (1 : ℝ) else 0))

/-! ## Forward direction: wide slices force bounded juntas -/

/-- **Filmus–Ihringer, forward direction.**
For every `d ≥ 1` there is a constant `m(d)` such that whenever `k ≥ 2d` and `n ≥ 2k`,
every Boolean degree-`d` function on the slice `binom([n],k)` is an `m(d)`-junta. -/
theorem boolean_degree_le_isSliceJunta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ (k n : ℕ), 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Finset (Fin n) → ℝ,
        IsBooleanOnSlice f k → HasSliceDegreeLE f k d → IsSliceJunta f k m := by
  sorry

/-! ## Converse direction: narrow slices allow unbounded junta size -/

/-- **Filmus–Ihringer, converse direction.**
If `1 ≤ k < 2d` then for every `m` there is some `n ≥ 2k` and a Boolean degree-`d`
function on the slice `binom([n],k)` that is not an `m`-junta. -/
theorem exists_boolean_degree_le_not_isSliceJunta
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Finset (Fin n) → ℝ,
        IsBooleanOnSlice f k ∧ HasSliceDegreeLE f k d ∧ ¬ IsSliceJunta f k m := by
  sorry

/-- **Filmus–Ihringer, converse direction with explicit witnesses.**
Put `e = min d k`.  For any number `ℓ` of blocks, once `n ≥ 2·ℓ·e` (and `n ≥ 2k`, so the
slice is nonempty), the function `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` is a Boolean
degree-`d` function on `binom([n],k)` that genuinely depends on all `ℓ·e` of its
coordinates, hence is not an `m`-junta for any `m < ℓ·e`. -/
theorem blockProdSlice_isBoolean_degree_le_not_isSliceJunta
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (ℓ n : ℕ) (hn : 2 * (ℓ * min d k) ≤ n) (hn' : 2 * k ≤ n) :
    IsBooleanOnSlice (blockProdSlice n (min d k) ℓ) k ∧
    HasSliceDegreeLE (blockProdSlice n (min d k) ℓ) k d ∧
    (∀ m : ℕ, m < ℓ * min d k →
      ¬ IsSliceJunta (blockProdSlice n (min d k) ℓ) k m) := by
  sorry

end FilmusIhringer
