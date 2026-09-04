import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.

We state:
* the junta ("upper bound") direction,
* the converse ("lower bound") direction with an existential witness, and
* the converse with the explicit witnessing family.
-/

open scoped BigOperators

namespace FilmusIhringer

/-- The slice `binom([n], k)`: the `k`-element subsets of `{0, 1, …, n-1}`.
The ground set is encoded as an initial segment of `ℕ`, which keeps the
polynomial machinery below coercion-free. -/
def Slice (n k : ℕ) : Type :=
  {S : Finset ℕ // S ⊆ Finset.range n ∧ S.card = k}

/-- The `0/1` indicator vector of a finite set, as a point of `ℕ → ℝ`. -/
def indicatorVec (S : Finset ℕ) : ℕ → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it only takes values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree ≤ d* on the slice if it agrees, at every point of the slice,
with the evaluation at the `0/1` indicator vector of some multilinear real
polynomial of total degree `≤ d`.

The multilinearity conjunct `∀ i, p.degreeOf i ≤ 1` is included for faithfulness to
"multilinear real polynomial"; it can be dropped without changing the class of
functions, since multilinearising on `{0,1}`-valued coordinates never raises the
total degree. -/
def HasSliceDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial ℕ ℝ,
    p.totalDegree ≤ d ∧ (∀ i, p.degreeOf i ≤ 1) ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (indicatorVec S.val) p

/-- `f` is an *m-junta* if there is a set `J` of at most `m` coordinates such that
`f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset ℕ, J.card ≤ m ∧
    ∀ S T : Slice n k, S.val ∩ J = T.val ∩ J → f S = f T

/-- **Filmus–Ihringer, junta direction.**
For every `d ≥ 1` there is a bound `M = m(d)`, depending only on `d`, such that
whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on the slice
`binom([n], k)` is an `M`-junta. -/
theorem junta_of_boolean_degree (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasSliceDegreeLE f d → IsJunta f M := by
  sorry

/-- **Filmus–Ihringer, converse direction.**
If `1 ≤ k < 2d` then the junta bound fails completely: for every `m` there exist
`n ≥ 2k` and a Boolean degree-`d` function on `binom([n], k)` that is not an
`m`-junta. -/
theorem not_junta_of_boolean_degree
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk0 : 1 ≤ k) (hk : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
      IsBoolean f ∧ HasSliceDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-! ### The explicit witnessing family -/

/-- The polynomial `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e + j})`, i.e. a product over
`ℓ` disjoint blocks of `e` variables each, the `i`-th block being
`{i·e, …, i·e + e - 1}` (0-indexed). -/
noncomputable def blockSumPoly (e ℓ : ℕ) : MvPolynomial ℕ ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e, MvPolynomial.X (i * e + j)

/-- The Boolean function on the slice "witnessed by" `blockSumPoly e ℓ`: it is `1`
exactly when the product of block-sums is non-zero — equivalently, when `S` meets
every one of the `ℓ` blocks.  (The product itself is integer- but not
`{0,1}`-valued, so the associated Boolean function is its support indicator.) -/
noncomputable def blockFun (n k e ℓ : ℕ) : Slice n k → ℝ :=
  fun S =>
    if MvPolynomial.eval (indicatorVec S.val) (blockSumPoly e ℓ) = 0 then 0 else 1

/-- **Filmus–Ihringer, explicit lower bound.**
With `e = min d k` and any number of blocks `ℓ ≥ 1`, once `n ≥ 2·ℓ·e` (and
`n ≥ 2k`), the function `blockFun` is Boolean, has slice-degree `≤ d`, yet is not
an `ℓ·e`-junta.  Choosing `ℓ` large makes `ℓ·e` exceed any prescribed `m`, which
yields `not_junta_of_boolean_degree`. -/
theorem blockFun_not_junta
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk0 : 1 ≤ k) (hk : k < 2 * d)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (e : ℕ) (he : e = min d k)
    (n : ℕ) (hn : 2 * ℓ * e ≤ n) (hn' : 2 * k ≤ n) :
    IsBoolean (blockFun n k e ℓ) ∧
    HasSliceDegreeLE (blockFun n k e ℓ) d ∧
    ¬ IsJunta (blockFun n k e ℓ) (ℓ * e) := by
  sorry

end FilmusIhringer
