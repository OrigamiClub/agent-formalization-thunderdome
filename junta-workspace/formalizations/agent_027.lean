import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Nothing is proved; every theorem ends with `:= by sorry`.
-/

/-- The `k`-slice of the `n`-cube: subsets of `Fin n` of cardinality exactly `k`,
i.e. `binom([n], k) = {S ⊆ {1,…,n} : |S| = k}`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector of `S ⊆ Fin n`, viewed as a point of `ℝ^n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`* on the slice if it agrees, on every point of the slice,
with the evaluation at the indicator vector of some multilinear real polynomial
(`degreeOf i p ≤ 1` for every coordinate `i`) of total degree `≤ d`. -/
def HasSliceDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ i, MvPolynomial.degreeOf i p ≤ 1) ∧
    p.totalDegree ≤ d ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S.1) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such that
`f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- The explicit lower-bound family.  As a polynomial on `Fin n` (with indices
reduced mod `n`, harmless once `n ≥ ℓ·e`):
`∏_{i=0}^{ℓ-1} ( ∑_{j=0}^{e-1} X_{i·e + j} )`.
Taking `e = min d k` gives the Filmus–Ihringer witness family
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`. -/
noncomputable def wedgePoly (n ℓ e : ℕ) (hn : 0 < n) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    MvPolynomial.X (⟨(i * e + j) % n, Nat.mod_lt _ hn⟩ : Fin n)

/-- `wedgePoly` evaluated at indicator vectors, as a function on the slice. -/
noncomputable def wedgeFun (n k ℓ e : ℕ) (hn : 0 < n) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (indicator S.1) (wedgePoly n ℓ e hn)

/-- **Filmus–Ihringer.**  Fix `d ≥ 1`.

* **(Forward)** There is a constant `m` (depending only on `d`) such that whenever
  `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on the slice
  `binom([n], k)` is an `m`-junta.

* **(Converse)** Whenever `1 ≤ k < 2d`, no uniform junta bound exists: for every
  `m` there are `n ≥ 2k` and a Boolean degree-`d` function on `binom([n], k)` that
  is not an `m`-junta.  It is witnessed by `wedgeFun` with `e = min d k` and `ℓ`
  taken large enough that `ℓ·e > m` (with `n ≥ 2·ℓ·e`), so that the function
  genuinely depends on `ℓ·e > m` coordinates. -/
theorem boolean_constant_degree_slice_junta (d : ℕ) (hd : 1 ≤ d) :
    (∃ m : ℕ,
      ∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
        ∀ f : Slice n k → ℝ,
          IsBoolean f → HasSliceDegreeLE d f → IsJunta m f)
    ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d →
      ∀ m : ℕ,
        ∃ (n ℓ : ℕ) (hn : 0 < n),
          2 * k ≤ n ∧
          2 * (ℓ * min d k) ≤ n ∧
          m < ℓ * min d k ∧
          IsBoolean (wedgeFun n k ℓ (min d k) hn) ∧
          HasSliceDegreeLE d (wedgeFun n k ℓ (min d k) hn) ∧
          ¬ IsJunta m (wedgeFun n k ℓ (min d k) hn)) := by
  sorry

end FilmusIhringer
