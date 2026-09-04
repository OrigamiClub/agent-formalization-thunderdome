import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.

Reference: Yuval Filmus, Ferdinand Ihringer,
*Boolean constant-degree functions on the slice are juntas*.
-/

open MvPolynomial

namespace FilmusIhringer

/-- The slice `binom([n],k)`: subsets of `Fin n` of cardinality exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-valued indicator vector of a slice point, as a map `Fin n → ℝ`. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.1 then (1 : ℝ) else 0

/-- `f : Slice n k → ℝ` is a *Boolean function of degree `≤ d`* on the slice when

* it is `{0,1}`-valued, and
* it agrees, at every point of the slice, with the evaluation at the indicator
  vector of some **multilinear** real polynomial of total degree `≤ d`
  (multilinearity is spelled out as: every exponent occurring in the support
  of the polynomial is `≤ 1`).

Because on `{0,1}`-points any polynomial can be multilinearized without changing
its values, dropping the multilinearity clause would define the same class of
functions. -/
def BooleanDegreeLE (n k d : ℕ) (f : Slice n k → ℝ) : Prop :=
  (∀ S : Slice n k, f S = 0 ∨ f S = 1) ∧
    ∃ p : MvPolynomial (Fin n) ℝ,
      p.totalDegree ≤ d ∧
      (∀ t ∈ p.support, ∀ i, t i ≤ 1) ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S) p

/-- `f` is an *`m`-junta* on the slice: there is a set `J` of at most `m`
coordinates such that the value `f S` depends only on `S ∩ J`. -/
def IsJunta (n k m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Forward direction (Filmus–Ihringer).**
For every `d ≥ 1` there is a constant `m = m(d)` such that whenever `k ≥ 2d` and
`n ≥ 2k`, every Boolean degree-`d` function on `binom([n],k)` is an `m`-junta.

Here `m(d)` is stated as an existential quantifier ranging over `ℕ`, placed after
`d` is fixed. -/
theorem boolean_degree_le_isJunta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, BooleanDegreeLE n k d f → IsJunta n k m f := by
  sorry

/-- **Sharpness of the hypothesis `k ≥ 2d`.**
If `1 ≤ k < 2d` then the junta bound fails on the slice `binom([n],k)`: for every
`m` there exist `n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)`
that is not an `m`-junta. -/
theorem exists_boolean_degree_le_not_isJunta
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, BooleanDegreeLE n k d f ∧ ¬ IsJunta n k m f := by
  sorry

/-- The explicit witnessing family, with `e := min d k`:
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{c i j})`, a product of `ℓ` linear forms supported on
`ℓ` pairwise–disjoint blocks of `e` coordinates, the block placement being an
injective map `c : Fin ℓ → Fin e → Fin n`.  Taking `c i j = (i-1)·e + j`
recovers the displayed formula `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`. -/
noncomputable def blockPoly (n e ℓ : ℕ) (c : Fin ℓ → Fin e → Fin n) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i : Fin ℓ, ∑ j : Fin e, MvPolynomial.X (c i j)

/-- The slice function induced by `blockPoly`. -/
noncomputable def blockFun (n k e ℓ : ℕ) (c : Fin ℓ → Fin e → Fin n) :
    Slice n k → ℝ :=
  fun S => MvPolynomial.eval (indicator S) (blockPoly n e ℓ c)

/-- **Sharpness, witnessed by the explicit family.**
For `1 ≤ k < 2d` and any `m`, set `e := min d k` and pick any `ℓ` with `ℓ·e > m`.
Then for every `n ≥ 2ℓe` and every injective block placement `c`, the function
`blockFun` is a Boolean degree-`d` function on `binom([n],k)` that is not an
`m`-junta.

(The source phrases the conclusion as "not an `ℓe`-junta"; since the function is
supported on exactly `ℓe` coordinates it is literally an `ℓe`-junta, so the
intended statement is that it is not an `m`-junta for any `m < ℓe`, i.e. its
smallest junta has size `ℓe`.) -/
theorem blockFun_not_isJunta
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ ℓ : ℕ, m < ℓ * min d k ∧
      ∀ n : ℕ, 2 * (ℓ * min d k) ≤ n →
        ∀ c : Fin ℓ → Fin (min d k) → Fin n,
          Function.Injective (fun p : Fin ℓ × Fin (min d k) => c p.1 p.2) →
            BooleanDegreeLE n k d (blockFun n k (min d k) ℓ c) ∧
              ¬ IsJunta n k m (blockFun n k (min d k) ℓ c) := by
  sorry

end FilmusIhringer
