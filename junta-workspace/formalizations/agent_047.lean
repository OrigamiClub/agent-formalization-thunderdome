import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization. Every theorem ends in `:= by sorry`.

We formalize:
* `filmus_ihringer_forward` : the junta direction (`k ≥ 2d`);
* `filmus_ihringer_tight`   : the converse, as a pure existential (`1 ≤ k < 2d`);
* `filmus_ihringer_witness` : the explicit witnessing family
  `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` with `e = min d k`.
-/

/-- The slice `binom([n],k)`: the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- Indicator (0/1) vector of a subset `S ⊆ Fin n`, as a point of `ℝ^n`. -/
def ind {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is Boolean if every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has degree `≤ d` on the slice: on every point of the slice it agrees with
the evaluation, at the indicator vector, of a **multilinear** real polynomial
(`degreeOf i ≤ 1` for every variable `i`) of total degree `≤ d`. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ i, MvPolynomial.degreeOf i p ≤ 1) ∧
    p.totalDegree ≤ d ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (ind S.1) p

/-- `f` is an `m`-junta: there is a set `J` of at most `m` coordinates such that
`f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Junta direction.** For every `d ≥ 1` there is a constant `m = m(d)`
(depending only on `d`) such that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean
degree-`≤ d` function on `binom([n],k)` is an `m`-junta. -/
theorem filmus_ihringer_forward (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ n k : ℕ, 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta m f := by
  sorry

/-- **Tightness (converse), existential form.** If `1 ≤ k < 2d` then for every `m`
there exist `n ≥ 2k` and a Boolean degree-`≤ d` function on `binom([n],k)` that is
not an `m`-junta. -/
theorem filmus_ihringer_tight (d k : ℕ)
    (hd : 1 ≤ d) (hk : 1 ≤ k) (hkd : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, ∃ f : Slice n k → ℝ,
      2 * k ≤ n ∧ IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta m f := by
  sorry

/-- Witnessing polynomial: with `e` the block size and `ℓ` blocks, the sum over the
`ℓ` pairwise-disjoint blocks of size `e` of the monomial that is the product of the
`e` variables in that block, i.e. `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`
(0-indexed here). Indices that fall outside `Fin n` contribute the term `0`. -/
noncomputable def witnessPoly (n ℓ e : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ i ∈ Finset.range ℓ, ∏ j ∈ Finset.range e,
    (if h : i * e + j < n then MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) else 0)

/-- The real function on the slice induced by `witnessPoly`. -/
noncomputable def witnessFun (n k ℓ e : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (ind S.1) (witnessPoly n ℓ e)

/-- **Tightness (converse), explicit family.** For `1 ≤ k < 2d`, set `e = min d k`.
For every number of blocks `ℓ ≥ 1` and every `n` with `n ≥ 2ℓe` (and `n ≥ 2k`),
the function `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` on `binom([n],k)` is Boolean, has
degree `≤ d`, and is not an `m`-junta for any `m < ℓe`. Taking `ℓ` large defeats any
prescribed `m`. -/
theorem filmus_ihringer_witness (d k : ℕ)
    (hd : 1 ≤ d) (hk : 1 ≤ k) (hkd : k < 2 * d)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (n : ℕ) (hn : 2 * (ℓ * min d k) ≤ n) (hnk : 2 * k ≤ n) :
    IsBoolean (witnessFun n k ℓ (min d k)) ∧
    HasDegreeLE (witnessFun n k ℓ (min d k)) d ∧
    (∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta m (witnessFun n k ℓ (min d k))) := by
  sorry

end FilmusIhringer
