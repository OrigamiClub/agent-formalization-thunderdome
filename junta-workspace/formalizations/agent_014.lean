import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.

The slice `binom([n],k) = {S ⊆ {1,…,n} : |S| = k}` is represented *implicitly*: a
"function on the slice" is a function `f : Finset (Fin n) → ℝ`, and every hypothesis
and conclusion only ever constrains `f` on sets `S` with `S.card = k`.  The 0/1
indicator vector of `S` is `fun i => if i ∈ S then (1 : ℝ) else 0`.
-/

open Finset MvPolynomial

namespace FilmusIhringer

/-- `f` is Boolean-valued on the slice `binom([n],k)`. -/
def IsBooleanOn (n k : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → f S = 0 ∨ f S = 1

/-- `p` is multilinear: every monomial occurring in `p` uses each variable at most once. -/
def IsMultilinearPoly {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ c ∈ p.support, ∀ i, c i ≤ 1

/-- `f` has degree `≤ d` on the slice `binom([n],k)`: it agrees, on every `S` with
`S.card = k`, with a multilinear real polynomial of total degree `≤ d`, evaluated at
the 0/1 indicator vector of `S`. -/
def HasSliceDegreeLE (n k d : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    IsMultilinearPoly p ∧
    ∀ S : Finset (Fin n), S.card = k →
      f S = MvPolynomial.eval (fun i => if i ∈ S then (1 : ℝ) else 0) p

/-- `f` is an `m`-junta on the slice `binom([n],k)`: there is a set `J` of at most `m`
coordinates such that the value of `f` on the slice depends only on `S ∩ J`. -/
def IsSliceJunta (n k m : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Finset (Fin n), S.card = k → T.card = k → S ∩ J = T ∩ J → f S = f T

/-- **Filmus–Ihringer.**  Fix `d ≥ 1`.

* (Forward) There is a constant `M = M(d)` (independent of `k`, `n`) such that whenever
  `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on `binom([n],k)` is an
  `M`-junta.
* (Converse) Whenever `1 ≤ k < 2d`, for every `m` there exist `n ≥ 2k` and a Boolean
  degree-`d` function on `binom([n],k)` that is not an `m`-junta. -/
theorem filmus_ihringer (d : ℕ) (hd : 1 ≤ d) :
    (∃ M : ℕ, ∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
        ∀ f : Finset (Fin n) → ℝ,
          IsBooleanOn n k f → HasSliceDegreeLE n k d f → IsSliceJunta n k M f)
    ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
        ∃ (n : ℕ) (f : Finset (Fin n) → ℝ),
          2 * k ≤ n ∧ IsBooleanOn n k f ∧ HasSliceDegreeLE n k d f ∧
            ¬ IsSliceJunta n k m f) := by
  sorry

/-- **Explicit witnesses for the converse.**  For `1 ≤ k < 2d`, put `e = min d k`.
For every `m`, taking `ℓ` with `ℓ · e > m` and `n ≥ 2 ℓ e` (hence also `n ≥ 2k`), and
any `ℓ` pairwise-disjoint blocks `B₀,…,B_{ℓ-1} ⊆ [n]` each of size `e`, the function

  `f(S) = Σ_{i} Π_{j ∈ Bᵢ} x_j`

(a sum of `ℓ` pairwise-disjoint degree-`e` monomials) is a Boolean degree-`d` function
on `binom([n],k)` that is not an `m`-junta.

See the accompanying note: the source writes the family as `Π_i Σ_j`; it is transcribed
here as `Σ_i Π_j`, which is the reading that actually produces Boolean-valued degree-`d`
functions.  The source's block coordinates are the consecutive indices `(i-1)e + j`;
here they are abstracted to arbitrary pairwise-disjoint `e`-sets. -/
theorem filmus_ihringer_explicit_witness
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ (ℓ n : ℕ) (B : Fin ℓ → Finset (Fin n)) (f : Finset (Fin n) → ℝ),
      m < ℓ * min d k ∧
      2 * k ≤ n ∧
      2 * ℓ * min d k ≤ n ∧
      (∀ i, (B i).card = min d k) ∧
      Pairwise (fun i i' => Disjoint (B i) (B i')) ∧
      (∀ S : Finset (Fin n),
        f S = ∑ i : Fin ℓ, ∏ j ∈ B i, (if j ∈ S then (1 : ℝ) else 0)) ∧
      IsBooleanOn n k f ∧
      HasSliceDegreeLE n k d f ∧
      ¬ IsSliceJunta n k m f := by
  sorry

end FilmusIhringer
