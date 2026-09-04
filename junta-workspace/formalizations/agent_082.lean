import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (every theorem ends in `:= by sorry`).

We work with the ambient coordinate set `Fin n` (i.e. `{1, …, n}`).
The slice `binom([n], k)` is modelled as the `k`-sets, `{S : Finset (Fin n) // S.card = k}`,
but carried informally: a "function on the slice" is a plain `f : Finset (Fin n) → ℝ`
and every property is stated under the guard `S.card = k`.

Codomain: `ℝ`, with a separate `{0,1}`-valued predicate `IsBooleanOn`.
Degree: existence of a multilinear `MvPolynomial (Fin n) ℝ` of `totalDegree ≤ d`
whose evaluation at the indicator vector agrees with `f` on every `k`-set.
Junta: existence of a coordinate set `J`, `J.card ≤ m`, with `f S` determined by `S ∩ J`.
-/

namespace FilmusIhringer

/-- The `{0,1}` indicator vector of a finite set `S ⊆ Fin n`, viewed as a point of `ℝ^n`. -/
def IndicatorVec {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- `f` is `{0,1}`-valued on the slice `binom([n], k) = {S : |S| = k}`. -/
def IsBooleanOn (n k : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → f S = 0 ∨ f S = 1

/-- `f` has degree `≤ d` on the slice `binom([n], k)`: there is a multilinear real
polynomial `p` of total degree `≤ d` such that, for every `k`-set `S`, evaluating `p`
at the `0/1` indicator vector of `S` gives `f S`. -/
def HasDegreeLEOn (n k d : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ t ∈ p.support, ∀ i, t i ≤ 1) ∧
    ∀ S : Finset (Fin n), S.card = k →
      MvPolynomial.eval (IndicatorVec S) p = f S

/-- `f` is an `m`-junta on the slice `binom([n], k)`: there is a set `J` of at most `m`
coordinates such that the value `f S` depends only on `S ∩ J`. -/
def IsJuntaOn (n k m : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Finset (Fin n), S.card = k → T.card = k →
      S ∩ J = T ∩ J → f S = f T

/-!
## Forward direction
-/

/-- **Filmus–Ihringer (forward direction).** For every degree `d ≥ 1` there is a
constant `m` (depending only on `d`) such that: whenever `k ≥ 2d` and `n ≥ 2k`, every
Boolean degree-`≤ d` function on the slice `binom([n], k)` is an `m`-junta. -/
theorem boolean_degree_le_isJunta
    (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Finset (Fin n) → ℝ,
        IsBooleanOn n k f → HasDegreeLEOn n k d f → IsJuntaOn n k m f := by
  sorry

/-!
## Converse / tightness
-/

/-- **Filmus–Ihringer (converse).** If `1 ≤ k < 2d` then the junta size cannot be
bounded: for every `m` there is a slice `binom([n], k)` with `n ≥ 2k` carrying a Boolean
degree-`≤ d` function that is not an `m`-junta. -/
theorem boolean_degree_le_not_isJunta
    (d k : ℕ) (hd : 1 ≤ d) (hk₁ : 1 ≤ k) (hk₂ : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Finset (Fin n) → ℝ,
        IsBooleanOn n k f ∧ HasDegreeLEOn n k d f ∧ ¬ IsJuntaOn n k m f := by
  sorry

/-!
## Explicit witnessing family

`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)·e + j})` with `e = min d k` (using `0`-indexed
coordinates `i·e + j` for `i < ℓ`, `j < e`).
-/

/-- The `i`-th block sum `x_{i·e} + x_{i·e+1} + ⋯ + x_{i·e+e-1}` (0-indexed) as a
polynomial in `MvPolynomial (Fin n) ℝ`; indices `≥ n` contribute `0`. -/
noncomputable def blockSumPoly (n e i : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ j ∈ Finset.range e,
    if h : i * e + j < n then MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) else 0

/-- The explicit witnessing polynomial `∏_{i<ℓ} (∑_{j<e} x_{i·e+j})`, `e = min d k`. -/
noncomputable def sliceProductPoly (n d k ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, blockSumPoly n (min d k) i

/-- The explicit witnessing family as a function on the slice. -/
noncomputable def sliceProductFun (n d k ℓ : ℕ) : Finset (Fin n) → ℝ :=
  fun S => MvPolynomial.eval (IndicatorVec S) (sliceProductPoly n d k ℓ)

/-- **Explicit witnesses.** With `e = min d k`, for every `ℓ` and every `n ≥ 2·ℓ·e`,
the function `sliceProductFun n d k ℓ` is a Boolean degree-`≤ d` function on
`binom([n], k)` that is not an `ℓ·e`-junta. Choosing `ℓ` with `ℓ·e > m` gives the
non-`m`-junta required by `boolean_degree_le_not_isJunta`. -/
theorem sliceProductFun_not_isJunta
    (d k ℓ : ℕ) (hd : 1 ≤ d) (hk₁ : 1 ≤ k) (hk₂ : k < 2 * d)
    (n : ℕ) (hn : 2 * ℓ * min d k ≤ n) :
    IsBooleanOn n k (sliceProductFun n d k ℓ) ∧
    HasDegreeLEOn n k d (sliceProductFun n d k ℓ) ∧
    ¬ IsJuntaOn n k (ℓ * min d k) (sliceProductFun n d k ℓ) := by
  sorry

end FilmusIhringer
