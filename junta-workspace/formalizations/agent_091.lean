import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-!
# Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer)

Statement-only formalization.  Every theorem ends in `:= by sorry`.

We formalize:
* the forward direction (`filmus_ihringer_forward`): existence of a bound `m(d)`;
* the converse / tightness direction (`filmus_ihringer_converse`): a clean existential
  counterexample for `k < 2d`;
* the converse with the explicit witnessing family (`filmus_ihringer_converse_witness`).
-/

/-- A point of the slice `binom([n], k)`: a `k`-element subset of `Fin n`. -/
abbrev Slice (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector of a subset, viewed as a real point of the cube `{0,1}^n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if each of its values is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- A multilinear polynomial: every variable occurs with exponent `≤ 1` in every monomial. -/
def IsMultilinear {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ m ∈ p.support, ∀ i, m i ≤ 1

/-- `f` has *degree `≤ d`* on the slice: it agrees on every `k`-set with the evaluation at the
indicator vector of a multilinear real polynomial of total degree `≤ d`. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    IsMultilinear p ∧ p.totalDegree ≤ d ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S.1) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that the value of
`f` on `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, (S.1 ∩ J : Finset (Fin n)) = T.1 ∩ J → f S = f T

/-- The explicit witnessing family
`∏_{i=0}^{ℓ-1} (∑_{j=0}^{e-1} x_{i*e+j})`:
a product of `ℓ` pairwise-disjoint blocks of `e` variables each.
Indices `≥ n` contribute `0` (they never occur when `ℓ * e ≤ n`). -/
noncomputable def blockProdPoly (ℓ e n : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) else 0)

/-- **Forward direction (Filmus–Ihringer).**
For every `d ≥ 1` there is a constant `m(d)` (here an existential `m : ℕ`) such that:
whenever `k ≥ 2d`, then for every `n ≥ 2k`, every Boolean degree-`d` function on the slice
`binom([n],k)` is an `m(d)`-junta. -/
theorem filmus_ihringer_forward (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f m := by
  sorry

/-- **Converse direction (tightness).**
If `1 ≤ k < 2d`, then no junta bound can exist: for every `m` there are `n ≥ 2k` and a Boolean
degree-`d` function on `binom([n],k)` that is not an `m`-junta. -/
theorem filmus_ihringer_converse (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk0 : 1 ≤ k) (hk : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
      IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- **Converse direction with the explicit witnesses.**
Set `e = min d k`.  For any number of blocks `ℓ ≥ 1`, and any `n` with `n ≥ 2 * ℓ * e` and
`n ≥ 2k`, the function `f` induced on the slice `binom([n],k)` by `blockProdPoly ℓ e n` is
Boolean, has degree `≤ d`, and depends on all `ℓ * e` block coordinates: it is not an
`m`-junta for any `m < ℓ * e`.  Taking `ℓ` large defeats any prescribed `m`, giving the
converse direction. -/
theorem filmus_ihringer_converse_witness (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk0 : 1 ≤ k) (hk : k < 2 * d)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (n : ℕ)
    (hn : 2 * (ℓ * min d k) ≤ n) (hkn : 2 * k ≤ n) :
    ∃ f : Slice n k → ℝ,
      (∀ S : Slice n k,
          f S = MvPolynomial.eval (indicator S.1) (blockProdPoly ℓ (min d k) n)) ∧
      IsBoolean f ∧
      HasDegreeLE f d ∧
      (∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta f m) := by
  sorry

end FilmusIhringer
