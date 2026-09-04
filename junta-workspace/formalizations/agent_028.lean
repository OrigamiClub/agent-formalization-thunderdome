/-
  Filmus–Ihringer / Filmus: Boolean constant-degree functions on the slice are juntas,
  and the sharp threshold `k ≥ 2d`.

  Reference: Y. Filmus, "Junta threshold for low degree Boolean functions on the slice",
  arXiv:2203.04760 (Theorem 1.1); building on Y. Filmus, F. Ihringer,
  "Boolean constant degree functions on the slice are juntas", Discrete Math. 342 (2019).

  STATEMENT ONLY.  Every theorem ends in `:= by sorry`.
-/
import Mathlib

open MvPolynomial

namespace FilmusIhringer

/-- The slice `binom([n], k)`: subsets of `Fin n` of size exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- Evaluate a real polynomial at the `{0,1}`-indicator vector of a slice point. -/
noncomputable def sliceEval {n k : ℕ} (S : Slice n k) (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  MvPolynomial.eval (fun i => if i ∈ (S : Finset (Fin n)) then (1 : ℝ) else 0) p

/-- `f` is Boolean-valued: it takes values in `{0,1} ⊆ ℝ`. -/
def IsBooleanValued {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has degree `≤ d`: it agrees on the whole slice with a real polynomial of total
degree `≤ d`, evaluated at the `{0,1}`-indicator vector.  (On `{0,1}`-points one may take the
polynomial multilinear without raising the total degree, so multilinearity is not imposed.) -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧ ∀ S, f S = sliceEval S p

/-- `f` is an `m`-junta: there is a set `J` of at most `m` coordinates such that `f S` depends
only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, (S : Finset (Fin n)) ∩ J = (T : Finset (Fin n)) ∩ J → f S = f T

/-- **Positive direction** (Filmus, Theorem 1.1, part 1; qualitative form Filmus–Ihringer 2019).
For every degree `d ≥ 1` there is a bound `m(d)` such that whenever `k ≥ 2d` and `n ≥ 2k`,
every Boolean degree-`d` function on the slice `binom([n],k)` is an `m(d)`-junta.
`m(d)` is packaged as an existential (a single constant depending only on `d`). -/
theorem junta_of_degree_le (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBooleanValued f → HasDegreeLE f d → IsJunta m f := by
  sorry

/-- **Converse / sharpness** (Filmus, Theorem 1.1, part 2), as a pure existential.
If `1 ≤ k < 2d` then the threshold genuinely fails: for every `m` there is a slice
`binom([n],k)` with `n ≥ 2k` carrying a Boolean degree-`d` function that is not an `m`-junta. -/
theorem not_junta_of_degree_le_of_lt
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBooleanValued f ∧ HasDegreeLE f d ∧ ¬ IsJunta m f := by
  sorry

/-!
### The explicit witnessing family

With `e = min d k`, take `ℓ` pairwise-disjoint blocks of `e` coordinates each, given by an
injective `ι : Fin ℓ → Fin e → Fin n` (the paper's concrete choice is `ι i j = (i-1)·e + j`).
The polynomial `∑_{i<ℓ} ∏_{j<e} x_{ι i j}` counts how many blocks are entirely contained in `S`.
Because `k < 2d`, no two disjoint `e`-blocks fit inside a `k`-set, so this count is `0` or `1`:
a Boolean function of total degree `e ≤ d` that genuinely uses all `ℓ·e` block coordinates.
-/

/-- `∑_{i<ℓ} ∏_{j<e} x_{ι i j}` : "number of blocks fully contained", as a polynomial. -/
noncomputable def blockPoly (n ℓ e : ℕ) (ι : Fin ℓ → Fin e → Fin n) : MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin ℓ, ∏ j : Fin e, MvPolynomial.X (ι i j)

/-- The induced function on the slice. -/
noncomputable def blockFun (n k ℓ e : ℕ) (ι : Fin ℓ → Fin e → Fin n) : Slice n k → ℝ :=
  fun S => sliceEval S (blockPoly n ℓ e ι)

/-- The explicit family witnesses the converse: for `1 ≤ k < 2d`, `e = min d k`, disjoint blocks
`ι`, and `n ≥ max (2k) (2ℓe)`, the function `blockFun` is Boolean, has degree `≤ d`, and is not an
`m`-junta for any `m < ℓ·e` (equivalently: not an `(ℓe − 1)`-junta — it needs all `ℓe` block
coordinates).  Taking `ℓ` with `ℓ·e > m` yields the previous theorem. -/
theorem blockFun_is_witness
    (d k : ℕ) (hd : 1 ≤ d) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (ℓ n e : ℕ) (he : e = min d k)
    (hn1 : 2 * k ≤ n) (hn2 : 2 * ℓ * e ≤ n)
    (ι : Fin ℓ → Fin e → Fin n)
    (hι : Function.Injective (fun p : Fin ℓ × Fin e => ι p.1 p.2)) :
    IsBooleanValued (blockFun n k ℓ e ι) ∧
      HasDegreeLE (blockFun n k ℓ e ι) d ∧
      ∀ m : ℕ, m < ℓ * e → ¬ IsJunta m (blockFun n k ℓ e ι) := by
  sorry

end FilmusIhringer
