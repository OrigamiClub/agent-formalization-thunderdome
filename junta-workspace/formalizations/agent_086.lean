import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`.

We formalize three statements:

* `boolean_degree_le_isJunta` — the forward (main) direction: for each `d ≥ 1`
  there is a junta bound `m` valid for all large slices with `k ≥ 2d`.
* `exists_boolean_degree_le_not_isJunta` — the converse, in purely existential form.
* `blockWitness_not_isJunta` — the converse with the explicit witnessing family.

See `agent_086.md` for the encoding decisions and uncertainties.
-/

open Finset

namespace FilmusIhringer

/-- The `k`-slice `binom([n],k)`: subsets of `Fin n` of cardinality exactly `k`. -/
abbrev Slice (n k : ℕ) := { S : Finset (Fin n) // S.card = k }

/-- The `{0,1}`-indicator point in `ℕ → ℝ` associated to a slice element `S`:
coordinate `i` is `1` when `i < n` and the corresponding element of `Fin n` lies in
`S`, and `0` otherwise (coordinates `i ≥ n` are set to `0`). -/
noncomputable def sliceIndicator (n k : ℕ) (S : Slice n k) : ℕ → ℝ :=
  fun i => if h : i < n then (if (⟨i, h⟩ : Fin n) ∈ S.1 then (1 : ℝ) else 0) else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBooleanValued {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`* on the slice if it agrees, on every slice element, with the
evaluation (at the `{0,1}` indicator point) of some multilinear multivariate real
polynomial of total degree `≤ d`.  Multilinearity is expressed as: every monomial in
the support is squarefree. -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial ℕ ℝ,
    (∀ m ∈ p.support, ∀ i, m i ≤ 1) ∧
    p.totalDegree ≤ d ∧
    ∀ S, f S = MvPolynomial.eval (sliceIndicator n k S) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such that the
value of `f` on a slice element depends only on its intersection with `J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- The explicit witnessing polynomial.  With `e = min d k`, this is an OR of `ℓ`
disjoint size-`e` block-ANDs:
`∑_{i=0}^{ℓ-1} ∏_{j=0}^{e-1} X (i * e + j)`.

The source phrases the witnesses as a *product of block-sums*
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`.  On the slice that product is not
`{0,1}`-valued in general (e.g. `d = 2, k = 3, ℓ = 2`), whereas the sum-of-block-products
form *is* Boolean whenever `k < 2·min d k` (which follows from `k < 2d`), because two
disjoint blocks cannot both fit inside a `k`-set.  We therefore formalize the
sum-of-products reading; see the note. -/
noncomputable def blockWitness (d k ℓ : ℕ) : MvPolynomial ℕ ℝ :=
  ∑ i ∈ Finset.range ℓ, ∏ j ∈ Finset.range (min d k), MvPolynomial.X (i * min d k + j)

/-- **Forward direction (main theorem).**  For every degree bound `d ≥ 1` there is a
junta bound `m` such that: on every slice with `k ≥ 2d` and `n ≥ 2k`, every Boolean
function of degree `≤ d` on `binom([n],k)` is an `m`-junta. -/
theorem boolean_degree_le_isJunta :
    ∀ d : ℕ, 1 ≤ d → ∃ m : ℕ,
      ∀ n k : ℕ, 2 * d ≤ k → 2 * k ≤ n →
        ∀ f : Slice n k → ℝ,
          IsBooleanValued f → HasDegreeLE d f → IsJunta m f := by
  sorry

/-- **Converse direction (existential form).**  If `1 ≤ k < 2d`, then for every `m`
there is an `n ≥ 2k` and a Boolean degree-`≤ d` function on `binom([n],k)` that is not
an `m`-junta. -/
theorem exists_boolean_degree_le_not_isJunta :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
      ∃ n : ℕ, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ,
          IsBooleanValued f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-- **Converse direction (explicit family).**  For `1 ≤ k < 2d`, every `ℓ ≥ 1`, and
every `n ≥ 2ℓe` with `e = min d k`, the slice function given by `blockWitness d k ℓ`
is Boolean, has degree `≤ d`, and is not an `(ℓe − 1)`-junta — i.e. it depends on all
`ℓe` block coordinates.  Since `ℓ` is unbounded this defeats every fixed junta bound.

(The source writes "not `ℓe`-juntas"; taken literally the function is manifestly an
`ℓe`-junta since it only reads the `ℓe` block coordinates, so we read the intended
claim as "not an `(ℓe − 1)`-junta".) -/
theorem blockWitness_not_isJunta :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∀ n : ℕ, 2 * (ℓ * min d k) ≤ n →
        ∃ f : Slice n k → ℝ,
          (∀ S, f S = MvPolynomial.eval (sliceIndicator n k S) (blockWitness d k ℓ)) ∧
          IsBooleanValued f ∧
          HasDegreeLE d f ∧
          ¬ IsJunta (ℓ * min d k - 1) f := by
  sorry

end FilmusIhringer
