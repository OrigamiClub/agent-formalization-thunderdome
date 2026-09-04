import Mathlib

/-!
# Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer)

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is
proved.

Encoding summary (see `agent_080.md` for the rationale):

* The slice `binom([n], k)` is `{ S : Finset ℕ // S ⊆ Finset.range n ∧ S.card = k }`
  (natural-number coordinates, so that polynomials over `ℕ`-indexed variables can
  be evaluated without `Fin n` bound proofs).
* Boolean functions are `Slice n k → ℝ` together with the hypothesis `IsBoolean`
  ("every value is `0` or `1`").
* "degree `≤ d`" means: agrees on the whole slice with a multilinear polynomial
  in `MvPolynomial ℕ ℝ` of `totalDegree ≤ d`, evaluated at the `0/1` indicator
  vector.
* "`m`-junta" means: there is a coordinate set `J` with `J.card ≤ m` such that the
  value depends only on `S ∩ J`.
* `m(d)` is an existential (`∃ M : ℕ`) inside the statement.

Both directions are stated (`filmus_ihringer`), plus the explicit witnessing
family for the converse (`filmus_ihringer_explicit_family`).
-/

open MvPolynomial

namespace AgentEightyFilmusIhringer

/-- The slice `binom([n], k)`: the `k`-element subsets of `{0, 1, …, n-1}`,
encoded with natural-number coordinates. -/
abbrev Slice (n k : ℕ) : Type :=
  { S : Finset ℕ // S ⊆ Finset.range n ∧ S.card = k }

/-- The real indicator vector `x ∈ ℝ^ℕ` of a point of the slice
(`x i = 1` iff `i ∈ S`). -/
def indicatorVec {n k : ℕ} (S : Slice n k) : ℕ → ℝ :=
  fun i => if i ∈ S.1 then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it only takes the
values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `p` is *multilinear* if every monomial occurring in it is square-free,
i.e. each variable has exponent `≤ 1`. -/
def IsMultilinear (p : MvPolynomial ℕ ℝ) : Prop :=
  ∀ t ∈ p.support, ∀ i : ℕ, t i ≤ 1

/-- A function `f` on the slice has *degree `≤ d`* if it agrees, on the whole
slice, with some multilinear real polynomial of total degree `≤ d`, evaluated at
the `0/1` indicator vector. -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial ℕ ℝ,
    IsMultilinear p ∧ p.totalDegree ≤ d ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (indicatorVec S) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such
that `f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset ℕ, J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Filmus–Ihringer** (both directions).

* Forward: for every `d ≥ 1` there is a constant `M = m(d)` such that whenever
  `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on `binom([n], k)`
  is an `M`-junta.
* Converse: for every `d ≥ 1` and every `k` with `1 ≤ k < 2d`, no such uniform
  junta bound exists: for every `m` there are `n ≥ 2k` and a Boolean degree-`d`
  function on `binom([n], k)` that is not an `m`-junta. -/
theorem filmus_ihringer (d : ℕ) (hd : 1 ≤ d) :
    (∃ M : ℕ, ∀ n k : ℕ, 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta M f)
  ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f) := by
  sorry

/-- The Filmus–Ihringer witnessing polynomial: a product of `ℓ` linear forms over
pairwise-disjoint blocks of `e` coordinates,
`∏_{i=0}^{ℓ-1} ( x_{i·e} + x_{i·e+1} + … + x_{i·e+e-1} )`
(0-based reindexing of `∏_{i=1}^{ℓ} Σ_{j=1}^{e} x_{(i-1)e+j}`). -/
noncomputable def blockProduct (e ℓ : ℕ) : MvPolynomial ℕ ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e, MvPolynomial.X (i * e + j)

/-- **Filmus–Ihringer**, explicit witnessing family for the converse direction.

For `d ≥ 1` and `1 ≤ k < 2d`, put `e = min d k`.  For every `ℓ` and every
`n ≥ 2·ℓ·e`, the function on `binom([n], k)` obtained by evaluating
`blockProduct e ℓ` at the indicator vector is Boolean, has degree `≤ d`, and is
not an `ℓ·e`-junta; letting `ℓ` grow defeats any prescribed junta bound `m`. -/
theorem filmus_ihringer_explicit_family
    (d k ℓ : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hk2 : k < 2 * d)
    (e : ℕ) (he : e = min d k)
    (n : ℕ) (hn : 2 * ℓ * e ≤ n) :
    ∃ f : Slice n k → ℝ,
      (∀ S : Slice n k,
        f S = MvPolynomial.eval (indicatorVec S) (blockProduct e ℓ)) ∧
      IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta (ℓ * e) f := by
  sorry

end AgentEightyFilmusIhringer
