import Mathlib

open scoped BigOperators

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`.

We formalize:

* the **positive direction** (`positive_direction`): for each `d ≥ 1` there is a
  constant `m(d)` (existentially quantified inside the statement) such that for
  `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`≤ d` function on the slice
  `binom([n],k)` is an `m(d)`-junta;

* the **converse direction** (`converse_direction`): for `1 ≤ k < 2d` and every
  `m`, some slice `binom([n],k)` with `n ≥ 2k` carries a Boolean degree-`≤ d`
  function that is not an `m`-junta;

* the **explicit witnessing family** (`witness_family`): the slice functions
  induced by the polynomials `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` with
  `e = min d k` realize the converse direction.
-/

namespace FilmusIhringer

/-- The slice `binom([n], k)`: the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-valued real indicator vector of a subset `S ⊆ Fin n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it takes only the values
`0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- A polynomial is *multilinear* if every exponent occurring in every monomial of
its support is `≤ 1`. -/
def IsMultilinear {n : ℕ} (P : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ m ∈ P.support, ∀ i, m i ≤ 1

/-- A slice function `f` has *degree ≤ d* if it agrees, on the whole slice, with
the evaluation at the `{0,1}` indicator vector of some multilinear real polynomial
of total degree `≤ d`. -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ P : MvPolynomial (Fin n) ℝ,
    IsMultilinear P ∧ P.totalDegree ≤ d ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S.1) P

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such
that the value `f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-! ## Positive direction -/

/-- **Filmus–Ihringer, positive direction.**
For every `d ≥ 1` there is a constant `M = m(d)` such that for all `k ≥ 2d` and all
`n ≥ 2k`, every Boolean degree-`≤ d` function on the slice `binom([n], k)` is an
`M`-junta.  Here `m(d)` is existentially quantified inside the statement. -/
theorem positive_direction (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : ℕ,
      ∀ (k : ℕ), 2 * d ≤ k →
        ∀ (n : ℕ), 2 * k ≤ n →
          ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta M f := by
  sorry

/-! ## Converse direction -/

/-- **Filmus–Ihringer, converse direction.**
If `1 ≤ k < 2d` then no uniform junta bound exists: for every `m` there are an
`n ≥ 2k` and a Boolean degree-`≤ d` function on the slice `binom([n], k)` that is
not an `m`-junta. -/
theorem converse_direction (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-! ## Explicit witnessing family -/

/-- The polynomial `∑_{i=0}^{ℓ-1} ∏_{j=0}^{e-1} x_{i·e + j}` with `e = min d k`
(a sum of `ℓ` disjoint "block" monomials, each of degree `e ≤ d`).
Coordinates whose index is `≥ n` are replaced by `0`; this does not happen once
`ℓ · e ≤ n`. -/
noncomputable def witnessPoly (n d k ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ i ∈ Finset.range ℓ,
    ∏ j ∈ Finset.range (min d k),
      (if h : i * min d k + j < n then
          MvPolynomial.X (⟨i * min d k + j, h⟩ : Fin n)
        else 0)

/-- The slice function induced by `witnessPoly`. -/
noncomputable def witnessFn (n d k ℓ : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (indicator S.1) (witnessPoly n d k ℓ)

/-- **Filmus–Ihringer, explicit family.**
Assume `1 ≤ k < 2d` and put `e = min d k`.  For every `ℓ` with `k ≤ ℓ · e` and
every `n ≥ 2 · ℓ · e`, the function `witnessFn n d k ℓ` is Boolean, has degree
`≤ d`, and is not an `m`-junta for any `m < ℓ · e`.  Consequently, given `m`,
taking any `ℓ` with `k ≤ ℓ · e` and `ℓ · e > m` yields a Boolean degree-`≤ d`
non-`m`-junta on a slice with `n ≥ 2k`, which is the converse direction. -/
theorem witness_family (d k ℓ : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hk2 : k < 2 * d)
    (hℓ : k ≤ ℓ * min d k) (n : ℕ) (hn : 2 * (ℓ * min d k) ≤ n) :
    IsBoolean (witnessFn n d k ℓ)
      ∧ HasDegreeLE d (witnessFn n d k ℓ)
      ∧ ∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta m (witnessFn n d k ℓ) := by
  sorry

end FilmusIhringer
