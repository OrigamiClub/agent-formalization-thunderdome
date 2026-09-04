import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.

Reference: Y. Filmus and F. Ihringer, *Boolean constant-degree functions on the
slice are juntas* (2019).
-/

open MvPolynomial Finset

namespace FilmusIhringer

/-- The slice `binom([n], k)`: subsets of `Fin n` of size exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-valued indicator vector of `S ⊆ Fin n`, i.e. the point of `ℝ^n`
at which a real polynomial gets evaluated. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- `f` is Boolean: every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has degree `≤ d` on the slice: `f` agrees, at every point of the slice,
with the evaluation of some real polynomial of total degree `≤ d` at the `{0,1}`
indicator vector.  Restricting to *multilinear* polynomials would define the same
class, since replacing `x_i^2` by `x_i` on `{0,1}` inputs does not raise the total
degree, so the more permissive form is used here. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = eval (indicator S.1) p

/-- `f` is an `m`-junta: there is a set `J` of at most `m` coordinates such that
the value of `f` at any slice element `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-! ## Forward direction -/

/-- **Filmus–Ihringer, positive direction.**
For every `d ≥ 1` there is a bound `M = m(d)`, depending only on `d`, such that
whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean function of degree `≤ d` on the
slice `binom([n], k)` is an `M`-junta.

`m(d)` is presented as an existential `∃ M : ℕ` at the front of the statement
(rather than an explicit `m : ℕ → ℕ`), which is what "there is a constant `m(d)`"
asserts. -/
theorem boolean_degree_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f M := by
  sorry

/-! ## Converse direction (pure existence) -/

/-- **Filmus–Ihringer, tightness (existential form).**
If `1 ≤ k < 2d`, the junta bound fails completely: for every `m` there are
`n ≥ 2k` and a Boolean function of degree `≤ d` on `binom([n], k)` that is not an
`m`-junta. -/
theorem boolean_degree_not_junta (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
      IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-! ## Explicit witnessing family -/

/-- Coordinate `(i, j)` of the `i`-th block (`i < ℓ`, `j < e`), placed inside
`Fin n` via the canonical injection `Fin ℓ × Fin e ≃ Fin (ℓ * e) ↪ Fin n`. -/
def blockCoord (n ℓ e : ℕ) (h : ℓ * e ≤ n) (i : Fin ℓ) (j : Fin e) : Fin n :=
  Fin.castLE h (finProdFinEquiv (i, j))

/-- The explicit family from Filmus–Ihringer with `e = min d k`:
`f(S) = Σ_{i=1}^{ℓ} Π_{j=1}^{e} x_{(i-1)e+j}`, evaluated at the indicator vector
of `S`.  The `i`-th term is the indicator that the `i`-th block of `e`
coordinates is fully contained in `S`.

Note: the source text writes this as a product of sums, `Π_i (Σ_j x_{(i-1)e+j})`;
that expression is not `{0,1}`-valued on the slice.  The intended object — the
Boolean degree-`d` function that depends on `ℓe` coordinates — is the sum of
degree-`e` monomials used here.  On `binom([n], k)` with `k < 2d` one has
`k < 2e`, so `S` contains at most one block and `f` is `{0,1}`-valued. -/
noncomputable def witnessFn (n k ℓ e : ℕ) (h : ℓ * e ≤ n) :
    Slice n k → ℝ :=
  fun S => ∑ i : Fin ℓ, ∏ _j : Fin e,
    (if blockCoord n ℓ e h i _j ∈ S.1 then (1 : ℝ) else 0)

/-- **Explicit witnesses for tightness.**
Let `d ≥ 1`, `1 ≤ k < 2d`, `e = min d k`, and `n ≥ 2·ℓ·e`.  Then `witnessFn` is a
Boolean function of degree `≤ d` on `binom([n], k)` that is not an `m`-junta for
any `m < ℓ·e` (its value genuinely depends on all `ℓ·e` block coordinates).

The source phrase "not `ℓe`-juntas" is read here as "not an `m`-junta for any
`m < ℓe`": the function *is* an `ℓe`-junta (it depends on exactly the `ℓe` block
coordinates), so `ℓe` is the number of relevant coordinates, not a value of `m`
for which junta-ness fails.

Combined with `ℓ := m + 1` and `e = min d k ≥ 1` (so `ℓ·e ≥ m + 1 > m`), this
yields `boolean_degree_not_junta`. -/
theorem witnessFn_spec (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (e : ℕ) (he : e = min d k)
    (ℓ n : ℕ) (hn : 2 * (ℓ * e) ≤ n) :
    IsBoolean (witnessFn n k ℓ e (by omega)) ∧
    HasDegreeLE (witnessFn n k ℓ e (by omega)) d ∧
    (∀ m : ℕ, m < ℓ * e → ¬ IsJunta (witnessFn n k ℓ e (by omega)) m) := by
  sorry

end FilmusIhringer
