import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (agent 022).  Every theorem ends in `:= by sorry`;
nothing is proved.

We formalize:
* the forward direction  (`boolean_degree_le_isJunta`): for `d ≥ 1` there is a
  `d`-only bound `m` so that for `k ≥ 2d` and `n ≥ 2k` every Boolean degree-`d`
  function on the slice `binom([n],k)` is an `m`-junta;
* the converse / sharpness (`not_isJunta_of_lt_two_mul`): for `1 ≤ k < 2d` and
  every `m` there is a Boolean degree-`d` function on some `binom([n],k)`
  (`n ≥ 2k`) that is not an `m`-junta;
* the explicit witnessing family (`witnessFun`, `witnessFun_spec`).

See `agent_022.md` for encoding decisions and caveats.
-/

namespace FilmusIhringer

open scoped BigOperators

/-- The slice `binom([n], k)` : the `k`-element subsets of `{1, …, n}`, carried as
a subtype of `Finset (Fin n)`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- Real `0/1` indicator vector of a subset of `Fin n` (the point of the cube at
which a polynomial is evaluated to read off its value on the slice). -/
def ind {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- A function on the slice `binom([n],k)` has **degree ≤ d** if it agrees, at
every point of the slice, with the evaluation at the `0/1` indicator vector of
some *multilinear* real polynomial (`∀ i, degreeOf i ≤ 1`) of total degree ≤ `d`.

(On `0/1` inputs every polynomial agrees with its multilinearization, whose total
degree does not increase, so dropping the multilinearity conjunct would give an
equivalent notion.) -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ i : Fin n, MvPolynomial.degreeOf i p ≤ 1) ∧
      MvPolynomial.totalDegree p ≤ d ∧
        ∀ S : Slice n k, f S = MvPolynomial.eval (ind S.1) p

/-- `f` depends only on the coordinates in `J` : any two slice points with the
same trace on `J` receive the same value. -/
def DependsOnlyOn {n k : ℕ} (f : Slice n k → ℝ) (J : Finset (Fin n)) : Prop :=
  ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- `f` is an **m-junta** : its value depends only on `S ∩ J` for some coordinate
set `J` with `|J| ≤ m`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧ DependsOnlyOn f J

/-! ## The two directions -/

/-- **Forward direction (Filmus–Ihringer).**  For every `d ≥ 1` there is a bound
`m = m(d)`, depending on `d` only (it is quantified before `k` and `n`), such that
whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on the slice
`binom([n],k)` is an `m`-junta. -/
theorem boolean_degree_le_isJunta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta m f := by
  sorry

/-- **Converse (sharpness).**  If `1 ≤ k < 2d` then no such junta bound exists:
for every `m` there is an `n ≥ 2k` and a Boolean degree-`d` function on
`binom([n],k)` that is not an `m`-junta. -/
theorem not_isJunta_of_lt_two_mul (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-! ## Explicit witnessing family

With `e = min d k`, block `i ∈ {0, …, ℓ-1}` is the set of coordinates
`{i·e, …, i·e + e - 1}` of `Fin n`.  The witness is

  `∑_{i=0}^{ℓ-1} ∏_{j=0}^{e-1} x_{i·e + j}`

read as a function on the slice by evaluating at the `0/1` indicator vector, i.e.
the number of blocks entirely contained in `S`.  For `1 ≤ k < 2d` one has
`k < 2·min d k`, so a `k`-set contains at most one block and this count is
`{0,1}`-valued; the polynomial is multilinear of total degree `e ≤ d`; and the
function genuinely depends on all `ℓ·e` block coordinates. -/

/-- Coordinates of `Fin n` in the `i`-th block of width `e` : `{i·e, …, i·e+e-1}`. -/
def block (e i n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v : Fin n => (v : ℕ) / e = i)

/-- The Filmus–Ihringer lower-bound witness on `binom([n],k)` :
`∑_{i<ℓ} ∏_{v ∈ block i} x_v`, the number of width-`(min d k)` blocks contained
in `S`. -/
noncomputable def witnessFun (d k ℓ n : ℕ) : Slice n k → ℝ :=
  fun S => ∑ i ∈ Finset.range ℓ, ∏ v ∈ block (min d k) i n, ind S.1 v

/-- **The explicit family witnesses the converse.**  For `1 ≤ k < 2d`,
`e = min d k`, any number of blocks `ℓ`, and `n ≥ 2·ℓ·e`, the function
`witnessFun d k ℓ n` is a Boolean degree-`d` function on `binom([n],k)` that is
not an `m`-junta for any `m < ℓ·e`.  Letting `ℓ → ∞` this rules out any
`d`-dependent junta bound. -/
theorem witnessFun_spec (d k ℓ n : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hk2 : k < 2 * d)
    (hn : 2 * ℓ * min d k ≤ n) :
    IsBoolean (witnessFun d k ℓ n) ∧
      HasDegreeLE d (witnessFun d k ℓ n) ∧
      (∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta m (witnessFun d k ℓ n)) := by
  sorry

end FilmusIhringer
