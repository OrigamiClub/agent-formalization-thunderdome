import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-!
# Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer)

Statement-only formalization.  All theorems end in `:= by sorry`.

We formalize three statements:

* `boolean_degree_junta_of_large_slice` — the upper bound: for `d ≥ 1` there is a
  constant `m(d)` (depending only on `d`) such that if `k ≥ 2d` and `n ≥ 2k`, every
  Boolean degree-`≤ d` function on `binom([n], k)` is an `m(d)`-junta.
* `exists_boolean_degree_not_junta` — tightness, existential form: if `1 ≤ k < 2d`
  then for every `m` there are `n ≥ 2k` and a Boolean degree-`≤ d` function on
  `binom([n], k)` that is not an `m`-junta.
* `sliceWitness_spec` — tightness with explicit witnesses (see the note file about a
  `∏`/`∑` transposition relative to the source phrasing).
-/

/-- The slice `binom([n], k)`: the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1} ⊆ ℝ` indicator vector of a slice point. -/
def indicatorVec {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.1 then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBooleanOnSlice {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *Boolean degree `≤ d`* on the slice: it agrees, on every slice point, with
a multilinear real polynomial of total degree `≤ d`, evaluated at the `{0,1}` indicator
vector.  The condition `∀ i, p.degreeOf i ≤ 1` encodes multilinearity. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ i, p.degreeOf i ≤ 1) ∧
    p.totalDegree ≤ d ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicatorVec S) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that
`f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-! ## The explicit witnessing family -/

/-- The `i`-th block (0-based), of width `e`: the coordinates `i*e, …, i*e + e - 1`
viewed inside `Fin n`. -/
def blockFin (n e i : ℕ) : Finset (Fin n) :=
  Finset.filter (fun x : Fin n => i * e ≤ (x : ℕ) ∧ (x : ℕ) < i * e + e) Finset.univ

/-- `sliceWitnessPoly n e ℓ = ∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e + j}` : a sum of `ℓ`
pairwise-disjoint squarefree monomials, each of degree `e`.

(The source statement writes the witnesses as a *product of sums*
`∏_{i}(∑_{j} x_{(i-1)e+j})`; this *sum of products* is the reading that is genuinely
Boolean of degree `≤ d` on the slice `binom([n],k)` when `k < 2d`, and that lets `ℓ`
grow without bound.  See the accompanying note.) -/
noncomputable def sliceWitnessPoly (n e ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ i ∈ Finset.range ℓ, ∏ x ∈ blockFin n e i, MvPolynomial.X x

/-- The function on the slice induced by `sliceWitnessPoly`.  On the slice it is the
indicator that `S` contains at least one of the `ℓ` disjoint width-`e` blocks. -/
noncomputable def sliceWitness {k : ℕ} (n e ℓ : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (indicatorVec S) (sliceWitnessPoly n e ℓ)

/-! ## The theorems -/

/-- **Filmus–Ihringer, upper bound.**  For every `d ≥ 1` there is a constant `m(d)`
depending only on `d` such that, as soon as `k ≥ 2d` and `n ≥ 2k`, every Boolean
degree-`≤ d` function on the slice `binom([n], k)` is an `m(d)`-junta. -/
theorem boolean_degree_junta_of_large_slice (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : ℕ, ∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ,
        IsBooleanOnSlice f → HasDegreeLE f d → IsJunta f M := by
  sorry

/-- **Filmus–Ihringer, tightness (existential form).**  If `1 ≤ k < 2d` then no junta
bound depending only on `d` can exist: for every `m` there are `n ≥ 2k` and a Boolean
degree-`≤ d` function on `binom([n], k)` that is not an `m`-junta. -/
theorem exists_boolean_degree_not_junta (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
      IsBooleanOnSlice f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- **Filmus–Ihringer, tightness (explicit witnesses).**  For `1 ≤ k < 2d` set
`e = min d k` (then `1 ≤ e ≤ d` and `2 * e > k`).  For every `ℓ`, and every `n` with
`n ≥ 2k` and `n ≥ 2 * ℓ * e`, the function `sliceWitness n e ℓ` on `binom([n], k)`:

* is Boolean;
* has Boolean degree `≤ d`;
* is not an `m`-junta for any `m < ℓ * e`.

Taking `ℓ` with `ℓ * e > m` therefore witnesses `exists_boolean_degree_not_junta`. -/
theorem sliceWitness_spec (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (ℓ n : ℕ) (hnk : 2 * k ≤ n) (hn : 2 * ℓ * (min d k) ≤ n) :
    IsBooleanOnSlice (sliceWitness (k := k) n (min d k) ℓ) ∧
    HasDegreeLE (sliceWitness (k := k) n (min d k) ℓ) d ∧
    (∀ m : ℕ, m < ℓ * (min d k) →
      ¬ IsJunta (sliceWitness (k := k) n (min d k) ℓ) m) := by
  sorry

end FilmusIhringer
