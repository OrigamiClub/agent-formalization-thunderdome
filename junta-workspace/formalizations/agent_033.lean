import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.

We formalize:
* the **forward** direction (`boolean_degree_d_on_slice_is_junta`): for `k ≥ 2d` and
  `n ≥ 2k`, every Boolean degree-`d` function on the slice `binom([n],k)` is an
  `m(d)`-junta, where `m : ℕ → ℕ` depends only on `d`;
* the **converse** (`no_junta_bound_below_2d`): for `1 ≤ k < 2d` there is no uniform
  junta bound;
* the **explicit witnessing family** (`witnessPoly` / `witness_family_not_junta`).
-/

namespace FilmusIhringer

/-- The `k`-slice of the `n`-cube: subsets of `Fin n` of cardinality exactly `k`,
i.e. `binom([n], k) = {S ⊆ {1,…,n} : |S| = k}`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector of a slice element, viewed as a point of `ℝ^n`. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.1 then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBooleanValued {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has **degree `≤ d`** on the slice if it agrees, on every slice element, with
the evaluation at the `0/1` indicator vector of some real multivariate polynomial of
total degree `≤ d`.  (Over `{0,1}` such a polynomial may be taken multilinear, so this
matches the "multilinear polynomial of total degree `≤ d`" formulation.) -/
def HasSliceDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S) p

/-- `f` is an **`m`-junta**: there is a coordinate set `J` with `|J| ≤ m` such that the
value of `f` on `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- The explicit witness polynomial
`∏_{i=1}^{ℓ} ( ∑_{j=1}^{e} x_{(i-1)·e + j} )`.
Zero-indexed here: `i` ranges over `range ℓ`, `j` over `range e`, and the variable used
is `x_{i·e + j}`; indices `≥ n` (which do not occur once `ℓ·e ≤ n`) contribute `0`. -/
noncomputable def witnessPoly (e ℓ n : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) else 0)

/-- The function on the `k`-slice obtained by restricting `witnessPoly e ℓ n`. -/
noncomputable def witnessFun (e ℓ n k : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (indicator S) (witnessPoly e ℓ n)

/-! ## Forward direction (Filmus–Ihringer)

There is a constant `m(d)` (a function of `d` alone) such that whenever `d ≥ 1`,
`k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on `binom([n], k)` is an
`m(d)`-junta. -/
theorem boolean_degree_d_on_slice_is_junta :
    ∃ m : ℕ → ℕ,
      ∀ d : ℕ, 1 ≤ d →
      ∀ k : ℕ, 2 * d ≤ k →
      ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ,
        IsBooleanValued f → HasSliceDegreeLE f d → IsJunta f (m d) := by
  sorry

/-! ## Converse

If `1 ≤ k < 2d` then for every `m` there are `n ≥ 2k` and a Boolean degree-`d` function
on `binom([n], k)` that is not an `m`-junta. -/
theorem no_junta_bound_below_2d :
    ∀ d : ℕ, 1 ≤ d →
    ∀ k : ℕ, 1 ≤ k → k < 2 * d →
    ∀ m : ℕ,
      ∃ n : ℕ, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ,
          IsBooleanValued f ∧ HasSliceDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-! ## Explicit witnessing family for the converse

Take `e = min d k`.  For every `ℓ` and every `n ≥ 2·(ℓ·e)`, the restriction of
`witnessPoly e ℓ n` to the `k`-slice is a Boolean function of degree `≤ d` whose junta
size is exactly `ℓ·e`: it is not an `m`-junta for any `m < ℓ·e`.  Given `m`, choosing
`ℓ` with `ℓ·e > m` produces the non-`m`-junta required by `no_junta_bound_below_2d`.

(The task's phrasing "not `ℓ·e`-juntas" is read as "not `(ℓ·e − 1)`-juntas", i.e. the
junta size is exactly `ℓ·e`; the function visibly depends only on the `ℓ·e` variables
`x_0, …, x_{ℓe-1}`, so it *is* an `ℓ·e`-junta.) -/
theorem witness_family_not_junta
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hk2 : k < 2 * d)
    (e : ℕ) (he : e = min d k)
    (ℓ : ℕ) (n : ℕ) (hn : 2 * (ℓ * e) ≤ n) :
    IsBooleanValued (witnessFun e ℓ n k) ∧
    HasSliceDegreeLE (witnessFun e ℓ n k) d ∧
    (∀ m : ℕ, m < ℓ * e → ¬ IsJunta (witnessFun e ℓ n k) m) := by
  sorry

end FilmusIhringer
