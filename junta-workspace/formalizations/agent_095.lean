import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  All theorems end in `:= by sorry`.

We formalize:

* the **forward** direction (`k ≥ 2d`  ⟹  bounded junta), with `m(d)` existentially
  quantified inside the statement (uniformly in `k`, `n`, `f`);
* the **converse** direction (`1 ≤ k < 2d`  ⟹  arbitrarily large non-juntas exist);
* the **explicit witnessing family**
  `∏_{i=1}^{ℓ} ( ∑_{j=1}^{e} x_{(i-1)e+j} )` with `e = min d k`.
-/

/-- The slice `binom([n],k)` : the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- Evaluate a real polynomial at the `0/1` indicator vector of a slice point. -/
noncomputable def sliceEval {n k : ℕ} (p : MvPolynomial (Fin n) ℝ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (fun i => if i ∈ S.1 then (1 : ℝ) else 0) p

/-- A real-valued function on the slice is *Boolean* if it only takes the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`* on the slice if it agrees, at every slice point, with the
evaluation at the `0/1` indicator vector of some real multilinear/real polynomial of
total degree `≤ d`. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = sliceEval p S

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such that the
value of `f` depends only on the intersection of the input with `J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- The explicit witnessing family
`∏_{i=1}^{ℓ} ( ∑_{j=1}^{e} x_{(i-1)·e + j} )`, with the variables of block `i`
(`0 ≤ i < ℓ`) occupying coordinates `i·e, …, i·e + e - 1` of `Fin n`.
The layout `Fin ℓ × Fin e → Fin (ℓ*e) → Fin n` is given by `finProdFinEquiv`
followed by `Fin.castLE`. -/
noncomputable def blockSumPoly (e ℓ n : ℕ) (h : 2 * (ℓ * e) ≤ n) : MvPolynomial (Fin n) ℝ :=
  ∏ i : Fin ℓ, ∑ j : Fin e,
    MvPolynomial.X
      (Fin.castLE (by first | omega | (rw [Nat.mul_comm]; omega))
        (finProdFinEquiv (i, j)))

/-! ## Forward direction : `k ≥ 2d` -/

/-- **Filmus–Ihringer, upper bound.**
For every `d ≥ 1` there is a constant `m(d)` such that: whenever `k ≥ 2d` and `n ≥ 2k`,
every Boolean degree-`d` function on `binom([n],k)` is an `m(d)`-junta.

`m(d)` is the leading existential, hence a single constant depending on `d` only,
uniform in `k`, `n` and `f`. -/
theorem boolean_degree_d_is_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f m := by
  sorry

/-! ## Converse direction : `1 ≤ k < 2d` -/

/-- **Filmus–Ihringer, lower bound (plain form).**
If `1 ≤ k < 2d` then for every `m` there exist `n ≥ 2k` and a Boolean degree-`d`
function on `binom([n],k)` that is not an `m`-junta. -/
theorem exists_boolean_degree_d_not_junta
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
      IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- **Filmus–Ihringer, lower bound (explicit witnesses).**
If `1 ≤ k < 2d`, set `e = min d k`.  For every `m` one can choose `ℓ` with `ℓ·e > m`
so that, for every `n ≥ 2·ℓ·e` (and `n ≥ 2k`), the function
`sliceEval (blockSumPoly e ℓ n …)` on `binom([n],k)` is Boolean, has degree `≤ d`,
and is not an `ℓ·e`-junta — hence not an `m`-junta. -/
theorem exists_boolean_degree_d_not_junta_explicit
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ ℓ : ℕ, m < ℓ * min d k ∧
      ∀ n : ℕ, ∀ h : 2 * (ℓ * min d k) ≤ n, 2 * k ≤ n →
        IsBoolean (sliceEval (n := n) (k := k) (blockSumPoly (min d k) ℓ n h)) ∧
        HasDegreeLE (sliceEval (n := n) (k := k) (blockSumPoly (min d k) ℓ n h)) d ∧
        ¬ IsJunta (sliceEval (n := n) (k := k) (blockSumPoly (min d k) ℓ n h)) (ℓ * min d k) := by
  sorry

end FilmusIhringer
