import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (agent 099).  Nothing is proved; every theorem
ends in `:= by sorry`.

We formalize:
* the positive direction (`juntas_of_degree_le`);
* the negative direction in abstract form (`not_juntas_of_degree_le`);
* the negative direction with the explicit witnessing family
  (`witness_not_junta`).
-/

open scoped BigOperators

namespace FilmusIhringer

/-- The slice `binom([n], k)`: subsets of `Fin n` of size exactly `k`.
An `abbrev` so that `.val`, `.card`, `∩` on the underlying `Finset` are
available without manual unfolding. -/
abbrev Slice (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector of a finite set, as a point of `Fin n → ℝ`.
This is the argument at which representing polynomials are evaluated. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- `f` takes only the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has degree `≤ d` on the slice: it agrees, on every point of the slice,
with the evaluation at the `0/1` indicator vector of some real polynomial in
`n` variables of total degree `≤ d`.  (Restricting to the slice, such a
polynomial can always be taken multilinear, so imposing multilinearity here
would give an equivalent notion; we keep the weaker hypothesis.) -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S.1) p

/-- `f` is an `m`-junta: there is a set `J` of at most `m` coordinates such that
the value of `f` on `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Positive direction (Filmus–Ihringer).**  For every `d ≥ 1` there is a
constant `m = m(d)` such that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean
degree-`d` function on the slice `binom([n], k)` is an `m`-junta.

Here `m(d)` is stated as an existential (`∃ m : ℕ`) depending on `d`. -/
theorem juntas_of_degree_le (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ n k : ℕ, 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f m := by
  sorry

/-- **Negative direction, abstract form.**  If `1 ≤ k < 2d` then no constant
junta bound can work: for every `m` there exist `n ≥ 2k` and a Boolean
degree-`d` function on `binom([n], k)` that is not an `m`-junta. -/
theorem not_juntas_of_degree_le (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hkd : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- The explicit witnessing polynomial
`∏_{i=1}^{ℓ} ( ∑_{j=1}^{e} x_{(i-1)e + j} )` in `n` real variables.

The `1`-based index `(i-1)e + j` (for `1 ≤ i ≤ ℓ`, `1 ≤ j ≤ e`) is reindexed
here to the `0`-based `i*e + j` with `i ∈ range ℓ`, `j ∈ range e`, so the
variables used are `x_0, …, x_{ℓe-1}`.  Indices that fall outside `Fin n`
(only possible when `ℓe > n`) contribute the zero polynomial. -/
noncomputable def witnessPoly (n e ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) else 0)

/-- The function on the slice `binom([n], k)` induced by `witnessPoly n e ℓ`
by evaluating at the `0/1` indicator vector. -/
noncomputable def witnessFun (n k e ℓ : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (indicator S.1) (witnessPoly n e ℓ)

/-- **Negative direction, explicit witnesses (Filmus–Ihringer).**  Assume
`1 ≤ k < 2d` and set `e = min d k`.  For every `m` there is an `ℓ` with
`ℓe > m` such that, for all `n ≥ 2ℓe` with `n ≥ 2k`, the function
`witnessFun n k e ℓ` is a Boolean degree-`d` function on `binom([n], k)` that
is not an `ℓe`-junta.  Since `ℓe > m`, it is a fortiori not an `m`-junta, so
the family defeats every constant junta bound. -/
theorem witness_not_junta (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hkd : k < 2 * d) (m : ℕ) :
    ∃ ℓ : ℕ, m < ℓ * min d k ∧
      ∀ n : ℕ, 2 * (ℓ * min d k) ≤ n → 2 * k ≤ n →
        IsBoolean (witnessFun n k (min d k) ℓ) ∧
        HasDegreeLE (witnessFun n k (min d k) ℓ) d ∧
        ¬ IsJunta (witnessFun n k (min d k) ℓ) (ℓ * min d k) := by
  sorry

end FilmusIhringer
