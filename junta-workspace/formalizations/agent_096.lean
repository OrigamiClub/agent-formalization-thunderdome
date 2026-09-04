/-
Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas.

Statement-only formalization (every theorem ends in `:= by sorry`).

We formalize:
  * the positive direction  (`boolean_degree_d_is_junta`),
  * the sharpness / converse as a pure existential
        (`boolean_degree_d_not_junta`),
  * the sharpness / converse with the explicit witnessing family
        (`boolean_degree_d_not_junta_explicit`).

See `agent_096.md` for the encoding decisions and the (several) uncertainties.
-/
import Mathlib

open Finset

namespace FilmusIhringer

/-- The slice `binom([n],k)` : the `k`-element subsets of `Fin n`
(a stand-in for `{1,…,n}`). -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-valued indicator vector of a slice element. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.1 then 1 else 0

/-- Evaluate a real multilinear polynomial at the indicator vector of a slice element. -/
noncomputable def evalSlice {n k : ℕ} (p : MvPolynomial (Fin n) ℝ) (S : Slice n k) : ℝ :=
  MvPolynomial.eval (indicator S) p

/-- `f` takes only the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has degree `≤ d` on the slice: it agrees, on every slice element, with the
evaluation at the indicator vector of some real polynomial that is multilinear
(each monomial exponent `≤ 1`) and of total degree `≤ d`. -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ s ∈ p.support, ∀ i, s i ≤ 1) ∧
    p.totalDegree ≤ d ∧
    ∀ S, f S = evalSlice p S

/-- `f` is an `m`-junta: there is a set `J` of at most `m` coordinates such that the
value of `f` on `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- The explicit Filmus–Ihringer family.

With `e = min d k` and `ℓ` pairwise-disjoint blocks of size `e`, this is the
polynomial `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`, here written with `0`-based
indices so that the blocks are `{ i*e, …, i*e + e-1 }` for `i = 0,…,ℓ-1`.
The variable index `i*e + j` is guarded by a proof that it is `< n`; any
out-of-range term is `0` (this never triggers once `n ≥ 2·ℓ·e`). -/
noncomputable def FIpoly (d k n ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range (min d k),
    if h : i * min d k + j < n then
      MvPolynomial.X (⟨i * min d k + j, h⟩ : Fin n)
    else (0 : MvPolynomial (Fin n) ℝ)

/-- The member of the explicit family, viewed as a real function on the slice. -/
noncomputable def FIfun (d k n ℓ : ℕ) : Slice n k → ℝ :=
  fun S => evalSlice (FIpoly d k n ℓ) S

/-- **Filmus–Ihringer, positive direction.**

For every `d ≥ 1` there is a bound `M = m(d)` (existentially quantified here, after
fixing `d`) such that: whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d`
function on the slice `binom([n],k)` is an `M`-junta. -/
theorem boolean_degree_d_is_junta :
    ∀ d : ℕ, 1 ≤ d → ∃ M : ℕ,
      ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta M f := by
  sorry

/-- **Filmus–Ihringer, sharpness (pure existential form).**

If `1 ≤ k < 2d` then no junta bound holds: for every `m` there is some `n ≥ 2k`
and a Boolean degree-`d` function on `binom([n],k)` that is not an `m`-junta. -/
theorem boolean_degree_d_not_junta :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
      ∃ n : ℕ, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-- **Filmus–Ihringer, sharpness with the explicit witnessing family.**

If `1 ≤ k < 2d`, then for every `m` one can choose a number `ℓ` of blocks and an
ambient size `n` (with `n ≥ 2·ℓ·e` and `n ≥ 2k`, where `e = min d k`) such that the
corresponding member `FIfun d k n ℓ` of the family
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` is a Boolean function of degree `≤ d` on
`binom([n],k)` that is not an `m`-junta.  (Concretely one takes `ℓ` with `ℓ·e > m`,
so that the family member genuinely depends on more than `m` coordinates; this is
the sense in which the members "are not `ℓe`-juntas".) -/
theorem boolean_degree_d_not_junta_explicit :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
      ∃ ℓ n : ℕ, 2 * (ℓ * min d k) ≤ n ∧ 2 * k ≤ n ∧
        IsBoolean (FIfun d k n ℓ) ∧
        HasDegreeLE d (FIfun d k n ℓ) ∧
        ¬ IsJunta m (FIfun d k n ℓ) := by
  sorry

end FilmusIhringer
