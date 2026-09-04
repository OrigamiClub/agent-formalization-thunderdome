import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (every theorem ends in `:= by sorry`).

We formalize:
* the forward direction (`k ≥ 2d` ⟹ constant-size junta), with `m(d)` an existential
  `M : ℕ` inside the statement;
* the converse direction (`1 ≤ k < 2d` ⟹ non-junta degree-`d` Boolean functions exist);
* the explicit witnessing family
  `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k`.

See `agent_092.md` for encoding decisions and caveats.
-/

namespace FilmusIhringer

/-- The slice `binom([n],k)`: subsets of `Fin n` of cardinality exactly `k`.
An `abbrev` so that `.val`, `.property` and the anonymous constructor are available. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-valued indicator vector of a slice element, as an assignment `Fin n → ℝ`. -/
def indicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.val then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it only takes the values `0` and `1`. -/
def IsBooleanValued {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *(slice-)degree `≤ d`* if it agrees on the slice with the evaluation, at the
`{0,1}`-indicator vector, of a **multilinear** real polynomial of total degree `≤ d`.
Multilinearity is expressed as: every monomial exponent is squarefree (`m i ≤ 1`). -/
def HasSliceDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ m ∈ p.support, ∀ i : Fin n, m i ≤ 1) ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such that the
value of `f` on `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.val ∩ J = T.val ∩ J → f S = f T

/-- **Filmus–Ihringer (both directions).**

*Forward.* For every `d ≥ 1` there is a constant `M = m(d)` such that whenever `k ≥ 2d`
and `n ≥ 2k`, every Boolean degree-`d` function on the slice `binom([n],k)` is an `M`-junta.

*Converse.* For every `d ≥ 1` and every `k` with `1 ≤ k < 2d`, and for every `m`, there is
some `n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is **not** an
`m`-junta. -/
theorem filmus_ihringer :
    (∀ d : ℕ, 1 ≤ d → ∃ M : ℕ,
      ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBooleanValued f → HasSliceDegreeLE f d → IsJunta f M)
    ∧
    (∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
      ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
        IsBooleanValued f ∧ HasSliceDegreeLE f d ∧ ¬ IsJunta f m) := by
  sorry

/-- The explicit witnessing polynomial.

With `e := min d k`, coordinates `0, …, ℓ·e − 1` are split into `ℓ` consecutive blocks of
size `e`; the polynomial is the product over blocks of the sum of that block's variables:
`∏_{i=0}^{ℓ-1} (∑_{j=0}^{e-1} X_{i·e + j})`  (the paper's `∏_{i=1}^{ℓ} ∑_{j=1}^{e} x_{(i-1)e+j}`).

Indices are guarded by `i·e + j < n`; the intended use has `n` much larger than `ℓ·e`. -/
noncomputable def witnessPoly (n e ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then
        (MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) : MvPolynomial (Fin n) ℝ)
      else 0)

/-- The witnessing Boolean function on the slice: evaluate `witnessPoly` at the indicator. -/
noncomputable def witnessFun (n k e ℓ : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (indicator S) (witnessPoly n e ℓ)

/-- The explicit witnessing family realizes the converse direction.

For `1 ≤ k < 2d`, put `e := min d k`. Then for every `m` there are `ℓ, n` with
`m < ℓ·e` and `n ≥ max (2k) (2·ℓ·e)` such that `witnessFun n k e ℓ` is a Boolean,
(slice-)degree-`d` function on `binom([n],k)` that is not an `m`-junta.
(In particular it is not an `ℓ·e`-junta once `n ≥ 2·ℓ·e`.) -/
theorem witness_spec
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ ℓ n : ℕ,
      1 ≤ ℓ ∧ m < ℓ * min d k ∧ 2 * k ≤ n ∧ 2 * (ℓ * min d k) ≤ n ∧
      IsBooleanValued (witnessFun n k (min d k) ℓ) ∧
      HasSliceDegreeLE (witnessFun n k (min d k) ℓ) d ∧
      ¬ IsJunta (witnessFun n k (min d k) ℓ) m := by
  sorry

end FilmusIhringer
