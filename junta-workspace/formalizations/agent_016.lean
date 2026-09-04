/-
Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas.

Statement-only formalization.  Every `theorem` ends in `:= by sorry`; nothing is
proved.

We formalize:
  * the positive direction  (`filmus_ihringer_junta_upper`);
  * the converse direction   (`filmus_ihringer_junta_lower`);
  * the explicit witnessing family for the converse
    (`filmus_ihringer_junta_lower_witnesses`).
-/
import Mathlib

open Finset MvPolynomial

namespace FilmusIhringer

/-! ## Basic notions on the slice `binom([n], k) = {S ⊆ Fin n : |S| = k}`

We represent a set on the slice as a `Finset (Fin n)`, and carry the cardinality
constraint `S.card = k` as a hypothesis everywhere it is needed (rather than
bundling it into a subtype).  A "Boolean function on the slice" is a function
`f : Finset (Fin n) → ℝ` whose values we only constrain on `k`-element sets. -/

/-- Indicator vector in `ℝ^n` of a set of coordinates `S ⊆ Fin n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- `f` is *Boolean on the `k`-slice*: it takes values in `{0, 1}` on every
`k`-element set. -/
def IsBooleanOnSlice (n k : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d` on the `k`-slice*: on every `k`-element set it agrees
with the evaluation, at the indicator vector, of a multilinear real polynomial
of total degree `≤ d`.  Multilinearity is encoded as `degreeOf i ≤ 1` for every
variable `i` (on `{0,1}`-points this is without loss of generality, and it
matches the phrasing "multilinear real polynomial" in the theorem). -/
def IsDegreeLE (n k d : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ (∀ i, p.degreeOf i ≤ 1) ∧
      ∀ S : Finset (Fin n), S.card = k → f S = MvPolynomial.eval (indicator S) p

/-- `f` is an *`m`-junta on the `k`-slice*: there is a set `J` of at most `m`
coordinates such that `f S` depends only on `S ∩ J` (for `S` on the slice). -/
def IsJunta (n k m : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Finset (Fin n),
      S.card = k → T.card = k → S ∩ J = T ∩ J → f S = f T

/-! ## The explicit lower-bound family

`e = min d k`.  Partition an initial segment of the coordinates into consecutive
blocks `B_i = {i*e, …, i*e + e - 1}` of size `e`.  The witness is the function

  `S ↦ #{ i < ℓ : B_i ⊆ S }`,

which is the evaluation at the indicator vector of the multilinear polynomial

  `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e + j}`     (total degree `e = min d k ≤ d`).

Because `k < 2d`, at most one block can be contained in a `k`-set (two disjoint
blocks would force `|S| ≥ 2e`, and `2e > k` whenever `e = d`, while `e = k`
forces `B_i = S`), so this sum is `{0,1}`-valued on the slice. -/

/-- The `i`-th block: the coordinates `{i*e, …, i*e + e - 1}` that lie in
`Fin n`. -/
def block (n e i : ℕ) : Finset (Fin n) :=
  univ.filter (fun x : Fin n => i * e ≤ (x : ℕ) ∧ (x : ℕ) < i * e + e)

/-- Witness function `S ↦ #{ i < ℓ : block e i ⊆ S }`, the evaluation at the
indicator vector of `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e + j}`. -/
def witness (n e ℓ : ℕ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ range ℓ, (if block n e i ⊆ S then (1 : ℝ) else 0)

/-! ## The theorem (Filmus–Ihringer) -/

/-- **Positive direction.**  For every `d ≥ 1` there is a bound `M = m(d)`
(depending only on `d`) such that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean
degree-`d` function on the slice `binom([n], k)` is an `M`-junta. -/
theorem filmus_ihringer_junta_upper (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Finset (Fin n) → ℝ,
        IsBooleanOnSlice n k f → IsDegreeLE n k d f → IsJunta n k M f := by
  sorry

/-- **Converse direction.**  If `1 ≤ k < 2d` then the junta size is unbounded:
for every `m` there are `n ≥ 2k` and a Boolean degree-`d` function on
`binom([n], k)` that is *not* an `m`-junta. -/
theorem filmus_ihringer_junta_lower (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk₀ : 1 ≤ k) (hk₁ : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Finset (Fin n) → ℝ,
      IsBooleanOnSlice n k f ∧ IsDegreeLE n k d f ∧ ¬ IsJunta n k m f := by
  sorry

/-- **Converse direction, explicit witnesses.**  With `e = min d k`, for every
`ℓ` and every `n` with `n ≥ 2k` and `n ≥ 2ℓe`, the function `witness n e ℓ`
(the evaluation of `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e + j}` at the indicator
vector) is a Boolean degree-`d` function on `binom([n], k)` that is not an
`m`-junta for any `m < ℓe`.  Taking `ℓ` with `ℓe > m` yields the previous
statement. -/
theorem filmus_ihringer_junta_lower_witnesses (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk₀ : 1 ≤ k) (hk₁ : k < 2 * d) (ℓ : ℕ) (n : ℕ)
    (hn₀ : 2 * k ≤ n) (hn₁ : 2 * ℓ * min d k ≤ n) :
    IsBooleanOnSlice n k (witness n (min d k) ℓ) ∧
    IsDegreeLE n k d (witness n (min d k) ℓ) ∧
    (∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta n k m (witness n (min d k) ℓ)) := by
  sorry

end FilmusIhringer
