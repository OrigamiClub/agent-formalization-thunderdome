import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (every theorem ends in `:= by sorry`).

We formalize:
* the FORWARD direction  (`filmus_ihringer_forward`),
* the CONVERSE direction as a pure existence statement (`filmus_ihringer_converse`),
* the CONVERSE with the explicit witnessing family (`filmus_ihringer_witness`),
  transcribed literally from the source's phrasing.

See `agent_024.md` for the encoding decisions and caveats.
-/

namespace Agent024

/-- The slice `binom([n], k)` : subsets of `Fin n` of cardinality exactly `k`.
Encoded as a subtype of `Finset (Fin n)`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The real characteristic (indicator) vector of a subset `S ⊆ Fin n`. -/
noncomputable def charVec {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- A real-valued function on the slice is *Boolean* if it takes only the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`* on the slice if it agrees, at every point of the slice, with the
evaluation at the characteristic vector of some **multilinear** real polynomial of total
degree `≤ d`.  Multilinearity is encoded as: every variable occurs with exponent `≤ 1` in
every monomial of the support. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ mono ∈ p.support, ∀ i, mono i ≤ 1) ∧
    ∀ S : Slice n k, MvPolynomial.eval (charVec S.val) p = f S

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such that the value
of `f` at `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.val ∩ J = T.val ∩ J → f S = f T

/-- The explicit witnessing polynomial
`∏_{i=1}^{ℓ} ( ∑_{j=1}^{e} x_{(i-1)e+j} )`, written with 0-based indices as
`∏_{i < ℓ} ∑_{j < e} x_{i*e+j}`.  Indices that would fall outside `Fin n` contribute `0`
(they never occur once `n ≥ ℓ*e`). -/
noncomputable def witnessPoly (n ℓ e : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then MvPolynomial.X (⟨i * e + j, h⟩ : Fin n)
      else (0 : MvPolynomial (Fin n) ℝ))

/-- The witnessing function on the slice `binom([n], k)`: evaluate `witnessPoly` at the
characteristic vector. -/
noncomputable def witnessFun (n k ℓ e : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (charVec S.val) (witnessPoly n ℓ e)

/-- **Forward direction.**  For every `d ≥ 1` there is a constant `M = m(d)` such that:
whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on the slice
`binom([n], k)` is an `M`-junta.  (`m(d)` is an existential inside the statement.) -/
theorem filmus_ihringer_forward (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f M := by
  sorry

/-- **Converse direction (existence form).**  For every `d ≥ 1` and every `k` with
`1 ≤ k < 2d`, and every `m`, there is a slice `binom([n], k)` with `n ≥ 2k` carrying a
Boolean degree-`d` function that is **not** an `m`-junta. -/
theorem filmus_ihringer_converse (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
      IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- **Converse direction, explicit witnesses.**  With `e = min d k` and `1 ≤ k < 2d`:
for every `ℓ` and every `n ≥ 2ℓe`, the function `witnessFun n k ℓ e` is Boolean, has
degree `≤ d` on the slice, and is not an `ℓe`-junta.  (Literal transcription of the
source's phrasing; see `agent_024.md`.) -/
theorem filmus_ihringer_witness (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (e : ℕ) (he : e = min d k) (ℓ n : ℕ) (hn : 2 * ℓ * e ≤ n) :
    IsBoolean (witnessFun n k ℓ e) ∧
      HasDegreeLE (witnessFun n k ℓ e) d ∧
      ¬ IsJunta (witnessFun n k ℓ e) (ℓ * e) := by
  sorry

end Agent024
