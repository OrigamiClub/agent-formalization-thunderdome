import Mathlib

/-!
# Agent 067 — Filmus–Ihringer

"Boolean constant-degree functions on the slice are juntas."

Statement-only formalization. Every theorem ends in `:= by sorry`; nothing is proved.
-/

set_option autoImplicit false

namespace Agent067

open Finset

/-- The slice `binom([n], k)`: subsets of `Fin n` of cardinality exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The real `0/1` indicator vector of a subset of `Fin n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- A real-valued function on the slice is *Boolean* if every value is `0` or `1`. -/
def IsBooleanFn {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree at most `d`* on the slice: it agrees, at every slice point, with
the evaluation at the `0/1` indicator vector of some real polynomial of total degree
at most `d`.

On `{0,1}^n` this is equivalent to the existence of such a *multilinear* polynomial,
since multilinearization (replacing `xᵢ^a` by `xᵢ`) preserves values at `0/1` points
and does not raise total degree; the multilinearity clause is therefore omitted. -/
def HasSliceDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S.1) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that the
value of `f` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Forward direction (Filmus–Ihringer).**
For every `d ≥ 1` there is a bound `m = m(d)` (existentially quantified here,
depending only on `d`) such that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean
degree-`d` function on the slice `binom([n], k)` is an `m`-junta. -/
theorem agent_067_forward (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ (k n : ℕ), 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBooleanFn f → HasSliceDegreeLE f d → IsJunta f m := by
  sorry

/-- **Converse direction (Filmus–Ihringer).**
If `1 ≤ k < 2d` then the junta size is unbounded: for every `m` there exist `n ≥ 2k`
and a Boolean degree-`d` function on `binom([n], k)` that is not an `m`-junta. -/
theorem agent_067_converse (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ,
        IsBooleanFn f ∧ HasSliceDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- The explicit witnessing family.  With block size `e` and `ℓ` pairwise-disjoint
blocks `B₀, …, B_{ℓ-1}`, where `Bᵢ = {i·e, i·e+1, …, i·e+e-1} ⊆ Fin n`, this is the
polynomial `∑_{i<ℓ} ∏_{j<e} x_{i·e+j}` read off the `0/1` indicator of the slice
point: a sum of `ℓ` degree-`e` monomials.  On the slice it equals `𝟙[∃ i, Bᵢ ⊆ S]`.

Transcription note: the problem text writes the family as a *product of sums*
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})`.  Read literally that function is
identically `0` on `binom([n], k)` as soon as `ℓ > k` (a `k`-set cannot meet `ℓ`
disjoint nonempty blocks), so it cannot witness unbounded juntas.  The
*sum of products* used here is the mathematically correct Filmus–Ihringer witness
(degree `e = min d k ≤ d`, Boolean because `2e > k` forces at most one block
`⊆ S`, and depending on all `ℓe` block coordinates). -/
def familyFn (n k e ℓ : ℕ) (hn : 2 * ℓ * e ≤ n) : Slice n k → ℝ :=
  fun S => ∑ i : Fin ℓ, ∏ j : Fin e,
    indicator S.1 ⟨i.val * e + j.val, by
      have hi : i.val + 1 ≤ ℓ := i.isLt
      have hj : j.val < e := j.isLt
      have step : (i.val + 1) * e ≤ ℓ * e := mul_le_mul_right' hi e
      have eq : (i.val + 1) * e = i.val * e + e := by ring
      have link : 2 * ℓ * e = ℓ * e + ℓ * e := by ring
      omega⟩

/-- **Explicit witnesses for the converse (Filmus–Ihringer).**
For `1 ≤ k < 2d`, block size `e = min d k`, any number of blocks `ℓ`, and
`n ≥ 2ℓe` (with also `n ≥ 2k`), the function `familyFn` is Boolean, has degree
`≤ d` on the slice, and is not an `m`-junta for any `m < ℓe`.  (It *is* an
`ℓe`-junta; the problem's phrase "not `ℓe`-juntas" is rendered as this
strictly-below statement.)  Letting `ℓ → ∞` yields, for every `m`, a Boolean
degree-`d` function that is not an `m`-junta, re-proving `agent_067_converse`. -/
theorem agent_067_family
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (e : ℕ) (he : e = min d k)
    (ℓ n : ℕ) (hn : 2 * ℓ * e ≤ n) (hnk : 2 * k ≤ n) :
    IsBooleanFn (familyFn n k e ℓ hn) ∧
    HasSliceDegreeLE (familyFn n k e ℓ hn) d ∧
    (∀ m : ℕ, m < ℓ * e → ¬ IsJunta (familyFn n k e ℓ hn) m) := by
  sorry

end Agent067
