/-
Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas.

Statement-only formalization (every theorem ends in `:= by sorry`).

We formalize:
  * `slice_degree_junta`        — the positive direction (k ≥ 2d ⇒ m(d)-junta),
                                   with `m(d)` an existential inside the statement;
  * `slice_degree_not_junta`    — the negative / sharpness direction (1 ≤ k < 2d),
                                   stated as pure existence;
  * `blockProd_witness`         — the explicit witnessing family
                                   ∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j}), e = min d k,
                                   pinned to ℓ = k (see the accompanying note).

Encoding choices (see agent_029.md for discussion):
  * The k-slice of [n] is modelled by `S : Finset (Fin n)` together with a side
    hypothesis `S.card = k`.  Boolean functions on the slice are `ℝ`-valued
    functions constrained to `{0,1}` on sets of size `k`.
  * "degree ≤ d on the slice" = agreement, on all sets of size `k`, with the
    evaluation of some `p : MvPolynomial (Fin n) ℝ` with `p.totalDegree ≤ d`
    at the 0/1 indicator vector.
  * "m-junta on the slice" = existence of `J : Finset (Fin n)` with `J.card ≤ m`
    such that the value depends only on `S ∩ J`.
-/
import Mathlib

open Finset

namespace FilmusIhringer

variable {n : ℕ}

/-- A real-valued function on subsets of `Fin n` is *Boolean on the `k`-slice* if it takes
values in `{0, 1}` on every subset of size `k`. -/
def IsBoolOn (f : Finset (Fin n) → ℝ) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → f S = 0 ∨ f S = 1

/-- `f` has *slice-degree `≤ d`* (on the `k`-slice) if it agrees, on every subset of size
`k`, with the evaluation of some real multilinear-representable polynomial of total degree
`≤ d` at the `0/1` indicator vector of the subset.  (Multilinearity is automatic up to
equivalence, since evaluation is only at `0/1` points; we phrase the condition with
`totalDegree` alone.) -/
def HasSliceDegreeLE (f : Finset (Fin n) → ℝ) (d k : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧
    ∀ S : Finset (Fin n), S.card = k →
      f S = MvPolynomial.eval (fun i => if i ∈ S then (1 : ℝ) else 0) p

/-- `f` is an *`m`-junta on the `k`-slice* if there is a set `J` of at most `m` coordinates
such that the value of `f` on any subset of size `k` depends only on its intersection with
`J`. -/
def IsJuntaOn (m : ℕ) (f : Finset (Fin n) → ℝ) (k : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Finset (Fin n), S.card = k → T.card = k →
      S ∩ J = T ∩ J → f S = f T

/-! ### Positive direction -/

/-- **Filmus–Ihringer, positive direction.**  For every `d ≥ 1` there is a constant `m(d)`
such that: whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean slice-degree-`d` function on
`binom([n], k)` is an `m(d)`-junta.  Here `m(d)` is packaged as an existential. -/
theorem slice_degree_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Finset (Fin n) → ℝ,
        IsBoolOn f k → HasSliceDegreeLE f d k → IsJuntaOn m f k := by
  sorry

/-! ### Negative direction (sharpness) -/

/-- **Filmus–Ihringer, sharpness.**  If `1 ≤ k < 2d` then the junta bound fails: for every
`m` there are `n ≥ 2k` and a Boolean slice-degree-`d` function on `binom([n], k)` that is
not an `m`-junta. -/
theorem slice_degree_not_junta (d : ℕ) (hd : 1 ≤ d)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Finset (Fin n) → ℝ,
      IsBoolOn f k ∧ HasSliceDegreeLE f d k ∧ ¬ IsJuntaOn m f k := by
  sorry

/-! ### The explicit witnessing family -/

/-- `blockProd n e ℓ S = ∏_{i=0}^{ℓ-1} ( Σ_{j=0}^{e-1} x_{i*e+j} ) (S)`, where
`x_t (S) = 1` if `t ∈ S` and `0` otherwise.  Equivalently, the product over `ℓ` consecutive
disjoint blocks of `e` coordinates of the number of elements of `S` lying in that block.
This is the family `∏_{i=1}^{ℓ} (Σ_{j=1}^{e} x_{(i-1)e+j})` from the theorem statement,
written with `0`-based indexing. -/
def blockProd (n e ℓ : ℕ) (S : Finset (Fin n)) : ℝ :=
  ∏ i ∈ Finset.range ℓ,
    ((S.filter (fun t : Fin n => i * e ≤ (t : ℕ) ∧ (t : ℕ) < i * e + e)).card : ℝ)

/-- **Explicit witnesses for sharpness.**  Let `1 ≤ k < 2d` and `e = min d k`.  Taking
`ℓ = k` blocks of `e` coordinates, the function `blockProd n e ℓ` on the `k`-slice is
Boolean, has slice-degree `≤ d`, and — once `n ≥ 2·ℓ·e` — is not an `m`-junta for any
`m < ℓ·e`.  (Letting `k`… hence `ℓ·e = k·e`… grow with `n` defeats every fixed junta
bound, giving `slice_degree_not_junta`.)

The theorem-statement phrase "which for `n ≥ 2ℓe` are not `ℓe`-juntas" is read here as
"not `m`-juntas for every `m < ℓe`" (equivalently: genuinely depend on all `ℓe` block
coordinates). -/
theorem blockProd_witness
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (ℓ : ℕ) (hℓ : ℓ = k)
    (n m : ℕ) (hn : 2 * ℓ * min d k ≤ n) (hm : m < ℓ * min d k) :
    IsBoolOn (blockProd n (min d k) ℓ) k ∧
    HasSliceDegreeLE (blockProd n (min d k) ℓ) d k ∧
    ¬ IsJuntaOn m (blockProd n (min d k) ℓ) k := by
  sorry

end FilmusIhringer
