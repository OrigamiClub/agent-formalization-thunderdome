import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Agent 013 — statement-only formalization.  Every theorem ends in `:= by sorry`;
nothing is proved.

We formalize:

* `filmus_ihringer` — BOTH directions, for a fixed degree `d ≥ 1`:
  - forward: a single junta bound `M = m(d)` works for all `k ≥ 2d`, `n ≥ 2k`;
  - converse: for `1 ≤ k < 2d` there is no uniform junta bound.

* `filmus_ihringer_explicit` — the explicit witnessing family
  `∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` with `e = min d k`, asserted to be
  `{0,1}`-valued on the slice, of Boolean degree ≤ `d`, and not an `ℓe`-junta
  once `n ≥ 2ℓe`.
-/

open Finset MvPolynomial

namespace AgentO13

variable {n k : ℕ}

/-- The slice `binom([n], k)` : the `k`-element subsets of `Fin n`.
(`{1,…,n}` is modelled by `Fin n`.) -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-valued real indicator vector of a subset `S ⊆ Fin n`. -/
def indicator (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- A polynomial is multilinear when every monomial occurring in it is square-free,
i.e. each variable appears to exponent at most `1`. -/
def IsMultilinear (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ t ∈ p.support, ∀ i, t i ≤ 1

/-- `f : Slice n k → Bool` has **Boolean degree ≤ d** when it agrees, at every point of
the slice, with a multilinear real polynomial of total degree ≤ `d`, evaluated at the
indicator vector of the point. -/
def BooleanDegreeLE (d : ℕ) (f : Slice n k → Bool) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    IsMultilinear p ∧ p.totalDegree ≤ d ∧
      ∀ S : Slice n k,
        MvPolynomial.eval (indicator (S : Finset (Fin n))) p = (if f S then (1 : ℝ) else 0)

/-- `f` is an **`m`-junta** when there is a set `J` of at most `m` coordinates such that
the value of `f` on `S` depends only on `S ∩ J`. -/
def IsJunta (m : ℕ) (f : Slice n k → Bool) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k,
      (S : Finset (Fin n)) ∩ J = (T : Finset (Fin n)) ∩ J → f S = f T

/-- **Filmus–Ihringer theorem** (both directions), stated for a fixed degree `d ≥ 1`.

* Forward: there is one junta bound `M = m(d)` (existentially quantified) such that
  whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on `binom([n],k)`
  is an `M`-junta.
* Converse: when `1 ≤ k < 2d`, no junta bound is uniform — for every `m` there are
  `n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is not an `m`-junta. -/
theorem filmus_ihringer (d : ℕ) (hd : 1 ≤ d) :
    (∃ M : ℕ, ∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
        ∀ f : Slice n k → Bool, BooleanDegreeLE d f → IsJunta M f)
    ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
        ∃ n : ℕ, 2 * k ≤ n ∧
          ∃ f : Slice n k → Bool, BooleanDegreeLE d f ∧ ¬ IsJunta m f) := by
  sorry

/-- The `i`-th block (0-indexed) of size `e`: the sum of the coordinate variables `x_c`
with `i·e ≤ c < (i+1)·e`.  This is `∑_{j=1}^{e} x_{(i-1)e+j}` in 1-indexed notation. -/
def blockSum (n e i : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ c ∈ univ.filter (fun c : Fin n => i * e ≤ (c : ℕ) ∧ (c : ℕ) < (i + 1) * e),
    MvPolynomial.X c

/-- The explicit Filmus–Ihringer lower-bound family
`∏_{i=1}^{ℓ} (∑_{j=1}^{e} x_{(i-1)e+j})` (0-indexed as `∏_{i=0}^{ℓ-1} (blockSum n e i)`).
The blocks use disjoint coordinate ranges, so this polynomial is already multilinear of
total degree `ℓ·e`; the content of the theorem is that on the slice it nevertheless
agrees with a multilinear polynomial of total degree ≤ `d`. -/
def fiFamily (n ℓ e : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ range ℓ, blockSum n e i

/-- **Explicit witnesses for the converse.**

With `e = min d k` and `1 ≤ k < 2d`: for every `ℓ` and every `n ≥ 2ℓe`, the function `g`
computed on the slice by `fiFamily n ℓ e` (via `g S = 1 ↔ eval (indicator S) = 1`) is
`{0,1}`-valued, has Boolean degree ≤ `d`, and is **not** an `ℓe`-junta.  Letting `ℓ → ∞`
defeats every fixed junta bound `m`. -/
theorem filmus_ihringer_explicit
    (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hkd : k < 2 * d)
    (e : ℕ) (he : e = min d k)
    (ℓ n : ℕ) (hn : 2 * ℓ * e ≤ n)
    (g : Slice n k → Bool)
    (hg : ∀ S : Slice n k,
        g S =
          decide (MvPolynomial.eval (indicator (S : Finset (Fin n))) (fiFamily n ℓ e) = 1)) :
    (∀ S : Slice n k,
        MvPolynomial.eval (indicator (S : Finset (Fin n))) (fiFamily n ℓ e) = 0 ∨
        MvPolynomial.eval (indicator (S : Finset (Fin n))) (fiFamily n ℓ e) = 1)
      ∧ BooleanDegreeLE d g
      ∧ ¬ IsJunta (ℓ * e) g := by
  sorry

end AgentO13
