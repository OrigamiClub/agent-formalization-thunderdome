import Mathlib

/-!
# Filmus–Ihringer junta threshold for Boolean degree-`d` functions on the slice

Formalization of the *statement* of:

Yuval Filmus, *Junta threshold for low degree Boolean functions on the slice*,
arXiv:2203.04760 (2022), **Theorem 1.1** — the sharp form of the
Filmus–Ihringer theorem "Boolean constant degree functions on the slice are
juntas" (Discrete Math. 342 (2019)).

Statement only: every `theorem` ends in `:= by sorry` and nothing is proved.
-/

open Finset

namespace FilmusJuntaThreshold

/-- A point of the slice `binom([n], k)`: a `k`-element subset of the `n`
coordinates.  We identify `x ∈ {0,1}^n` of Hamming weight `k` with its support
`S ⊆ {1, …, n}`, `|S| = k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The real indicator vector `(x₁, …, xₙ) ∈ {0,1}^n ⊆ ℝ^n` of a slice point. -/
def ind {n k : ℕ} (S : Slice n k) : Fin n → ℝ := fun i => if i ∈ S.1 then 1 else 0

/-- A real-valued function on the slice is **Boolean** if it is `{0,1}`-valued. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop := ∀ S, f S = 0 ∨ f S = 1

/-- `f` has **degree ≤ d** if it agrees, on every point of the slice, with the
evaluation at the indicator vector of some real polynomial of total degree `≤ d`.

This is the paper's alternative characterization: "the minimum degree of a real
polynomial (not necessarily multilinear or harmonic) which agrees with the
function on all points of the slice". -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ P : MvPolynomial (Fin n) ℝ,
    P.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = MvPolynomial.eval (ind S) P

/-- `f` is an **m-junta** if there is a set `J` of at most `m` coordinates such
that the value of `f` depends only on the intersection of the input with `J`
(equivalently `f x = g (x|_J)` for some `g`). -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Filmus (2022), Theorem 1.1.**

Let `d ≥ 1`.  There is a constant `m = m(d)` such that:

* **(threshold)** if `k ≥ 2d` then for every `n ≥ 2k`, every Boolean degree-`d`
  function on the slice `binom([n], k)` is an `m(d)`-junta;

* **(sharpness)** if `1 ≤ k < 2d` then for every `M` there are `n ≥ 2k` and a
  Boolean degree-`d` function on `binom([n], k)` that is **not** an `M`-junta.

Both directions are stated (as one theorem, mirroring the paper). Statement only. -/
theorem filmus_junta_threshold (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ,
      (∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
          ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f m)
      ∧
      (∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ M : ℕ,
          ∃ n : ℕ, 2 * k ≤ n ∧
            ∃ f : Slice n k → ℝ,
              IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f M) := by
  sorry

/-- The explicit non-junta witnesses of the sharpness part, evaluated at a slice
point `S`:
`∑_{i=0}^{ℓ-1} ∏_{j=0}^{e-1} x_{i·e + j}` — a sum of `ℓ` pairwise-disjoint
degree-`e` monomials on the coordinates `0, 1, …, ℓ·e − 1`, with `e = min d k`.

(The problem prompt writes this as a *product of sums*; the paper's family — and
the only form that is `{0,1}`-valued on the slice when `k < 2e` — is this
*sum of products*.  See the accompanying note.) -/
def witness (n k e ℓ : ℕ) (S : Slice n k) : ℝ :=
  ∑ i ∈ Finset.range ℓ, ∏ j ∈ Finset.range e,
    (if h : i * e + j < n then
        (if (⟨i * e + j, h⟩ : Fin n) ∈ S.1 then (1 : ℝ) else 0)
      else 0)

/-- The explicit witness family behind the sharpness part of
`filmus_junta_threshold`.

For `1 ≤ k < 2d`, put `e = min d k`.  For any block count `ℓ ≥ 1` and any slice
`binom([n], k)` with `n ≥ 2·ℓ·e`, the function `witness n k e ℓ` is Boolean, has
degree `≤ d`, and is not an `(ℓ·e − 1)`-junta.  Choosing `ℓ` with `ℓ·e − 1 ≥ M`
then yields, for every `M`, a Boolean degree-`d` function that is not an
`M`-junta.

(The paper's remark says "not `ℓ·e`-juntas"; since the function visibly depends
only on `ℓ·e` coordinates it *is* an `ℓ·e`-junta, and the sharp provable claim,
via the paper's Lemma 2.2, is "not an `(ℓ·e − 1)`-junta".)

Statement only. -/
theorem filmus_witness_family
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hk2 : k < 2 * d)
    (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) (hn : 2 * (ℓ * min d k) ≤ n) :
    IsBoolean (witness n k (min d k) ℓ)
      ∧ HasDegreeLE (witness n k (min d k) ℓ) d
      ∧ ¬ IsJunta (witness n k (min d k) ℓ) (ℓ * min d k - 1) := by
  sorry

end FilmusJuntaThreshold
