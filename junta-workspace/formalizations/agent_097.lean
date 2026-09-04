/-
Filmus–Ihringer junta threshold for low-degree Boolean functions on the slice.

Primary source for the exact statement being formalized:
  Yuval Filmus, "Junta threshold for low degree Boolean functions on the slice",
  arXiv:2203.04760, Theorem 1.1 (building on Filmus–Ihringer, Discrete Math. 2019).

Theorem 1.1 (Boolean case).  Let d ≥ 1.  There is a constant m(d) such that:
  * if k ≥ 2d then for every n ≥ 2k, every Boolean degree-d function on the slice
    C(n,k) is an m(d)-junta;
  * conversely, if 1 ≤ k < 2d then for every m there exist n ≥ 2k and a Boolean
    degree-d function on C(n,k) that is not an m-junta.
  The converse is witnessed by
        f(x) = Σ_{i=1}^{ℓ} Π_{j=1}^{e} x_{(i-1)e+j},      e = min(d,k),
  which for n ≥ 2ℓe is not an ℓe-junta.

This file states the theorem only.  Every theorem ends in `:= by sorry`.
-/

import Mathlib

open Finset MvPolynomial

namespace FilmusJuntaThreshold

/-- The slice `C(n,k)` = `\binom{[n]}{k}`, encoded as the subtype of `k`-element
subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector of a finite set, viewed as a point of the real
hypercube `Fin n → ℝ`.  Slice points are exactly the indicator vectors of
`k`-element sets. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- `f` is Boolean: it takes only the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has degree at most `d` on the slice: it agrees, at every point of the
slice, with the evaluation of some real polynomial of total degree at most `d`
(the polynomial need not be multilinear or harmonic).  This is the
"minimum degree of an agreeing polynomial" notion of degree on the slice. -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S.1) p

/-- `f` is an `m`-junta: there is a set `J` of at most `m` coordinates such that
the value of `f` depends only on the intersection of the input with `J`
(equivalently, `f` is invariant under permutations of the coordinates outside
`J`). -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Filmus–Ihringer junta threshold (Theorem 1.1).**
For each `d ≥ 1` there is a constant `m` (depending only on `d`) such that:
* (forward) if `2 * d ≤ k` then for every `n ≥ 2 * k`, every Boolean degree-`d`
  function on the slice `C(n,k)` is an `m`-junta;
* (converse) if `1 ≤ k < 2 * d` then for every `m'` there exist `n ≥ 2 * k` and a
  Boolean degree-`d` function on `C(n,k)` that is not an `m'`-junta.

`m(d)` is rendered as an existential `∃ m : ℕ` after `d` is fixed. -/
theorem filmus_junta_threshold :
    ∀ d : ℕ, 1 ≤ d →
      (∃ m : ℕ,
        ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
          ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta m f)
      ∧
      (∀ k : ℕ, 1 ≤ k → k < 2 * d →
        ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
          ∃ f : Slice n k → ℝ,
            IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f) := by
  sorry

/-- The explicit non-junta witness polynomial

  `Σ_{i < ℓ} Π_{j < e} X_{i·e + j}`,   with `e = min d k`,

a sum of `ℓ` pairwise-disjoint degree-`e` monomials sitting on contiguous blocks
of `e` coordinates.  `finProdFinEquiv (i, j)` enumerates the pair `(i, j)` as the
index `i·e + j < ℓ·e`, and `Fin.castLE h` embeds it into `Fin n`. -/
noncomputable def witnessPoly (d k ℓ n : ℕ) (h : ℓ * min d k ≤ n) :
    MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin ℓ, ∏ j : Fin (min d k),
    MvPolynomial.X (Fin.castLE h (finProdFinEquiv (i, j)))

/-- **The explicit witnessing family for the converse.**
With `e = min d k` and `1 ≤ k < 2 * d`, for every number `ℓ` of blocks and every
`n ≥ 2 * ℓ * e` (and `n ≥ 2 * k`), the function computed on the slice `C(n,k)` by
`witnessPoly d k ℓ n` is Boolean, has degree at most `d`, and is not an `m`-junta
for any `m < ℓ * e`.  (Filmus, arXiv:2203.04760, Theorem 1.1: "not ℓe-juntas".)
Letting `ℓ → ∞` yields the converse part of `filmus_junta_threshold`. -/
theorem filmus_junta_threshold_witness
    (d k ℓ n : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hkd : k < 2 * d) (hℓ : 1 ≤ ℓ)
    (hn : 2 * (ℓ * min d k) ≤ n) (hnk : 2 * k ≤ n)
    (hle : ℓ * min d k ≤ n) :
    ∃ f : Slice n k → ℝ,
      (∀ S : Slice n k,
        f S = MvPolynomial.eval (indicator S.1) (witnessPoly d k ℓ n hle)) ∧
      IsBoolean f ∧
      HasDegreeLE d f ∧
      (∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta m f) := by
  sorry

end FilmusJuntaThreshold
