import Mathlib

/-!
# Filmus–Ihringer junta threshold on the slice (statement only)

Formalization of the *statement* of:

  Yuval Filmus, "Junta threshold for low degree Boolean functions on the slice",
  Electron. J. Combin. 30(1) (2023), #P1.55  (arXiv:2203.04760), **Theorem 1.1**,

which sharpens

  Yuval Filmus, Ferdinand Ihringer, "Boolean constant degree functions on the slice
  are juntas", Discrete Math. 342(12) (2019), 111614.

Every declared theorem ends in `:= by sorry`; nothing is proved here.
-/

open Finset

namespace FilmusIhringer

/-- A point of the slice `binom([n], k)`: a `k`-element subset of `Fin n`
(equivalently, a `0/1` vector of Hamming weight `k`). -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` indicator vector of a slice point, used as the point at which polynomials
in the variables `x₁, …, xₙ` are evaluated. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function on the slice is **Boolean** if it takes only the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has **degree ≤ d** on the slice: it agrees, on every point of the slice, with the
evaluation at the indicator vector of some real polynomial of total degree `≤ d`.  (The
polynomial is not required to be multilinear or harmonic; on the slice this is no loss of
generality, cf. Filmus–Ihringer, "the minimum degree of a real polynomial … which agrees
with the function on all points of the slice".) -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S.1) p

/-- `f` is an **m-junta**: there is a set `J` of at most `m` coordinates such that the value
`f S` depends only on `S ∩ J`.  (Equivalent, on the slice, to the existence of
`g : {0,1}^J → ℝ` with `f x = g (x|_J)`.) -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Filmus–Ihringer junta threshold (Theorem 1.1).**

Let `d ≥ 1`.  There is a constant `m(d)` such that:

* (threshold direction)  if `k ≥ 2d` then for every `n ≥ 2k`, every Boolean degree-`d`
  function on `binom([n], k)` is an `m(d)`-junta;

* (sharpness direction)  if `1 ≤ k < 2d` then for every `m` there exist `n ≥ 2k` and a
  Boolean degree-`d` function on `binom([n], k)` that is not an `m`-junta.

Encoding choice: **both directions**, stated together, with `m(d)` an existential
`∃ m : ℕ` scoping over the threshold direction only (matching "there exists a constant
`m(d)`" in the paper). -/
theorem junta_threshold (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ,
      (∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f m) ∧
      (∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ M : ℕ,
        ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
          IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f M) := by
  sorry

/-- The `i`-th block of `e` consecutive coordinates of `Fin n`: those `x : Fin n` with
`i·e ≤ x < i·e + e`.  For `i < ℓ` and `ℓ·e ≤ n` this block has exactly `e` elements and
distinct blocks are disjoint; this realizes the coordinate set `{(i-1)e+1, …, ie}` of the
paper (0-indexed here). -/
def block (n e i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n => i * e ≤ (x : ℕ) ∧ (x : ℕ) < i * e + e)

/-- The witnessing polynomial `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`, i.e. a sum of `ℓ`
degree-`e` monomials, one per block.  (This is the family in Theorem 1.1 of
arXiv:2203.04760; see the note file for the exact wording.) -/
noncomputable def familyPoly (n e ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ i ∈ Finset.range ℓ, ∏ x ∈ block n e i, MvPolynomial.X x

/-- **Explicit witnessing family for the sharpness direction.**

Let `1 ≤ k < 2d`, `ℓ ≥ 1`, and `e = min d k`.  For every `n ≥ 2ℓe`, the function on
`binom([n], k)` obtained by evaluating `familyPoly n e ℓ` at the indicator vector is
Boolean, has degree `≤ d`, and is **not an `(ℓe − 1)`-junta**.

Note on the last clause: the paper's introduction writes "these functions are not
`ℓe`-juntas", but the function depends on exactly the first `ℓe` coordinates, so it *is*
an `ℓe`-junta; the sharp statement, proved through the paper's Lemma 2.2 and the §3
converse construction, is that it is not an `(ℓe − 1)`-junta.  That is what is formalized. -/
theorem junta_threshold_witness
    (d k ℓ e : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hk2d : k < 2 * d) (hℓ : 1 ≤ ℓ)
    (he : e = min d k) (n : ℕ) (hn : 2 * ℓ * e ≤ n) :
    IsBoolean
        (fun S : Slice n k => MvPolynomial.eval (indicator S.1) (familyPoly n e ℓ)) ∧
      HasDegreeLE
        (fun S : Slice n k => MvPolynomial.eval (indicator S.1) (familyPoly n e ℓ)) d ∧
      ¬ IsJunta
        (fun S : Slice n k => MvPolynomial.eval (indicator S.1) (familyPoly n e ℓ))
        (ℓ * e - 1) := by
  sorry

end FilmusIhringer
