import Mathlib

/-!
# Filmus–Ihringer junta threshold for Boolean degree-`d` functions on the slice

Statement-only formalization (agent 009).  Every theorem ends in `:= by sorry`;
nothing is proved.

Reference: Y. Filmus, F. Ihringer (with N. Lindzey), "Boolean constant-degree
functions on the slice are juntas" / "Junta threshold for low degree Boolean
functions on the slice".
-/

open scoped BigOperators

namespace FilmusIhringer

/-- The slice `binom([n], k)`, encoded as the subtype of `Finset (Fin n)` of
subsets of cardinality exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-valued indicator vector of `S` as a point of `ℝ^n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real-valued function is *Boolean* if it only takes the values `0` and `1`. -/
def IsBooleanValued {α : Type*} (f : α → ℝ) : Prop :=
  ∀ x, f x = 0 ∨ f x = 1

/-- `f` has *degree `≤ d`* on the slice `binom([n],k)` if it agrees, at every
slice point `S`, with the evaluation at the corresponding `{0,1}` indicator
vector of some real polynomial `p` of total degree `≤ d`.

(On `{0,1}` inputs a polynomial may be replaced by its multilinearization
without increasing the total degree, so requiring `p` multilinear would give an
equivalent notion; it is omitted here.) -/
def DegreeLE (n k d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
      ∀ S : Slice n k,
        f S = MvPolynomial.eval (indicator (S : Finset (Fin n))) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such
that the value of `f` on a slice point `S` depends only on `S ∩ J`. -/
def IsJunta (n k m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k,
      (S : Finset (Fin n)) ∩ J = (T : Finset (Fin n)) ∩ J → f S = f T

/-- **Filmus–Ihringer junta threshold (both directions).**

Fix `d ≥ 1`.

* *Positive direction.* There is a constant `m = m(d)` (existentially quantified
  at the head of the statement) such that whenever `k ≥ 2d` and `n ≥ 2k`, every
  Boolean degree-`d` function on the slice `binom([n],k)` is an `m`-junta.

* *Negative direction.* Whenever `1 ≤ k < 2d`, for every `m` there exist `n ≥ 2k`
  and a Boolean degree-`d` function on `binom([n],k)` that is **not** an
  `m`-junta.  (This captures the tightness of the threshold `k = 2d`: the
  witnessing functions require unboundedly many relevant coordinates.) -/
theorem junta_threshold (d : ℕ) (hd : 1 ≤ d) :
    (∃ m : ℕ,
      ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ,
          IsBooleanValued f → DegreeLE n k d f → IsJunta n k m f)
    ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
      ∃ n : ℕ, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ,
          IsBooleanValued f ∧ DegreeLE n k d f ∧ ¬ IsJunta n k m f) := by
  sorry

end FilmusIhringer
