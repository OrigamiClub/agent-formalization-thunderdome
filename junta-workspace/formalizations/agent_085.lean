import Mathlib

open scoped BigOperators
open MvPolynomial

namespace FilmusIhringer

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization. Every theorem ends in `:= by sorry`; nothing is proved.

Encoding choices (see the accompanying `.md` note for rationale):

* The slice `binom([n],k) = { S ⊆ {1,…,n} : |S| = k }` is `Slice n k`, the subtype of
  `Finset (Fin n)` consisting of the `k`-element subsets.
* A "Boolean function on the slice" is a real-valued `f : Slice n k → ℝ` all of whose
  values lie in `{0,1}` (`IsBoolean`).
* "Degree ≤ d" (`HasSliceDegreeLE`) means: `f` agrees on the *whole* slice with the
  evaluation of some multilinear polynomial in `MvPolynomial (Fin n) ℝ` of
  `totalDegree ≤ d` at the `0/1` characteristic vector of the set.
* "`m`-junta" (`IsJunta`) means: there is a coordinate set `J` with `|J| ≤ m` such that
  `f S` depends only on `S ∩ J`.
* The constant `m(d)` is an existential (`∃ m : ℕ`) *inside* the statement, quantified
  before `k` and `n`, so it depends on `d` only.
* Both directions are stated, as a conjunction.  An explicit-witness theorem
  (`filmus_ihringer_witness`) transcribes the product family from the problem statement.
-/

/-- The slice `binom([n],k)` = `{ S ⊆ {1,…,n} : |S| = k }`, as the `k`-element subsets
of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `0/1` characteristic vector of a subset, i.e. the point at which real
polynomials are evaluated. -/
def charVec {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real function on the slice is *Boolean* if it only takes the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `p` is *multilinear*: in every monomial of its support, each variable occurs with
exponent at most `1`. -/
def IsMultilinearPoly {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ c ∈ p.support, ∀ i, c i ≤ 1

/-- `f` has *degree ≤ d* on the slice `binom([n],k)`: it agrees, on the whole slice,
with a multilinear real polynomial of total degree `≤ d`, evaluated at the `0/1`
characteristic vector of the set. -/
def HasSliceDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    IsMultilinearPoly p ∧ p.totalDegree ≤ d ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (charVec S.1) p

/-- A Boolean degree-`d` function on the slice. -/
def IsBooleanSliceDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  IsBoolean f ∧ HasSliceDegreeLE d f

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that the
value of `f` on `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Filmus–Ihringer junta theorem for Boolean constant-degree functions on the slice.**

Let `d ≥ 1`.

* (Forward) There is a bound `m`, depending on `d` only, such that whenever `k ≥ 2d`
  and `n ≥ 2k`, every Boolean degree-`d` function on `binom([n],k)` is an `m`-junta.

* (Converse) Whenever `1 ≤ k < 2d`, there is no uniform junta bound: for every `m`
  there are some `n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is
  not an `m`-junta.

Statement only. -/
theorem filmus_ihringer (d : ℕ) (hd : 1 ≤ d) :
    (∃ m : ℕ, ∀ k n : ℕ, 2 * d ≤ k → 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBooleanSliceDegreeLE d f → IsJunta m f)
    ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
        ∃ n : ℕ, ∃ f : Slice n k → ℝ,
          2 * k ≤ n ∧ IsBooleanSliceDegreeLE d f ∧ ¬ IsJunta m f) := by
  sorry

/-- The explicit Filmus–Ihringer witness polynomial
`∏_{i=1}^{ℓ} ( Σ_{j=1}^{e} x_{emb i j} )`, where the blocks `emb i ·` are (via
injectivity of `emb`) pairwise disjoint `e`-element sets of coordinates. -/
noncomputable def witnessPoly {n : ℕ} (e ℓ : ℕ) (emb : Fin ℓ → Fin e → Fin n) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i : Fin ℓ, ∑ j : Fin e, MvPolynomial.X (emb i j)

/-- **Explicit witnesses for the converse direction.**

Fix `1 ≤ k < 2d` and set `e = min d k`.  Given `ℓ` pairwise-disjoint blocks of `e`
coordinates inside `Fin n` (encoded by an injective `emb`, with `n ≥ 2ℓe`), the
function on `binom([n],k)` obtained by evaluating `witnessPoly e ℓ emb` at the `0/1`
characteristic vector is a Boolean degree-`d` function that is not an `ℓ·e`-junta.
Letting `ℓ → ∞` yields the non-junta family of the theorem.

Statement only. -/
theorem filmus_ihringer_witness
    (d k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (e : ℕ) (he : e = min d k)
    (ℓ n : ℕ)
    (emb : Fin ℓ → Fin e → Fin n)
    (hemb : Function.Injective fun p : Fin ℓ × Fin e => emb p.1 p.2)
    (hn : 2 * (ℓ * e) ≤ n) :
    ∃ f : Slice n k → ℝ,
      (∀ S : Slice n k, f S = MvPolynomial.eval (charVec S.1) (witnessPoly e ℓ emb)) ∧
      IsBooleanSliceDegreeLE d f ∧
      ¬ IsJunta (ℓ * e) f := by
  sorry

end FilmusIhringer
