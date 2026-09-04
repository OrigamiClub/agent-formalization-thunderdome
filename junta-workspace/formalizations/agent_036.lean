import Mathlib

/-!
# Agent 036 — Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.

Encoding summary (see `agent_036.md` for the reasoning):
* the slice `binom([n],k)` is `{S : Finset (Fin n) // S.card = k}`;
* Boolean codomain: real-valued functions constrained to `{0,1}` (`IsBooleanFun`);
* "degree ≤ d": agreement on the slice with the indicator-vector evaluation of a
  multilinear `MvPolynomial (Fin n) ℝ` of `totalDegree ≤ d`;
* "m-junta": a coordinate set `J` with `J.card ≤ m` on which the value depends only
  through `S ∩ J`;
* `m(d)` is an existential `m : ℕ → ℕ` at the head of the forward statement;
* both directions are stated, plus the explicit witnessing family.
-/

open Finset

namespace Agent036

/-- The slice `binom([n],k)`: the `k`-element subsets of `Fin n`, encoded as a subtype
of `Finset (Fin n)`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-valued indicator (hypercube point) of a subset of `Fin n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real function on the slice is **Boolean** if it takes only the values `0` and `1`. -/
def IsBooleanFun {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- A monomial (a `Finsupp` of exponents) is **multilinear** if every exponent is `≤ 1`. -/
def MonoMultilinear {n : ℕ} (m : Fin n →₀ ℕ) : Prop :=
  ∀ i, m i ≤ 1

/-- `f` has **degree at most `d`** on the slice `binom([n],k)` if it agrees, on every
`k`-set `S`, with the evaluation at the indicator vector of `S` of some multilinear real
polynomial of total degree at most `d`. -/
def HasSliceDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ m ∈ p.support, MonoMultilinear m) ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S.1) p

/-- `f` is an **`m`-junta** if there is a set `J` of at most `m` coordinates such that the
value of `f` at a `k`-set `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-!
## Main theorem (both directions)
-/

/-- **Filmus–Ihringer dichotomy at `k = 2d`.**

*Forward:* there is a single bound `m(d)` such that whenever `k ≥ 2d` (and `n ≥ 2k`),
every Boolean degree-`d` function on `binom([n],k)` is an `m(d)`-junta.

*Converse:* whenever `1 ≤ k < 2d`, there is no such bound: for every `m` some Boolean
degree-`d` function on some slice `binom([n],k)` fails to be an `m`-junta. -/
theorem filmus_ihringer :
    (∃ m : ℕ → ℕ,
      ∀ d : ℕ, 1 ≤ d →
      ∀ k : ℕ, 2 * d ≤ k →
      ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ,
        IsBooleanFun f → HasSliceDegreeLE d f → IsJunta (m d) f)
    ∧
    (∀ d : ℕ, 1 ≤ d →
     ∀ k : ℕ, 1 ≤ k → k < 2 * d →
     ∀ m : ℕ,
       ∃ n : ℕ, 2 * k ≤ n ∧
       ∃ f : Slice n k → ℝ,
         IsBooleanFun f ∧ HasSliceDegreeLE d f ∧ ¬ IsJunta m f) := by
  sorry

/-!
## The explicit witnessing family

With `e = min d k`, block `i` (for `i = 0, …, ℓ-1`) is the coordinate set
`{i*e, i*e+1, …, i*e+e-1}`.  The witness is

  `F(S) = ∏_{i=0}^{ℓ-1} ( Σ_{j=0}^{e-1} x_{i*e+j} )`

evaluated at the indicator vector of `S`; equivalently, the product over blocks of the
number of elements of `S` lying in that block.
-/

/-- The witnessing family `∏_{i<ℓ} (Σ_{j<e} x_{i*e+j})` with `e = min d k`, written
directly as a function on the slice (product over blocks of `|S ∩ block i|`). -/
def familyFun (n k d ℓ : ℕ) : Slice n k → ℝ :=
  fun S =>
    ∏ i ∈ Finset.range ℓ,
      ((S.1.filter
        (fun x : Fin n =>
          (x : ℕ) ∈ Finset.Ico (i * min d k) (i * min d k + min d k))).card : ℝ)

/-- The family members are Boolean degree-`d` functions on `binom([n],k)` which, once
`n ≥ 2ℓe` (`e = min d k`), are not `ℓe`-juntas.  Choosing `ℓ` with `ℓ·e > m` then yields
the converse direction of `filmus_ihringer`. -/
theorem filmus_ihringer_witness
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hk2 : k < 2 * d)
    (ℓ n : ℕ) (hn : 2 * (ℓ * min d k) ≤ n) :
    IsBooleanFun (familyFun n k d ℓ)
    ∧ HasSliceDegreeLE d (familyFun n k d ℓ)
    ∧ ¬ IsJunta (ℓ * min d k) (familyFun n k d ℓ) := by
  sorry

end Agent036
