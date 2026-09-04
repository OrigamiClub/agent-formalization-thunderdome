import Mathlib

open scoped BigOperators

namespace Agent065

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`; nothing is proved.
-/

/-- The slice `binom([n], k)`: subsets of `Fin n` of cardinality exactly `k`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- A real-valued function on the slice is *Boolean* if it only takes the values `0` and `1`. -/
def IsBooleanOn (n k : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree ≤ d* on the slice `binom([n],k)` if it agrees, at every point of the
slice, with the evaluation at the `0/1` indicator vector of `S` of some **multilinear**
real polynomial of total degree `≤ d`.

Multilinearity is expressed directly: every monomial in the support uses each variable
with exponent at most `1`.  (On `0/1` inputs one can always multilinearize without raising
the total degree, so on the slice this coincides with dropping the multilinearity clause.) -/
def IsSliceDegreeLE (n k d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ u ∈ p.support, ∀ i, u i ≤ 1) ∧
    ∀ S : Slice n k,
      f S = MvPolynomial.eval (fun i => if i ∈ S.1 then (1 : ℝ) else 0) p

/-- `f` is an *m-junta* if there is a set `J` of at most `m` coordinates such that the
value of `f` at `S` depends only on `S ∩ J`. -/
def IsJunta (n k m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- The explicit Filmus–Ihringer counterexample family, as a function on the slice.

Given `ℓ` pairwise-disjoint blocks of `e` coordinates each — block `i` being
`{i*e, i*e+1, …, i*e+e-1}`, injected into `Fin n` via the bound `hidx` — this is
`∑_{i=0}^{ℓ-1} ∏_{j=0}^{e-1} x_{i*e+j}` evaluated at the `0/1` indicator of `S`, i.e. the
number of blocks entirely contained in `S`.

NOTE.  The source text writes this family as a *product of sums*,
`∏_{i} (∑_{j} x_{(i-1)e+j})`.  Taken literally that polynomial is identically `0` on the
slice as soon as `ℓ > k` (some block is disjoint from `S`), hence a `0`-junta, so it
cannot be the intended witness.  The mathematically correct Filmus–Ihringer witness — the
one that is Boolean of degree `min d k` precisely because `k < 2d` forbids two disjoint
`(min d k)`-blocks inside a `k`-set, and that depends on all `ℓ·(min d k)` block
coordinates — is the *sum of products* used here.  See the accompanying note. -/
noncomputable def witnessFun (n k ℓ e : ℕ)
    (hidx : ∀ i, i < ℓ → ∀ j, j < e → i * e + j < n) :
    Slice n k → ℝ :=
  fun S => ∑ i : Fin ℓ, ∏ j : Fin e,
    (if (⟨(i : ℕ) * e + (j : ℕ), hidx (i : ℕ) i.isLt (j : ℕ) j.isLt⟩ : Fin n) ∈ S.1
      then (1 : ℝ) else 0)

/-- **Filmus–Ihringer (2019): Boolean constant-degree functions on the slice are juntas.**

Both directions, for a fixed degree bound `d ≥ 1`.

* Forward: there is a constant `m` (depending only on `d`) such that for every `k ≥ 2d`,
  every `n ≥ 2k`, and every Boolean degree-`≤ d` function on `binom([n],k)`, that function
  is an `m`-junta.

* Converse: for every `k` with `1 ≤ k < 2d` and every `m`, there is some `n ≥ 2k` and a
  Boolean degree-`≤ d` function on `binom([n],k)` that is **not** an `m`-junta.

Statement only. -/
theorem filmus_ihringer (d : ℕ) (hd : 1 ≤ d) :
    (∃ m : ℕ, ∀ k, 2 * d ≤ k → ∀ n, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ,
        IsBooleanOn n k f → IsSliceDegreeLE n k d f → IsJunta n k m f)
    ∧
    (∀ k, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
      ∃ n, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ,
          IsBooleanOn n k f ∧ IsSliceDegreeLE n k d f ∧ ¬ IsJunta n k m f) := by
  sorry

/-- The converse direction, made explicit through the witnessing family.

For `1 ≤ k < 2d` and any `m`, there are `n ≥ 2k` and a number of blocks `ℓ` such that the
function `∑_{i<ℓ} ∏_{j<e} x_{i*e+j}` with `e = min d k`, viewed on `binom([n],k)`, is
Boolean, has degree `≤ d`, and is not an `m`-junta.  (It depends on all `ℓ·e` block
coordinates; `ℓ` is taken large enough that `ℓ·e > m`.)

Statement only. -/
theorem filmus_ihringer_explicit_witness
    (d k : ℕ) (hd : 1 ≤ d) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) (m : ℕ) :
    ∃ (n ℓ : ℕ) (hidx : ∀ i, i < ℓ → ∀ j, j < min d k → i * min d k + j < n),
      2 * k ≤ n ∧
      IsBooleanOn n k (witnessFun n k ℓ (min d k) hidx) ∧
      IsSliceDegreeLE n k d (witnessFun n k ℓ (min d k) hidx) ∧
      ¬ IsJunta n k m (witnessFun n k ℓ (min d k) hidx) := by
  sorry

end Agent065
