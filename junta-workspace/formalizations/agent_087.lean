/-
Agent 087 — formalization of the *statement* of the Filmus–Ihringer theorem:
"Boolean constant-degree functions on the slice are juntas."

Statement only. Every theorem ends in `:= by sorry`. Nothing is proved.

We state BOTH directions plus the explicit witnessing family (three theorems).
See `agent_087.md` for encoding rationale and uncertainties.
-/
import Mathlib

open MvPolynomial

namespace Agent087

/-- The slice `binom([n],k)`: the `k`-element subsets of `Fin n`.
    Encoded as a subtype of `Finset (Fin n)`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The 0/1 indicator vector of a slice element, viewed as a real point of `Fin n → ℝ`.
    Used to evaluate real polynomials on the slice. -/
def sliceIndicator {n k : ℕ} (S : Slice n k) : Fin n → ℝ :=
  fun i => if i ∈ S.val then (1 : ℝ) else 0

/-- A real-valued function on the slice is *Boolean* if it only takes the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`*: it agrees on the whole slice with the evaluation, at the
    0/1 indicator vector, of some real polynomial of total degree `≤ d`.

    Requiring the polynomial to be multilinear would define the same class of functions,
    because `xᵢ^2 = xᵢ` at 0/1 points lets one reduce any polynomial to a multilinear one
    of no larger total degree; so we omit that constraint. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = MvPolynomial.eval (sliceIndicator S) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that the
    value of `f` at `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.val ∩ J = T.val ∩ J → f S = f T

/-!
### Forward direction (positive result)

For every `d ≥ 1` there is a constant `m` (depending only on `d`; here packaged as an
existential) such that: whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function
on `binom([n],k)` is an `m`-junta.
-/
theorem agent_087_slice_juntas_forward :
    ∀ d : ℕ, 1 ≤ d →
      ∃ m : ℕ,
        ∀ k : ℕ, 2 * d ≤ k →
          ∀ n : ℕ, 2 * k ≤ n →
            ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f m := by
  sorry

/-!
### Converse direction (tightness)

If `1 ≤ k < 2d`, then the junta bound fails completely: for every `m` there is some
`n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is not an `m`-junta.
-/
theorem agent_087_slice_juntas_converse :
    ∀ d : ℕ, 1 ≤ d →
      ∀ k : ℕ, 1 ≤ k → k < 2 * d →
        ∀ m : ℕ,
          ∃ n : ℕ, 2 * k ≤ n ∧
            ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-!
### Explicit witnessing family

With `e = min d k` and `ℓ` blocks, block `i` (for `i < ℓ`) is the set of coordinates
with index in `[i·e, i·e + e)`.  The real polynomial

  `∏_{i<ℓ} ( ∑_{j<e} x_{i·e+j} )`

is a product of `ℓ` disjoint block-sums.  The associated Boolean function on the slice is
its "is it nonzero" indicator, i.e. the AND over blocks of (OR over the block of `xⱼ`):
it is `1` exactly when `S` meets every block.  The theorem states this function is
Boolean, has degree `≤ d`, and (for `n ≥ 2ℓe`) essentially depends on all `ℓe` block
coordinates — it is not an `m`-junta for any `m < ℓe`.  Letting `ℓ → ∞` recovers the
converse direction.
-/

open Classical in
/-- The polynomial `∏_{i<ℓ} ∑_{j<e} x_{i·e+j}` over `Fin n` (out-of-range indices contribute `0`). -/
noncomputable def sliceWitnessPoly (n ℓ e : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then MvPolynomial.X (⟨i * e + j, h⟩ : Fin n) else 0)

open Classical in
/-- Boolean "AND of ORs": value `1` iff every block `[i·e, i·e+e)` meets `S`, else `0`.
    This is the Boolean function represented by `sliceWitnessPoly` on the slice. -/
noncomputable def sliceWitnessFun (n k ℓ e : ℕ) (S : Slice n k) : ℝ :=
  if (∀ i ∈ Finset.range ℓ, ∃ x ∈ S.val, i * e ≤ (x : ℕ) ∧ (x : ℕ) < i * e + e)
  then (1 : ℝ) else 0

theorem agent_087_slice_juntas_explicit_family
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hkd : k < 2 * d)
    (ℓ n : ℕ) (hn : 2 * ℓ * min d k ≤ n) (hn' : 2 * k ≤ n) :
    IsBoolean (sliceWitnessFun n k ℓ (min d k)) ∧
    HasDegreeLE (sliceWitnessFun n k ℓ (min d k)) d ∧
    (∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta (sliceWitnessFun n k ℓ (min d k)) m) := by
  sorry

end Agent087
