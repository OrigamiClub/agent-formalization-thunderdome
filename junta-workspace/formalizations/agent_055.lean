/-
  Agent 055 — Formalization of the *statement* only (Filmus–Ihringer):
  "Boolean constant-degree functions on the slice are juntas."

  Statement only: every theorem ends in `:= by sorry`.  Nothing is proved.

  See `agent_055.md` for the encoding decisions and uncertainties.
-/
import Mathlib

namespace Agent055

open scoped BigOperators

/-! ### Basic objects -/

/-- The slice `binom([n], k)`, encoded as the subtype of `k`-element subsets of
`Fin n`.  (`{1,…,n}` is modelled by `Fin n`; a set `S ⊆ {1,…,n}` by a
`Finset (Fin n)`; the membership indicator vector is `fun i => if i ∈ S then 1 else 0`.) -/
def Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- A real-valued function on the slice is *Boolean* if all its values are `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree `≤ d`* on the slice if it agrees, on every point of the slice,
with the evaluation of some multilinear real polynomial of total degree `≤ d`
at the `0/1` indicator vector of the point.

Multilinearity is expressed by requiring every monomial occurring in `p` to have
all exponents `≤ 1`. -/
def HasDegreeLE {n : ℕ} (d k : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ t ∈ p.support, ∀ i, t i ≤ 1) ∧
    ∀ S : Slice n k,
      f S = MvPolynomial.eval (fun i => if i ∈ (S : Slice n k).1 then (1 : ℝ) else 0) p

/-- `f` is an *`m`-junta* if its value depends only on the intersection of the point
with some fixed set `J` of at most `m` coordinates. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-! ### The theorem (Filmus–Ihringer) -/

/-- **Positive direction.**  For every `d ≥ 1` there is a constant `M = m(d)`
(here existentially quantified, depending only on `d`) such that whenever
`k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on the slice
`binom([n], k)` is an `M`-junta. -/
theorem filmus_ihringer_juntas (d : ℕ) (hd : 1 ≤ d) :
    ∃ M : ℕ, ∀ (n k : ℕ), 2 * d ≤ k → 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d k f → IsJunta M f := by
  sorry

/-- **Sharpness / converse direction (existential form).**  If `1 ≤ k < 2d`, then
for every `m` there are `n ≥ 2k` and a Boolean degree-`d` function on
`binom([n], k)` that is not an `m`-junta. -/
theorem filmus_ihringer_sharp (d k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d k f ∧ ¬ IsJunta m f := by
  sorry

/-! ### The explicit witnessing family

The source describes the witnesses as
`∏_{i=1}^{ℓ} ( ∑_{j=1}^{e} x_{(i-1)e+j} )` with `e = min d k`.

Taken literally (product of block-sums) this is `∏_i |S ∩ B_i|`, which is **not**
`{0,1}`-valued, and its total degree is `ℓ` rather than `≤ d`.  The function that
*is* Boolean, has degree `e = min d k ≤ d`, and genuinely depends on all `ℓ·e`
coordinates is the **sum of block-products** `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}`
(i.e. "`S` contains one of `ℓ` disjoint blocks of size `e`"); on the slice with
`k < 2d` at most one block can be contained, so the sum lands in `{0,1}`.
The theorem below is stated for that form; the literal transcription is kept, unused,
directly beneath for reference.  See `agent_055.md`. -/

/-- Sum-of-block-products form (the one used in `filmus_ihringer_explicit_family`).
Blocks are `B_i = { i·e, i·e+1, …, i·e+e-1 }` for `i < ℓ`; out-of-range indices
contribute `0`. -/
noncomputable def explicitFamily (n k ℓ e : ℕ) : Slice n k → ℝ :=
  fun S => ∑ i ∈ Finset.range ℓ, ∏ j ∈ Finset.range e,
    (if h : i * e + j < n then
        (if (⟨i * e + j, h⟩ : Fin n) ∈ S.1 then (1 : ℝ) else 0)
     else (0 : ℝ))

/-- Literal transcription of the source formula `∏_i ( ∑_j x_{(i-1)e+j} )`.
Included only for transparency; not referenced by any theorem. -/
noncomputable def explicitFamilyLiteral (n k ℓ e : ℕ) : Slice n k → ℝ :=
  fun S => ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e,
    (if h : i * e + j < n then
        (if (⟨i * e + j, h⟩ : Fin n) ∈ S.1 then (1 : ℝ) else 0)
     else (0 : ℝ))

/-- **Sharpness via the explicit family.**  For `1 ≤ k < 2d`, with `e = min d k`
and any number of blocks `ℓ`, if `n ≥ 2·ℓ·e` then `explicitFamily n k ℓ e` is a
Boolean degree-`d` function on `binom([n], k)` that is not an `m`-junta for any
`m < ℓ·e`.  (Letting `ℓ → ∞` yields non-`m`-juntas for every `m`, matching
`filmus_ihringer_sharp`.) -/
theorem filmus_ihringer_explicit_family
    (d k ℓ : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (e : ℕ) (he : e = min d k)
    (n : ℕ) (hn : 2 * (ℓ * e) ≤ n) :
    IsBoolean (explicitFamily n k ℓ e) ∧
    HasDegreeLE d k (explicitFamily n k ℓ e) ∧
    (∀ m : ℕ, m < ℓ * e → ¬ IsJunta m (explicitFamily n k ℓ e)) := by
  sorry

end Agent055
