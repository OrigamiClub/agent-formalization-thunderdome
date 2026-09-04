import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (every theorem ends in `:= by sorry`).

We fix an encoding of the slice `binom([n], k)` as size-`k` subsets of
`{0, 1, …, n-1}`, carried as a `Finset ℕ` supported inside `Finset.range n`.
Coordinates are natural numbers, which keeps the explicit witnessing family
free of `Fin`-index side conditions.

Three statements are given:

* `filmus_ihringer_junta` — the positive direction (`k ≥ 2d ⇒ junta`);
* `filmus_ihringer_sharp` — sharpness, abstract form (`k < 2d ⇒` non-juntas exist);
* `filmus_ihringer_sharp_witness` — sharpness with the explicit family.

See `agent_049.md` for the encoding rationale and uncertainties (in particular
the reading of the witnessing family's formula).
-/

namespace FilmusIhringer

/-- The slice `binom([n], k)`: subsets of `{0, 1, …, n-1}` of size exactly `k`,
carried as a `Finset ℕ` supported in `Finset.range n`. -/
abbrev Slice (n k : ℕ) : Type :=
  {S : Finset ℕ // S ⊆ Finset.range n ∧ S.card = k}

/-- Real indicator vector of a set of coordinates. -/
def ind (S : Finset ℕ) : ℕ → ℝ := fun i => if i ∈ S then 1 else 0

/-- `f` takes only the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `f` has degree at most `d` on the slice: it agrees, at every point of the
slice, with the evaluation at the indicator vector of a **multilinear** real
polynomial of total degree at most `d`.  (Multilinearity is encoded as "every
exponent in every monomial of the support is `≤ 1`".) -/
def HasSliceDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial ℕ ℝ,
    (∀ t ∈ p.support, ∀ i, t i ≤ 1) ∧
    p.totalDegree ≤ d ∧
    ∀ S : Slice n k, f S = MvPolynomial.eval (ind S.1) p

/-- `f` is an `m`-junta: there is a set `J` of at most `m` coordinates such that
the value of `f` depends only on the intersection of the input with `J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset ℕ, J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Filmus–Ihringer, positive direction.**
For every `d ≥ 1` there is a bound `m` (depending only on `d`) such that whenever
`k ≥ 2d` and `n ≥ 2k`, every Boolean function of degree `≤ d` on the slice
`binom([n], k)` is an `m`-junta.

Here `m(d)` is an existential quantified *inside* the statement (`d` is already
fixed), so it depends only on `d`. -/
theorem filmus_ihringer_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ,
        IsBoolean f → HasSliceDegreeLE f d → IsJunta f m := by
  sorry

/-- **Filmus–Ihringer, sharpness (abstract form).**
If `1 ≤ k < 2d` then the junta bound fails: for every `m` there is some
`n ≥ 2k` and a Boolean degree-`d` function on `binom([n], k)` that is not an
`m`-junta. -/
theorem filmus_ihringer_sharp (d : ℕ) (hd : 1 ≤ d) (k : ℕ)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ n : ℕ, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
      IsBoolean f ∧ HasSliceDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- The witnessing family.  With `e` coordinates per block and `ℓ` disjoint
blocks laid out as `{0,…,e-1}`, `{e,…,2e-1}`, …, this is
`S ↦ Σ_{i<ℓ} Π_{j<e} x_{i·e+j}` evaluated at the indicator vector of `S`,
i.e. the number of blocks that are entirely contained in `S`.

NB: the task's displayed formula is a product of sums; we use the sum of
products (see `agent_049.md` for why this is the intended witness). -/
def blockCount (e ℓ : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ i ∈ Finset.range ℓ, ∏ j ∈ Finset.range e,
    (if i * e + j ∈ S then (1 : ℝ) else 0)

/-- **Filmus–Ihringer, sharpness (explicit witnesses).**
Fix `1 ≤ k < 2d` and set `e = min d k`.  For every `m`, taking enough blocks
`ℓ` (so that `ℓ · e > m`), the function `blockCount e ℓ` is, on every slice
`binom([n], k)` with `n ≥ 2k` and `n ≥ 2·ℓ·e`, a Boolean function of degree
`≤ d` on the slice that is not an `m`-junta. -/
theorem filmus_ihringer_sharp_witness (d : ℕ) (hd : 1 ≤ d) (k : ℕ)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * d) :
    ∀ m : ℕ, ∃ ℓ : ℕ, ∀ n : ℕ, 2 * k ≤ n → 2 * ℓ * min d k ≤ n →
      IsBoolean (fun S : Slice n k => blockCount (min d k) ℓ S.1) ∧
      HasSliceDegreeLE (fun S : Slice n k => blockCount (min d k) ℓ S.1) d ∧
      ¬ IsJunta (fun S : Slice n k => blockCount (min d k) ℓ S.1) m := by
  sorry

end FilmusIhringer
