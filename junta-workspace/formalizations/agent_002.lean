/-
Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas.

Statement-only formalization (both directions + explicit witnessing family).
Every theorem ends in `:= by sorry`.  Agent 002.
-/
import Mathlib

open scoped Classical

namespace FilmusIhringer

/-- The slice `binom([n], k)`: the `k`-element subsets of `Fin n`
(used here as a proxy for `{1, …, n}`). -/
abbrev Slice (n k : ℕ) : Type := { S : Finset (Fin n) // S.card = k }

/-- A real-valued function on the slice is *Boolean* if it only takes the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has *degree at most `d`* on the slice if it agrees, at every point of the slice,
with the evaluation of some real multivariate polynomial of total degree `≤ d` at the
`{0,1}`-indicator vector of the subset.

No multilinearity is imposed on the polynomial: on the slice this does not change the
class of functions of degree `≤ d` (squares of coordinates can be removed using
`x_i^2 = x_i` on `{0,1}` points, which never increases total degree). -/
def HasDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
      ∀ S : Slice n k,
        f S = MvPolynomial.eval (fun i : Fin n => if i ∈ S.1 then (1 : ℝ) else 0) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such that the
value of `f` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n),
    J.card ≤ m ∧ ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- Coordinate number `i·e + j` of `Fin n`, i.e. the `j`-th coordinate of the `i`-th block,
for `i < ℓ` and `j < e`, provided `2·ℓ·e ≤ n`. -/
def blockCoord {n ℓ e : ℕ} (hn : 2 * ℓ * e ≤ n) (i : Fin ℓ) (j : Fin e) : Fin n :=
  ⟨(i : ℕ) * e + (j : ℕ), by
    have hi : (i : ℕ) < ℓ := i.2
    have hj : (j : ℕ) < e := j.2
    have e1 : (i : ℕ) * e + e = ((i : ℕ) + 1) * e := by ring
    have e2 : 2 * ℓ * e = ℓ * e + ℓ * e := by ring
    have h3 : ((i : ℕ) + 1) * e ≤ ℓ * e := mul_le_mul_right' (by omega) e
    omega⟩

/-- The Filmus–Ihringer lower-bound family.

With block size `e = min d k`, `juntaWitness d ℓ hn S` is the number of the first `ℓ`
pairwise-disjoint size-`e` blocks of coordinates that are entirely contained in `S`.
As a polynomial this is `∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}` (total degree `e ≤ d`),
evaluated at the indicator vector of `S`.

When `1 ≤ k < 2d` one has `k < 2e`, so at most one block can fit inside a `k`-set and this
count is `{0,1}`-valued on the slice, while it genuinely depends on all `ℓ·e` block
coordinates. -/
noncomputable def juntaWitness {n k : ℕ} (d ℓ : ℕ)
    (hn : 2 * ℓ * min d k ≤ n) (S : Slice n k) : ℝ :=
  ((Finset.univ.filter
      (fun i : Fin ℓ => ∀ j : Fin (min d k), blockCoord hn i j ∈ S.1)).card : ℝ)

/-- **Filmus–Ihringer.**  Fix `d ≥ 1`.

1. (Positive direction.)  There is a constant `m = m(d)` such that whenever `k ≥ 2d` and
   `n ≥ 2k`, every Boolean function of degree `≤ d` on the slice `binom([n],k)` is an
   `m`-junta.

2. (Negative direction.)  Whenever `1 ≤ k < 2d`, for every `m` there exist `n ≥ 2k` and a
   Boolean function of degree `≤ d` on `binom([n],k)` that is not an `m`-junta.

3. (Explicit witnesses.)  In the range `1 ≤ k < 2d`, the family `juntaWitness d ℓ` is, on
   every slice with `n ≥ 2·ℓ·min d k` (which also gives `n ≥ 2k`), Boolean of degree `≤ d`
   and not an `m`-junta for any `m < ℓ·min d k`.  Letting `ℓ → ∞` yields part 2. -/
theorem filmus_ihringer (d : ℕ) (hd : 1 ≤ d) :
    (∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta m f)
    ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
        ∃ n : ℕ, 2 * k ≤ n ∧
          ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f)
    ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ ℓ n : ℕ, ∀ hn : 2 * ℓ * min d k ≤ n, 2 * k ≤ n →
        IsBoolean (juntaWitness d ℓ hn)
        ∧ HasDegreeLE d (juntaWitness d ℓ hn)
        ∧ ∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta m (juntaWitness d ℓ hn)) := by
  sorry

end FilmusIhringer
