import Mathlib

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization (every theorem ends in `:= by sorry`; nothing is proved).

We state three things:

* `boolean_degLE_isJunta` — the **positive direction**: for `d ≥ 1` there is a
  constant `m = m(d)` such that for `k ≥ 2d` and `n ≥ 2k`, every Boolean
  slice-degree-`d` function on `binom([n],k)` is an `m`-junta;
* `exists_boolean_degLE_not_isJunta` — the **negative direction / sharpness**: for
  `1 ≤ k < 2d` and every `m`, some slice `binom([n],k)` (`n ≥ 2k`) carries a
  Boolean slice-degree-`d` function that is not an `m`-junta;
* `witnessFun_spec` — properties of the **explicit witnessing family**
  `∏_{i=0}^{k-1} ∑_{j=0}^{e-1} X_{i·e+j}` with `e = min d k`.
-/

namespace FilmusIhringer

open scoped BigOperators

/-- Ground-set points are natural numbers; the ground set of `binom([n],k)` is
`Finset.range n`.  The **slice** `binom([n],k)` is the type of `k`-element subsets
of `range n`. -/
abbrev Slice (n k : ℕ) : Type :=
  {S : Finset ℕ // S ⊆ Finset.range n ∧ S.card = k}

/-- The `0/1` indicator vector of a set of coordinates, as a function `ℕ → ℝ`. -/
def ind (S : Finset ℕ) : ℕ → ℝ := fun t => if t ∈ S then (1 : ℝ) else 0

/-- `f` is Boolean: every value is `0` or `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- `p` is multilinear: in every monomial each variable occurs with exponent `≤ 1`. -/
def IsMultilin (p : MvPolynomial ℕ ℝ) : Prop :=
  ∀ μ ∈ p.support, ∀ t, μ t ≤ 1

/-- `f : Slice n k → ℝ` has **slice-degree `≤ d`**: on every point of the slice it
agrees with the evaluation, at the `0/1` indicator vector, of some multilinear
real polynomial of total degree `≤ d`. -/
def HasSliceDegreeLE {n k : ℕ} (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial ℕ ℝ,
    IsMultilin p ∧ p.totalDegree ≤ d ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (ind S.1) p

/-- `f` is an **`m`-junta**: there is a coordinate set `J` with `|J| ≤ m` such
that `f S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset ℕ, J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Positive direction (Filmus–Ihringer).**  For `d ≥ 1` there is a constant
`m = m(d)` such that whenever `k ≥ 2d`, on every slice `binom([n],k)` with
`n ≥ 2k`, every Boolean function of slice-degree `≤ d` is an `m`-junta. -/
theorem boolean_degLE_isJunta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k, 2 * d ≤ k → ∀ n, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasSliceDegreeLE d f → IsJunta m f := by sorry

/-- **Negative direction (sharpness).**  For `d ≥ 1` and `1 ≤ k < 2d` the junta
bound fails for every `m`: some slice `binom([n],k)` with `n ≥ 2k` carries a
Boolean function of slice-degree `≤ d` that is not an `m`-junta. -/
theorem exists_boolean_degLE_not_isJunta
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk0 : 1 ≤ k) (hk : k < 2 * d) (m : ℕ) :
    ∃ n, 2 * k ≤ n ∧ ∃ f : Slice n k → ℝ,
      IsBoolean f ∧ HasSliceDegreeLE d f ∧ ¬ IsJunta m f := by sorry

/-- The Filmus–Ihringer **witness polynomial**: with `e = min d k` and `ℓ = k`
blocks of `e` consecutive variables,
`∏_{i=0}^{k-1} ( ∑_{j=0}^{e-1} X_{i·e + j} )`. -/
noncomputable def witnessPoly (d k : ℕ) : MvPolynomial ℕ ℝ :=
  ∏ i ∈ Finset.range k,
    ∑ j ∈ Finset.range (min d k), MvPolynomial.X (i * min d k + j)

/-- The function the witness polynomial induces on the slice. -/
noncomputable def witnessFun (d k n : ℕ) : Slice n k → ℝ :=
  fun S => MvPolynomial.eval (ind S.1) (witnessPoly d k)

/-- **The explicit family works.**  For `1 ≤ k < 2d` and `n ≥ 2·k·(min d k)`, the
function `witnessFun d k n` is Boolean, has slice-degree `≤ d`, and is not a
`(k·(min d k) − 1)`-junta: its value genuinely depends on all `k·(min d k)`
block coordinates. -/
theorem witnessFun_spec
    (d k n : ℕ) (hd : 1 ≤ d) (hk0 : 1 ≤ k) (hk : k < 2 * d)
    (hn : 2 * (k * min d k) ≤ n) :
    IsBoolean (witnessFun d k n) ∧
      HasSliceDegreeLE d (witnessFun d k n) ∧
      ¬ IsJunta (k * min d k - 1) (witnessFun d k n) := by sorry

end FilmusIhringer
