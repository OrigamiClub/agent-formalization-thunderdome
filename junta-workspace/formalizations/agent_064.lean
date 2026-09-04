import Mathlib

open Finset

namespace FilmusIhringer

/-!
# Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas

Statement-only formalization.  Every theorem ends in `:= by sorry`.

We formalize:
* `forward_junta`     — the positive direction (`k ≥ 2d` ⇒ `m(d)`-junta), with `m(d)`
                        existentially quantified inside the statement;
* `converse_exists`   — the sharpness direction in plain existential form
                        (`1 ≤ k < 2d` ⇒ not a junta at all);
* `converse_witness`  — the sharpness direction with the explicit witnessing family
                        `∏_{i<ℓ} (Σ_{j<e} x_{i·e+j})`, `e = min d k`.
-/

/-- The slice `binom([n], k)`: subsets of `{0, 1, …, n-1}` of size exactly `k`,
represented as a `Finset ℕ` together with the size and boundedness conditions. -/
abbrev Slice (n k : ℕ) : Type :=
  {S : Finset ℕ // S.card = k ∧ ∀ x ∈ S, x < n}

variable {n k : ℕ}

/-- The `0/1` indicator vector (a point of `ℝ^ℕ`) of a slice element. -/
def ind (S : Slice n k) (i : ℕ) : ℝ := if i ∈ S.1 then 1 else 0

/-- A real-valued function on the slice is *Boolean* if it takes only the values `0`
and `1`. -/
def IsBoolean (f : Slice n k → ℝ) : Prop := ∀ S, f S = 0 ∨ f S = 1

/-- `f` has *degree at most `d`* if it agrees on the slice with the evaluation at the
indicator vector of some real polynomial of total degree `≤ d`.  Requiring `p` to be
multilinear would give an equivalent notion (reduce mod `xᵢ² - xᵢ`), so we do not
impose it. -/
def HasDegreeLE (d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial ℕ ℝ,
    p.totalDegree ≤ d ∧ ∀ S : Slice n k, f S = MvPolynomial.eval (ind S) p

/-- `f` is an *`m`-junta* if there is a set `J` of at most `m` coordinates such that
the value `f S` depends only on `S ∩ J`. -/
def IsJunta (m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset ℕ, J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Forward direction (Filmus–Ihringer).**  For every `d ≥ 1` there is a bound
`m = m(d)`, independent of `n` and `k`, such that whenever `k ≥ 2d` (and `n ≥ 2k`),
every Boolean degree-`d` function on the slice `binom([n], k)` is an `m`-junta. -/
theorem forward_junta (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE d f → IsJunta m f := by
  sorry

/-- **Converse / sharpness, existential form.**  If `1 ≤ k < 2d` then the junta bound
fails completely: for every `m` there is some `n ≥ 2k` and a Boolean degree-`d`
function on `binom([n], k)` that is not an `m`-junta. -/
theorem converse_exists (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE d f ∧ ¬ IsJunta m f := by
  sorry

/-- The explicit witnessing family.  With `e := min d k`, split the coordinates
`{0, …, ℓ·e - 1}` into `ℓ` consecutive blocks of size `e`; block `i` is
`{i·e, …, i·e + e - 1}`.  The witness is the product over the `ℓ` blocks of the sum of
that block's coordinate indicators, i.e. `∏_{i<ℓ} (Σ_{j<e} x_{i·e+j})`. -/
noncomputable def witness (n k e ℓ : ℕ) : Slice n k → ℝ :=
  fun S => ∏ i ∈ Finset.range ℓ, ∑ j ∈ Finset.range e, ind S (i * e + j)

/-- **Converse / sharpness, explicit form.**  For `1 ≤ k < 2d`, with `e := min d k`,
for any number of blocks `ℓ ≥ 1`, and for any `n` large enough (`n ≥ 2k` and
`n ≥ 2·ℓ·e`), the function `witness n k e ℓ` is Boolean, has degree `≤ d`, and is
*not* an `ℓ·e`-junta.  Choosing `ℓ` with `ℓ·e ≥ m` recovers `converse_exists`. -/
theorem converse_witness (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (n : ℕ) (hn : 2 * k ≤ n) (hn' : 2 * (ℓ * min d k) ≤ n) :
    IsBoolean (witness n k (min d k) ℓ) ∧
      HasDegreeLE d (witness n k (min d k) ℓ) ∧
      ¬ IsJunta (ℓ * min d k) (witness n k (min d k) ℓ) := by
  sorry

end FilmusIhringer
