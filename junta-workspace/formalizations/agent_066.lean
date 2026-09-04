import Mathlib

open scoped BigOperators

namespace FilmusIhringer

/-- The slice `binom([n],k)` as the subtype of `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- A real-valued function is Boolean if it only takes the values `0` and `1`. -/
def IsBooleanValued {α : Type*} (f : α → ℝ) : Prop :=
  ∀ x, f x = 0 ∨ f x = 1

/-- `f : Slice n k → ℝ` has (slice) degree `≤ d` if it agrees on the slice with the
evaluation, at the `0/1` indicator vector of `S`, of a *multilinear* real polynomial
in `n` variables of total degree `≤ d`.  Multilinearity is encoded by requiring every
monomial occurring in `p` to be squarefree (each exponent `≤ 1`); this is harmless
since on the hypercube `xᵢ^2 = xᵢ`, and it matches the wording of the problem. -/
def HasSliceDegreeLE (n k d : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ t ∈ p.support, ∀ i, t i ≤ 1) ∧
    ∀ S : Slice n k,
      f S = MvPolynomial.eval (fun i => if i ∈ S.1 then (1 : ℝ) else 0) p

/-- `f` is an `m`-junta: there is a set `J` of at most `m` coordinates such that the
value `f S` depends only on `S ∩ J`. -/
def IsJunta (n k m : ℕ) (f : Slice n k → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- The explicit lower-bound family of Filmus–Ihringer.
With `e = min d k`, split the coordinates `{0, …, ℓ·e - 1}` into `ℓ` consecutive
blocks of size `e` (block `i` is `{i·e, …, i·e + e - 1}`), and take the product over
the blocks of the linear form `∑_{j in block i} x_j`.  Evaluated at a set `S`, the
`i`-th factor is `|S ∩ Bᵢ|`, so `fiWitness n d k ℓ S = ∏_{i<ℓ} |S ∩ Bᵢ|`. -/
noncomputable def fiWitness (n d k ℓ : ℕ) : Slice n k → ℝ :=
  fun S => ∏ i ∈ Finset.range ℓ, ∑ x ∈ S.1,
    (if i * min d k ≤ (x : ℕ) ∧ (x : ℕ) < i * min d k + min d k then (1 : ℝ) else 0)

/-- **Filmus–Ihringer, positive direction.**
For every `d ≥ 1` there is a constant `M = m(d)` such that whenever `k ≥ 2d` and
`n ≥ 2k`, every Boolean degree-`≤ d` function on the slice `binom([n],k)` is an
`M`-junta.  (`m(d)` is stated as an existential.) -/
theorem filmus_ihringer_forward {d : ℕ} (hd : 1 ≤ d) :
    ∃ M : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ f : Slice n k → ℝ,
        IsBooleanValued f → HasSliceDegreeLE n k d f → IsJunta n k M f := by
  sorry

/-- **Filmus–Ihringer, converse direction (clean existential form).**
If `1 ≤ k < 2d` then the junta bound fails unboundedly: for every `m` there are
`n ≥ 2k` and a Boolean degree-`≤ d` function on `binom([n],k)` that is not an
`m`-junta. -/
theorem filmus_ihringer_converse {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hkd : k < 2 * d) (m : ℕ) :
    ∃ n : ℕ, 2 * k ≤ n ∧
      ∃ f : Slice n k → ℝ,
        IsBooleanValued f ∧ HasSliceDegreeLE n k d f ∧ ¬ IsJunta n k m f := by
  sorry

/-- **Filmus–Ihringer, converse direction with the explicit witnessing family.**
If `1 ≤ k < 2d` then, with `e = min d k`, for every `m` there is a member
`fiWitness n d k ℓ` of the family (with `ℓ·e ≥ m` and `n ≥ 2·ℓ·e`) which is Boolean,
has slice degree `≤ d`, and is not an `ℓ·e`-junta — and hence not an `m`-junta. -/
theorem filmus_ihringer_converse_explicit {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hkd : k < 2 * d) (m : ℕ) :
    ∃ ℓ n : ℕ,
      2 * k ≤ n ∧ 2 * ℓ * min d k ≤ n ∧ m ≤ ℓ * min d k ∧
      IsBooleanValued (fiWitness n d k ℓ) ∧
      HasSliceDegreeLE n k d (fiWitness n d k ℓ) ∧
      ¬ IsJunta n k (ℓ * min d k) (fiWitness n d k ℓ) := by
  sorry

end FilmusIhringer
