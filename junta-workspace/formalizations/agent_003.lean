/-
Filmus–Ihringer: Boolean constant-degree functions on the slice are juntas.

Statement-only formalization (no proofs).  Agent 003, formalization diversity study.

We state BOTH directions of the theorem, plus (as a separate theorem) the explicit
witnessing family for the converse direction.

Reference: Y. Filmus, F. Ihringer, "Boolean constant degree functions on the slice
are juntas", Discrete Mathematics (2019); and Y. Filmus, "Junta threshold for low
degree Boolean functions on the slice" (arXiv:2203.04760), which gives the sharp
constant and the explicit family  ∑_{i=1}^{ℓ} ∏_{j=1}^{e} x_{(i-1)e+j}  with
e = min(d,k).
-/

import Mathlib

namespace FilmusIhringer

open Classical MvPolynomial

/-- The slice `binom([n],k)` : the `k`-element subsets of `Fin n`, as a subtype. -/
abbrev Slice (n k : ℕ) : Type := {S : Finset (Fin n) // S.card = k}

/-- The real 0/1 indicator vector of a subset `S ⊆ Fin n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- `f` is Boolean: it takes only the values `0` and `1`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S : Slice n k, f S = 0 ∨ f S = 1

/-- `f` has (slice-)degree `≤ d`: it agrees on the slice with a multilinear real
polynomial in `Fin n` variables of total degree `≤ d`, evaluated at the 0/1
indicator vector.  Multilinearity is encoded by `degreeOf i p ≤ 1` for every `i`
(it is well known to be WLOG on the slice). -/
def HasSliceDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
    (∀ i, p.degreeOf i ≤ 1) ∧
    (∀ S : Slice n k, f S = MvPolynomial.eval (indicator S.1) p)

/-- `f` is an `m`-junta: there is a coordinate set `J` with `|J| ≤ m` such that the
value of `f` on `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-!
### Main theorem (both directions)

* Positive direction: for every `d ≥ 1` there is a constant `m` (an existential,
  i.e. `m = m(d)`) such that whenever `k ≥ 2d` and `n ≥ 2k`, every Boolean
  degree-`d` function on `binom([n],k)` is an `m`-junta.

* Converse: whenever `1 ≤ k < 2d`, no such constant exists — for every `m` there
  are `n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is not an
  `m`-junta.
-/
theorem filmus_ihringer :
    (∀ d : ℕ, 1 ≤ d →
        ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
          ∀ f : Slice n k → ℝ, IsBoolean f → HasSliceDegreeLE f d → IsJunta f m)
      ∧
    (∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
        ∃ n : ℕ, 2 * k ≤ n ∧
          ∃ f : Slice n k → ℝ,
            IsBoolean f ∧ HasSliceDegreeLE f d ∧ ¬ IsJunta f m) := by
  sorry

/-!
### Explicit witnessing family for the converse

With `e = min d k`, the `i`-th block is the set of coordinates
`{ i·e, i·e + 1, …, i·e + e - 1 } ⊆ Fin n`, and the witness is

  `f_ℓ(S) = ∑_{i < ℓ} ∏_{x ∈ block i} x`   evaluated at the indicator of `S`,

i.e. `f_ℓ(S) = 1` iff some block is entirely contained in `S`.  Because `k < 2d`,
no two disjoint `e`-blocks fit inside a `k`-set, so at most one block lies in `S`
and `f_ℓ` is Boolean; it has degree `e ≤ d`; and it depends on all `ℓ·e`
coordinates, so it is not an `m`-junta for any `m < ℓ·e`.  Since `ℓ` is arbitrary
this defeats any fixed bound `m(d)`.
-/

/-- The `i`-th block of `e` consecutive coordinates inside `Fin n`. -/
def block (n e i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n => i * e ≤ (x : ℕ) ∧ (x : ℕ) < i * e + e)

/-- The explicit real polynomial `∑_{i < ℓ} ∏_{x ∈ block i} X x`. -/
def explicitPoly (n e ℓ : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ i ∈ Finset.range ℓ, ∏ x ∈ block n e i, MvPolynomial.X x

/-- The explicit Boolean witness: `1` iff some `min d k`-block is contained in `S`. -/
def explicitBoolFn (d k n ℓ : ℕ) : Slice n k → ℝ :=
  fun S => if ∃ i ∈ Finset.range ℓ, block n (min d k) i ⊆ S.1 then (1 : ℝ) else 0

/-- Properties of the explicit family.  Fix `d ≥ 1` and `1 ≤ k < 2d`, put
`e = min d k`, and take any `ℓ` and any `n ≥ 2·ℓ·e` with `n ≥ 2k`.  Then
`explicitBoolFn d k n ℓ`:
* is Boolean;
* is computed by `explicitPoly n e ℓ` on the slice;
* that polynomial is multilinear of total degree `≤ d`, hence the function has
  slice-degree `≤ d`;
* is not an `m`-junta for any `m < ℓ·e`.
Letting `ℓ → ∞` yields, for every `m`, a Boolean degree-`d` function on some slice
that is not an `m`-junta. -/
theorem filmus_ihringer_lower_explicit
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (hk2 : k < 2 * d)
    (ℓ n : ℕ) (hn : 2 * (ℓ * min d k) ≤ n) (hnk : 2 * k ≤ n) :
    IsBoolean (explicitBoolFn d k n ℓ)
      ∧ (∀ S : Slice n k,
          explicitBoolFn d k n ℓ S
            = MvPolynomial.eval (indicator S.1) (explicitPoly n (min d k) ℓ))
      ∧ (explicitPoly n (min d k) ℓ).totalDegree ≤ d
      ∧ (∀ i, (explicitPoly n (min d k) ℓ).degreeOf i ≤ 1)
      ∧ HasSliceDegreeLE (explicitBoolFn d k n ℓ) d
      ∧ (∀ m : ℕ, m < ℓ * min d k → ¬ IsJunta (explicitBoolFn d k n ℓ) m) := by
  sorry

end FilmusIhringer
