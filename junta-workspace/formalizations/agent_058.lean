import Mathlib

/-!
# Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer)

Statement-only formalization.  Every theorem ends in `:= by sorry`.

We state three things:

* `boolean_degree_d_junta_forward`  — the positive direction: for `d ≥ 1` there is a
  constant `m(d)` so that `k ≥ 2d` and `n ≥ 2k` force every Boolean degree-`d`
  function on the slice `binom([n],k)` to be an `m(d)`-junta.
* `boolean_degree_d_junta_converse` — sharpness of `k ≥ 2d`: if `1 ≤ k < 2d` then
  for every `m` there is a Boolean degree-`d` function on some slice `binom([n],k)`
  (with `n ≥ 2k`) that is not an `m`-junta.
* `boolean_degree_d_junta_explicit` — the explicit witnessing family used for the
  converse (see the accompanying note for the reading of the family).
-/

namespace FilmusIhringer

/-- The slice `binom([n],k)`: the `k`-element subsets of `Fin n`. -/
abbrev Slice (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- The `{0,1}`-indicator vector of a subset, as a point of `ℝ^n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (1 : ℝ) else 0

/-- A real function on the slice is *Boolean* if every value lies in `{0,1}`. -/
def IsBoolean {n k : ℕ} (f : Slice n k → ℝ) : Prop :=
  ∀ S, f S = 0 ∨ f S = 1

/-- A polynomial is *multilinear* if every monomial in its support is square-free
(all exponents `≤ 1`). -/
def IsMultilinearPoly {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ m ∈ p.support, ∀ i, m i ≤ 1

/-- `f` has *degree `≤ d`* on the slice: it agrees, at every slice point `S`, with
a multilinear real polynomial of total degree `≤ d`, evaluated at the `{0,1}`
indicator vector of `S`. -/
def HasDegreeLE {n k : ℕ} (f : Slice n k → ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧ IsMultilinearPoly p ∧
      ∀ S : Slice n k, f S = MvPolynomial.eval (indicator S.1) p

/-- `f` is an *`m`-junta*: there is a set `J` of at most `m` coordinates such that
the value of `f` at a slice point `S` depends only on `S ∩ J`. -/
def IsJunta {n k : ℕ} (f : Slice n k → ℝ) (m : ℕ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Slice n k, S.1 ∩ J = T.1 ∩ J → f S = f T

/-- **Filmus–Ihringer, positive direction.**
For every degree `d ≥ 1` there is a constant `m = m(d)` such that whenever
`k ≥ 2d` and `n ≥ 2k`, every Boolean degree-`d` function on the slice
`binom([n],k)` is an `m`-junta. -/
theorem boolean_degree_d_junta_forward :
    ∀ d : ℕ, 1 ≤ d →
      ∃ m : ℕ, ∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Slice n k → ℝ, IsBoolean f → HasDegreeLE f d → IsJunta f m := by
  sorry

/-- **Filmus–Ihringer, sharpness of the bound `k ≥ 2d`.**
If `1 ≤ k < 2d` then no constant junta bound can work: for every `m` there are
`n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is *not* an
`m`-junta. -/
theorem boolean_degree_d_junta_converse :
    ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ m : ℕ,
      ∃ n : ℕ, 2 * k ≤ n ∧
        ∃ f : Slice n k → ℝ, IsBoolean f ∧ HasDegreeLE f d ∧ ¬ IsJunta f m := by
  sorry

/-- **Explicit witnessing family for the converse.**
Fix `d ≥ 1` and `1 ≤ k < 2d`, put `e = min d k`, and take `ℓ` pairwise-disjoint
blocks `B 0, …, B (ℓ-1) ⊆ Fin n`, each of size `e`.  Let

  `p = ∑ i, ∏_{c ∈ B i} X c`   and   `f S = #{ i | B i ⊆ S }`.

Then `f` agrees on the slice with `p`, which is multilinear of total degree
`e ≤ d`; `f` is Boolean (because `k < 2d` forces a `k`-set to contain at most one
whole block); and, once `n ≥ 2ℓe`, `f` depends on all `ℓe` block-coordinates, so
it is not an `m`-junta for any `m < ℓe`.  Letting `ℓ → ∞` yields the converse.

The concrete family from the theorem statement is the special case
`B i = { (i·e + 1), …, (i·e + e) }`. -/
theorem boolean_degree_d_junta_explicit
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (n ℓ e : ℕ) (he : e = min d k)
    (hnk : 2 * k ≤ n) (hn : 2 * (ℓ * e) ≤ n)
    (B : Fin ℓ → Finset (Fin n))
    (hBcard : ∀ i, (B i).card = e)
    (hBdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (p : MvPolynomial (Fin n) ℝ)
    (hp : p = ∑ i, ∏ c ∈ B i, MvPolynomial.X c)
    (f : Slice n k → ℝ)
    (hf : ∀ S : Slice n k,
        f S = ((Finset.univ.filter (fun i => B i ⊆ S.1)).card : ℝ)) :
    (∀ S : Slice n k, f S = MvPolynomial.eval (indicator S.1) p) ∧
      p.totalDegree ≤ d ∧ IsMultilinearPoly p ∧
      IsBoolean f ∧ HasDegreeLE f d ∧
      (∀ m : ℕ, m < ℓ * e → ¬ IsJunta f m) := by
  sorry

end FilmusIhringer
