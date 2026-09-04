import Mathlib

/-!
# Boolean constant-degree functions on the slice are juntas (Filmus–Ihringer)

Formalization of the *statement* of the sharp junta-threshold theorem:

> Yuval Filmus, *Junta threshold for low degree Boolean functions on the slice*,
> arXiv:2203.04760, Theorem 1.1.
> (This sharpens the earlier `O(2^d)`-threshold theorem of Filmus–Ihringer,
> *Boolean constant degree functions on the slice are juntas*, Discrete Math. 2019.)

Everything here is `:= by sorry`.  Nothing is proved.

What is stated:
* `filmus_junta_threshold` — Theorem 1.1, **both directions** bundled under the
  existential constant `m(d)`.
* `filmus_junta_threshold_witness` — the **explicit witnessing family** for the
  sharpness (converse) direction.

See `agent_042.md` for the encoding rationale and the (minor) discrepancies
between the prose in the task prompt and the source paper.
-/

namespace FilmusJuntaThreshold

/-- The 0/1 indicator vector of a finite set `S ⊆ Fin n`, viewed as a point of `ℝ^n`. -/
def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- A real-valued function on the slice `binom([n],k) = {S ⊆ Fin n : |S| = k}`
is **Boolean** if it takes values in `{0,1}` on every `k`-subset. -/
def BooleanOnSlice (n k : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → f S = 0 ∨ f S = 1

/-- `f` has **degree ≤ d** on the slice `binom([n],k)` if, on every `k`-subset,
it agrees with the evaluation at the indicator vector of some real polynomial in
`x_1, …, x_n` of total degree ≤ `d`.

Following the source paper, the polynomial is *not* required to be multilinear or
harmonic (on the slice this makes no difference to the notion of degree). -/
def HasDegreeAtMostOnSlice (n k d : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ d ∧
      ∀ S : Finset (Fin n), S.card = k →
        f S = MvPolynomial.eval (indicator S) p

/-- `f` is an **m-junta** on the slice `binom([n],k)` if there is a set `J` of at
most `m` coordinates such that the value of `f` on any `k`-subset `S` depends
only on `S ∩ J`. -/
def IsJuntaOnSlice (n k m : ℕ) (f : Finset (Fin n) → ℝ) : Prop :=
  ∃ J : Finset (Fin n), J.card ≤ m ∧
    ∀ S T : Finset (Fin n), S.card = k → T.card = k →
      S ∩ J = T ∩ J → f S = f T

/-- **Theorem 1.1 (Filmus, arXiv:2203.04760).**
Let `d ≥ 1`.  There is a constant `m(d)` such that:

* *(junta side)* if `k ≥ 2d` then for every `n ≥ 2k`, every Boolean degree-`d`
  function on `binom([n],k)` is an `m(d)`-junta;

* *(sharpness)* if `1 ≤ k < 2d` then for every `M` there exist `n ≥ 2k` and a
  Boolean degree-`d` function on `binom([n],k)` that is **not** an `M`-junta.
-/
theorem filmus_junta_threshold (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ,
      (∀ k : ℕ, 2 * d ≤ k → ∀ n : ℕ, 2 * k ≤ n →
        ∀ f : Finset (Fin n) → ℝ,
          BooleanOnSlice n k f → HasDegreeAtMostOnSlice n k d f →
          IsJuntaOnSlice n k m f) ∧
      (∀ k : ℕ, 1 ≤ k → k < 2 * d → ∀ M : ℕ,
        ∃ n : ℕ, 2 * k ≤ n ∧
          ∃ f : Finset (Fin n) → ℝ,
            BooleanOnSlice n k f ∧
            HasDegreeAtMostOnSlice n k d f ∧
            ¬ IsJuntaOnSlice n k M f) := by
  sorry

/-- The `i`-th block of `e` consecutive coordinates, `{i·e, …, i·e+e-1} ⊆ Fin n`. -/
def block (n e i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n => i * e ≤ (x : ℕ) ∧ (x : ℕ) < i * e + e)

/-- The explicit witnessing family of Theorem 1.1:

`f_ℓ(x) = Σ_{i=1}^{ℓ} Π_{j=1}^{e} x_{(i-1)e + j}`,  with `e = min d k`,

here evaluated at the indicator vector of `S` (so each block-monomial
`Π_{j} x_{(i-1)e+j}` becomes `1` iff the whole `i`-th block is contained in `S`). -/
def witnessFn (n e ℓ : ℕ) : Finset (Fin n) → ℝ :=
  fun S => ∑ i ∈ Finset.range ℓ, ∏ x ∈ block n e i, (if x ∈ S then (1 : ℝ) else 0)

/-- **Sharpness of Theorem 1.1, witnessed explicitly.**
With `e = min d k` and `1 ≤ k < 2d`: for every number `ℓ ≥ 1` of blocks and every
`n` with `n ≥ 2·ℓ·e` (and `n ≥ 2k`), the function `witnessFn n e ℓ` is a Boolean
degree-`d` function on `binom([n],k)` which is **not** an `m`-junta for any
`m < ℓ·e`.  Since `ℓ` is arbitrary, the junta arity in the first part of the
theorem cannot be bounded once `k < 2d`.

(The paper's abstract phrases the last clause loosely as "not `ℓe`-juntas"; the
function does depend on exactly the `ℓe` block coordinates, so it *is* an
`ℓe`-junta.  The precise claim, via Lemma 2.2 of the paper, is the one stated
here: not an `m`-junta for any `m < ℓe`.) -/
theorem filmus_junta_threshold_witness
    (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k < 2 * d)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (n : ℕ)
    (hn : 2 * ℓ * min d k ≤ n) (hnk : 2 * k ≤ n) :
    BooleanOnSlice n k (witnessFn n (min d k) ℓ) ∧
    HasDegreeAtMostOnSlice n k d (witnessFn n (min d k) ℓ) ∧
    (∀ m : ℕ, m < ℓ * min d k →
      ¬ IsJuntaOnSlice n k m (witnessFn n (min d k) ℓ)) := by
  sorry

end FilmusJuntaThreshold
