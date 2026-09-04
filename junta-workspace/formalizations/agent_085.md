# Agent 085 — formalization note

## What I stated

Both directions of the Filmus–Ihringer junta theorem, as a single conjunction
`filmus_ihringer`, plus an optional explicit-witness theorem
`filmus_ihringer_witness` transcribing the product family from the problem
statement. Everything is statement-only (`:= by sorry`), no proofs.

* Forward: `∃ m : ℕ, ∀ k n, 2*d ≤ k → 2*k ≤ n → ∀ f, (Boolean ∧ degree ≤ d) → IsJunta m f`.
  The `m` is bound before `k, n`, so it is a constant depending on `d` only — this
  is the "`m(d)`" of the statement, rendered as an existential inside the theorem.
* Converse: `∀ k, 1 ≤ k → k < 2*d → ∀ m, ∃ n f, 2*k ≤ n ∧ (Boolean ∧ degree ≤ d) ∧ ¬ IsJunta m f`.
* Hypothesis `d ≥ 1` is carried as `hd : 1 ≤ d`.

## Encoding decisions

| Concept | Choice | Why |
|---|---|---|
| Slice `binom([n],k)` | `Slice n k := {S : Finset (Fin n) // S.card = k}` | Direct, matches "`S ⊆ {1,…,n}`, `|S| = k`"; `Fin n` is the ambient coordinate set. |
| Boolean codomain | `f : Slice n k → ℝ` with `IsBoolean f := ∀ S, f S = 0 ∨ f S = 1` | Keeps the polynomial-agreement statement coercion-free (values already in ℝ). |
| Characteristic vector | `charVec S i := if i ∈ S then 1 else 0 : Fin n → ℝ` | The `0/1` point of evaluation. |
| Degree ≤ d | `HasSliceDegreeLE`: `∃ p : MvPolynomial (Fin n) ℝ`, `p` multilinear, `p.totalDegree ≤ d`, and `∀ S, f S = eval (charVec S.1) p` | Faithful to "agrees on the slice with a multilinear real polynomial of total degree ≤ d evaluated at the indicator vector". Using an *existential* agreeing polynomial (rather than fixing one) is the robust reading: on the slice the degree of a representation is not unique. |
| Multilinear | `IsMultilinearPoly p := ∀ c ∈ p.support, ∀ i, c i ≤ 1` | Mathlib has no `MvPolynomial.IsMultilinear`; "each variable appears to power ≤ 1 in every monomial" is the standard meaning. Included for fidelity; on `{0,1}` inputs it is WLOG and does not raise total degree. |
| `m`-junta | `IsJunta m f := ∃ J : Finset (Fin n), J.card ≤ m ∧ ∀ S T, S.1 ∩ J = T.1 ∩ J → f S = f T` | "value depends only on `S ∩ J`" for a set `J` of `≤ m` coordinates. |
| `m(d)` | existential `∃ m : ℕ` inside the statement, quantified outside `k, n` | Matches "there is a constant `m(d)`"; avoids committing to a specific function `ℕ → ℕ`. |
| `n, k, d` | plain `ℕ` arguments; `n ≥ 2k` as `2*k ≤ n`, `k ≥ 2d` as `2*d ≤ k` | — |
| Explicit family | separate theorem `filmus_ihringer_witness` with `witnessPoly e ℓ emb := ∏ i : Fin ℓ, ∑ j : Fin e, X (emb i j)` | `e := min d k` carried as a parameter `e` with `he : e = min d k`. Disjointness of the `ℓ` blocks is encoded by `emb : Fin ℓ → Fin e → Fin n` injective as a function of the pair. `n ≥ 2ℓe` as `2*(ℓ*e) ≤ n`. The claim: the evaluated function is Boolean, degree ≤ d on the slice, and not an `ℓ*e`-junta. |

## Uncertainties

* Guessed / assumed Mathlib identifiers (all standard, high confidence):
  `MvPolynomial`, `MvPolynomial.eval`, `MvPolynomial.X`, `MvPolynomial.totalDegree`,
  `MvPolynomial.support`, `Function.Injective`, `Finset.card`, `Finset.inter` (`∩`).
* `IsMultilinearPoly` is my own definition (no Mathlib equivalent found).
* The literal polynomial `witnessPoly e ℓ emb` is a product of `ℓ` linear forms, so its
  *syntactic* `totalDegree` is `ℓ`, not `≤ d`. The theorem asserts only the on-slice
  notion (`HasSliceDegreeLE`, an existential over agreeing polynomials), which is what
  the source result is about; I did not attempt to justify that reduction.
* I could not fully verify from memory that the product family is genuinely `{0,1}`-valued
  on `binom([n],k)` for every admissible `(d, k, ℓ)`; the problem statement's parenthetical
  is transcribed as given. The witness theorem is offered as a faithful transcription, not
  a checked claim. The two main directions in `filmus_ihringer` do not depend on it.
* Slices with `k > n` are empty, making some instantiations vacuous; the `2*k ≤ n`
  hypotheses rule this out where it matters.
