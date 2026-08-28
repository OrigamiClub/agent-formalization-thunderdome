# Agent 013 — Improved sunflower lemma, statement formalization

## Form chosen

Two `sorry`ed theorems in namespace `ImprovedSunflower`:

1. `improved_sunflower_lemma` — the "counting" form: `∃ C > 0`, for all `α`, all
   positive `k, r`, every `Finset (Finset α)` family `W` of exact-`k`-cardinality
   sets with `|W| > (C·r·log k)^k` contains a sunflower with `r` petals.
2. `improved_sunflower_lemma_function` — the `f(k,r) ≤ (C·r·log k)^k` form, with
   the sunflower function `f` passed in as a hypothesis characterising the
   threshold (Mathlib has no such named function, so hypothesising it keeps the
   file self-contained).

Two auxiliary definitions:

* `IsSunflower 𝓢 Y` : any two distinct members of `𝓢 : Finset (Finset α)` meet
  exactly in the core `Y`.
* `ContainsSunflower W r` : some `𝓢 ⊆ W` with `𝓢.card = r` and `IsSunflower 𝓢 Y`
  for some `Y`.

## Encoding decisions and rationale

* **Set representation:** `Finset (Finset α)` over an ambient type `α`. This makes
  "finite family" and "each set finite of cardinality `k`" free, and distinctness
  of the `r` chosen petals is automatic from `Finset` membership. `α` is
  quantified *inside* the theorem, after `∃ C`, so `C` does not depend on `α`.
* **Sunflower predicate:** defined explicitly via a common core `Y` with
  `A ∩ B = Y` for distinct `A, B`. This is the "pairwise intersections all
  coincide" formulation with the core named. Petals are *not* required nonempty
  (at most one member can equal the core when `r ≥ 2` and all sets have the same
  cardinality, so this is harmless and matches the classical statement).
* **"sunflower with `r` petals":** `𝓢.card = r` (exact count), the standard
  reading. Distinctness needs no separate hypothesis (Finset).
* **Constant `C`:** existentially quantified as a `ℝ` with `0 < C`, outermost, so
  it is a genuine absolute constant.
* **Logarithm:** `Real.log` (natural log). To handle `k = 1` (`Real.log 1 = 0`,
  which would make the bound `0` and the statement false for `r ≥ 2`,
  `|W| = 1`), the factor is written `max 1 (Real.log k)`. For `k ≥ 3` this is
  exactly `Real.log k`; the small-`k` adjustment is absorbable into `C` and is a
  standard convention. `k = 0` is excluded by `0 < k` (and `r = 0` by `0 < r`).
* **Cardinality:** `Finset.card`, cast `ℕ → ℝ` to compare against the real bound
  `(C * r * max 1 (Real.log k)) ^ k`. The exponent `^ k` is natural-number power.

## Uncertainties

* **Mathlib sunflower API:** Mathlib does contain a sunflower file
  (`Mathlib.Combinatorics.SetFamily.Sunflower`) with, I believe, a predicate
  named something like `Finset.IsSunflower` / `Set.IsSunflower` and the classical
  Erdős–Ko–Rado bound (`exists_sunflower` with a `(r-1)^k · k!`-type hypothesis).
  I did not rely on it: exact identifier names and argument order are uncertain,
  and the improved bound is definitely not in Mathlib. My local `IsSunflower` may
  clash in spirit but not in name.
* **Coercions:** wrote `(r : ℝ)`, `Real.log (k : ℝ)`, `(W.card : ℝ)` explicitly to
  avoid elaboration ambiguity; exact placement of casts may need adjustment under
  a real compiler.
* **Instance binder in `∀` telescope:** `∀ (α : Type*) [DecidableEq α] (k r : ℕ), …`
  inside a `Prop` after `∃ C` is expected to be legal Lean 4; not compiler-checked
  here.
* **Literature bound variant:** some statements of the refined lemma use
  `(C·r·log(rk))^k` or `(C log k)^k · r^k`; I used the `(C·r·log k)^k` form given
  in the task. The `max 1 (·)` wrapper is my addition for well-definedness at
  `k = 1`.
* No compiler was available; the file is written from memory of Mathlib.
