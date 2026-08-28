# Agent 035 — improved sunflower lemma, statement formalization

## Form chosen

Two `theorem ... := by sorry` statements in namespace `ImprovedSunflower`, plus one
local definition `IsSunflower`.

* `improved_sunflower_lemma` — the primary form: an absolute `C > 0` such that any
  `k`-uniform finite family with `|W| > (C·r·log k)^k` contains an `r`-petal sunflower.
* `improved_sunflower_bound` — the contrapositive "upper bound on the sunflower
  function" phrasing (`f(k,r) ≤ (C r log k)^k`): if `W` contains no `r`-petal
  sunflower then `|W| ≤ (C·r·log k)^k`. Included because the task explicitly mentions
  both phrasings; they are trivially interchangeable.

## Encoding decisions

| Choice | Decision | Reason |
| --- | --- | --- |
| Set representation | `Finset α` over an arbitrary `Type*` `α`, family `W : Finset (Finset α)` | Cleanest `Finset.card` for the `|W|` comparison; no separate finiteness hypotheses; `α` fully general. |
| Sunflower predicate | local `IsSunflower P Y : Prop := ∀ S ∈ P, ∀ T ∈ P, S ≠ T → S ∩ T = Y`, with `P : Finset (Finset α)`, core `Y : Finset α` | "pairwise intersections all coincide with an explicit core". Self-contained, so the file does not depend on the exact current spelling of Mathlib's sunflower API. |
| Number of petals | `P.card = r` | Members of a `Finset` are distinct, so this already encodes "`r` distinct sets"; no separate injectivity/distinctness hypothesis needed. |
| Petals nonempty? | Not required | Matches the standard (Erdős–Rado) definition; degenerate petals are harmless. Noted in the docstring. |
| `Y ⊆ S`, pairwise-disjoint petals, "in ≥2 ⇒ in all" | Not stated separately | All follow from `S ∩ T = Y` once `2 ≤ P.card`. Docstring records this. |
| Cardinality operator | `Finset.card` (`W.card`, `P.card`) | Native to the `Finset` representation. |
| Logarithm | `Real.log` (natural log), argument `(k : ℝ)` | Base only affects `C`, which is existential; natural log is the lightest choice. `Real.logb 2` would be equivalent. |
| Bound expression | `(C * (r : ℝ) * Real.log (k : ℝ)) ^ k < (W.card : ℝ)`, strict `<` | Direct transcription of `|W| > (C·r·log k)^k`. Exponent is `k : ℕ` via monoid power on `ℝ`. |
| `k = 0, 1` handling | Hypothesis `2 ≤ k` | For `k ≤ 1`, `log k ≤ 0` and the RHS degenerates (`log 1 = 0` gives bound `0`, which fails to detect the genuine singleton sunflowers). `2 ≤ k` is the usual literature convention and keeps `log k ≥ log 2 > 0`. |
| `r` range | Hypothesis `1 ≤ r` | Positive integers as stated. `r = 1` is trivially true (any one set); `r = 2` is the first substantial case. |
| Constant `C` | Existentially quantified as the **outermost** binder, before `∀ α k r W` | Makes `C` genuinely absolute: independent of the ambient type and of `k, r`. If `α` were bound first, `C` could depend on it. |
| `α` binder | Explicit `(α : Type*)` with `[DecidableEq α]` immediately after | `DecidableEq` is needed for `Finset` intersection `S ∩ T`. Explicit (not implicit) to avoid elaboration quirks inside a nested `∀` in a `Prop`. |

## Uncertainties

* **Mathlib sunflower API not used.** I believe `Mathlib/Combinatorics/SetFamily/Sunflower.lean`
  exists and provides a predicate along the lines of `Finset.IsSunflower` /
  `IsSunflower (𝒮 : Set (Finset α)) (core : Finset α)` together with the classical
  Erdős–Rado bound `(r - 1) ^ k * k !` (theorem name possibly `Finset.exists_isSunflower`
  or similar). I did **not** rely on these because I am not certain of the exact
  names/signatures, and the *improved* `(C r log k)^k` bound is (to my knowledge) not
  in Mathlib. The local `IsSunflower` is a faithful stand-in.
* **`import Mathlib`** is used wholesale (no compiler available). The only real
  dependency is `Real.log` (`Mathlib.Analysis.SpecialFunctions.Log.Basic`) plus
  `Finset` basics.
* **Exact constant / bound variant.** The literature has minor variants
  (`(C r log k)^k`, `(C r log(rk))^k`, `(a log k)^k · r^k`, etc.), all equivalent up to
  the absolute constant for `k ≥ 2`. I used the plain `(C · r · log k)^k` from the task
  statement.
* **`∀ (α : Type*) [DecidableEq α] ...` inside `∃ C, _ ∧ _`.** Binding an instance
  argument in a `∀` nested inside a `Prop` is legal Lean 4 but slightly unusual; if an
  elaborator complains, the fix is to pull `α` out to a `variable` and instead
  quantify `C` via a wrapper, or to use `Fintype`-free `Classical` decidability.
