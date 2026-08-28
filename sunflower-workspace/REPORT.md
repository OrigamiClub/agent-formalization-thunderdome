# Improved Sunflower Lemma — 100-Agent Independent Formalization Sweep

## Method

100 independent, context-isolated agents were each given the same natural-language
description of the **improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang 2019;
refined by Rao and by Bell–Chueluecha–Warnke) and asked to produce a Lean 4
`theorem … := by sorry` statement of it, plus a short note on their encoding
choices. Exact prompt: [`PROMPT.md`](PROMPT.md).

Target statement: *there is an absolute constant `C` such that for all positive
integers `k`, `r`, every finite family `W` of sets each of cardinality exactly `k`
with `|W| > (C · r · log k)^k` contains a sunflower with `r` petals* (equivalently
`f(k,r) ≤ (C · r · log k)^k`).

Unlike the `gvb-workspace` and `glaisher-workspace` runs, this run has **no
comparison / bridging component** and the files were **not compiled** — they are
100 unverified statement formalizations. Every file was mechanically checked to
contain a `theorem` and to terminate in `sorry`; nothing further.

## Headline finding: very low structural diversity

The prompt fixed the bound shape (`(C·r·log k)^k`) and the core-based sunflower
definition, and — as in the GVB run, whose prompt was similarly leading — the 100
agents converged almost completely. **All 100** share the same skeleton:

| Axis | Choice | Count |
|---|---|---|
| Set representation | `W : Finset (Finset α)` over an ambient `[DecidableEq α]` type | 100 / 100 |
| Cardinality | `Finset.card` (never `Set.ncard` / `Nat.card`) | 100 / 100 |
| Logarithm | `Real.log` (natural log; never `Real.logb 2` / `Nat.log 2`) | 100 / 100 |
| Constant | `∃ C : ℝ, 0 < C ∧ …`, quantified outermost (before `∀ α`), so `C` is genuinely absolute | 100 / 100 |
| Sunflower predicate | locally defined in-file (no agent's *statement* depends on a Mathlib sunflower API; 17 mention one in prose) | 100 / 100 |
| Petals nonempty | not required — all followed the classical "`r` distinct sets" convention | 100 / 100 |
| Proof | `:= by sorry`, statement only | 100 / 100 |

## Where the agents did differ

These are cosmetic-to-minor variations within the single shared form; no proof of
equivalence is offered, but none looks mathematically substantive.

| Axis | Variants observed |
|---|---|
| **Degenerate small-`k` handling** | `2 ≤ k` hypothesis to keep `Real.log k > 0` (**73**); admit `0 < k` / `1 ≤ k` and repair the bound instead — `Real.log (k+1)` (**18**) or `max 1 (Real.log k)` (**9**). This is the one axis with a real modelling decision behind it (`Real.log 1 = 0` makes the bare bound false at `k = 1`, where `f(1,r) = r`). |
| **Core condition spelling** | explicit `∀ A ∈ 𝒮, ∀ B ∈ 𝒮, A ≠ B → A ∩ B = Y` (**82**) vs. `(↑𝒮 : Set _).Pairwise (· ∩ · = Y)` (**18**). |
| **Redundant core clause** | additionally assert `Y ⊆ A` for every member (**52**) vs. rely on pairwise-intersection alone (**48**). |
| **Petal count placement** | `𝒮.card = r` bundled inside the `IsSunflower` predicate vs. stated separately on the subfamily `𝒮 ⊆ W` — roughly evenly split. |
| **Predicate packaging** | plain `def … : Prop` vs. a `structure` with named fields (7 files). |
| **`α` binder** | implicit `∀ {α}` vs. explicit `∀ (α)` vs. a section `variable` (one agent's `variable {α}` sits before `∃ C`, arguably weakening "absolute"). |
| **Secondary restatement** | 72 files add the `f(k,r) ≤ (C·r·log k)^k` "sunflower function" phrasing alongside the "large family ⇒ contains a sunflower" form; agent 003 also gives an indexed-family variant; one agent offers a fixed-`C` parameter version next to the `∃ C` one. |

## Takeaway

As with GVB, a prompt that writes the bound out symbolically and names the
core-based sunflower definition leaves almost no room for structural diversity:
100/100 agents produced the same `Finset (Finset α)` / `Real.log` / `∃ C > 0`
statement. The only place independent judgement showed up was the `k ≤ 1`
degeneracy of `(C·r·log k)^k`, which split the field 73 / 27 between excluding the
case by hypothesis and patching the logarithm. These statements are unverified —
no compilation was run.
