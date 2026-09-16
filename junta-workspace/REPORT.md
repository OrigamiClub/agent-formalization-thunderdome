# Boolean degree-d functions on the slice are juntas — 100-agent formalization sweep

## Method

100 independent, context-isolated agents were each given the same natural-language
statement of **Filmus–Ihringer Theorem 1.1** ("Boolean constant-degree functions
on the slice are juntas", arXiv:2203.04760) and asked to produce a Lean 4
`theorem … := by sorry` formalization. **Each agent chose which part(s) to state**
(forward direction, converse, explicit witnessing family, or any combination).
Exact prompt: [`PROMPT.md`](PROMPT.md).

The target, informally: *let `d ≥ 1`; there is a constant `m(d)` such that if
`k ≥ 2d` then for every `n ≥ 2k`, every Boolean degree-`d` function on the slice
`binom([n],k)` is an `m(d)`-junta; conversely if `1 ≤ k < 2d` then for every `m`
there are `n ≥ 2k` and a Boolean degree-`d` function on `binom([n],k)` that is not
an `m`-junta, witnessed by `∏_{i}(Σ_{j} x_{(i-1)e+j})`, `e = min(d,k)`.*

Unlike the `sunflower-workspace` run, this run's 100 files were **compiled** against
the pinned checkout (`leanprover/lean4:v4.29.0-rc3`, Mathlib
`777aaa61dcd2a1258d2b4962dbe983ede4d23b2e`). PASS = the file elaborates and
type-checks; the expected `declaration uses 'sorry'` warning does not count as a
failure. No bridging/equivalence pass was done.

## Compilation result

<!-- COMPILE_RESULT -->
**100 / 100 PASS** (run 2026-09-03, strictly serial — every file does
`import Mathlib` and this box has 8 GB RAM; fixes applied and reverified
2026-09-15). PASS = elaborates and type-checks; the expected
`declaration uses 'sorry'` warning does not count as a failure.

The initial pass found 10 failures, **none a wrong or mis-stated theorem** — in
every case the theorem propositions themselves elaborated (the `sorry` warnings
fired *after* the error); the break was always in an auxiliary `def` —
overwhelmingly the explicit witness family — or a stray token. Three mechanical
classes, each fixed with a one-line change and reverified clean:

| Class | Count | Agents | Fix applied |
|---|---|---|---|
| Missing `noncomputable` on a `def` built from `MvPolynomial` (`instCommRingMvPolynomial` is noncomputable) | 5 | 003, 013, 054, 071, 100 | prepended `noncomputable` |
| Witness family: `S.1.filter (fun a => … (a : ℕ) …)` — `S.1 : Finset (Fin n)` but the `ℕ`-literal block predicate forced the binder to `ℕ`, so `↑S` was asked to coerce to `Finset ℕ` and couldn't | 4 | 015, 026, 032, 089 | ascribed the binder `fun a : Fin n =>` |
| Stray `open … in` token mid-declaration (`unexpected token 'open'; expected 'lemma'`) — the docstring sat between `open Classical in` and the `def`, but `open … in` wraps the whole next command so the docstring couldn't attach | 1 | 068 | moved the docstring to after `open Classical in` |

Matches the earlier runs' takeaway that compilation catches encoding/syntax
slips inspection misses, never a wrong proposition.

Details: [`compile/results.csv`](compile/results.csv), per-file logs in
[`compile/logs/`](compile/logs). The earlier `-P 6` parallel attempt melted the
box (every job hit the wall-clock cap); its output is kept as
`compile/results.csv.bogus-run1`.

## Encoding diversity

This is a genuinely harder theorem to state than the sunflower lemma — "Boolean
degree-`d` function on the slice" and "`m`-junta" both need built-from-scratch
definitions — so there was more room to diverge. Yet on the core modelling
choices the agents again converged almost completely, differing mainly on details
the prompt left open that have no single "obvious" Mathlib answer.

### Near-unanimous

| Axis | Choice | Count |
|---|---|---|
| Codomain | real-valued `f : … → ℝ` with a **separate** `{0,1}`-valued predicate (never `Bool`, `Fin 2`, `ZMod 2`, or `Prop` as the actual codomain) | 100 / 100 |
| Degree | "agrees on the slice with `MvPolynomial.eval` (at the 0/1 indicator vector) of some `p` with `totalDegree ≤ d`"; 99 also impose or mention multilinearity (`degreeOf i p ≤ 1`) | 100 / 100 |
| Degree — alternatives | Johnson/Fourier-level or discrete-`(d+1)`-derivative definitions | **0** used one |
| Mathlib "Boolean degree" API | none exists in this checkout; every agent defined its own predicate | 100 / 100 |
| `m`-junta | `∃ J : Finset (Fin n), J.card ≤ m ∧ (S ∩ J = T ∩ J → f S = f T)` | 100 / 100 |
| `m(d)` | stated as an existential (`∃ m` / `∃ M`) — 12 files additionally give an `m : ℕ → ℕ` explicit-function variant | 100 / 100 |

### Where they differed

| Axis | Variants |
|---|---|
| **Slice representation** | `{S : Finset (Fin n) // S.card = k}` subtype (**84**); bare `S : Finset (Fin n)` carried with a side `S.card = k` hypothesis (**~9**); a subtype over `Finset ℕ` with `MvPolynomial ℕ ℝ` variables instead of `Fin n` (**~9**). |
| **Scope chosen** (agents were free) | 1 theorem: 4 files · 2 theorems: 22 files · 3 theorems: 74 files. Essentially all stated the forward direction; the large majority also stated the converse; **~91** included an explicit witnessing family, **9** deliberately omitted it (arguing the literal family is not Boolean on the slice). |
| **The witnessing family** | **35** files explicitly flagged that the prompt's literal `∏_i(Σ_j x)` product-of-sums is not `{0,1}`-valued / has the wrong degree on the slice, and formalized the **dual `Σ_i(∏_j x)` sum-of-products** (the form in Filmus's actual paper); the rest transcribed the literal `∏(Σ)` (some flagging it as suspect, some not). Many also rephrased "not an `ℓe`-junta" as "not an `m`-junta for every `m < ℓe`". |
| **`m(d)` binder placement** | `∃` before vs. after the `∀ k, n` — cosmetic. |
| **Junta phrasing** | `S ∩ J = T ∩ J → f S = f T` vs. "`f` factors through `S ↦ S ∩ J`" — equivalent. |

## Takeaway

As in the earlier runs, the parts of the statement with a "natural" Mathlib
rendering drew near-total convergence (100/100 on codomain, the
`MvPolynomial`/`totalDegree` degree definition, the junta predicate, `∃ m(d)`).
The real divergence was on the parts the prompt genuinely underdetermined — how to
carry the slice (`Fin n` subtype vs. side-condition vs. `ℕ`-indexed), how much of
the two-directional theorem to state, and whether to trust or silently correct the
garbled `∏(Σ)` witness formula: a third of the agents independently identified that
the literal family is not Boolean on the slice and substituted the paper's
`Σ(∏)` form.
