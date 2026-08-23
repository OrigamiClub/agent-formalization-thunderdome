# Glaisher's Theorem — 20-Agent Independent Formalization Comparison

## Method

20 independent, context-isolated agents were each given the same natural-language
statement of Glaisher's theorem (for fixed `k ≥ 2`: partitions of `n` with no part
divisible by `k` ↔ equinumerous with partitions of `n` where no part repeats `k` or
more times) and asked to produce a Lean 4 `theorem ... := by sorry` capturing only
the *statement* (no proof, no compiler available), plus a short note on encoding
choices.

Comparison, as requested, in two passes:

1. **Bridging** — determine whether pairs/groups of formalizations that differ
   syntactically are provably equivalent, and classify *how hard* the bridge is
   (pure notation vs. a short standard lemma vs. a real — if mechanical — equivalence
   construction).
2. **Lexicographic "looks-good-enough" check** — group formalizations that are
   textually identical (mod alpha-renaming of variables) once auxiliary named
   definitions are inlined.

No compiler was used; all bridge claims are argued from known Mathlib facts, not
machine-checked.

## Headline finding: real structural diversity (unlike GVB)

Unlike the Gilbert–Varshamov exercise, agents genuinely diverged along three
independent axes:

| Axis | Split |
|---|---|
| **Partition representation** | `Nat.Partition n` (Mathlib's bundled structure) — 16 agents, vs. a raw `Multiset ℕ` predicate (`∀x∈s,0<x` ∧ `s.sum=n`) defined from scratch — 4 agents (01, 02, 05, 13) |
| **Cardinality mechanism** | `Nat.card` of a subtype (14 agents) vs. `Set.ncard` of a set-builder (5 agents: 02, 08, 13, 14, 15) vs. `Finset.card` of a `Finset.univ.filter` (1 agent: 16) |
| **Scope of the "occurs < k times" condition** | quantified only over parts that occur, `∀ i ∈ p.parts, count i < k` (16 agents) vs. quantified over *all* naturals, `∀ i, count i < k` (4 agents: 03, 04, 11, 17) — several of these agents explicitly note in their own comments that this is equivalent since `count i = 0` for non-occurring `i` |

This gives **6 distinct lexicographic groups** (exact match after alpha-renaming),
ranging in size from 8 down to 1 agent — see the table below.

## Lexicographic groups

| Group | Representation | Cardinality mechanism | Scope | Agents | Size |
|---|---|---|---|---|---|
| G1 | `Nat.Partition` | `Nat.card` | scoped | 06, 07, 09, 10, 12, 18, 19, 20 | 8 |
| G2 | `Nat.Partition` | `Nat.card` | unscoped | 03, 04, 11, 17 | 4 |
| G3 | `Nat.Partition` | `Set.ncard` | scoped | 08, 14, 15 | 3 |
| G4 | raw `Multiset` | `Nat.card` | scoped | 01, 05 | 2 |
| G5 | raw `Multiset` | `Set.ncard` | scoped | 02, 13 | 2 |
| G6 | `Nat.Partition` | `Finset.card(filter)` | scoped | 16 | 1 |

All content *within* a group is identical modulo variable naming (`i`/`j`/`x`/`p`
for the part, `p`/`c` for the partition object) and cosmetic phrasing — a `rfl`-level
lexicographic match.

## Bridging across groups (all groups ultimately form one equivalence class)

Taking **G1** (the largest group, `Nat.card` on a `Nat.Partition` subtype with the
condition scoped to `i ∈ p.parts`) as the reference form, every other group bridges
to it, each via a bridge of a different, escalating difficulty:

- **Tier 1 — pure notation (`rfl`-level):** `Set.ncard s` is *defined* as
  `Nat.card ↥s`, and for a set-builder `{p | P p}` the coercion `↥{p | P p}` is
  definitionally the subtype `{p // P p}`. So **G3 → G1** and (combined with Tier 3
  below) **G5 → G4** are bridged for free once the set-vs-subtype spelling is
  unfolded.
- **Tier 2 — a short, standard Mathlib lemma (not `rfl`, but mechanical):**
  - **G6 → G1**: `Finset.card (Finset.univ.filter P) = Nat.card {x // P x}` follows
    from `Nat.card_eq_fintype_card` plus `Fintype.card_subtype` — a couple of
    `simp`/`rw` steps, not a deep theorem.
  - **G2 → G1**: `(∀ i, p.parts.count i < k) ↔ (∀ i ∈ p.parts, p.parts.count i < k)`
    follows by a `by_cases i ∈ p.parts` split, using
    `Multiset.count_eq_zero_of_not_mem` for the negative case (`count i = 0 < k`
    since `k ≥ 2`). Several of the source agents (03, 11, 17) already spell out this
    exact argument in their own comments — a case of agents independently
    recognizing and documenting their own bridge.
- **Tier 3 — a real (but standard/mechanical) equivalence construction:**
  **G4/G5 → G1**: `Nat.Partition n` is *literally defined* in Mathlib as a structure
  with fields `parts : Multiset ℕ`, `parts_pos`, `parts_sum` — exactly the two
  conjuncts the raw-`Multiset` agents wrote out by hand as `IsPartition`. An
  `Equiv (Nat.Partition n) {s : Multiset ℕ // (∀ i ∈ s, 0 < i) ∧ s.sum = n}` is a
  few lines (repackage the three structure fields into a subtype pair and back),
  and `Nat.card_congr` transports the cardinality equality across it. This is the
  only tier that requires writing new supporting code rather than just unfolding
  definitions or invoking one lemma, but it is routine, standard "structure ≃
  subtype" boilerplate, not new mathematics.

**Conclusion:** despite six distinct lexicographic shapes, no agent's formalization
asserts a different theorem — every group is bridgeable to the same reference
statement, escalating from free (Tier 1) to a short lemma (Tier 2) to a small
explicit `Equiv` (Tier 3). All 20 formalizations correctly capture the same
`k ≥ 2` hypothesis, the same "not divisible by `k`" condition, and the same
"occurs fewer than `k` times" condition — no sign-flip, off-by-one, or missing
hypothesis was found in any of the 20.

Full per-agent table: [`glaisher_equivalence.csv`](glaisher_equivalence.csv).

## Compiled verification (update)

All 20 formalizations, plus every bridge tier claimed above, were actually compiled
against a live local Lean/Mathlib checkout — `leanprover/lean4:v4.29.0-rc3`, Mathlib
commit `777aaa61dcd2a1258d2b4962dbe983ede4d23b2e` (all 20 files batched into one
combined file, each in its own `namespace AgentNN`, to pay the one-time
`import Mathlib` elaboration cost once instead of 20 times).

**20/20 type-check cleanly** — only the expected `declaration uses sorry` warning
on each, confirming `Nat.Partition`'s API (`.parts`, `.count`, `Fintype`/`Nat.card`
instances) and the raw-`Multiset` encodings are all well-formed as written.

Every bridge tier from the table above was also written out as a real Lean proof
and compiled — see [`bridges.lean`](bridges.lean):

- **Tier 1** (`Set.ncard s = Nat.card {p // ...}`): closes by `rfl`.
- **Tier 2a** (`Finset.card(univ.filter P) = Nat.card {p // P p}`): closes by
  `rw [Nat.card_eq_fintype_card, Fintype.card_subtype]`.
- **Tier 2b** (unscoped `∀i, count i<k` ↔ scoped `∀i∈parts, count i<k`): closes by
  a `by_cases i ∈ s` split using `Multiset.count_eq_zero_of_notMem` — note the
  actual Mathlib lemma name is `count_eq_zero_of_notMem` (capital `M`, no
  underscore before `Mem`), not `count_eq_zero_of_not_mem` as guessed in the
  original report; corrected here after the compiler caught it.
- **Tier 3** (`Nat.Partition n ≃ {s : Multiset ℕ // (∀i∈s,0<i) ∧ s.sum=n}`): a
  genuine `Equiv` was constructed (`partitionEquivSubtype`) using
  `Nat.Partition`'s actual fields `parts`/`parts_pos`/`parts_sum` (confirmed by
  reading `Mathlib/Combinatorics/Enumerative/Partition/Basic.lean` in the local
  checkout — `parts_pos` takes its index *implicitly*, which required
  eta-expanding it as `fun i hi => p.parts_pos hi` rather than passing it directly
  as a field), and cardinality transport via `Nat.card_congr` + `Equiv.subtypeEquiv`
  compiles cleanly.

This upgrades every bridge claim in this report from "argued by inspection" to
machine-verified, and the one incorrect guess (the Mathlib lemma name) was caught
and fixed by the compiler rather than by re-reading documentation.

Full per-agent compile status is in the `compiled_lean_v4.29.0-rc3_mathlib_777aaa6`
and `compile_note` columns of [`glaisher_equivalence.csv`](glaisher_equivalence.csv).

## Caveat

Compilation was done in a single pinned Mathlib environment (777aaa6, Lean
v4.29.0-rc3). A different/newer Mathlib revision could behave differently — API
names and instance availability do shift over time, as illustrated by the lemma-name
correction above.
