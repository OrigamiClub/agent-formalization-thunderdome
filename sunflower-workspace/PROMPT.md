# Sunflower lemma (improved / log bound) — 100-agent independent formalization sweep

Run date: 2026-08-27. No comparison/bridging component this run — formalizations only.

## Target statement

The **improved sunflower lemma** (Alweiss–Lovett–Wu–Zhang 2019, "Improved bounds
for the sunflower lemma"; refined by Rao, and by Bell–Chueluecha–Warnke):

> There is an absolute constant `C` such that for all positive integers `k`, `r`,
> every finite family `W` of sets each of cardinality exactly `k` with
> `|W| > (C · r · log k)^k` contains a sunflower with `r` petals.
> Equivalently `f(k, r) ≤ (C · r · log k)^k`.

A **sunflower with `r` petals** is a family of `r` distinct sets `S₁, …, S_r` for
which there is a core set `Y` with `Sᵢ ∩ Sⱼ = Y` for all `i ≠ j` (so every element
in ≥ 2 of the sets is in all of them; the petals `Sᵢ \ Y` are pairwise disjoint).

## Exact prompt given to each agent

> You are agent {NNN} in an independent formalization diversity study. You are
> context-isolated: produce your answer with no coordination with any other agent.
>
> TASK: Produce a Lean 4 formalization of the *statement* of the improved sunflower
> lemma. Statement only — end every theorem with `:= by sorry`. Do NOT prove
> anything. You do NOT have a Lean compiler; work from knowledge of Mathlib.
>
> THE THEOREM (improved sunflower lemma; Alweiss–Lovett–Wu–Zhang 2019, refined by
> Rao and by Bell–Chueluecha–Warnke):
>
> A *sunflower with r petals* is a family of r distinct sets S₁,…,S_r for which
> there is a core set Y with Sᵢ ∩ Sⱼ = Y for every i ≠ j. (Every element contained
> in ≥ 2 of the sets is contained in all of them; the petals Sᵢ \ Y are pairwise
> disjoint.)
>
> The improved bound: there is an absolute constant C such that for all positive
> integers k and r, every finite family W of sets, each of cardinality exactly k,
> with |W| > (C · r · log k)^k contains a sunflower with r petals. Equivalently,
> writing f(k,r) for the sunflower function, f(k,r) ≤ (C r log k)^k.
>
> YOUR ENCODING CHOICES ARE YOURS TO MAKE: set representation (Finset over an
> ambient type, Set with a finiteness hypothesis, Finset (Finset α), an indexed
> family, …); which logarithm (Real.log, Real.logb 2, Nat.log 2, …) and how to
> handle k = 1 / k = 0 where log k is 0 or undefined; whether C is existentially
> quantified inside the theorem or supplied as a hypothesis vs a named constant;
> how you define "sunflower" (explicit core Y; or "pairwise intersections all
> coincide"; or a Mathlib sunflower predicate if you believe one exists — name it
> as best you can); whether petals must be nonempty; cardinality via Finset.card /
> Set.ncard / Nat.card; whether distinctness of members needs stating.
>
> DELIVERABLES — write exactly two files:
> 1. `sunflower-workspace/formalizations/agent_{NNN}.lean` — imports, any auxiliary
>    definitions, and the `theorem … := by sorry`. Self-contained.
> 2. `sunflower-workspace/formalizations/agent_{NNN}.md` — short note: form chosen,
>    encoding decisions and why, uncertainties (e.g. guessed Mathlib identifiers).
>
> Do not read any other agent's files. Do not create any other files. When both
> files are written, reply with a one-line summary of your chosen encoding.
