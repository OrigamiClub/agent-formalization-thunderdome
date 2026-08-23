# Glaisher's theorem — formalization notes (agent_12)

I represented "a partition of `n`" using Mathlib's `Nat.Partition n` structure,
which bundles a multiset `parts : Multiset ℕ` together with proofs that all
parts are positive (`parts_pos`) and that they sum to `n` (`parts_sum`). This
avoids re-deriving partition machinery and gives direct access to the
multiset of parts via `p.parts`.

The two conditions are encoded directly on that multiset: "no part divisible
by `k`" is `∀ i ∈ p.parts, ¬ (k ∣ i)`, and "every part occurs fewer than `k`
times" is `∀ i ∈ p.parts, p.parts.count i < k`, using `Multiset.count` for
multiplicity. I stated the theorem as an equality of `Nat.card` of the two
corresponding subtypes of `Nat.Partition n` (rather than an explicit
bijection), since `Nat.card` requires no `Fintype`/`Decidable` instances and
both subtypes are automatically finite (subtypes of the finite type
`Nat.Partition n`). The hypothesis `k ≥ 2` is taken as an explicit argument
`hk : 2 ≤ k`, matching the "fix an integer k ≥ 2" framing; taking `k = 2`
specializes to Euler's odd-parts/distinct-parts theorem. I was moderately
confident about the exact field names of `Nat.Partition` (`parts`,
`parts_pos`, `parts_sum`) but did not verify compilation since no Lean
compiler was available.
