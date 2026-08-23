# Glaisher's theorem — formalization notes (agent 06)

I represented "a partition of `n`" using Mathlib's built-in `Nat.Partition n`
structure, whose data is a multiset `parts : Multiset ℕ` of positive natural
numbers with `parts.sum = n`; I did not reinvent partitions from scratch,
relying instead on this existing Mathlib type and its `parts` field.

The condition "no part is divisible by `k`" is encoded directly on the
multiset as `∀ x ∈ p.parts, ¬ (k ∣ x)`. The condition "every part occurs at
most `k − 1` times" (equivalently, strictly fewer than `k` times) is encoded
via `Multiset.count`, as `∀ x ∈ p.parts, p.parts.count x < k`, i.e. the
multiplicity of every occurring part value is bounded below `k`.

I stated the theorem as a cardinality equality, `Nat.card` of the subtype of
`Nat.Partition n` satisfying the first predicate equals `Nat.card` of the
subtype satisfying the second, rather than exhibiting an explicit bijection
— this matches the natural-language statement "the number of partitions ...
equals the number of partitions ..." most directly and avoids committing to
a specific (Glaisher) bijection construction, which belongs in the proof,
not the statement.

The parameter `k` is universally quantified with hypothesis `hk : 2 ≤ k`,
and `n` is an arbitrary natural number (including `n = 0`, where both counts
are `1`, corresponding to the empty partition). I am fairly confident about
the field name `parts` and the constraint fields `parts_pos`/`parts_sum` on
`Nat.Partition`, though I did not verify compilation since no Lean compiler
was available in this task.
