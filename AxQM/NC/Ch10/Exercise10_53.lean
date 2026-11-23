/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StandardFormEncodedZ

/-!
# Nielsen & Chuang, Exercise 10.53 — the encoded `Z` operators are independent of one another

*(N&C §10.5.7, p. 471.)*

Prove the encoded Z operators (from standard-form check matrix) are independent of one another.

## Context

For an `[n, k]` stabilizer code, putting the check matrix into **standard form** (10.111) — `X`-part
of rank `r`, with the `n` qubits split into blocks of sizes `r`, `n − k − r`, `k` — makes the
encoded logical operators transparent to define. Nielsen & Chuang give the `k` **encoded `Z`
operators** by the `k × 2n` check matrix `G_Z = [0 0 0 | A₂ᵀ 0 I]`: each is a pure product of `Z`'s
(zero `X`-part), with `Z`-part the `j`-th row of `[A₂ᵀ 0 I]` — the transpose block `A₂ᵀ` on the
first `r` qubits, `0` on the middle `n − k − r`, and the `k × k` identity `I` on the last `k` data
qubits (`A₂` is the arbitrary `r × k` block of the standard form (10.111)). This exercise asks to
prove these `k` operators are **independent of one another** — Nielsen & Chuang's eq. (10.82):
dropping any one strictly shrinks the group they generate. The identity block `I` is exactly what
makes this so: it forces the encoded-`Z` rows to be `𝔽₂`-linearly independent, which by
Proposition 10.3 is independence of the operators.

## Faithfulness

The theorem is stated at full generality: `A₂` is an arbitrary `r × k` `𝔽₂`-matrix and the block
sizes `r`, `s = n − k − r`, `k` are arbitrary, so the encoded-`Z` check matrix `[A₂ᵀ 0 I]` is the
general standard-form one — not a specific code. "Independent of one another" is
`Concrete.IndependentGenerators` (N&C eq. 10.82) verbatim, applied to the encoded-`Z` operators as
`PauliGroup (r + s + k)` elements. No hypothesis is added or the statement weakened; the proof is
Nielsen & Chuang's own (the identity block `⟹` linearly independent rows `⟹`, by the easy half of
Proposition 10.3, independent operators).

## Declarations

The formalisation is in `AxQM/Concrete/StandardFormEncodedZ.lean` (namespace `AxQM.Concrete`),
building on the Proposition 10.3 development (`AxQM/Concrete/StabilizerIndependence.lean`,
`AxQM/Concrete/CheckMatrix.lean`, `AxQM/Concrete/PauliGroup.lean`). Compare the sibling stabilizer
items: Proposition 10.3 (`AxQM/Concrete/StabilizerIndependence.lean`) and the five-qubit code
(`AxQM/Concrete/FiveQubitCode.lean`).

* `encodedZOp_independentGenerators` — **Exercise 10.53 itself**: for a standard-form code with
  block sizes `r, s, k` and top block `A₂`, the encoded `Z` operators `encodedZOp s A₂ : Fin k →
  PauliGroup (r + s + k)` satisfy `IndependentGenerators (encodedZOp s A₂)`.
* `encodedZOp` / `encodedZRow` — the encoded `Z` operators and their `Z`-supports (the rows of
  `[A₂ᵀ 0 I]`), the latter via a pure-`Z` `zIndexOf` index string.
* `encodedZRow_linearIndependent` / `encodedZOp_checkRow_linearIndependent` — the encoded-`Z` rows
  (resp. check rows) are `𝔽₂`-linearly independent, the linear-algebra core (the identity block).
* `encodedZOp_checkRowHom` — the `j`-th operator's check row is `(0 | encodedZRow s A₂ j)`.
* `independentGenerators_of_linearIndependent_of_hom`
  (in `AxQM/Concrete/StabilizerIndependence.lean`) — the "easy half" of Proposition 10.3:
  linearly independent check rows force independent generators, needing no `-I ∉ S` hypothesis.

See the module docstring of `AxQM/Concrete/StandardFormEncodedZ.lean` for the full rationale.
-/
