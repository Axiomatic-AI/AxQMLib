/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerConcatenationDimension

/-!
# Nielsen & Chuang, Exercise 10.62 — concatenation gives an `[n₁n₂,1]` code

*(N&C §10.6.1, p. 482.)*

Show concatenating [n1,1] and [n2,1] stabilizer codes gives an [n1n2,1] stabilizer code.

## What the exercise asks, and the explicit construction

Concatenation encodes each of the `n₂` physical qubits of the **outer** `[n₂, 1]` code into a
separate block of `n₁` qubits using the **inner** `[n₁, 1]` code, for `n₁n₂` physical qubits total.
The exercise asks to write down generators for the stabilizer of the concatenated code *explicitly*
and read off that the result is an `[n₁n₂, 1]` code. The explicit generators are:

* for each of the `n₂` blocks, the `n₁ − 1` **inner** generators acting on that block (identity on
  the others) — `n₂ (n₁ − 1)` generators;
* the `n₂ − 1` **outer** generators, each an `n₂`-qubit Pauli whose single-qubit factor on every
  block is replaced by the inner code's logical encoding `X̄^x Z̄^z` of that factor —
  `n₂ − 1` generators.

That is `n₂ (n₁ − 1) + (n₂ − 1) = n₁n₂ − 1` generators on `n₁n₂` qubits, and they must pairwise
commute and be independent; then Proposition 10.5 gives a `2^{n₁n₂ − (n₁n₂ − 1)} = 2^1`-dimensional
code space, i.e. `k = 1`. Establishing exactly these four facts (count, commutation, independence,
`k = 1` dimension) for the explicit generators is the formalisation.

## The model

An `[n, 1]` code is modelled abstractly by `StabCode1 g` (`n = g + 1`): its `g` generators and its
logical `X̄, Z̄`, bundled with the Pauli-commutation / check-row-independence conditions. "Pairwise
commute" is the mod-2 vanishing of the symplectic (twisted) inner product `ω` of check rows
(Exercise 10.33, `pauliString_commute_iff_symplecticForm`); "independent" is `𝔽₂`-linear
independence of the `2n`-bit check rows (Proposition 10.3); and the `[n₁n₂, 1]` dimension count is
the honest `Module.finrank ℂ V_S = 2^k` of Proposition 10.5 (`stabilizedSubspace_finrank`). Every
statement is about `Fin n → Fin 4` Pauli index data, `ZMod 2`, `Matrix`, and `Submodule` /
`Module.finrank` on the concrete register. Compare the stabilizer exercises 10.53
(`Concrete/StandardFormEncodedZ`), 10.54 (`Concrete/StabilizerStandardForm`) and 10.57 (the
standard-form check matrices).

## Faithfulness

The generators are constructed **explicitly** (as N&C demands) for **arbitrary** inner and outer
codes `C₁ : StabCode1 g₁`, `C₂ : StabCode1 g₂` — no specific code, no added hypothesis, no fixed
dimension. All three defining properties of an `[n₁n₂, 1]` stabilizer code are proved outright:

* the register has `n₁n₂ = (g₂+1)(g₁+1)` qubits and there are exactly `n₁n₂ − 1` generators
  (`concatIdx_card`);
* the generators pairwise **commute** (`concatGen_commute`);
* their check rows are `𝔽₂`-**linearly independent** (`concatGen_checkRow_linearIndependent`,
  N&C Proposition 10.3: independent generators);
* hence, by Proposition 10.5, the code space is `2 = 2¹`-dimensional
  (`concat_stabilizedSubspace_finrank`) — exactly `k = 1`.

The `k = 1` conclusion is the genuine dimension of the stabilized subspace, not a mere generator
count, so independence is load-bearing and the statement is not weakened.

## The declarations

All declarations are in namespace `AxQM.Concrete`.

**Explicit generators + `𝔽₂` symplectic toolkit** (`Concrete/StabilizerConcatenation.lean`):

* `StabCode1` — an abstract `[g+1, 1]` stabilizer code: `g` generators + logical `X̄, Z̄`, with the
  fields "generators pairwise commute", "generator check rows linearly independent" (Prop 10.3),
  "`X̄, Z̄` each commute with every generator", and "`X̄` anticommutes with `Z̄`".
* `encStr` / `encStr_checkVec` — the inner encoding of a single-qubit Pauli `X^x Z^z` by the inner
  logical string `X̄^x Z̄^z`, and its check row `x · r(X̄) + z · r(Z̄)`.
* `ConcatIdx`, `concatRaw`, `concatGen` — the concatenated generator index
  `(Fin n₂ × Fin (n₁−1)) ⊕ Fin (n₂−1)`, the generators on the product qubit index
  `Fin n₂ × Fin n₁`, and their flattening onto `Fin (n₁n₂)` (`finProdFinEquiv`).
* `concatIdx_card` — **the count**: `Fintype.card (ConcatIdx g₁ g₂) = n₁n₂ − 1`.
* `concatGen_commute` — **commutation half**: the generators pairwise commute, via the block
  decomposition of `ω` over the `n₂` blocks (inner–inner, inner–encoded-outer via `X̄, Z̄`
  commuting with inner generators, encoded-outer–encoded-outer via the hyperbolic relation
  `ω(r(X̄), r(Z̄)) = 1`), reduced to operator commutation by Exercise 10.33.
* The reusable `𝔽₂`-symplectic toolkit: general-index `checkRowG` / `checkVecG`; `symplecticForm`
  bi-additivity / `symplecticForm_self = 0` / `symplecticForm_comm` / reindex-invariance
  (`symplecticForm_comp_sumMap`); and the hyperbolic-pair lemma
  `linearIndependent_sumElim_hyperbolic` (a linearly independent family orthogonal to a hyperbolic
  pair extends to a linearly independent one — the check-row form of "logical operators are
  independent of the stabilizer").

**Independence** (`Concrete/StabilizerConcatenationIndependence.lean`):

* `concatGen_checkRow_linearIndependent` — **independence half**: the `n₁n₂ − 1` concatenated check
  rows are `𝔽₂`-linearly independent. Proof by block restriction (`blockRestr`) onto each inner
  block, using the joint independence of the inner generators together with `X̄, Z̄`
  (`stabCode1_jointIndep`, from the hyperbolic-pair lemma) and the outer code's own independence.

**`[n₁n₂, 1]` parameter conclusion** (`Concrete/StabilizerConcatenationDimension.lean`):

* `concatIdxEquivFin` / `concatGenFin` — the generators reindexed off `ConcatIdx g₁ g₂` onto
  `Fin (n₁n₂ − 1)` (the `Fin (n − k)` shape Proposition 10.5 consumes), with the transported
  properties `concatGenFin_commute` and `concatGenFin_checkRow_linearIndependent`.
* `concat_stabilizedSubspace_finrank` — **Exercise 10.62's `[n₁n₂, 1]` conclusion**:
  `Module.finrank ℂ (stabilizedSubspace (concatGenFin C₁ C₂)) = 2`, i.e. `k = 1`, by Proposition
  10.5 (`Concrete/StabilizerCodeDimension.lean`, `stabilizedSubspace_finrank`) with `n = n₁n₂`,
  `k = 1`.

See the module docstrings of the four `Concrete/` files for the full rationale and worked proofs.
-/
