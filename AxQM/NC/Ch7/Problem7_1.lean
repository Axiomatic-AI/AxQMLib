/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.FieldTheory.Finite.GeneratorMulPermutation

/-!
# Nielsen & Chuang, Problem 7.1 (Efficient temporal labeling)

Efficient temporal labeling: can one construct O(poly(n))-gate circuits cyclically permuting all
diagonal elements except |0ⁿ⟩⟨0ⁿ|?

(N&C p. 346.) This is the temporal-labeling / effective-pure-state trick from NMR quantum computing:
to distil a pseudo-pure state from a highly mixed thermal state one runs the computation several
times, each time first cyclically permuting the populations of the excited states (the diagonal
entries of the density matrix other than the ground-state `|0ⁿ⟩⟨0ⁿ|` term) and averaging the
results. The technique is only useful if each such cyclic permutation is realised by a circuit with
polynomially many gates.

**Answer: yes.** Identify the `n`-qubit register with the finite field `GF(2ⁿ)`, whose elements are
the `2ⁿ` computational-basis labels (`0` is `|0ⁿ⟩`). Its multiplicative group `GF(2ⁿ)ˣ` is cyclic of
order `2ⁿ − 1`; for a generator `g`, the map `x ↦ g · x` (left multiplication)

* fixes `0` (leaving the `|0ⁿ⟩⟨0ⁿ|` population alone),
* is `𝔽₂`-linear, and
* cyclically permutes the `2ⁿ − 1` non-zero labels as a single `(2ⁿ − 1)`-cycle.

The `𝔽₂`-linearity is what makes it **efficient**: `GF(2ⁿ)` is an `n`-dimensional `𝔽₂`-space, so the
permutation is an `n × n` `𝔽₂` matrix — a linear feedback shift register on `n` wires — and any
invertible `𝔽₂`-linear map is a circuit of `O(n²)` `CNOT` gates (standard linear-reversible
synthesis). A *generic* permutation of the `2ⁿ` states would instead require exponentially many
gates, so linearity is precisely the property the problem is asking for. This is the general-`n`
version of the concrete three-qubit partial cyclic permutation of Exercise 4.27
(`AxQM/Concrete/PartialCyclicPermutation.lean`), which fixes `|000⟩` and cycles
`1 → 2 → ⋯ → 7 → 1`.

The content is pure finite-field / permutation-group mathematics — the existence of an
`𝔽₂`-linear cyclic permutation of `GF(2ⁿ)` fixing `0`.

## The formalisation

In `ToMathlib/FieldTheory/Finite/GeneratorMulPermutation.lean`:

* `Units.mulLeft_pow_apply` — iterating left multiplication by a unit `u` is left multiplication by
  a power: `(u.mulLeft ^ k) x = ↑(u ^ k) * x` (a general monoid fact, the engine of the orbit
  computation).
* `Units.exists_pow_mulLeft_apply_eq` — for a generator `g` of `Kˣ` (`K` a `GroupWithZero`, e.g. a
  field), `Units.mulLeft g` acts transitively on the non-zero elements: any non-zero `x` reaches any
  non-zero `y` in finitely many steps. This is the "single cyclic orbit through all the non-zero
  diagonal elements".
* `Units.isCycle_mulLeft` — for a non-identity generator, `Units.mulLeft g` is a genuine cycle
  (`Equiv.Perm.IsCycle`); its support is the non-zero elements.
* `GaloisField.card_units` — `GF(2ⁿ)` has `2ⁿ − 1` non-zero elements (the length of the cycle).
* `GaloisField.exists_linear_isCycle_perm` — the cyclic-permutation half: for `n ≥ 2` there is an
  `𝔽₂`-linear equivalence `L` of `GF(2ⁿ)` with `L 0 = 0`, `L.toEquiv` an `IsCycle`, and `L.toEquiv`
  transitive on the non-zero elements.
* `GaloisField.exists_linear_isCycle_perm_transvecCount` — the **full affirmative answer**: for
  `n ≥ 2` there is such an `L` (fixing `0`, `IsCycle`, transitive on non-zeros) together with a
  basis `b` and a list `T` of transvections with `LinearMap.toMatrix b b L = (T.map toMatrix).prod`
  and `T.length ≤ 2 * n²`. Since an `𝔽₂`-transvection with coefficient `1` is a `CNOT` gate, `T` is
  an explicit reversible circuit of `≤ 2n²` `CNOT`s realising the cyclic permutation — the efficient
  (`O(poly(n))`-gate) circuit the problem asks for.
* `GaloisField.transvecCount_isBigO_sq` — the asymptotics `2n² = O(n²)`, confirming the gate count
  is polynomial in `n`.

The gate-count bound is specialised from the generic length-bounded linear-reversible synthesis in
`ToMathlib/LinearAlgebra/Matrix/TransvectionCount.lean`
(`Matrix.exists_transvecStruct_prod_length_le`
and `Matrix.exists_transvecStruct_prod_toMatrix_length_le`), itself a length-tracked re-run of
Mathlib's transvection reduction (`Matrix.Pivot.exists_transvec_mul_diagonal_length`).

## Fidelity

* **Both halves of the claim are proved propositions.** The problem asks for an *efficient*
  (`O(poly(n))`-gate) *cyclic permutation*. Both are formalised: the cyclic structure
  (`exists_linear_isCycle_perm`) and the `O(n²)`-`CNOT` gate-count bound for the same permutation
  (`exists_linear_isCycle_perm_transvecCount`, `transvecCount_isBigO_sq`). Efficiency is not left to
  the linearity certificate alone — it is a proved gate count. `𝔽₂`-linearity is what makes it
  possible: `GF(2ⁿ)` is an `n`-dimensional `𝔽₂`-space, an `𝔽₂`-linear permutation is an `n × n`
  matrix, and Gaussian elimination writes it as `O(n²)` transvections (= `CNOT`s), whereas a generic
  permutation of the `2ⁿ` states needs exponentially many gates.

* **Scope of the cycle.** The `n = 1` case (`GF(2)`, a single non-zero state) is degenerate — there
  is nothing to permute — so the statements are for `n ≥ 2`; the transitivity and fixed-point
  content holds for all `n`.

* **The explicit `CNOT` list vs. the abstract gate count.** The gate count is proved via the
  transvection *count* (`T.length ≤ 2n²`), an `𝔽₂`-transvection being definitionally a `CNOT`; the
  concrete wiring of each `CNOT` onto physical qubits is the routine reading of a transvection and
  is not spelled out. The statements are pure finite-field / linear-algebra mathematics, with no
  quantum-circuit `Evolution` involved.
-/
