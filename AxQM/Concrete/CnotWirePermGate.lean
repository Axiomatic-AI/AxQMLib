/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliNormalizerZClear
import AxQM.Concrete.PermutationGate
import AxQM.Concrete.MultiControlledNot

/-!
# Concrete: the single `CNOT` matrix bridge — `permGate` of a one-control `mcNotPerm` is the
reindexed `cnotWireGate`

This file bridges the **two matrix incarnations of a single `CNOT`** that Nielsen & Chuang
**Problem 4.3(3)** puts side by side:

* the reversible-register gate `permGate enc (mcNotPerm {a} b hb)` — the permutation matrix on the
  flat register `Fin d` (`enc : (Fin m → Fin 2) ≃ Fin d`) of the one-control multiply-controlled
  `NOT` with control `a`, target `b`, the matrix underlying the register `Evolution`
  `AxQM.mcNotWireEvolution` (`Postulates/API/FourGateReversibleWire`); and
* the Clifford gate matrix `cnotWireGate a b` — the `CNOT`-fan building block of the Figure-4.19
  parity circuit (`Concrete/PauliStringParityCascade`), indexed by the bit strings `Fin m → Fin 2`.

The two are the same permutation (`mcNot {a} b = cnotPerm a b`, since a single control's control bit
is just that wire's value, `ctrlBit_singleton`), so the flat gate is exactly the bit-string gate
reindexed along `enc`:

`permGate enc (mcNotPerm {a} b hb) = (cnotWireGate a b).submatrix enc.symm enc.symm`.

This is the factor-level identity that lets the register `CNOT` fan `cnotFanIntoEvolution`
(`Postulates/API/CnotFanEvolution`) be identified — through `Matrix.toEuclideanCLM` — with the
reindexed matrix fan `Concrete.cnotFanInto` of Figure 4.19, chaining the Evolution-level Figure-4.19
circuit to the matrix-level parity collapse `pauliString_exp_smul_conj_cnotFanInto`.
-/

open Matrix

namespace AxQM.Concrete

variable {m : ℕ}

/-- **A one-control multiply-controlled `NOT` permutation is the `CNOT` bit-permutation.** For
control `a`, target `b` (`hb : b ∉ {a}`), the classical gate `mcNot {a} b` equals `cnotPerm a b`:
both flip the target bit `x b` by the single control bit `x a` (`ctrlBit {a} x = x a`,
`ctrlBit_singleton`) and leave every other wire unchanged. The pointwise identity behind the matrix
bridge `permGate_mcNotPerm_singleton_eq_submatrix_cnotWireGate`. -/
theorem mcNot_singleton_eq_cnotPerm (a b : Fin m) (x : Fin m → Fin 2) :
    mcNot {a} b x = cnotPerm a b x := by
  rw [mcNot, cnotPerm, ctrlBit_singleton]

/-- **The single-`CNOT` matrix bridge.** For control `a`, target `b` (`hb : b ∉ {a}`) and any
encoding `enc : (Fin m → Fin 2) ≃ Fin d` of the bit strings as the flat register `Fin d`, the
reversible-register gate matrix `permGate enc (mcNotPerm {a} b hb)` is exactly the Clifford `CNOT`
matrix `cnotWireGate a b` reindexed from bit strings to `Fin d` along `enc`:

`permGate enc (mcNotPerm {a} b hb) = (cnotWireGate a b).submatrix enc.symm enc.symm`.

Proved entrywise: both `(I, J)`-entries are the indicator of the same event, since the two gates
realise the same bit-string permutation (`mcNot_singleton_eq_cnotPerm`) and `enc` intertwines the
flat and bit-string index conventions (`I = enc y ↔ enc.symm I = y`, `Equiv.symm_apply_eq`). -/
theorem permGate_mcNotPerm_singleton_eq_submatrix_cnotWireGate {d : ℕ}
    (enc : (Fin m → Fin 2) ≃ Fin d) (a b : Fin m) (hb : b ∉ ({a} : Finset (Fin m))) :
    permGate enc (mcNotPerm {a} hb)
      = (cnotWireGate a b).submatrix enc.symm enc.symm := by
  ext I J
  rw [permGate_apply, Matrix.submatrix_apply, cnotWireGate, Matrix.of_apply, mcNotPerm_apply,
    mcNot_singleton_eq_cnotPerm]
  exact if_congr (Equiv.symm_apply_eq enc).symm rfl rfl

/-- **The matrix of a single `CNOT` step.** For distinct wires `a ≠ b`, the one-gate circuit
`cnotStep a b = [CNOT_{a→b}]` has matrix `cnotWireGate a b`. The reduction feeding the register
faithfulness `cnotWireEvolution_op` (`Postulates/API/CnotFanEvolution`) in its genuine-`CNOT`
branch. -/
theorem cnotStep_toMatrix_of_ne {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    CliffordCircuit.toMatrix (cnotStep a b) = cnotWireGate a b := by
  rw [cnotStep, dite_eq_right hab]
  simp only [CliffordCircuit.toMatrix, CliffordGate.toMatrix, mul_one]

end AxQM.Concrete
