/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuditKroneckerGate
import AxQM.Postulates.API.DeutschGateRegisterBridge
import AxQM.Concrete.DeutschTensorSplit

/-!
# The Deutsch gate placed on the leading three wires as `deutschGate α ⊗ identity` (N&C Ex 4.44)

The Deutsch-gate universality reduction (Nielsen & Chuang, Exercise 4.44) places
the gate `G = C²(iR_x(πα))` on three wires of a larger register and needs to name the resulting
`Evolution` as the physical Deutsch gate acting on those three wires while the remaining wires are
untouched — the tensor product `G ⊗ 𝟙`. This file supplies that identification, composing three
bridges into the general **register tensor-split** of a placed Deutsch gate.

Fix a wire-splitting equivalence `e : Fin M ≃ Fin 3 ⊕ Fin n` (three leading wires plus `n` further
wires) and a `rest`-register encoding `restEnc : (Fin n → Fin 2) ≃ Fin r`. Against the combined
encoding `Concrete.regTensorEnc e restEnc : (Fin M → Fin 2) ≃ Fin (8 · r)`, the two-control
single-qubit wire gate placing the Deutsch target `iR_x(πα)` on the leading target wire
`e.symm (inl 2)` with controls the leading wires `e.symm (inl 0)`, `e.symm (inl 1)` promotes to

  `quditGate (…placement…)
    = Evolution.congr (quditProdIso 8 r).symm
        ((Evolution.congr threeQuditIso (ccontrolledUnitary (iRxGate (πα)))).tmul Evolution.id)`,

i.e. the physical Deutsch gate transported to the eight-level register `qudit 8`, tensored with the
identity on the trailing `qudit r`. (`deutschGate α = ccontrolledUnitary (iRxGate (Real.pi·α))` is
defined in `AxQM/NC/Ch4/Exercise4_44.lean`, so the gate is named in its unfolded form
`ccontrolledUnitary (iRxGate (Real.pi·α))`, definitionally `deutschGate α`.)

## The proof, by composition of three bridges

1. **Matrix tensor-split** (`Concrete.mcCtrlSingleQubit_regTensorEnc_eq_kroneckerFin`,
   `Concrete/DeutschTensorSplit.lean`): the placement matrix factors as
   `kroneckerFin (ccontrolledMatFin8 (iRxMat (πα))) 1`, and the `Fin 8` factor
   `ccontrolledMatFin8 g` *is* the base three-wire placement
   `mcCtrlSingleQubit finThreeRegEnc {0, 1} 2 g`
   (`Concrete.ccontrolledMatFin8_eq_mcCtrlSingleQubit`). Transported through `quditGate` by
   `quditGate_congr` (an evolution is determined by its matrix).
2. **`quditGate` of a Kronecker product** (`quditGate_kroneckerFin_eq_congr_tmul`,
   `Postulates/API/QuditKroneckerGate.lean`): the promoted packed Kronecker product is the tensor of
   the two factors' `quditGate`s, transported along the register-factoring isomorphism
   `quditProdIso 8 r`.
3. **The base three-wire bridge** (`congr_threeQuditIso_deutschGate_eq_quditGate_mcCtrlSingleQubit`,
   `Postulates/API/DeutschGateRegisterBridge.lean`): the leading factor's `quditGate` is
   `deutschGate α` transported to `qudit 8`; the trailing factor's is `quditGate 1 = Evolution.id`
   (`quditGate_one_eq_id`).

The general placement on *arbitrary* distinct wires reduces to this leading-three-wires case by the
wire relabelling of `AxQM/Concrete/WireGateRelabel.lean`.
-/

namespace AxQM

open Matrix Concrete

noncomputable section

/-- **The leading-three-wires placement of the Deutsch gate is `deutschGate α ⊗ 𝟙`** (Nielsen &
Chuang, Exercise 4.44). For a wire-splitting equivalence `e : Fin M ≃ Fin 3 ⊕ Fin n`
and a `rest`-register encoding `restEnc : (Fin n → Fin 2) ≃ Fin r`, the two-control single-qubit
wire gate placing the Deutsch target `iR_x(πα)` on the leading target wire `e.symm (inl 2)` with
controls the leading wires `e.symm (inl 0)`, `e.symm (inl 1)` of the tensor-split encoding
`regTensorEnc e restEnc`, promoted to an evolution, is the physical Deutsch gate transported to the
eight-level register `qudit 8` tensored with the identity on the trailing `qudit r`:

  `quditGate (…placement…)
    = Evolution.congr (quditProdIso 8 r).symm
        ((Evolution.congr threeQuditIso (ccontrolledUnitary (iRxGate (Real.pi·α)))).tmul
          Evolution.id)`.

Composes the matrix tensor-split `mcCtrlSingleQubit_regTensorEnc_eq_kroneckerFin` (transported
through `quditGate` by `quditGate_congr`), the `quditGate`-of-Kronecker bridge
`quditGate_kroneckerFin_eq_congr_tmul`, the base three-wire bridge
`congr_threeQuditIso_deutschGate_eq_quditGate_mcCtrlSingleQubit`, and `quditGate_one_eq_id` for the
trailing identity factor. As `deutschGate α = ccontrolledUnitary (iRxGate (Real.pi·α))` is defined
in `AxQM/NC/Ch4/Exercise4_44.lean`, the gate is named in its unfolded form. -/
theorem quditGate_mcCtrlSingleQubit_regTensorEnc_eq_congr_tmul_ccontrolledUnitary
    {M n r : ℕ} (e : Fin M ≃ Fin 3 ⊕ Fin n) (restEnc : (Fin n → Fin 2) ≃ Fin r) (α : ℝ) :
    quditGate (mcCtrlSingleQubit_mem_unitaryGroup (regTensorEnc e restEnc)
        {e.symm (Sum.inl 0), e.symm (Sum.inl 1)} (e.symm (Sum.inl 2))
        (iRxMat_mem_unitaryGroup (Real.pi * α)))
      = Evolution.congr (quditProdIso 8 r).symm
          ((Evolution.congr threeQuditIso (ccontrolledUnitary (iRxGate (Real.pi * α)))).tmul
            Evolution.id) := by
  have hbase := mcCtrlSingleQubit_mem_unitaryGroup finThreeRegEnc {0, 1} 2
    (iRxMat_mem_unitaryGroup (Real.pi * α))
  have hone : (1 : Matrix (Fin r) (Fin r) ℂ) ∈ Matrix.unitaryGroup (Fin r) ℂ := Submonoid.one_mem _
  have hkron := kroneckerFin_mem_unitaryGroup hbase hone
  have hmat : mcCtrlSingleQubit (regTensorEnc e restEnc)
        {e.symm (Sum.inl 0), e.symm (Sum.inl 1)} (e.symm (Sum.inl 2)) (iRxMat (Real.pi * α))
      = kroneckerFin (mcCtrlSingleQubit finThreeRegEnc {0, 1} 2 (iRxMat (Real.pi * α))) 1 := by
    rw [← ccontrolledMatFin8_eq_mcCtrlSingleQubit]
    exact mcCtrlSingleQubit_regTensorEnc_eq_kroneckerFin e restEnc (iRxMat (Real.pi * α))
  rw [quditGate_congr _ hkron hmat, quditGate_kroneckerFin_eq_congr_tmul hbase hone hkron,
    ← congr_threeQuditIso_deutschGate_eq_quditGate_mcCtrlSingleQubit, quditGate_one_eq_id]

end

end AxQM
