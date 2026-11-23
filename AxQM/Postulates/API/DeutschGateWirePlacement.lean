/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DeutschGateTensorSplit
import AxQM.Postulates.API.QuditGateSubmatrix
import AxQM.Concrete.WireGateEncodingChange

/-!
# The Deutsch gate placed on the leading wires of *any* register encoding names `deutschGate α`
(N&C Ex 4.44)

The Deutsch-gate universality reduction (Nielsen & Chuang, Exercise 4.44) places
the gate `G = C²(iR_x(πα))` on three wires of a larger register `qudit (8·r)` and must name the
resulting `Evolution` as the physical Deutsch gate acting on those wires. The tensor-split bridge
`quditGate_mcCtrlSingleQubit_regTensorEnc_eq_congr_tmul_ccontrolledUnitary`
(`Postulates/API/DeutschGateTensorSplit.lean`) does this — but only for the *specific* register
encoding `regTensorEnc e restEnc`, which packs the leading three wires through the canonical
`finThreeRegEnc`. The universality argument, however, iterates placements against an
*arbitrary* encoding `fullEnc`. This file removes that restriction: it names `deutschGate α` for the
leading-wires placement against **any** encoding.

The bridge is a change of encoding. Fixing a wire-splitting `e : Fin M ≃ Fin 3 ⊕ Fin n` and a
`rest`-encoding `restEnc : (Fin n → Fin 2) ≃ Fin r`, an arbitrary encoding `fullEnc` and the
tensor-split encoding `regTensorEnc e restEnc` differ only by the permutation
`ρ = fullEnc.symm.trans (regTensorEnc e restEnc)` of the `8·r` basis indices, so their placements
differ by the reindex `submatrix ρ ρ` (`Concrete.mcCtrlSingleQubit_encoding_change`), which promotes
through `quditGate` to conjugation by the register-permutation gate `quditPerm ρ`
(`quditGate_submatrix_eq_conj`). Composing with the tensor-split bridge gives, for the leading-wires
placement against `fullEnc`,

  `quditGate (…placement against fullEnc…)
    = quditPerm ρ.symm
        * Evolution.congr (quditProdIso 8 r).symm
            ((Evolution.congr threeQuditIso (deutschGate α)).tmul Evolution.id)
        * quditPerm ρ`,

the physical Deutsch gate `deutschGate α` transported to `qudit 8` and tensored with the identity on
the trailing wires, conjugated by the basis relabelling that matches `fullEnc` to the tensor-split
encoding. (`deutschGate α = ccontrolledUnitary (iRxGate (Real.pi·α))` is defined in
`AxQM/NC/Ch4/Exercise4_44.lean`, so it is named in its unfolded form
`ccontrolledUnitary (iRxGate (Real.pi·α))`.)

The wires `e.symm (Sum.inl 0)`, `e.symm (Sum.inl 1)`, `e.symm (Sum.inl 2)` are an *arbitrary* triple
of distinct register wires (any distinct triple `a, b, j` arises as `e` ranges over the wire
splittings sending `a, b, j` to the leading three), so this names `deutschGate α` for a placement on
*any* three distinct wires of *any* encoding.
-/

namespace AxQM

open Matrix Concrete

noncomputable section

/-- **The Deutsch gate placed on the leading wires of any register encoding is `deutschGate α`
transported and conjugated by the encoding permutation** (Nielsen & Chuang, Exercise 4.44). For an
arbitrary encoding `fullEnc : (Fin M → Fin 2) ≃ Fin (8·r)`, a wire-splitting
`e : Fin M ≃ Fin 3 ⊕ Fin n` and a `rest`-encoding `restEnc : (Fin n → Fin 2) ≃ Fin r`, the
two-control single-qubit wire gate placing the Deutsch target `iR_x(πα)` on the leading target wire
`e.symm (Sum.inl 2)` with controls `e.symm (Sum.inl 0)`, `e.symm (Sum.inl 1)`, promoted to an
evolution, is the physical Deutsch gate `deutschGate α` transported to `qudit 8` and tensored with
the identity on the trailing `qudit r`, conjugated by the basis-permutation gate `quditPerm ρ` for
`ρ = fullEnc.symm.trans (regTensorEnc e restEnc)`:

  `quditGate (mcCtrlSingleQubit fullEnc {e⁻¹(inl 0), e⁻¹(inl 1)} (e⁻¹(inl 2)) (iRxMat (πα)))
    = quditPerm ρ.symm
        * Evolution.congr (quditProdIso 8 r).symm
            ((Evolution.congr threeQuditIso (ccontrolledUnitary (iRxGate (πα)))).tmul Evolution.id)
        * quditPerm ρ`.

The tensor-split bridge `quditGate_mcCtrlSingleQubit_regTensorEnc_eq_congr_tmul_ccontrolledUnitary`
supplies the identity against `regTensorEnc e restEnc`; the change of encoding to `fullEnc` is the
reindex `submatrix ρ ρ` (`Concrete.mcCtrlSingleQubit_encoding_change`) promoted to conjugation by
`quditPerm ρ` (`quditGate_submatrix_eq_conj`), with the two placements' matrices matched by
`quditGate_congr`. As `deutschGate α = ccontrolledUnitary (iRxGate (Real.pi·α))` is defined in
`AxQM/NC/Ch4/Exercise4_44.lean`, the gate is named in its unfolded form. -/
theorem quditGate_mcCtrlSingleQubit_eq_conj_congr_tmul_ccontrolledUnitary {M n r : ℕ}
    (fullEnc : (Fin M → Fin 2) ≃ Fin (8 * r)) (e : Fin M ≃ Fin 3 ⊕ Fin n)
    (restEnc : (Fin n → Fin 2) ≃ Fin r) (α : ℝ) :
    quditGate (mcCtrlSingleQubit_mem_unitaryGroup fullEnc
        {e.symm (Sum.inl 0), e.symm (Sum.inl 1)} (e.symm (Sum.inl 2))
        (iRxMat_mem_unitaryGroup (Real.pi * α)))
      = quditPerm (fullEnc.symm.trans (regTensorEnc e restEnc)).symm
        * Evolution.congr (quditProdIso 8 r).symm
            ((Evolution.congr threeQuditIso
              (ccontrolledUnitary (iRxGate (Real.pi * α)))).tmul Evolution.id)
        * quditPerm (fullEnc.symm.trans (regTensorEnc e restEnc)) := by
  set ρ := fullEnc.symm.trans (regTensorEnc e restEnc) with hρ
  have hbase := mcCtrlSingleQubit_mem_unitaryGroup (regTensorEnc e restEnc)
    {e.symm (Sum.inl 0), e.symm (Sum.inl 1)} (e.symm (Sum.inl 2))
    (iRxMat_mem_unitaryGroup (Real.pi * α))
  have hfull := mcCtrlSingleQubit_mem_unitaryGroup fullEnc
    {e.symm (Sum.inl 0), e.symm (Sum.inl 1)} (e.symm (Sum.inl 2))
    (iRxMat_mem_unitaryGroup (Real.pi * α))
  have hmat : mcCtrlSingleQubit fullEnc {e.symm (Sum.inl 0), e.symm (Sum.inl 1)}
        (e.symm (Sum.inl 2)) (iRxMat (Real.pi * α))
      = (mcCtrlSingleQubit (regTensorEnc e restEnc) {e.symm (Sum.inl 0), e.symm (Sum.inl 1)}
          (e.symm (Sum.inl 2)) (iRxMat (Real.pi * α))).submatrix ρ ρ :=
    mcCtrlSingleQubit_encoding_change (regTensorEnc e restEnc) fullEnc _ _ _
  have hsub : (mcCtrlSingleQubit (regTensorEnc e restEnc) {e.symm (Sum.inl 0), e.symm (Sum.inl 1)}
      (e.symm (Sum.inl 2)) (iRxMat (Real.pi * α))).submatrix ρ ρ
      ∈ Matrix.unitaryGroup (Fin (8 * r)) ℂ := hmat ▸ hfull
  rw [quditGate_congr hfull hsub hmat, quditGate_submatrix_eq_conj hbase ρ hsub,
    quditGate_mcCtrlSingleQubit_regTensorEnc_eq_congr_tmul_ccontrolledUnitary e restEnc α]

end

end AxQM
