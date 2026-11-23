/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DeutschGateWirePlacement
import AxQM.Concrete.WireTripleSplit

/-!
# The Deutsch gate placed on *any distinct triple* of wires names `deutschGate α` (N&C Ex 4.44)

The general-wire naming `quditGate_mcCtrlSingleQubit_eq_conj_congr_tmul_ccontrolledUnitary`
(`Postulates/API/DeutschGateWirePlacement.lean`) names the physical Deutsch gate
`G = C²(iR_x(πα))` for a placement on the **leading** three wires `e.symm (Sum.inl 0/1/2)` of a
wire-splitting `e : Fin M ≃ Fin 3 ⊕ Fin n`. The register-realisation development, however, places
`G` on *arbitrary* distinct control/target wires `a, b, j`, existentially bound with no reference to
a splitting `e`. This file removes the leading-wire restriction: it names `deutschGate α` for a
placement on **any** distinct triple `a, b, j`.

The bridge is the `a, b, j → e` construction
(`Concrete.exists_wireSplitEquiv_of_distinct`, `Concrete/WireTripleSplit.lean`): three distinct
wires `a, b, j` are the three leading wires of *some* splitting `e : Fin M ≃ Fin 3 ⊕ Fin (M - 3)`,
and instantiating the leading-wire naming at that `e` names `deutschGate α` for the arbitrary-triple
placement. The two controls `a, b` become the leading control pair `e.symm (Sum.inl 0/1)` and the
target `j` the leading target `e.symm (Sum.inl 2)`, so the control *set* `{a, b}` and target `j`
match the leading-wire placement verbatim.

-/

namespace AxQM

open Matrix Concrete

noncomputable section

/-- **The Deutsch gate placed on any distinct triple of wires is `deutschGate α` transported and
conjugated by an encoding permutation** (Nielsen & Chuang, Exercise 4.44). For an
arbitrary register encoding `fullEnc : (Fin M → Fin 2) ≃ Fin (8·r)`, a `rest`-encoding
`restEnc : (Fin (M - 3) → Fin 2) ≃ Fin r`, and *any three distinct wires* `a, b, j : Fin M`, the
two-control single-qubit wire gate placing the Deutsch target `iR_x(πα)` on the target wire `j` with
controls `a, b`, promoted to an evolution, is the physical Deutsch gate `deutschGate α` transported
to `qudit 8` and tensored with the identity on the trailing `qudit r`, conjugated by the
basis-permutation gate `quditPerm ρ` for `ρ = fullEnc.symm.trans (regTensorEnc e restEnc)`, where
`e : Fin M ≃ Fin 3 ⊕ Fin (M - 3)` is a wire-splitting with `a, b, j` leading:

  `quditGate (mcCtrlSingleQubit fullEnc {a, b} j (iRxMat (πα)))
    = quditPerm ρ.symm
        * Evolution.congr (quditProdIso 8 r).symm
            ((Evolution.congr threeQuditIso (ccontrolledUnitary (iRxGate (πα)))).tmul Evolution.id)
        * quditPerm ρ`.

Immediate from the leading-wire naming
`quditGate_mcCtrlSingleQubit_eq_conj_congr_tmul_ccontrolledUnitary` at the splitting `e` produced by
`Concrete.exists_wireSplitEquiv_of_distinct`: substituting the leading-wire values
`e.symm (Sum.inl 0/1/2) = a/b/j` turns the leading-wire placement into the arbitrary-triple
placement `mcCtrlSingleQubit fullEnc {a, b} j (iRxMat (πα))`. As `deutschGate α = ccontrolledUnitary
(iRxGate (Real.pi·α))`, the gate is named in its unfolded form. -/
theorem quditGate_mcCtrlSingleQubit_distinct_eq_conj_congr_tmul_ccontrolledUnitary {M r : ℕ}
    (fullEnc : (Fin M → Fin 2) ≃ Fin (8 * r)) (restEnc : (Fin (M - 3) → Fin 2) ≃ Fin r)
    {a b j : Fin M} (hab : a ≠ b) (haj : a ≠ j) (hbj : b ≠ j) (α : ℝ) :
    ∃ e : Fin M ≃ Fin 3 ⊕ Fin (M - 3),
      quditGate (mcCtrlSingleQubit_mem_unitaryGroup fullEnc {a, b} j
          (iRxMat_mem_unitaryGroup (Real.pi * α)))
        = quditPerm (fullEnc.symm.trans (regTensorEnc e restEnc)).symm
          * Evolution.congr (quditProdIso 8 r).symm
              ((Evolution.congr threeQuditIso
                (ccontrolledUnitary (iRxGate (Real.pi * α)))).tmul Evolution.id)
          * quditPerm (fullEnc.symm.trans (regTensorEnc e restEnc)) := by
  obtain ⟨e, h0, h1, h2⟩ := exists_wireSplitEquiv_of_distinct a b j hab haj hbj
  refine ⟨e, ?_⟩
  subst h0 h1 h2
  exact quditGate_mcCtrlSingleQubit_eq_conj_congr_tmul_ccontrolledUnitary fullEnc e restEnc α

end

end AxQM
