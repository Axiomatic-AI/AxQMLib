/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PhaseFlipProjectorCode

/-!
# Nielsen & Chuang, Exercise 10.9 — the phase-flip code protects against `{I, Pᵢ, Qᵢ}`

Prove three qubit phase flip code protects against error set {I,P1,Q1,P2,Q2,P3,Q3}.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 10.9 (p. 441).

The three-qubit **phase-flip code** encodes `|0_L⟩ = |+++⟩`, `|1_L⟩ = |−−−⟩`. "Protects against a
set of errors" is N&C's term (introduced on p. 440) for the **quantum error-correction conditions**
(Theorem 10.1, eq. (10.16)) `P Eᵢ† Eⱼ P = αᵢⱼ P` holding for a Hermitian coefficient matrix `α`.

`Pᵢ = |0⟩⟨0|` and `Qᵢ = |1⟩⟨1|` on qubit `i` decompose over the single-qubit spectral identities
`|0⟩⟨0| = ½(I + Z)`, `|1⟩⟨1| = ½(I − Z)`; hence each of `{I, P₁, Q₁, P₂, Q₂, P₃, Q₃}` is a **linear
combination** of `{I, Z₁, Z₂, Z₃}`, the set already shown correctable in **Exercise 10.8**. By N&C's
discretization principle (Theorem 10.2, p. 440 — a code correcting a set corrects every linear
combination of that set) the phase-flip code therefore protects against the projector set as well.
No fresh Knill–Laflamme calculation is needed (indeed `Pᵢ`, `Qᵢ` are not permutations of the `±`
basis, so a direct check would be harder): correctability is inherited from `{I, Z₁, Z₂, Z₃}`.

The formalisation is in `AxQM/Postulates/API/PhaseFlipProjectorCode.lean`:

* `AxQM.qubitZeroProj` / `AxQM.qubitOneProj` — the single-qubit
  computational-basis projectors `|0⟩⟨0|`, `|1⟩⟨1|`; with
  `AxQM.qubitZeroProj_add_qubitOneProj_eq_one` (completeness `|0⟩⟨0| + |1⟩⟨1| = 1`) and the
  spectral identities `AxQM.qubitZeroProj_eq_half_one_add_pauliZ` /
  `AxQM.qubitOneProj_eq_half_one_sub_pauliZ` (`|0⟩⟨0| = ½(I + Z)`, `|1⟩⟨1| = ½(I − Z)`).
* `AxQM.phaseFlipFullError` — the error set `{I, P₁, Q₁, P₂, Q₂, P₃, Q₃}` as operators on
  the register, each `Pᵢ`/`Qᵢ` the genuine single-wire computational-basis projector
  `|0⟩⟨0|`/`|1⟩⟨1|`.
* `AxQM.phaseFlipRecombineMatrix` — the `4 × 7` matrix realising each error as a linear
  combination of `phaseFlipErrorOp = {I, Z₁, Z₂, Z₃}`; `AxQM.phaseFlipFullError_recombine`
  proves the pointwise identity (`Pᵢ = ½(I + Zᵢ)`, `Qᵢ = ½(I − Zᵢ)`).
* `AxQM.phaseFlipCode_satisfiesQECConditions_fullErrorSet` — **Exercise 10.9**:
  `SatisfiesQECConditions phaseFlipCodeProj phaseFlipFullError`, via
  `SatisfiesQECConditions.recombine` applied to Exercise 10.8
  (`phaseFlipCode_satisfiesQECConditions`; see `AxQM/NC/Ch10/Exercise10_8.lean`).

The discretization core — `SatisfiesQECConditions.recombine` (the QEC-predicate form of
N&C Theorem 10.2) and the Knill–Laflamme lemma
`ContinuousLinearMap.SatisfiesKLConditions.recombine` — is in
`AxQM/Postulates/API/QuantumErrorCorrection.lean` and
`ToMathlib/Analysis/InnerProductSpace/QuantumErrorCorrection.lean`.
-/
