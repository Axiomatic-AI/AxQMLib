/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ConditionalPhaseShift
import AxQM.Postulates.API.ControlledUnitaryDecomposition
import AxQM.Postulates.API.ProjectorHamiltonian
import AxQM.Postulates.API.RelativePhaseToffoli
import AxQM.Postulates.API.Teleportation
import AxQM.Postulates.API.CnotPauliPropagation

/-!
# The marking oracle and the projector-Hamiltonian simulation circuit (N&C Exercise 6.7, Fig 6.4)

Nielsen & Chuang, §6.2 ("Quantum search as a quantum simulation", p. 258) simulates the search
Hamiltonian `H = |x⟩⟨x| + |ψ⟩⟨ψ|` (eq. 6.18) by alternately simulating its two projector summands.
**Figure 6.4** is the circuit for the first summand: it implements `exp(-i|x⟩⟨x|Δt)` using **two
oracle calls** flanking a single-qubit phase gate, a textbook *compute–phase–uncompute* circuit.
This file builds that circuit and proves its correctness; the statement of Exercise 6.7 is
in `AxQM/NC/Ch6/Exercise6_7.lean`.

## The marking oracle

For a marked pure state `x : PureState S`, the search oracle acts on a query register `S` together
with a response qubit by `O|q⟩|b⟩ = |q⟩|b ⊕ [q = x]⟩` — flip the response iff the query is the
marked state. Extended linearly this is exactly the self-adjoint involution

`markingOracle x = |x⟩⟨x| ⊗ X + (I − |x⟩⟨x|) ⊗ I`

(`X = pauliXGate`), which is N&C's oracle for a single marked item, faithful for an *arbitrary*
marked pure state `x` (generalising N&C's computational-basis marked item). We build it concretely
— a genuine unitary, no vacuous oracle-spec hypothesis — via `markingOracle_op_mem_unitary`
(a self-adjoint involution `M† = M`, `M² = I`, so `M ∈ unitary`, mirroring `controlledUnitary` and
`reflectionEvolution`). Its computational action is `markingOracle_op_tmul`.

## The simulation circuit (Fig 6.4)

`hamSimCircuit x Δt = O · (I ⊗ P(-Δt)) · O` with `O = markingOracle x` and `P(-Δt) =
phaseShiftGate (-Δt) = diag(1, e^{-iΔt})` on the response qubit: compute the marker with `O`, kick
the phase `e^{-iΔt}` onto the marked branch with `P(-Δt)`, and uncompute with the second `O`. Its
correctness is `hamSimCircuit_op_tmul_zero`: on a response qubit supplied in `|0⟩`, the circuit
maps `v ⊗ |0⟩` to `(exp(-i|x⟩⟨x|Δt) v) ⊗ |0⟩` for **every** query vector `v` — i.e. it acts as the
genuine projector-Hamiltonian propagator `x.projObservable.propagator 1 0 Δt`
(`ProjectorHamiltonian.lean`) on the query register and returns the response to `|0⟩`. The
proof reduces the operator to `|x⟩⟨x|⊗X + (I−|x⟩⟨x|)⊗I` on each factor and tracks the two branches
through the compute–phase–uncompute sandwich, using idempotence `|x⟩⟨x|² = |x⟩⟨x|` to collapse the
double oracle call and the propagator closed form `exp(-i|x⟩⟨x|Δt) v = v + (e^{-iΔt}−1)⟨x,v⟩|x⟩`.

`AxQM/NC/Ch6/Exercise6_7.lean` restates Fig 6.4's verification in terms of
`Evolution.evolvePure`, `PureState.tmul`, `qubitBasis`, `projObservable` and `propagator`. The
operator-level `hamSimCircuit_op_tmul_zero` (general `v`) is used in the proof there.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **Unitarity of the marking oracle** `|x⟩⟨x| ⊗ X + (I − |x⟩⟨x|) ⊗ I`. The operator is a
self-adjoint involution: writing `P = |x⟩⟨x|` (idempotent, `P² = P`, since `⟨x, x⟩ = 1`) and
`X = pauliXGate.op` (`X² = I`, `X† = X`), it equals its own adjoint, and `M · M = mapL P (X²) +
mapL (P(I−P)) (X) + mapL ((I−P)P) X + mapL ((I−P)²) I = mapL P I + mapL (I−P) I = mapL I I = I` (the
cross terms vanish by `P(I−P) = (I−P)P = 0`), so `M ∈ unitary`. Stated at the raw tensor head
`S.space ⊗ qubit.space` (where `star`/`adjoint` present a single head); it discharges the `unitary`
obligation of `markingOracle` by definitional equality with `(S ⊗ qubit).space`. -/
theorem markingOracle_op_mem_unitary (x : PureState S) :
    (TensorProduct.mapL (rankOne ℂ x.vec x.vec) pauliXGate.op
      + TensorProduct.mapL (1 - rankOne ℂ x.vec x.vec) 1)
      ∈ unitary (S.space ⊗[ℂ] qubit.space →L[ℂ] S.space ⊗[ℂ] qubit.space) := by
  set P : S.space →L[ℂ] S.space := rankOne ℂ x.vec x.vec with hP
  set X : qubit.space →L[ℂ] qubit.space := pauliXGate.op with hX
  have hPP : P * P = P := InnerProductSpace.isIdempotentElem_rankOne_self x.normalized
  have hXX : X * X = 1 := by
    have := congrArg Evolution.op pauliXGate_comp_pauliXGate
    rwa [Evolution.comp_op, Evolution.id_op, ← ContinuousLinearMap.mul_def] at this
  have hPQ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPP, sub_self]
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by rw [sub_mul, one_mul, hPQ, sub_zero]
  have hPQsum : P + (1 - P) = 1 := by abel
  have hadjP : adjoint P = P := by rw [hP, InnerProductSpace.adjoint_rankOne]
  have hadjX : adjoint X = X := by
    have := congrArg Evolution.op
      (Evolution.adjoint_eq_self_of_comp_self pauliXGate pauliXGate_comp_pauliXGate)
    rwa [Evolution.adjoint_op] at this
  have hadj1' : adjoint (1 : qubit.space →L[ℂ] qubit.space) = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  have hadjQ : adjoint (1 - P) = 1 - P := by
    rw [map_sub, hadjP]; rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  have hsa : star (TensorProduct.mapL P X + TensorProduct.mapL (1 - P) 1)
      = TensorProduct.mapL P X + TensorProduct.mapL (1 - P) 1 := by
    rw [ContinuousLinearMap.star_eq_adjoint, map_add, TensorProduct.adjoint_mapL,
      TensorProduct.adjoint_mapL, hadjP, hadjX, hadjQ, hadj1']
  have hinv : (TensorProduct.mapL P X + TensorProduct.mapL (1 - P) 1)
      * (TensorProduct.mapL P X + TensorProduct.mapL (1 - P) 1) = 1 := by
    rw [mul_add, add_mul, add_mul, ← TensorProduct.mapL_mul, ← TensorProduct.mapL_mul,
      ← TensorProduct.mapL_mul, ← TensorProduct.mapL_mul, hPP, hXX, hPQ, hQP, hQQ]
    simp only [TensorProduct.mapL_zero_left, add_zero, zero_add, mul_one, one_mul]
    rw [← TensorProduct.mapL_add_left, hPQsum, TensorProduct.mapL_one]
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩ <;> rw [hsa] <;> exact hinv

/-- **The marking oracle** `O = |x⟩⟨x| ⊗ X + (I − |x⟩⟨x|) ⊗ I` for a marked pure state `x`, as an
`Evolution` on the query register `S` tensored with a response qubit. It flips the response qubit
exactly when the query is in the marked state `x`: `O|q⟩|b⟩ = |q⟩|b ⊕ [q = x]⟩` on the computational
basis (`markingOracle_op_tmul`). This is N&C's search oracle for a single marked item (§6.2, the
`f(q) = [q = x]` bit-flip oracle), extended linearly to an arbitrary marked pure state. Unitarity is
`markingOracle_op_mem_unitary` (a self-adjoint involution). -/
def markingOracle (x : PureState S) : Evolution (S ⊗ qubit) where
  op := TensorProduct.mapL (rankOne ℂ x.vec x.vec) pauliXGate.op
      + TensorProduct.mapL (1 - rankOne ℂ x.vec x.vec) 1
  unitary := markingOracle_op_mem_unitary x

/-- The underlying operator of the marking oracle is `|x⟩⟨x| ⊗ X + (I − |x⟩⟨x|) ⊗ I`. -/
@[simp]
theorem markingOracle_op (x : PureState S) :
    (markingOracle x).op = TensorProduct.mapL (rankOne ℂ x.vec x.vec) pauliXGate.op
      + TensorProduct.mapL (1 - rankOne ℂ x.vec x.vec) 1 := rfl

/-- **Computational action of the marking oracle.** On a product `v ⊗ |b⟩` the oracle flips the
response `|b⟩` on the `|x⟩`-component of `v` and leaves the orthogonal complement's response alone:
`O(v ⊗ |b⟩) = (|x⟩⟨x| v) ⊗ |b + 1⟩ + ((I − |x⟩⟨x|) v) ⊗ |b⟩`. For `v = |q⟩` a marked/unmarked
computational basis state this is exactly the bit-flip oracle `|q⟩|b⟩ ↦ |q⟩|b ⊕ [q = x]⟩`. -/
theorem markingOracle_op_tmul (x : PureState S) (w : S.space) (b : Fin 2) :
    (markingOracle x).op (w ⊗ₜ[ℂ] (qubitBasis b).vec)
      = (rankOne ℂ x.vec x.vec w) ⊗ₜ[ℂ] (qubitBasis (b + 1)).vec
        + (w - rankOne ℂ x.vec x.vec w) ⊗ₜ[ℂ] (qubitBasis b).vec := by
  change ((TensorProduct.mapL (rankOne ℂ x.vec x.vec) pauliXGate.op
      + TensorProduct.mapL (1 - rankOne ℂ x.vec x.vec) 1 :
      S.space ⊗[ℂ] qubit.space →L[ℂ] S.space ⊗[ℂ] qubit.space))
      (w ⊗ₜ[ℂ] (qubitBasis b).vec)
    = (rankOne ℂ x.vec x.vec w) ⊗ₜ[ℂ] (qubitBasis (b + 1)).vec
      + (w - rankOne ℂ x.vec x.vec w) ⊗ₜ[ℂ] (qubitBasis b).vec
  rw [_root_.add_apply, TensorProduct.mapL_tmul, TensorProduct.mapL_tmul,
    pauliXGate_op_apply_qubitBasis, one_apply_eq_self,
    _root_.sub_apply, one_apply_eq_self]

/-- **The Figure 6.4 simulation circuit** `O · (I ⊗ P(-Δt)) · O` for `exp(-i|x⟩⟨x|Δt)`: the
marking oracle `O = markingOracle x`, then the response-qubit phase gate `P(-Δt) =
phaseShiftGate (-Δt) = diag(1, e^{-iΔt})`, then the marking oracle again — the
compute–phase–uncompute circuit of N&C §6.2 using **two** oracle calls. Its correctness (that it
implements the projector-Hamiltonian propagator on the query register) is
`hamSimCircuit_op_tmul_zero`. -/
def hamSimCircuit (x : PureState S) (Δt : ℝ) : Evolution (S ⊗ qubit) :=
  (markingOracle x).comp (((phaseShiftGate (-Δt)).onRight S).comp (markingOracle x))

/-- **Figure 6.4 implements `exp(-i|x⟩⟨x|Δt)` (operator form).** With the response qubit supplied in
`|0⟩`, the circuit acts on `v ⊗ |0⟩` as `(exp(-i|x⟩⟨x|Δt) v) ⊗ |0⟩` for every query vector `v` —
i.e. it realises the genuine projector-Hamiltonian propagator `x.projObservable.propagator 1 0 Δt`
on the query register and returns the response to `|0⟩`. The proof unfolds the two oracle calls via
`markingOracle_op_tmul`, evaluates the phase gate on the marked (`|1⟩`) branch (picking up
`e^{-iΔt}`) and the unmarked (`|0⟩`) branch (unchanged), collapses the double oracle call using the
idempotence facts `|x⟩⟨x|(|x⟩⟨x| v) = |x⟩⟨x| v` and `|x⟩⟨x|(v − |x⟩⟨x| v) = 0`, and matches the
propagator's closed form `exp(-i|x⟩⟨x|Δt) v = v + (e^{-iΔt} − 1)⟨x, v⟩ |x⟩`
(`projObservable_propagator_op_apply`). This op-level statement is the reusable handle Figure 6.5
conjugates by a state-preparation unitary `W` (with `|ψ⟩ = W|0⟩`). -/
theorem hamSimCircuit_op_tmul_zero (x : PureState S) (Δt : ℝ) (v : S.space) :
    (hamSimCircuit x Δt).op (v ⊗ₜ[ℂ] (qubitBasis 0).vec)
      = ((x.projObservable.propagator 1 0 Δt).op v) ⊗ₜ[ℂ] (qubitBasis 0).vec := by
  have hidem : rankOne ℂ x.vec x.vec (rankOne ℂ x.vec x.vec v) = rankOne ℂ x.vec x.vec v := by
    rw [← mul_apply_eq_comp, isIdempotentElem_rankOne_self x.normalized]
  have hP0 : rankOne ℂ x.vec x.vec (v - rankOne ℂ x.vec x.vec v) = 0 := by
    rw [map_sub, hidem, sub_self]
  have hc : Complex.exp ((↑(-Δt) : ℂ) * Complex.I) = Complex.exp (-(Complex.I * (↑Δt : ℂ))) := by
    push_cast; ring_nf
  change (((TensorProduct.mapL (rankOne ℂ x.vec x.vec) pauliXGate.op
        + TensorProduct.mapL (1 - rankOne ℂ x.vec x.vec) 1).comp
        ((TensorProduct.mapL (1 : S.space →L[ℂ] S.space) (phaseShiftGate (-Δt)).op).comp
          (TensorProduct.mapL (rankOne ℂ x.vec x.vec) pauliXGate.op
            + TensorProduct.mapL (1 - rankOne ℂ x.vec x.vec) 1))) :
        S.space ⊗[ℂ] qubit.space →L[ℂ] S.space ⊗[ℂ] qubit.space)
      (v ⊗ₜ[ℂ] (qubitBasis 0).vec)
    = ((x.projObservable.propagator 1 0 Δt).op v) ⊗ₜ[ℂ] (qubitBasis 0).vec
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  simp only [_root_.add_apply, _root_.sub_apply,
    one_apply_eq_self, map_add, map_smul, TensorProduct.mapL_tmul,
    pauliXGate_op_apply_qubitBasis, phaseShiftGate_op_apply_qubitBasis,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_smul,
    TensorProduct.tmul_smul, hidem, hP0,
    show (0 : Fin 2) + 1 = 1 from rfl, show (1 : Fin 2) + 1 = 0 from rfl,
    sub_self, sub_zero, TensorProduct.zero_tmul, add_zero, zero_add]
  rw [PureState.projObservable_propagator_op_apply, hc, rankOne_apply,
    TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
  congr 1
  module

end AxQM
