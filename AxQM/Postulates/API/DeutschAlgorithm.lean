/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.KitaevPhaseEstimation
import AxQM.Postulates.API.RelativePhase
import AxQM.Postulates.API.CnotXBasis
import AxQM.Postulates.API.ControlledControlledUnitary

/-!
# AxQM.Postulates.API — Deutsch's one-bit algorithm engine

The reusable engine for **Deutsch's algorithm** (the one-bit *Deutsch–Jozsa* problem, Nielsen &
Chuang §1.4.3), the quantum algorithm realised optically in Exercise 7.13. It determines, with a
**single** query to a function `f : {0,1} → {0,1}`, the global property `f(0) ⊕ f(1)` — i.e. whether
`f` is *constant* (`f(0) ⊕ f(1) = 0`) or *balanced* (`= 1`).

* `deutschCircuit Uf` — the circuit `(H ⊗ I) · U_f · (H ⊗ H)`: a Hadamard on each qubit, the oracle
  `U_f`, then a Hadamard on the query (first) qubit.
* `IsDeutschOracle f Uf` — the defining property of the oracle for `f`: the reversible XOR oracle
  `U_f|x, y⟩ = |x, y ⊕ f(x)⟩` (`⊕` = `Fin 2` addition).
* `IsDeutschOracle.op_tmul_qubitMinus` — **phase kickback**:
  `U_f(|x⟩ ⊗ |−⟩) = (−1)^{f(x)}|x⟩ ⊗ |−⟩`. Feeding the answer register the `X`-eigenstate `|−⟩`
  turns the bit-flip oracle into a phase oracle, the mechanism of the algorithm (N&C eq. 1.43).
* `IsDeutschOracle.deutschCircuit_op` — the full circuit computation: on the input `|0⟩ ⊗ |1⟩`,
  `deutschCircuit U_f` produces `(−1)^{f(0)} |f(0) ⊕ f(1)⟩ ⊗ |−⟩` — the query register is
  `|f(0) ⊕ f(1)⟩` up to the physically-irrelevant global phase `(−1)^{f(0)}` (N&C writes `±`, eq.
  1.45), tensored with the untouched answer register `|−⟩`.
* `IsDeutschOracle.deutschCircuit_bornProb` — **the outcome**: measuring the query qubit in the
  computational basis (`controlMeasurement`) yields `f(0) ⊕ f(1)` with probability `1`. This is
  N&C's "by measuring the first qubit we may determine `f(0) ⊕ f(1)`"; the global phase is invisible
  to the Born rule (it is killed by `‖·‖`).

## Design notes

* **Global phase.** The output carries the global phase `(−1)^{f(0)}` (present already in N&C's own
  `±` in eqs. 1.44–1.45). Since a `PureState` is only a unit vector and `−|−⟩` is not a *named*
  state, we state the deterministic result as a **Born probability** (`bornProb = 1`), which is
  phase-invariant — the physically meaningful, and literal, form of the exercise's conclusion. This
  matches the Kitaev-phase-estimation outcome style (Problem 5.3).
* **Use.** The four optical oracles of Exercise 7.13 (`AxQM/NC/Ch7/Exercise7_13.lean`) are verified
  against `IsDeutschOracle`, and the circuit computation here is used for each.
* **XOR-oracle spec.** `IsDeutschOracle` is stated on the computational basis (via `evolvePure`),
  so the four concrete optical oracles are verified against it with the existing gate truth tables,
  and the single circuit computation is instantiated once per oracle — never re-proved. The proofs
  keep the two-qubit vectors at the composite `(A ⊗ B).vec` head (rather than the raw `⊗ₜ` head), so
  the linearity lemmas `map_smul`/`map_add`/`map_sub` fire through the arbitrary operator `U_f.op`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {f : Fin 2 → Fin 2} {Uf : Evolution (qubit ⊗ qubit)}

/-- **The Deutsch circuit** `(H ⊗ I) · U_f · (H ⊗ H)` on two qubits (Nielsen & Chuang §1.4.3,
Figure 1.19): a Hadamard on each qubit, the oracle `U_f`, then a final Hadamard on the query
(first, left) qubit. With the input `|0⟩ ⊗ |1⟩`, measuring the query qubit afterwards reveals
`f(0) ⊕ f(1)` (`deutschCircuit_bornProb`). Here `U_f` is an arbitrary evolution; the physical
content is fixed by the oracle property `IsDeutschOracle`. -/
def deutschCircuit (Uf : Evolution (qubit ⊗ qubit)) : Evolution (qubit ⊗ qubit) :=
  (hadamardGate.onLeft qubit).comp (Uf.comp (hadamardGate ⊗ hadamardGate))

/-- **`U_f` is the (reversible) oracle for `f : {0,1} → {0,1}`** (Nielsen & Chuang §1.4.3): the XOR
oracle `U_f|x, y⟩ = |x, y ⊕ f(x)⟩`, i.e. it leaves the query register `|x⟩` alone and adds `f(x)`
into the answer register `|y⟩` (`⊕` is addition in `Fin 2`). Stated on the computational basis via
`evolvePure`, so it is verified for each concrete oracle by its gate truth table. -/
def IsDeutschOracle (f : Fin 2 → Fin 2) (Uf : Evolution (qubit ⊗ qubit)) : Prop :=
  ∀ x y : Fin 2, Uf.evolvePure (qubitBasis x ⊗ qubitBasis y) = qubitBasis x ⊗ qubitBasis (y + f x)

/-- A `Fin 2` value is `0` or `1` — the two-way split used to case on `f 0` and `f 1`. -/
private theorem fin2_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by omega

/-- **Lift an `evolvePure` equality to the operator on the underlying vector.** From `U ψ = φ` (as
pure states) read off `U.op ψ.vec = φ.vec` — the bridge from the `evolvePure` statement to the
operator on state vectors. -/
theorem Evolution.op_vec_eq {S : QSystem} {U : Evolution S} {ψ φ : PureState S}
    (h : U.evolvePure ψ = φ) : U.op ψ.vec = φ.vec := by
  rw [← Evolution.evolvePure_vec, h]

/-- **Phase kickback** (Nielsen & Chuang eq. 1.43): a Deutsch oracle for `f`, fed the
answer-register `X`-eigenstate `|−⟩`, acts as a *phase* oracle on the query register:
`U_f(|x⟩ ⊗ |−⟩) = (−1)^{f(x)} |x⟩ ⊗ |−⟩`. Since `|−⟩ = (|0⟩ − |1⟩)/√2`, the bit flip `y ↦ y ⊕ f(x)`
either fixes `|−⟩` (`f(x) = 0`) or sends it to `−|−⟩` (`f(x) = 1`), so the result is
`(−1)^{f(x)}|x⟩ ⊗ |−⟩`. This is the mechanism that lets one query decide `f(0) ⊕ f(1)`. -/
theorem IsDeutschOracle.op_tmul_qubitMinus (h : IsDeutschOracle f Uf) (x : Fin 2) :
    Uf.op ((qubitBasis x ⊗ qubitMinus).vec)
      = ((-1 : ℂ) ^ (f x).val) • ((qubitBasis x ⊗ qubitMinus).vec) := by
  have hUf : ∀ y : Fin 2, Uf.op ((qubitBasis x ⊗ qubitBasis y).vec)
      = (qubitBasis x ⊗ qubitBasis (y + f x)).vec := fun y => Evolution.op_vec_eq (h x y)
  -- Expand `|−⟩ = (|0⟩ − |1⟩)/√2` keeping the two-qubit vectors at the composite head.
  have key : (qubitBasis x ⊗ qubitMinus).vec
      = Concrete.invSqrt2
          • ((qubitBasis x ⊗ qubitBasis 0).vec - (qubitBasis x ⊗ qubitBasis 1).vec) := by
    conv_lhs => rw [PureState.tmul_vec, qubitMinus_vec_eq_smul_sub, TensorProduct.tmul_smul,
      TensorProduct.tmul_sub]
    rfl
  rw [key, map_smul, map_sub, hUf 0, hUf 1]
  rcases fin2_eq_zero_or_one (f x) with hfx | hfx <;> rw [hfx] <;>
    simp only [Fin.isValue, zero_add, add_zero, Fin.reduceAdd, Fin.val_zero, Fin.val_one, pow_zero,
      pow_one, one_smul, neg_one_smul]
  module

-- The `try` below is needed: without it `rw` fails on closed goals.
set_option linter.unusedTactic false in
/-- **Full circuit computation.** On the input `|0⟩ ⊗ |1⟩`, `deutschCircuit U_f` (for a Deutsch
oracle `U_f`) produces `(−1)^{f(0)} |f(0) ⊕ f(1)⟩ ⊗ |−⟩`: the query register ends in the
computational basis state `|f(0) ⊕ f(1)⟩` (up to the global phase `(−1)^{f(0)}`), the answer
register in `|−⟩` (Nielsen & Chuang eq. 1.45). The three stages: `H ⊗ H` makes `|+⟩ ⊗ |−⟩`; `U_f`
kicks the phase back (`op_tmul_qubitMinus`), leaving `(−1)^{f(0)} |0⟩ + (−1)^{f(1)} |1⟩` (up to
`1/√2`) in the
query register; the final `H` on the query interferes this into `|f(0) ⊕ f(1)⟩`. -/
theorem IsDeutschOracle.deutschCircuit_op (h : IsDeutschOracle f Uf) :
    (deutschCircuit Uf).op ((qubitBasis 0 ⊗ qubitBasis 1).vec)
      = ((-1 : ℂ) ^ (f 0).val) • ((qubitBasis (f 0 + f 1) ⊗ qubitMinus).vec) := by
  -- Stage 1: `(H ⊗ H)|0⟩|1⟩ = |+⟩ ⊗ |−⟩`.
  have hA : (hadamardGate ⊗ hadamardGate).op ((qubitBasis 0 ⊗ qubitBasis 1).vec)
      = (qubitPlus ⊗ qubitMinus).vec :=
    Evolution.op_vec_eq (by rw [Evolution.tmul_evolvePure, hadamardGate_evolvePure_qubitBasis_zero,
      hadamardGate_evolvePure_qubitBasis_one])
  -- Split `|+⟩ ⊗ |−⟩` into the two query branches (composite head).
  have hexpP : (qubitPlus ⊗ qubitMinus).vec
      = Concrete.invSqrt2
          • ((qubitBasis 0 ⊗ qubitMinus).vec + (qubitBasis 1 ⊗ qubitMinus).vec) := by
    conv_lhs => rw [PureState.tmul_vec, qubitPlus_vec_eq_smul_add, ← TensorProduct.smul_tmul',
      TensorProduct.add_tmul]
    rfl
  -- Stage 3: the final `H` on the query, acting on each branch.
  have hHL0 : (hadamardGate.onLeft qubit).op ((qubitBasis 0 ⊗ qubitMinus).vec)
      = (qubitPlus ⊗ qubitMinus).vec :=
    Evolution.op_vec_eq
      (by rw [Evolution.onLeft_evolvePure, hadamardGate_evolvePure_qubitBasis_zero])
  have hHL1 : (hadamardGate.onLeft qubit).op ((qubitBasis 1 ⊗ qubitMinus).vec)
      = (qubitMinus ⊗ qubitMinus).vec :=
    Evolution.op_vec_eq
      (by rw [Evolution.onLeft_evolvePure, hadamardGate_evolvePure_qubitBasis_one])
  have hexpM : (qubitMinus ⊗ qubitMinus).vec
      = Concrete.invSqrt2
          • ((qubitBasis 0 ⊗ qubitMinus).vec - (qubitBasis 1 ⊗ qubitMinus).vec) := by
    rw [PureState.tmul_vec]
    nth_rewrite 1 [qubitMinus_vec_eq_smul_sub]
    rw [← TensorProduct.smul_tmul', TensorProduct.sub_tmul]
    rfl
  rw [deutschCircuit, Evolution.comp_op, Evolution.comp_op, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, hA, hexpP, map_smul, map_add, h.op_tmul_qubitMinus 0,
    h.op_tmul_qubitMinus 1, map_smul, map_add, map_smul, map_smul, hHL0, hHL1, hexpP, hexpM]
  -- Both query branches now sit over the common basis `|0⟩⊗|−⟩`, `|1⟩⊗|−⟩`; the `1/√2`s combine
  -- (`invSqrt2² = 1/2`) so the interference collapses to the single term `|f(0) ⊕ f(1)⟩ ⊗ |−⟩`.
  rcases fin2_eq_zero_or_one (f 0) with h0 | h0 <;>
    rcases fin2_eq_zero_or_one (f 1) with h1 | h1 <;>
    (rw [h0, h1]
     simp only [Fin.reduceAdd, Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
       neg_one_smul]
     match_scalars <;> (ring_nf; try (rw [Concrete.invSqrt2_sq]; ring)))

/-- **Deutsch's algorithm outcome** (Nielsen & Chuang eq. 1.45): running `deutschCircuit U_f` on
`|0⟩ ⊗ |1⟩` and measuring the **query** (first) qubit in the computational basis yields
`f(0) ⊕ f(1)` with **probability 1**. So a single query decides the global property `f(0) ⊕ f(1)` —
`0` iff `f` is constant, `1` iff `f` is balanced. The output query register is `|f(0) ⊕ f(1)⟩` up to
the global phase `(−1)^{f(0)}` (`deutschCircuit_op`), which the Born rule `‖·‖²` erases; the answer
register `|−⟩` factors out with unit norm. -/
theorem IsDeutschOracle.deutschCircuit_bornProb (h : IsDeutschOracle f Uf) :
    (controlMeasurement qubit).bornProb
        ((deutschCircuit Uf).evolvePure (qubitBasis 0 ⊗ qubitBasis 1)).toState (f 0 + f 1)
      = 1 := by
  rw [Measurement.bornProb_toState_eq_normSq, Evolution.evolvePure_vec, h.deutschCircuit_op,
    map_smul, PureState.tmul_vec, controlMeasurement_op_tmul, InnerProductSpace.rankOne_apply,
    qubitBasis_inner_qubitBasis]
  simp only [↓reduceIte, one_smul]
  change ‖(-1 : ℂ) ^ (f 0 : ℕ) •
      ((qubitBasis (f 0 + f 1)).vec ⊗ₜ[ℂ] qubitMinus.vec : qubit.space ⊗[ℂ] qubit.space)‖ ^ 2 = 1
  rw [norm_smul, TensorProduct.norm_tmul, (qubitBasis (f 0 + f 1)).normalized,
      qubitMinus.normalized,
    mul_one, mul_one]
  simp [norm_pow]

end AxQM
