/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch2.Exercise2_75
import AxQM.Postulates.API.MutualInformation
import AxQM.Postulates.API.EntropyComposite
import AxQM.NC.Ch11.Exercise11_24

/-!
# N&C Exercise 11.26 — `S(A:B) + S(A:C) ≤ 2 S(A)`, and an example where `S(A:B) > S(A)`

Nielsen & Chuang, *Quantum Computation and Quantum Information*,
Exercise 11.26, p. 522.

The exercise has two parts:

1. **The bound.** For a tripartite state `ρ` on `A ⊗ B ⊗ C`, the two pairwise mutual informations
   obey `S(A:B) + S(A:C) ≤ 2 S(A)` (N&C eq. (11.114)). N&C notes that the corresponding Shannon
   inequality holds *for a different reason* — namely `H(A:B) ≤ H(A)` for each term separately.
2. **The example.** In the quantum case the per-term bound `S(A:B) ≤ S(A)` can **fail**: one is
   asked to find a state with `S(A:B) > S(A)`.

Both parts are formalised here.

## Part (1): the bound `S(A:B) + S(A:C) ≤ 2 S(A)`

For a tripartite state `ρ` on `A ⊗ (B ⊗ C)`, with `S(A:B)` the mutual information of the `A ⊗ B`
marginal and `S(A:C)` the mutual information of the `A ⊗ C` marginal, `S(A:B) + S(A:C) ≤ 2 S(A)`.
Expanding both mutual informations, `S(A:B) + S(A:C) = 2 S(A) + S(B) + S(C) − S(A,B) − S(A,C)`, so
the bound is exactly

`S(B) + S(C) ≤ S(A,B) + S(A,C)`,

which is **weak monotonicity** (`State.vonNeumannEntropy_weakMonotonicity`, the "form-1"
strong-subadditivity inequality, N&C eq. (11.107) / **Exercise 11.24**). N&C notes the corresponding
Shannon inequality holds for a *different, stronger* reason — `H(A:B) ≤ H(A)` per term — which fails
quantumly (part (2)); the *sum* nonetheless obeys the bound, because weak monotonicity survives.

Weak monotonicity `State.vonNeumannEntropy_weakMonotonicity` is stated in the "shared-`A`" form
`S(A) + S(C) ≤ S(A,B) + S(B,C)`, i.e. with the two joint terms sharing the *middle* subsystem. The
bound above needs the two joint terms to share the *first* subsystem `A`, so weak monotonicity is
applied to the reshape of `ρ` onto `B ⊗ (A ⊗ C)` (`QSystem.Iso.leftComm`): its `A ⊗ C` marginal is
that reshape's `reducedRight`, and its `B ⊗ A` marginal is the `reducedLeft` of the reshape's
`assoc`-regrouping. Two transport-backbone reshape-frame identities
(`QSystem.Iso.leftComm_trans_assoc`, `QSystem.Iso.leftComm_trans_comm`) identify those two
marginals with `ρ`'s honest `A ⊗ B` and `A ⊗ C` marginals; the assembly is then `linarith`.

* `AxQM.QSystem.Iso.leftComm` — the reshape `A ⊗ (B ⊗ C) ≃ₛ B ⊗ (A ⊗ C)` (the shared
  transport-backbone reshape, in `Postulates/API/SystemIsoComm.lean`);
* `AxQM.State.vonNeumannMutualInfo_add_le_two_mul_vonNeumannEntropy` — the bound
  `S(A:B) + S(A:C) ≤ 2 S(A)`.

## Part (2): the example `S(A:B) > S(A)`

A **Bell state** `|β_xy⟩` on `qubit ⊗ qubit` is the canonical witness. It is pure, so `S(A,B) = 0`,
while each marginal is maximally mixed (`bellState_reducedLeft`/`bellState_reducedRight`,
N&C Exercise 2.75), so `S(A) = S(B) = log 2`. Hence

`S(A:B) = S(A) + S(B) − S(A,B) = log 2 + log 2 − 0 = 2 log 2 > log 2 = S(A)`,

since `log 2 > 0`. This is impossible for Shannon entropies, where `H(A:B) ≤ H(A)` always holds:
the excess correlation of a maximally entangled state has no classical analogue. (Indeed every pure
entangled bipartite state has `S(A:B) = 2 S(A) > S(A)`.)

The declarations:

* `AxQM.bellState_reducedLeft_vonNeumannEntropy` /
  `AxQM.bellState_reducedRight_vonNeumannEntropy` — each marginal has entropy `log 2`;
* `AxQM.bellState_vonNeumannMutualInfo` — the mutual information of a Bell state is
  `S(A:B) = 2 log 2`;
* `AxQM.bellState_reducedLeft_vonNeumannEntropy_lt_vonNeumannMutualInfo` — the strict
  inequality `S(A) < S(A:B)` for a Bell state;
* `AxQM.exists_vonNeumannMutualInfo_gt_reducedLeft_vonNeumannEntropy` — the existence
  statement realising "find an example where `S(A:B) > S(A)`".

The mutual information is the shared generator `State.vonNeumannMutualInfo`
(`S(A:B) = S(A) + S(B) − S(A,B)`, `Postulates/API/MutualInformation`) that Theorem 11.15 is also
phrased over; the marginal-entropy value `S(I/d) = log d` is
`State.vonNeumannEntropy_maximallyMixed` (N&C Theorem 11.8).
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable (x y : Fin 2)

/-- The first-qubit marginal of a Bell state has von Neumann entropy `log 2`: it is the maximally
mixed qubit `I/2` (`bellState_reducedLeft`, N&C Exercise 2.75), and `S(I/d) = log d`
(`State.vonNeumannEntropy_maximallyMixed`) with `d = dim qubit = 2` (`finrank_qubit_space`). -/
theorem bellState_reducedLeft_vonNeumannEntropy :
    (bellState x y).toState.reducedLeft.vonNeumannEntropy = Real.log 2 := by
  rw [bellState_reducedLeft, State.vonNeumannEntropy_maximallyMixed, finrank_qubit_space,
    Nat.cast_ofNat]

/-- The second-qubit marginal of a Bell state has von Neumann entropy `log 2`: it too is the
maximally mixed qubit `I/2` (`bellState_reducedRight`, N&C Exercise 2.75). -/
theorem bellState_reducedRight_vonNeumannEntropy :
    (bellState x y).toState.reducedRight.vonNeumannEntropy = Real.log 2 := by
  rw [bellState_reducedRight, State.vonNeumannEntropy_maximallyMixed, finrank_qubit_space,
    Nat.cast_ofNat]

/-- **The mutual information of a Bell state is `2 log 2`.** For the maximally entangled Bell state
`|β_xy⟩` on `qubit ⊗ qubit`, `S(A:B) = S(A) + S(B) − S(A,B) = log 2 + log 2 − 0 = 2 log 2`: both
marginals are maximally mixed (`S(A) = S(B) = log 2`) while the joint state is pure (`S(A,B) = 0`,
`PureState.vonNeumannEntropy_toState_eq_zero`). -/
theorem bellState_vonNeumannMutualInfo :
    (bellState x y).toState.vonNeumannMutualInfo = 2 * Real.log 2 := by
  rw [State.vonNeumannMutualInfo_def, bellState_reducedLeft_vonNeumannEntropy,
    bellState_reducedRight_vonNeumannEntropy, PureState.vonNeumannEntropy_toState_eq_zero]
  ring

/-- **A Bell state has `S(A:B) > S(A)`** (Nielsen & Chuang, Exercise 11.26, the example): the mutual
information `S(A:B) = 2 log 2` of a Bell state strictly exceeds its marginal entropy `S(A) = log 2`,
because `log 2 > 0`. This is impossible for Shannon entropies, where `H(A:B) ≤ H(A)` always
holds. -/
theorem bellState_reducedLeft_vonNeumannEntropy_lt_vonNeumannMutualInfo :
    (bellState x y).toState.reducedLeft.vonNeumannEntropy
      < (bellState x y).toState.vonNeumannMutualInfo := by
  rw [bellState_reducedLeft_vonNeumannEntropy, bellState_vonNeumannMutualInfo]
  have h : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- **N&C Exercise 11.26 (the example).** There is a bipartite state `ρ` on some `A ⊗ B` whose
quantum mutual information strictly exceeds the marginal entropy of the first system,
`S(A) < S(A:B)` — witnessing that the classical bound `H(A:B) ≤ H(A)` fails in the quantum setting.
Any Bell state on `qubit ⊗ qubit` realises it: `S(A) = log 2 < 2 log 2 = S(A:B)`. -/
theorem exists_vonNeumannMutualInfo_gt_reducedLeft_vonNeumannEntropy :
    ∃ (A B : QSystem.{0}) (ρ : State (A ⊗ B)),
      ρ.reducedLeft.vonNeumannEntropy < ρ.vonNeumannMutualInfo :=
  ⟨qubit, qubit, (bellState 0 0).toState,
    bellState_reducedLeft_vonNeumannEntropy_lt_vonNeumannMutualInfo 0 0⟩

/-! ### Part (1): the bound `S(A:B) + S(A:C) ≤ 2 S(A)` -/

variable {A B C : QSystem}

/-- **N&C Exercise 11.26 (the bound).** For a tripartite state `ρ` on `A ⊗ (B ⊗ C)`, the two
pairwise quantum mutual informations obey

`S(A:B) + S(A:C) ≤ 2 S(A)`  (N&C eq. (11.114)),

where `S(A:B)` is the mutual information of the `A ⊗ B` marginal
`(ρ.congr (assoc A B C)).reducedLeft` and `S(A:C)` that of the `A ⊗ C` marginal
`((ρ.congr (id ⊗ comm B C)).congr (assoc A C B)).reducedLeft`. Expanding both mutual informations
by `State.vonNeumannMutualInfo_def`, the shared `S(A) = S(ρ.reducedLeft)` term appears twice (both
marginals restrict to the same `A`-marginal, `State.reducedLeft_reducedLeft_congr_assoc`), so the
claim reduces to `S(B) + S(C) ≤ S(A,B) + S(A,C)`. That is **weak monotonicity**
(`State.vonNeumannEntropy_weakMonotonicity`, N&C Exercise 11.24) applied to the left-commutation
reshape `QSystem.Iso.leftComm`, whose `A ⊗ C` and `B ⊗ A` marginals are identified with `ρ`'s honest
`A ⊗ C` and `A ⊗ B` marginals by the reshape-frame identities. Contrast part (2): the *per-term*
Shannon bound `H(A:B) ≤ H(A)` has no quantum analogue, yet the *sum* still obeys `≤ 2 S(A)`. -/
theorem State.vonNeumannMutualInfo_add_le_two_mul_vonNeumannEntropy (ρ : State (A ⊗ (B ⊗ C))) :
    (ρ.congr (QSystem.assoc A B C)).reducedLeft.vonNeumannMutualInfo
        + ((ρ.congr (QSystem.Iso.tmul (QSystem.Iso.refl A) (QSystem.Iso.comm B C))).congr
            (QSystem.assoc A C B)).reducedLeft.vonNeumannMutualInfo
      ≤ 2 * ρ.reducedLeft.vonNeumannEntropy := by
  set σ := ρ.congr (QSystem.Iso.leftComm A B C) with hσ
  -- The `A ⊗ C` marginal of `ρ` is `σ`'s `reducedRight` (trace out the front `B`).
  have hAC : σ.reducedRight
      = ((ρ.congr (QSystem.Iso.tmul (QSystem.Iso.refl A) (QSystem.Iso.comm B C))).congr
          (QSystem.assoc A C B)).reducedLeft := by
    rw [State.reducedRight_congr_comm, hσ, ← State.congr_trans,
      QSystem.Iso.leftComm_trans_comm, State.congr_trans]
  -- The `A ⊗ B` marginal of `ρ`, swapped, is `reducedLeft` of `σ`'s `assoc`-regrouping.
  have hAB : (σ.congr (QSystem.assoc B A C)).reducedLeft
      = (ρ.congr (QSystem.assoc A B C)).reducedLeft.congr (QSystem.Iso.comm A B) := by
    rw [hσ, ← State.congr_trans, QSystem.Iso.leftComm_trans_assoc, State.congr_trans,
      State.reducedLeft_congr_tmul_left]
  -- Weak monotonicity on `σ` : `S(B) + S(C) ≤ S(B,A) + S(A,C)`.
  have hwm := State.vonNeumannEntropy_weakMonotonicity σ
  rw [hAC, hAB, State.vonNeumannEntropy_congr] at hwm
  -- `σ.reducedLeft` (the `B`-marginal) is the `B`-marginal of the `A ⊗ B` marginal.
  have hσL : σ.reducedLeft
      = ((ρ.congr (QSystem.assoc A B C)).reducedLeft).reducedRight := by
    rw [← State.reducedLeft_reducedLeft_congr_assoc σ, hAB, ← State.reducedRight_congr_comm]
  rw [hσL] at hwm
  -- Both mutual informations share the `A`-marginal `S(A) = S(ρ.reducedLeft)`.
  have hA1 : (ρ.congr (QSystem.assoc A B C)).reducedLeft.reducedLeft = ρ.reducedLeft :=
    State.reducedLeft_reducedLeft_congr_assoc ρ
  have hA2 : ((ρ.congr (QSystem.Iso.tmul (QSystem.Iso.refl A) (QSystem.Iso.comm B C))).congr
        (QSystem.assoc A C B)).reducedLeft.reducedLeft = ρ.reducedLeft := by
    rw [State.reducedLeft_reducedLeft_congr_assoc, State.reducedLeft_congr_tmul_refl]
  rw [State.vonNeumannMutualInfo_def, State.vonNeumannMutualInfo_def, hA1, hA2]
  linarith [hwm]

end AxQM
