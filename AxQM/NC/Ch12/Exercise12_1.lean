/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.OrthogonalStateCloning
import AxQM.Postulates.API.FidelityPure

/-!
# Nielsen & Chuang, Exercise 12.1 — copying two orthogonal qubit states

Design a 2-qubit circuit copying orthogonal single-qubit states |psi>,|phi>.

This exercise is the constructive companion of the **no-cloning theorem** (N&C Box 12.1 / Problem
12.2, formalised here as `AxQM.no_cloning_unitary`): cloning is impossible for
*non-orthogonal* states, but for *orthogonal* states it "is rather easy to design quantum circuits
which copy such states" (N&C p. 530). Where no-cloning phrases non-orthogonality as `0 < F < 1`,
this item's hypothesis is the boundary case `F(ψ, φ) = 0` — orthogonality expressed through the
grounded fidelity.

## The result

`exists_orthogonalCloningCircuit` states the exercise's headline: for orthogonal `|ψ⟩`, `|φ⟩`, there
**exists** a two-qubit unitary evolution copying both, `U(|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩` and
`U(|φ⟩ ⊗ |0⟩) = |φ⟩ ⊗ |φ⟩`. The witness is the explicit circuit `qubitCopyCircuit ψ φ` and its two
copying identities `qubitCopyCircuit_evolvePure_fst` / `_snd`, all constructed in
`AxQM/Postulates/API/OrthogonalStateCloning.lean` (the change-of-basis unitary and the
orthonormality of `{|ψ⟩, |φ⟩}` are stated in terms of `PureState.vec` and the inner product). The
circuit is the textbook `U = (V ⊗ V) ∘ CNOT ∘ (V† ⊗ 1)`, where
`V = qubitPairUnitary ψ φ` is the single-qubit unitary rotating the computational basis to the pair
(`V|0⟩ = |ψ⟩`, `V|1⟩ = |φ⟩`) — a unitary that exists exactly because `{|ψ⟩, |φ⟩}` is orthonormal.

The grounded fidelity hypothesis is converted to the orthogonality `⟨ψ|φ⟩ = 0` through
`State.fidelity_toState_toState` (`F(ψ, φ) = ‖⟨ψ|φ⟩‖`) and `norm_eq_zero`.
-/

open scoped InnerProductSpace

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 12.1: orthogonal single-qubit states can be cloned.** For two
orthogonal pure states `|ψ⟩`, `|φ⟩` of a qubit — orthogonality expressed as the vanishing fidelity
`F(ψ, φ) = 0`, the boundary case of the no-cloning hypothesis `0 < F < 1` — there exists a two-qubit
unitary evolution `U` (the "copying circuit", the data qubit as control and a `|0⟩` target) that
copies both: `U(|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩` and `U(|φ⟩ ⊗ |0⟩) = |φ⟩ ⊗ |φ⟩`.

The witness is the explicit circuit `qubitCopyCircuit ψ φ = (V ⊗ V) ∘ CNOT ∘ (V† ⊗ 1)`
(`V = qubitPairUnitary ψ φ` the change-of-basis unitary sending `|0⟩ ↦ |ψ⟩`, `|1⟩ ↦ |φ⟩`), whose
two copying actions are `qubitCopyCircuit_evolvePure_fst` and `qubitCopyCircuit_evolvePure_snd`. The
grounded orthogonality `F(ψ, φ) = 0` is turned into `⟨ψ|φ⟩ = 0` via `State.fidelity_toState_toState`
(the fidelity of two pure states is `‖⟨ψ|φ⟩‖`). Contrast `no_cloning_unitary`: no such circuit
exists when `0 < F(ψ, φ) < 1`. -/
theorem exists_orthogonalCloningCircuit (ψ φ : PureState qubit)
    (h : ψ.toState.fidelity φ.toState = 0) :
    ∃ U : Evolution (qubit ⊗ qubit),
      U.evolvePure (ψ.tmul (qubitBasis 0)) = ψ.tmul ψ ∧
      U.evolvePure (φ.tmul (qubitBasis 0)) = φ.tmul φ := by
  have hinner : inner ℂ ψ.vec φ.vec = (0 : ℂ) := by
    have hF : ‖inner ℂ ψ.vec φ.vec‖ = 0 := by
      rw [← State.fidelity_toState_toState ψ φ, h]
    exact norm_eq_zero.mp hF
  exact ⟨qubitCopyCircuit ψ φ hinner, qubitCopyCircuit_evolvePure_fst hinner,
    qubitCopyCircuit_evolvePure_snd hinner⟩

end AxQM
