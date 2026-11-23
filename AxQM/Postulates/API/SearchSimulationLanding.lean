/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SearchSimulationStep
import AxQM.Postulates.API.Evolution
import ToMathlib.Analysis.InnerProductSpace.OperatorSumChoiKraus

/-!
# AxQM.Postulates.API — the search-simulation step as an `Evolution`, and its exact landing

The physics behind **Nielsen & Chuang, Exercise 6.10**: the lowest-order
quantum-search simulation step

`U(Δt) ≡ exp(−i|ψ⟩⟨ψ|Δt) exp(−i|x⟩⟨x|Δt)`   (Exercise 6.9, eq. 6.25)

packaged as an `Evolution` of the effective search qubit, and the density-operator statement of the
tuned exact-landing search. Here `|x⟩ = |0⟩ = blochPureState 0 0` (Bloch vector `ẑ`) and
`|ψ⟩ = blochPureState θ 0` (Bloch vector `⃗ψ = (sin θ, 0, cos θ)`), the §1.2 Bloch pure states.

## What is formalised

* `searchStepEvolution θ Δt` — the step `U(Δt)` as a genuine `Evolution qubit`: the sequential
  composition (`Evolution.comp`) of the two projector-Hamiltonian propagators of Exercise 6.7
  (`projObservable.propagator`), the `|ψ⟩`-propagator applied second. It is a unitary evolution
  because each factor is (`Observable.propagator`).
* `searchStepEvolution_op` — its underlying operator is `e^{−iΔt}` times
  `Matrix.toEuclideanCLM (Concrete.searchStepReduced Δt ⃗ψ ẑ)`, the eq.-6.25 reduced form. Immediate
  from `Evolution.comp_op` and Exercise 6.9's `searchSimulationStep_op`.
* `searchStepEvolution_pow_evolvePure_toState` — **the exact-landing lift.** *Given* the
  Bloch-matrix conjugation landing (the `Concrete` result for Exercise 6.10)
  `(searchStepReduced Δt ⃗ψ ẑ)^j · blochMatrix ⃗ψ · ((…)^j)† = blochMatrix ẑ`, evolving the pure
  state `|ψ⟩` under the `j`-th power of `U(Δt)` yields the solution state `|x⟩` **exactly** (up to a
  global phase, which is invisible to the density operator): the two states coincide,
  `((U(Δt))^j |ψ⟩ as a state) = |x⟩`. The global phase `e^{−iΔt}` of `U(Δt)` cancels in the
  conjugation `U ρ U†`, so the density picture depends only on the phase-free `searchStepReduced`.

## Use in Exercise 6.10

`AxQM/NC/Ch6/Exercise6_10.lean` combines `searchStepEvolution` with the `Concrete` tuning
(`Concrete.searchStepReduced_pow_conj_blochMatrix_exactSearch`) to state the physics claim — `O(√N)`
steps landing `|ψ⟩` exactly on `|x⟩`. The step operator `searchStepEvolution_op` sits alongside
`searchSimulationStep_op` (Exercise 6.9).

The proof of the exact-landing lift avoids `NC/Ch8`'s `toState_evolvePure`: it reduces
(`State.ext`) to the operator identity and conjugates the rank-one projector directly with the
lemma `ContinuousLinearMap.comp_rankOne_self_comp_adjoint`
(`f |ψ⟩⟨ψ| f† = |fψ⟩⟨fψ|`).
-/

open scoped InnerProductSpace
open Matrix Complex ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

/-- **The search-simulation step `U(Δt)` as an `Evolution`** (Nielsen & Chuang, Exercise 6.9/6.10).
`U(Δt) = exp(−i|ψ⟩⟨ψ|Δt) exp(−i|x⟩⟨x|Δt)` for the effective search qubit, with `|x⟩ = |0⟩ =
blochPureState 0 0` and `|ψ⟩ = blochPureState θ 0`: the sequential composition (`Evolution.comp`) of
the two Exercise 6.7 projector-Hamiltonian propagators (`projObservable.propagator`), the
`|ψ⟩`-propagator applied second. A genuine unitary `Evolution` of the qubit; its operator is
computed in `searchStepEvolution_op`. -/
def searchStepEvolution (θ Δt : ℝ) : Evolution qubit :=
  ((blochPureState θ 0).projObservable.propagator 1 0 Δt).comp
    ((blochPureState 0 0).projObservable.propagator 1 0 Δt)

/-- **The operator of the search step `U(Δt)`** (Exercise 6.9, eq. 6.25, at the `Evolution` level).
`(searchStepEvolution θ Δt).op = e^{−iΔt} · Matrix.toEuclideanCLM (Concrete.searchStepReduced Δt ⃗ψ
ẑ)` (`⃗ψ = blochSphereVector θ 0`, `ẑ = blochSphereVector 0 0`). Immediate from `Evolution.comp_op`
(the operator of a composition is the composition/product of operators) and
`searchSimulationStep_op` (the operator-product form of eq. 6.25). -/
theorem searchStepEvolution_op (θ Δt : ℝ) :
    (searchStepEvolution θ Δt).op
      = Complex.exp (-(Complex.I * (Δt : ℂ)))
        • Matrix.toEuclideanCLM (𝕜 := ℂ)
            (Concrete.searchStepReduced Δt (Concrete.blochSphereVector θ 0)
              (Concrete.blochSphereVector 0 0)) := by
  rw [searchStepEvolution, Evolution.comp_op]
  exact searchSimulationStep_op θ Δt

/-- **Nielsen & Chuang, Exercise 6.10 — exact landing at the state level.** *Given* the Bloch-matrix
conjugation landing (`Concrete.searchStepReduced_pow_conj_blochMatrix_land`, the Exercise 6.10
geometry) for the effective search qubit `⃗ψ = blochSphereVector θ 0` and target `ẑ =
blochSphereVector 0 0`,

`(searchStepReduced Δt ⃗ψ ẑ)^j · blochMatrix ⃗ψ · ((searchStepReduced Δt ⃗ψ ẑ)^j)† = blochMatrix ẑ`,

evolving the pure state `|ψ⟩ = blochPureState θ 0` under the `j`-th power of the search step
`U(Δt) = searchStepEvolution θ Δt` produces the solution state `|x⟩ = blochPureState 0 0`
**exactly** (up to a global phase, invisible to the density operator): the states coincide,
`((U(Δt))^j |ψ⟩).toState = |x⟩.toState`. This is the density-operator reading of "the final state is
`|x⟩`, probability `1`".

Proof: `State.ext` reduces to the operator identity `W |ψ⟩⟨ψ| W† = |x⟩⟨x|`, where
`W = (U(Δt)^j).op`. The conjugation of a rank-one self-projector is
`ContinuousLinearMap.comp_rankOne_self_comp_adjoint` (`W |ψ⟩⟨ψ| W† = |Wψ⟩⟨Wψ|`, run in reverse).
`W = e^{−ijΔt} · Matrix.toEuclideanCLM (searchStepReduced Δt ⃗ψ ẑ)^j`
(`Evolution.op_pow` + `searchStepEvolution_op`, the phase pulled out of the power), whose adjoint is
`conj(e^{−ijΔt}) · Matrix.toEuclideanCLM ((…)^j)†`
(`Matrix.toEuclideanCLM_conjTranspose_eq_adjoint`); the global-phase factors multiply to
`|e^{−ijΔt}|² = 1` and cancel, and `Matrix.toEuclideanCLM` (a `⋆`-algebra homomorphism, `map_mul`)
turns the matrix product `(searchStepReduced)^j · blochMatrix ⃗ψ · ((…)^j)†` into the operator,
which is `blochMatrix ẑ = |x⟩⟨x|` by the hypothesis. -/
theorem searchStepEvolution_pow_evolvePure_toState (θ Δt : ℝ) (j : ℕ)
    (hland : (Concrete.searchStepReduced Δt (Concrete.blochSphereVector θ 0)
          (Concrete.blochSphereVector 0 0)) ^ j
        * Concrete.blochMatrix (Concrete.blochSphereVector θ 0)
        * ((Concrete.searchStepReduced Δt (Concrete.blochSphereVector θ 0)
          (Concrete.blochSphereVector 0 0)) ^ j)ᴴ
      = Concrete.blochMatrix (Concrete.blochSphereVector 0 0)) :
    ((searchStepEvolution θ Δt ^ j).evolvePure (blochPureState θ 0)).toState
      = (blochPureState 0 0).toState := by
  set A := Concrete.searchStepReduced Δt (Concrete.blochSphereVector θ 0)
      (Concrete.blochSphereVector 0 0) with hA
  set p := Complex.exp (-(Complex.I * (Δt : ℂ))) with hp
  -- `(U(Δt)^j).op = pʲ · toEuclideanCLM (Aʲ)`: pull the global phase out of the power (`smul_pow`,
  -- whose `IsScalarTower`/`SMulCommClass` instances hold for `ℂ` on the CLM algebra), proved at
  -- `EuclideanSpace ℂ (Fin 2)`.
  have hpe : (p • Matrix.toEuclideanCLM (𝕜 := ℂ) A) ^ j
      = p ^ j • Matrix.toEuclideanCLM (𝕜 := ℂ) (A ^ j) := by
    rw [smul_pow, ← map_pow]
  have hEj : (searchStepEvolution θ Δt ^ j).op
      = p ^ j • Matrix.toEuclideanCLM (𝕜 := ℂ) (A ^ j) := by
    rw [Evolution.op_pow, searchStepEvolution_op, ← hA, ← hp]
    exact hpe
  have hadj : ContinuousLinearMap.adjoint (p ^ j • Matrix.toEuclideanCLM (𝕜 := ℂ) (A ^ j))
      = (starRingEnd ℂ) (p ^ j) • Matrix.toEuclideanCLM (𝕜 := ℂ) ((A ^ j)ᴴ) := by
    rw [map_smulₛₗ ContinuousLinearMap.adjoint]
    congr 1
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, Matrix.star_eq_conjTranspose]
  -- the two global-phase factors cancel: `pʲ · conj(pʲ) = |pʲ|² = 1`
  have hconj : (starRingEnd ℂ) p = Complex.exp (Complex.I * (Δt : ℂ)) := by
    rw [hp, ← Complex.exp_conj]
    refine congrArg Complex.exp ?_
    rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hp1 : p * (starRingEnd ℂ) p = 1 := by
    rw [hconj, hp, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hpc : p ^ j * (starRingEnd ℂ) (p ^ j) = 1 := by
    rw [map_pow, ← mul_pow, hp1, one_pow]
  -- middle projector `|ψ⟩⟨ψ| = toEuclideanCLM (blochMatrix ⃗ψ)`
  have hmid : (rankOne ℂ (blochPureState θ 0).vec (blochPureState θ 0).vec
        : qubit.space →L[ℂ] qubit.space)
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (Concrete.blochMatrix (Concrete.blochSphereVector θ 0)) := by
    rw [← PureState.toState_op, blochPureState_toState_op]
  -- The conjugation `W |ψ⟩⟨ψ| W† = |x⟩⟨x|`, proved entirely at `EuclideanSpace ℂ (Fin 2)` (all
  -- types uniform), where the phase factors cancel and `toEuclideanCLM` collapses the product.
  have core : (p ^ j • Matrix.toEuclideanCLM (𝕜 := ℂ) (A ^ j)).comp
        ((Matrix.toEuclideanCLM (𝕜 := ℂ)
            (Concrete.blochMatrix (Concrete.blochSphereVector θ 0))).comp
          (ContinuousLinearMap.adjoint (p ^ j • Matrix.toEuclideanCLM (𝕜 := ℂ) (A ^ j))))
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (Concrete.blochMatrix (Concrete.blochSphereVector 0 0)) := by
    rw [hadj]
    simp only [← ContinuousLinearMap.mul_def]
    rw [← map_smul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)),
      ← map_smul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)), ← map_mul, ← map_mul]
    refine congrArg _ ?_
    -- `(pʲ • Aʲ) · (blochMatrix ⃗ψ · (conj(pʲ) • (Aʲ)ᴴ)) = blochMatrix ẑ`
    rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, hpc, one_smul, ← mul_assoc, hland]
  -- Reduce the state equality to the operator identity, expose the conjugation of the rank-one
  -- projector (`comp_rankOne_self_comp_adjoint`, in reverse), rewrite `W = (U(Δt)^j).op` (`hEj`),
  -- and close by `core` up to the identification `qubit.space ≟ EuclideanSpace ℂ (Fin 2)`.
  apply State.ext
  rw [blochPureState_toState_op, PureState.toState_op, Evolution.evolvePure_vec,
    ← comp_rankOne_self_comp_adjoint, hmid, hEj]
  exact core

end AxQM
