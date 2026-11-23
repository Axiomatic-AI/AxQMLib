/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CompositeMeasurement
import AxQM.Postulates.API.CompositeStateEvolution
import AxQM.Postulates.API.Evolution

/-!
# A right-factor gate and measurement act factorwise on a product state (N&C Problem 5.2, 3b-v)

The measured quantum Fourier transform (Problem 5.2) is assembled by an outer induction over the
tower depth. Its Figure 5.1 head-layer peel measures the **head wire** first
(`controlMeasurement`, the left factor of `qtower (n+1) qubit = qubit ⊗ qtower n qubit`); a
computational-basis measurement of the head wire collapses the register to a **product state**
`|i⟩⟨i| ⊗ τ` — the head wire disentangled from the tail (`controlMeasurement_postMeasurement_*`).
Everything the induction then does to the tail — the recursive tail QFT
`qftTailEvolution n = (qftTowerEvolution n).onRight qubit = 1 ⊗ Q`, its classically-controlled
branch phase cascades, and the recursive per-wire measurement `(qtowerMeasurement n).onRight qubit`
— is a **right-factor** object acting on that product state, idle on the head wire.

This file supplies the step that lets the level-`n` measured QFT plug into the
level-`(n+1)` reduction across that product cut: on a product state `ξ ⊗ τ`, a right-factor gate
`g.onRight S = 1 ⊗ g` and a right-factor measurement `m.onRight S = 1 ⊗ m` act **factorwise**,
leaving the left factor `ξ` untouched and reducing to `g` / `m` on the right factor `τ` alone. This
holds for an **arbitrary** gate `g` — no commutation `Mᵢ g = Wᵢ Mᵢ` is assumed (unlike the sibling
`DeferredMeasurementOnRight.lean`, where the state need not be a product): here the *state* is a
product, so the two factors never interact. It is exactly the step that turns the tail's onRight
recursion into the level-`n` measured QFT.

* `Evolution.onRight_evolve_tmul` — `(1 ⊗ g) (ξ ⊗ τ) (1 ⊗ g)† = ξ ⊗ (g τ g†)`: a right-factor gate
  evolves a product state factorwise. Immediate from `Evolution.tmul_evolve` at the identity on the
  left factor.
* `Evolution.onRight_onRight_evolve_tmul` — `(1 ⊗ f)(1 ⊗ g)(ξ ⊗ τ) = ξ ⊗ f (g τ)`: two right-factor
  gates compose factorwise on a product state (the previous applied twice), the left factor `ξ` left
  untouched and the two gates composed on the right factor `τ`.
* `Measurement.bornProb_onRight_tmul` — `p(i ∣ ξ ⊗ τ) = p(i ∣ τ)` (Postulate 3): a right-factor
  measurement's statistics on a product state ignore the (trace-one) left factor.
* `Measurement.postMeasurement_onRight_tmul` — `postMeas(ξ ⊗ τ, i) = ξ ⊗ postMeas(τ, i)` (Postulate
  4): a right-factor measurement collapses only the right factor of a product state.
* `Measurement.bornProb_onRight_evolve_tmul` / `Measurement.postMeasurement_onRight_evolve_tmul` —
  the two composed with the gate step, the shape the measured-QFT outer induction plugs in: after a
  right-factor gate on a product state, a right-factor measurement reads / collapses only the right
  factor.
-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S T : QSystem}

/-- **A right-factor gate evolves a product state factorwise.** On the product state `ξ ⊗ τ`, the
right-factor gate `g.onRight S = 1 ⊗ g` acts as the identity on the left factor `ξ` and as `g` on
the right factor `τ`: `(1 ⊗ g)(ξ ⊗ τ)(1 ⊗ g)† = ξ ⊗ (g τ g†)`. Immediate from the factorwise action
of a product unitary on a product state (`Evolution.tmul_evolve`) at the identity on the left factor
(`Evolution.evolve_id`), since `g.onRight S = Evolution.id ⊗ g`. -/
theorem Evolution.onRight_evolve_tmul (g : Evolution T) (S : QSystem) (ξ : State S) (τ : State T) :
    (g.onRight S).evolve (ξ ⊗ τ) = ξ ⊗ g.evolve τ := by
  rw [Evolution.onRight, Evolution.tmul_evolve, Evolution.evolve_id]

/-- **Two right-factor gates compose factorwise on a product state.** Applying the right-factor gate
`g.onRight S = 1 ⊗ g` and *then* `f.onRight S = 1 ⊗ f` to a product state `ξ ⊗ τ` leaves the left
factor `ξ` untouched and composes the two gates on the right factor `τ`:

  `(1 ⊗ f)(1 ⊗ g)(ξ ⊗ τ)(1 ⊗ g)†(1 ⊗ f)† = ξ ⊗ (f (g τ g†) f†)`.

The single-gate factorwise action (`Evolution.onRight_evolve_tmul`) applied twice — the shape a
two-gate tail recursion takes on a disentangled product (a classically-controlled branch gate `g`
then a recursive gate `f`, both idle on the left factor). -/
theorem Evolution.onRight_onRight_evolve_tmul (ξ : State S) (f g : Evolution T) (τ : State T) :
    (f.onRight S).evolve ((g.onRight S).evolve (ξ ⊗ τ)) = ξ ⊗ f.evolve (g.evolve τ) := by
  rw [Evolution.onRight_evolve_tmul g S, Evolution.onRight_evolve_tmul f S]

/-- **Operator factorisation of a right-factor post-measurement operation on a product state.** The
unnormalised branch operator `Eᵢ(ξ ⊗ τ) = (1 ⊗ Mᵢ)(ξ ⊗ τ)(1 ⊗ Mᵢ)†` of the right-factor
measurement `m.onRight S` on a product state factors as `ξ ⊗ Eᵢ(τ)`, the left factor `ξ` carried
along untouched. The operator identity underlying both the Born-probability and the collapse
readings: `m.onRight S`'s operator is `TensorProduct.mapL 1 (m.op i)` (`Measurement.onRight_op`)
and the product state's is `TensorProduct.mapL ξ.op τ.op` (`State.tmul_op`), so the conjugation
distributes over `TensorProduct.mapL` (`mapL_comp`, `mapL_adjoint`), the left slot
collapsing `1 ξ 1† = ξ`. -/
private theorem postOp_onRight_tmul (m : Measurement ι T) (S : QSystem) (ξ : State S) (τ : State T)
    (i : ι) :
    ContinuousLinearMap.postOp (m.onRight S).op (ξ ⊗ τ).op i
      = TensorProduct.mapL ξ.op (ContinuousLinearMap.postOp m.op τ.op i) := by
  have := FiniteDimensional.completeSpace ℂ S.space
  have := FiniteDimensional.completeSpace ℂ T.space
  simp only [ContinuousLinearMap.postOp, Measurement.onRight_op, State.tmul_op]
  -- Rewrite the left factor `ξ.op` of the RHS as the trivial conjugation `1 ξ.op 1†`, so both
  -- sides become `mapL (·∘·∘·) (·∘·∘·)`; `← mapL_comp` splits the RHS into the same
  -- `X.comp (Y.comp Z)` shape as the LHS, and `congr`/`mapL_adjoint` discharges the adjoint slot.
  conv_rhs =>
    rw [show ξ.op = (1 : S.space →L[ℂ] S.space).comp
          (ξ.op.comp (adjoint (1 : S.space →L[ℂ] S.space))) by
        simp [ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id]]
  rw [TensorProduct.mapL_comp, TensorProduct.mapL_comp]
  congr 2
  exact TensorProduct.adjoint_mapL (1 : S.space →L[ℂ] S.space) (m.op i)

/-- **The unnormalised branch trace of a right-factor measurement ignores the left factor of a
product state.** `re Tr(Eᵢ(ξ ⊗ τ)) = re Tr(Eᵢ(τ))`: the branch operator factors as `ξ ⊗ Eᵢ(τ)`
(`postOp_onRight_tmul`), whose trace splits as `Tr(ξ)·Tr(Eᵢ(τ)) = 1·Tr(Eᵢ(τ))`
(`ContinuousLinearMap.trace_mapL`, `State.trace_op_eq_one`). Shared by the Born-probability
(Postulate 3) and the collapse normalisation (Postulate 4). -/
private theorem re_trace_postOp_onRight_tmul (m : Measurement ι T) (S : QSystem) (ξ : State S)
    (τ : State T) (i : ι) :
    RCLike.re (LinearMap.trace ℂ (S ⊗ T).space
        (ContinuousLinearMap.postOp (m.onRight S).op (ξ ⊗ τ).op i : (S ⊗ T).space →ₗ[ℂ] _))
      = RCLike.re (LinearMap.trace ℂ T.space
          (ContinuousLinearMap.postOp m.op τ.op i : T.space →ₗ[ℂ] _)) := by
  rw [postOp_onRight_tmul]
  have h : LinearMap.trace ℂ (TensorProduct ℂ S.space T.space)
        (TensorProduct.mapL ξ.op (ContinuousLinearMap.postOp m.op τ.op i))
      = LinearMap.trace ℂ T.space (ContinuousLinearMap.postOp m.op τ.op i) := by
    rw [ContinuousLinearMap.trace_mapL, State.trace_op_eq_one, one_mul]
  exact congrArg RCLike.re h

/-- **A right-factor measurement's statistics on a product state ignore the left factor** (Postulate
3). Measuring the right-factor measurement `m.onRight S = 1 ⊗ m` on a product state `ξ ⊗ τ` gives,
for every outcome `i`, the same Born probability as measuring `m` on the right factor `τ` alone:
`p(i ∣ ξ ⊗ τ) = p(i ∣ τ)` — the left factor contributes only its unit trace
(`re_trace_postOp_onRight_tmul`). -/
theorem Measurement.bornProb_onRight_tmul (m : Measurement ι T) (S : QSystem) (ξ : State S)
    (τ : State T) (i : ι) :
    (m.onRight S).bornProb (ξ ⊗ τ) i = m.bornProb τ i := by
  rw [Measurement.bornProb_eq_re_trace_postOp, Measurement.bornProb_eq_re_trace_postOp,
    re_trace_postOp_onRight_tmul]

/-- **Operator factorisation of a right-factor post-measurement (normalised) state on a product
state.** `postState((1 ⊗ Mᵢ), ξ ⊗ τ, i) = ξ ⊗ postState(Mᵢ, τ, i)`: the normalised collapse of the
right-factor measurement on a product state carries the left factor `ξ` along untouched and
collapses the right factor. The unnormalised branch factors as `ξ ⊗ Eᵢ(τ)`
(`postOp_onRight_tmul`); the normalisation factor is the same on both factors
(`re_trace_postOp_onRight_tmul`), so it pulls into the right slot of `TensorProduct.mapL`
(`mapL_smul_right`). -/
private theorem postState_onRight_tmul (m : Measurement ι T) (S : QSystem) (ξ : State S)
    (τ : State T) (i : ι) :
    ContinuousLinearMap.postState (m.onRight S).op (ξ ⊗ τ).op i
      = TensorProduct.mapL ξ.op (ContinuousLinearMap.postState m.op τ.op i) := by
  rw [ContinuousLinearMap.postState, ContinuousLinearMap.postState, re_trace_postOp_onRight_tmul,
    postOp_onRight_tmul, TensorProduct.mapL_smul_right]
  rfl

/-- **A right-factor measurement collapses only the right factor of a product state** (Postulate 4).
The state after measuring outcome `i` of the right-factor measurement `m.onRight S = 1 ⊗ m` on a
product state `ξ ⊗ τ` equals the product of the untouched left factor `ξ` with the collapse of the
right factor `τ` under `m`:

  `postMeas(ξ ⊗ τ, i) = ξ ⊗ postMeas(τ, i)`.

The outcome is equally possible on `τ` because the probabilities agree
(`Measurement.bornProb_onRight_tmul`). Proved on the operator (`postState_onRight_tmul`, which
carries the left factor along and collapses the right). -/
theorem Measurement.postMeasurement_onRight_tmul (m : Measurement ι T) (S : QSystem) (ξ : State S)
    (τ : State T) (i : ι) (hp : (m.onRight S).bornProb (ξ ⊗ τ) i ≠ 0) :
    (m.onRight S).postMeasurement (ξ ⊗ τ) i hp
      = ξ ⊗ m.postMeasurement τ i (by rwa [Measurement.bornProb_onRight_tmul] at hp) := by
  apply State.ext
  rw [Measurement.postMeasurement_op, postState_onRight_tmul, State.tmul_op,
    Measurement.postMeasurement_op]

/-- **A right-factor gate then a right-factor measurement read only the right factor of a product
state** (Postulate 3 composed). After a right-factor gate `g.onRight S = 1 ⊗ g` on a product state
`ξ ⊗ τ`, the right-factor measurement `m.onRight S = 1 ⊗ m` has, for every outcome `i`, the same
Born probability as measuring `m` after `g` on the right factor `τ` alone:
`p(i ∣ (1 ⊗ g)(ξ ⊗ τ)(1 ⊗ g)†) = p(i ∣ g τ g†)`. The gate step (`Evolution.onRight_evolve_tmul`)
leaves a product `ξ ⊗ (g τ g†)`, on which the measurement ignores the left factor
(`Measurement.bornProb_onRight_tmul`). This is the outer-induction step that pushes the tail QFT and
the terminal tail measurement onto the level-`n` register alone. -/
theorem Measurement.bornProb_onRight_evolve_tmul (m : Measurement ι T) (g : Evolution T)
    (S : QSystem) (ξ : State S) (τ : State T) (i : ι) :
    (m.onRight S).bornProb ((g.onRight S).evolve (ξ ⊗ τ)) i = m.bornProb (g.evolve τ) i := by
  rw [Evolution.onRight_evolve_tmul, Measurement.bornProb_onRight_tmul]

/-- **A right-factor gate then a right-factor measurement collapse only the right factor of a
product state** (Postulate 4 composed). The state after a right-factor gate `g.onRight S = 1 ⊗ g` on
a product state `ξ ⊗ τ` and *then* measuring outcome `i` of the right-factor measurement
`m.onRight S = 1 ⊗ m` equals the untouched left factor `ξ` tensored with the collapse of the right
factor under `g` then `m`:

  `postMeas((1 ⊗ g)(ξ ⊗ τ)(1 ⊗ g)†, i) = ξ ⊗ postMeas(g τ g†, i)`.

The gate step (`Evolution.onRight_evolve_tmul`) leaves a product `ξ ⊗ (g τ g†)`, on which the
measurement collapses only the right factor (`Measurement.postMeasurement_onRight_tmul`). This is
the outer-induction step at the collapse level: the tail QFT and the terminal tail measurement act
on the level-`n` register alone, the measured head wire carried along as the product's left factor —
the recursion connector the measured-QFT reduction plugs the level-`n` measured QFT into. -/
theorem Measurement.postMeasurement_onRight_evolve_tmul (m : Measurement ι T) (g : Evolution T)
    (S : QSystem) (ξ : State S) (τ : State T) (i : ι)
    (hp : (m.onRight S).bornProb ((g.onRight S).evolve (ξ ⊗ τ)) i ≠ 0) :
    (m.onRight S).postMeasurement ((g.onRight S).evolve (ξ ⊗ τ)) i hp
      = ξ ⊗ m.postMeasurement (g.evolve τ) i
          (by rwa [Measurement.bornProb_onRight_evolve_tmul] at hp) := by
  apply State.ext
  rw [Measurement.postMeasurement_op, State.tmul_op, Measurement.postMeasurement_op,
    Evolution.onRight_evolve_tmul, postState_onRight_tmul]

end AxQM
