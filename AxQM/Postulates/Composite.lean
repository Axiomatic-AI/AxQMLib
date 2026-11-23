/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.PartialTrace
import AxQM.Postulates.Evolution
import ToMathlib.Analysis.InnerProductSpace.TensorProduct
import ToMathlib.Analysis.InnerProductSpace.QuantumRelativeEntropy
import ToMathlib.Analysis.InnerProductSpace.Purification

/-!
# AxQM — Postulate 6: composite systems

The state space of a composite system `S ⊗ T` is the **tensor product** of the
component state spaces (`QSystem.compose`). This file constructs
joint states and evolutions from component ones (Nielsen–Chuang Postulate 4 / §2.2.8):

* `PureState.tmul` (`ψ ⊗ φ`) — the product pure state on `S ⊗ T`.
* `State.tmul` (`ρ ⊗ σ`) — the product (density) state.
* `Evolution.tmul` (`U ⊗ V`) — the product unitary; `Evolution.onLeft`/`onRight` act with a
  gate on one factor (`U ⊗ 1` / `1 ⊗ U`).
* `State.purify` (N&C §2.5) — the canonical purification of a state `ρ` to a pure state on
  `S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin S.dim))` (the doubled system, ancilla a copy of
  `S`), with `State.purify_isPurification` / `State.purify_reducedLeft_eq` recovering `ρ` as its
  left marginal (via `TensorProduct.canonicalPurification`).

**Notation.** The circle-cross `⊗` is the uniform tensor: `S ⊗ T` (systems),
`ρ ⊗ σ` / `ψ ⊗ φ` (states), `U ⊗ V` (evolutions) — overloaded by argument type, scoped to
`AxQM`. Statements read `⊗`, never `tmul`; the tensor product of vectors is written `⊗ₜ`.

`PureState.tmul`'s normalization is proved on
the explicit underlying space and closed into the bundled goal by defeq.
`State.purify`'s ancilla is named through the `QSystem.ofModel` wrapper, so the
purification lands on a genuine composite system `S ⊗ ·`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {S T : QSystem}

/-- **Composite pure state** `ψ ⊗ φ`: the product state of two pure states, on `S ⊗ T`. -/
def PureState.tmul (ψ : PureState S) (φ : PureState T) : PureState (S ⊗ T) where
  vec := ψ.vec ⊗ₜ[ℂ] φ.vec
  normalized := by
    have h : ‖(ψ.vec ⊗ₜ[ℂ] φ.vec : S.space ⊗[ℂ] T.space)‖ = 1 := by
      rw [TensorProduct.norm_tmul, ψ.normalized, φ.normalized, mul_one]
    exact h

@[inherit_doc] scoped infixr:70 " ⊗ " => PureState.tmul

@[simp]
theorem PureState.tmul_vec (ψ : PureState S) (φ : PureState T) :
    (ψ ⊗ φ).vec = ψ.vec ⊗ₜ[ℂ] φ.vec := rfl

/-- **Composite state** `ρ ⊗ σ`: the product of two states, on `S ⊗ T`. A genuine `State`,
since the tensor of density operators is a density operator. -/
def State.tmul (ρ : State S) (σ : State T) : State (S ⊗ T) where
  op := TensorProduct.mapL ρ.op σ.op
  isDensity := ContinuousLinearMap.IsDensityOp.mapL ρ.isDensity σ.isDensity

@[inherit_doc] scoped infixr:70 " ⊗ " => State.tmul

@[simp]
theorem State.tmul_op (ρ : State S) (σ : State T) :
    (ρ ⊗ σ).op = TensorProduct.mapL ρ.op σ.op := rfl

/-- **Composite evolution** `U ⊗ V`: the product unitary on `S ⊗ T` (the tensor of
unitaries is unitary, `TensorProduct.mapL_mem_unitary`). -/
def Evolution.tmul (U : Evolution S) (V : Evolution T) : Evolution (S ⊗ T) where
  op := TensorProduct.mapL U.op V.op
  unitary := TensorProduct.mapL_mem_unitary U.unitary V.unitary

@[inherit_doc] scoped infixr:70 " ⊗ " => Evolution.tmul

@[simp]
theorem Evolution.tmul_op (U : Evolution S) (V : Evolution T) :
    (U ⊗ V).op = TensorProduct.mapL U.op V.op := rfl

/-- **A gate on the left factor**: `U ⊗ 1` acts as `U` on `S`, identity on `T`. -/
def Evolution.onLeft (U : Evolution S) (T : QSystem) : Evolution (S ⊗ T) := U ⊗ Evolution.id

/-- **A gate on the right factor**: `1 ⊗ V` acts as `V` on `T`, identity on `S`. -/
def Evolution.onRight (V : Evolution T) (S : QSystem) : Evolution (S ⊗ T) := Evolution.id ⊗ V

/-- **Canonical purification** of a state `ρ` (Nielsen–Chuang §2.5): a pure state on the
doubled system `S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin S.dim))` — the ancilla is a copy
of `S`, named through the §3.2 model-space wrapper — whose left marginal is `ρ`
(`State.purify_reducedLeft_eq`). Grounds `TensorProduct.canonicalPurification` into the
postulate framework. The witness is `∑ᵢ √λᵢ • (eᵢ ⊗ fᵢ)` for the spectral data `(λᵢ, eᵢ)`
of `ρ`. -/
def State.purify (ρ : State S) :
    PureState (S ⊗ QSystem.ofModel (EuclideanSpace ℂ (Fin S.dim))) where
  vec := TensorProduct.canonicalPurification ρ.isDensity (EuclideanSpace.basisFun _ ℂ)
  normalized := TensorProduct.norm_canonicalPurification ρ.isDensity _

@[simp]
theorem State.purify_vec (ρ : State S) :
    (ρ.purify).vec =
      TensorProduct.canonicalPurification ρ.isDensity (EuclideanSpace.basisFun _ ℂ) :=
  rfl

/-- **The canonical purification is a purification**: the right-partial-trace of
`|ρ.purify⟩⟨ρ.purify|` recovers `ρ.op`. The bridge to `TensorProduct.IsPurification`. -/
theorem State.purify_isPurification (ρ : State S) :
    TensorProduct.IsPurification ρ.op (ρ.purify).vec :=
  TensorProduct.isPurification_canonicalPurification ρ.isDensity _

/-- **The left marginal of the canonical purification is the state itself**: tracing out
the ancilla of `ρ.purify` recovers `ρ`. -/
theorem State.purify_reducedLeft_eq (ρ : State S) :
    (ρ.purify).toState.reducedLeft = ρ := by
  ext1
  rw [State.reducedLeft_op, PureState.toState_op]
  exact (congrArg LinearMap.toContinuousLinearMap ρ.purify_isPurification).trans
    (ContinuousLinearMap.toLinearMap_toContinuousLinearMap _)

end AxQM
