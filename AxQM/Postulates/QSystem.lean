/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# AxQM.Postulates — quantum systems (Postulate 1)

A **quantum system** is the physical object whose mathematical realization is a
finite-dimensional complex Hilbert space. This file introduces `QSystem`, the
*name* for that object, so that signatures can read `State S` / `S ⊗ T` rather than the raw
`EuclideanSpace`/`TensorProduct` mathematics.

The underlying Hilbert space is `S.space`.

States, observables, measurements and evolutions (`State`/`PureState`/`Observable`/
`Measurement`/`Evolution`) are parameterized over `QSystem`, with `S` coercing to its space
`S.space`. `QSystem` bundles the standing assumptions
(finite-dimensional complex Hilbert space), so `CompleteSpace` and finite-dimensionality
derive everywhere and the per-section instance juggling is gone. The *concrete* systems
(`qubit`, `qudit d`, …) are defined in `AxQM/Postulates/API/` via `QSystem.ofModel`.

## Main definitions

* `QSystem` — a quantum system: a bundled finite-dimensional complex Hilbert space.
* `QSystem.compose` (`S ⊗ T`) — the composite system (Postulate 6): systems compose by
  the tensor product of their state spaces.
-/

open scoped TensorProduct

namespace AxQM

/-- A **quantum system** (Postulate 1): the physical object whose
mathematical realization is a finite-dimensional complex Hilbert space `space`. Bundling the
instances lets typeclass resolution flow through `S.space` automatically. -/
structure QSystem where
  /-- The underlying Hilbert space. -/
  space : Type*
  [norm : NormedAddCommGroup space]
  [inner : InnerProductSpace ℂ space]
  [findim : FiniteDimensional ℂ space]

attribute [instance] QSystem.norm QSystem.inner QSystem.findim

/-- A system **coerces to its state space**: `↑S` is `S.space`, so `S : QSystem` stands
in wherever a type/vector/operator is expected (`x : S`, `op : S →L[ℂ] S`). This is the
Mathlib bundled idiom (`Grp`/`ModuleCat`/`TopCat`): there is one fundamental definition,
`QSystem`, and the system/state-space distinction disappears at the surface. The coercion
unfolds to `QSystem.space`. -/
instance : CoeSort QSystem (Type _) := ⟨QSystem.space⟩

/-- The **dimension** of a quantum system: the (finite) dimension of its state space. The
dimension `finrank ℂ S.space`, which lets statements such as `Real.log S.dim` name the
dimension without mentioning `.space`. -/
noncomputable def QSystem.dim (S : QSystem) : ℕ := Module.finrank ℂ S.space

/-- **Composite system** (Postulate 6; Nielsen–Chuang Postulate 4 / §2.2.8): two systems
compose to a system whose state space is the tensor product of the components'. The
physical content is the *choice* of the tensor product (over, say, a direct sum). -/
noncomputable def QSystem.compose (S T : QSystem) : QSystem :=
  { space := S.space ⊗[ℂ] T.space }

@[inherit_doc] scoped infixr:70 " ⊗ " => QSystem.compose

/-- **A quantum system from a model Hilbert space**: wrap a finite-dimensional complex
Hilbert space `H` as the system whose state space is `H`. The general model-space
constructor — constructions that produce an *anonymous* system (e.g. the ancilla of a
purification, N&C §2.5) use `ofModel`. The concrete
named systems (`qubit`, …) are defined via `ofModel` of their standard model spaces. -/
def QSystem.ofModel (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] : QSystem := { space := H }

@[simp]
theorem QSystem.ofModel_space (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] : (QSystem.ofModel H).space = H := rfl

end AxQM
