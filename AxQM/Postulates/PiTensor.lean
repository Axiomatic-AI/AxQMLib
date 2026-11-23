/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.InnerProductSpace.PiTensorProduct
import AxQM.Postulates.QSystem
import AxQM.Postulates.SystemIso

/-!
# AxQM.Postulates — indexed composite systems (`⨂ₛ i, S i`)

Postulate 6 states that systems *compose* by the tensor product of their state spaces.
`QSystem.compose` (`S ⊗ T`, in `QSystem.lean`) is the binary form. This file introduces the
**indexed** form `QSystem.piTensor` (`⨂ₛ i, S i`), the composite of a whole finite family of
systems over the n-ary `PiTensorProduct`.

The binary `S ⊗ T` is recovered as the two-factor case (up to a system isomorphism
`S ⊗ T ≃ₛ ⨂ₛ i : Fin 2, ![S, T] i`), not the other way around. The many-body constructions
(`⨂ₛ i : Fin n, S i`) then read directly off the index, with no associator/reindex bookkeeping
needed to state them.

Like `QSystem.compose`, this builds the composite system from the Hilbert space
`⨂[ℂ] i, (S i).space`. The per-factor `NormedAddCommGroup`/`InnerProductSpace ℂ`/
`FiniteDimensional ℂ` instances flow from each `S i`'s bundled instances, so the n-ary
inner-product-space structure (`ToMathlib.Analysis.InnerProductSpace.PiTensorProduct`) fires
automatically; finite-dimensionality comes from the tensor-product basis
(`Basis.piTensorProduct`).

## Main definitions

* `QSystem.piTensor` (`⨂ₛ i, S i`) — the indexed composite system of a finite family
  `S : ι → QSystem`: the system whose state space is the n-ary tensor product `⨂[ℂ] i, (S i).space`.
* `QSystem.binaryPiEquiv` — the binary ↔ indexed bridge: the system isomorphism
  `S ⊗ T ≃ₛ ⨂ₛ i : Fin 2, ![S, T] i`, exhibiting the binary `compose` as the two-factor
  special case of the indexed `⨂ₛ`.
-/

open scoped TensorProduct

namespace AxQM

/-- **Indexed composite system** (Postulate 6, n-ary form): a finite family of systems
`S : ι → QSystem` composes to a system whose state space is the n-ary tensor product
`⨂[ℂ] i, (S i).space`. The binary `S ⊗ T` is the two-factor case. The physical content is the
*choice* of the tensor product; the mathematics (including finite-dimensionality, via the
tensor-product basis) is that of `PiTensorProduct`. -/
noncomputable def QSystem.piTensor {ι : Type*} [Fintype ι] (S : ι → QSystem) : QSystem where
  space := ⨂[ℂ] i, (S i).space
  findim := Module.Basis.finiteDimensional_of_finite
    (Basis.piTensorProduct fun i ↦ Module.finBasis ℂ (S i).space)

@[inherit_doc QSystem.piTensor]
scoped notation3:100 "⨂ₛ "(...)", "r:67:(scoped f => QSystem.piTensor f) => r

/-- The state space of an indexed composite is the n-ary tensor product of the factors' state
spaces — `QSystem.space` unfolds by definition. -/
@[simp] theorem QSystem.piTensor_space {ι : Type*} [Fintype ι] (S : ι → QSystem) :
    (⨂ₛ i, S i).space = ⨂[ℂ] i, (S i).space := rfl

/-! ## Binary ↔ indexed bridge

The binary composite `S ⊗ T` is the two-factor case of the indexed `⨂ₛ`: there is a system
isomorphism `S ⊗ T ≃ₛ ⨂ₛ i : Fin 2, ![S, T] i` (`QSystem.binaryPiEquiv`), so the binary
`compose` is *recovered* from `piTensor`, not the other way around. -/

/-- The two-factor family `Fin 1 ⊕ Fin 1 → QSystem` splitting `S` on the left and `T` on the
right. Its re-indexing along `finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2` is `![S, T]`
(`QSystem.binaryFamily_finSumFinEquiv`), the shape that lets the head-split isometries
(`tmulEquivDepₗᵢ` / `subsingletonEquivₗᵢ` / `reindexₗᵢ`) assemble the bridge. -/
private def QSystem.binaryFamily (S T : QSystem) : Fin 1 ⊕ Fin 1 → QSystem :=
  Sum.elim (fun _ ↦ S) (fun _ ↦ T)

/-- Re-indexing the two-factor `Sum` family along `finSumFinEquiv` recovers `![S, T]`. Checked
at the two concrete `Fin 2` indices (`finSumFinEquiv.symm 0 = .inl 0`, `.symm 1 = .inr 0`). -/
private theorem QSystem.binaryFamily_finSumFinEquiv (S T : QSystem) :
    (fun i : Fin 2 ↦ binaryFamily S T (finSumFinEquiv.symm i)) = ![S, T] := by
  funext i; fin_cases i <;> rfl

/-- The isometry underlying `QSystem.binaryPiEquiv`:
`S.space ⊗[ℂ] T.space ≃ₗᵢ[ℂ] ⨂[ℂ] i : Fin 2, (![S, T] i).space`, splitting the index type
`Fin 2` as `Fin 1 ⊕ Fin 1`. `PiTensorProduct.tmulEquivDepₗᵢ` bridges the binary tensor of the
two single-factor tensor powers to the `Sum`-indexed tensor power, the `Fin 1` powers collapse
via `PiTensorProduct.subsingletonEquivₗᵢ`, and `PiTensorProduct.reindexₗᵢ` along `finSumFinEquiv`
recovers the `Fin 2` index (`binaryFamily_finSumFinEquiv`). -/
noncomputable def QSystem.binaryPiIsometry (S T : QSystem) :
    S.space ⊗[ℂ] T.space ≃ₗᵢ[ℂ] ⨂[ℂ] i : Fin 2, (![S, T] i).space := by
  rw [← binaryFamily_finSumFinEquiv S T]
  have split := PiTensorProduct.tmulEquivDepₗᵢ ℂ (fun i ↦ (binaryFamily S T i).space)
  have collapse := TensorProduct.congrIsometry
    (PiTensorProduct.subsingletonEquivₗᵢ ℂ (fun i ↦ (binaryFamily S T (.inl i)).space) 0).symm
    (PiTensorProduct.subsingletonEquivₗᵢ ℂ (fun i ↦ (binaryFamily S T (.inr i)).space) 0).symm
  exact collapse.trans
    (split.trans (PiTensorProduct.reindexₗᵢ ℂ (fun i ↦ (binaryFamily S T i).space) finSumFinEquiv))

/-- **Binary composition is the two-factor indexed tensor**:
the system isomorphism `S ⊗ T ≃ₛ ⨂ₛ i : Fin 2, ![S, T] i`, exhibiting binary `⊗` as the special
case of the indexed `⨂ₛ`. The underlying isometry is `QSystem.binaryPiIsometry`. -/
noncomputable def QSystem.binaryPiEquiv (S T : QSystem) : (S ⊗ T) ≃ₛ QSystem.piTensor ![S, T] :=
  ⟨QSystem.binaryPiIsometry S T⟩

/-! ## The `n`-fold tensor power `S ^⊗ₛ n` -/

/-- **`n`-fold tensor power** of a system: `S ^⊗ₛ n = ⨂ₛ (_ : Fin n), S`, the composite of
`n` copies of `S`. The constant-family case of the indexed
composite `⨂ₛ` — `n` registers of the same system. -/
noncomputable def QSystem.tensorPow (S : QSystem) (n : ℕ) : QSystem := ⨂ₛ _ : Fin n, S

-- The subscript `ₛ` (system) is deliberate: bare `^⊗` is a global Mathlib notation for
-- `LinearMap.tensorPow` (`TensorPower/Endomorphism`, in this file's import closure). As a
-- `scoped` 3-glyph token, `^⊗ₛ` wins longest-match over `^⊗` wherever `AxQM` is
-- open/scoped (every intended use site); outside that scope it would fall back to `^⊗`.
@[inherit_doc QSystem.tensorPow] scoped infixr:75 " ^⊗ₛ " => QSystem.tensorPow

/-- `S ^⊗ₛ n` is the indexed composite of the constant family `fun _ : Fin n ↦ S` — the
system-level unfold lemma (use in place of `unfold QSystem.tensorPow`). -/
theorem QSystem.tensorPow_eq (S : QSystem) (n : ℕ) :
    S ^⊗ₛ n = QSystem.piTensor (fun _ : Fin n ↦ S) := rfl

/-- The state space of `S ^⊗ₛ n` is the `n`-ary tensor power of `S.space` — `QSystem.space`
unfolds by definition. -/
@[simp] theorem QSystem.tensorPow_space (S : QSystem) (n : ℕ) :
    (S ^⊗ₛ n).space = ⨂[ℂ] _ : Fin n, S.space := rfl

end AxQM
