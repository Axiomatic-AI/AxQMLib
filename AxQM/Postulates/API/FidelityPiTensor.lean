/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.FidelityPure
import AxQM.Postulates.API.PureState
import AxQM.Postulates.PiTensorState
import Mathlib.Analysis.Complex.Norm

/-!
# Overlap and fidelity of product pure states factorize over the factors

For a finite family of pure states, the amplitude (`overlap`) and the fidelity of two *product*
pure states `⨂ᵢ ψᵢ`, `⨂ᵢ φᵢ` factorize as the product, over the factors, of the per-factor
amplitudes / fidelities:

* `PureState.overlap_piTensor` — `⟨⨂ᵢ ψᵢ | ⨂ᵢ φᵢ⟩ = ∏ᵢ ⟨ψᵢ | φᵢ⟩`;
* `PureState.fidelity_piTensor` — `F(⨂ᵢ ψᵢ, ⨂ᵢ φᵢ) = ∏ᵢ F(ψᵢ, φᵢ)`.

Both are immediate consequences of the fundamental inner-product formula for elementary tensors,
`PiTensorProduct.inner_tprod_tprod` (`⟨⨂ᵢ aᵢ | ⨂ᵢ bᵢ⟩ = ∏ᵢ ⟨aᵢ | bᵢ⟩`), transported to
pure states through `PureState.piTensor_vec` (the state vector of `⨂ᵢ ψᵢ` is the elementary tensor
`⨂ₜ[ℂ] i, (ψ i).vec`) and, for fidelity, `State.fidelity_toState_toState` (`F(ψ, φ) = ‖⟨ψ | φ⟩‖`)
together with the multiplicativity of the complex norm (`Complex.norm_prod`).

These are the multi-factor siblings of the existing two-factor lemma `PureState.overlap_tmul`; they
are the workhorse for computing the amplitude of a many-qubit product state in a product basis (e.g.
Schumacher compression, N&C Box 12.4 / Exercise 12.6).
-/

open scoped InnerProductSpace BigOperators

namespace AxQM

variable {ι : Type*} [Fintype ι] {S : ι → QSystem}

/-- **The amplitude of a product pure state factorizes.** For finite families of pure states
`ψ φ : (i : ι) → PureState (S i)`, the overlap of the two product states `⨂ᵢ ψᵢ` and `⨂ᵢ φᵢ`
equals the product over the factors of the per-factor overlaps: `⟨⨂ᵢ ψᵢ | ⨂ᵢ φᵢ⟩ = ∏ᵢ ⟨ψᵢ | φᵢ⟩`.
The multi-factor form of `PureState.overlap_tmul`, from `PiTensorProduct.inner_tprod_tprod` via
`PureState.piTensor_vec`. -/
theorem PureState.overlap_piTensor (ψ φ : (i : ι) → PureState (S i)) :
    (PureState.piTensor ψ).overlap (PureState.piTensor φ) = ∏ i, (ψ i).overlap (φ i) := by
  simp only [PureState.overlap_def, PureState.piTensor_vec]
  exact PiTensorProduct.inner_tprod_tprod ℂ (fun i => (ψ i).vec) (fun i => (φ i).vec)

/-- **The fidelity of a product pure state factorizes.** For finite families of pure states
`ψ φ : (i : ι) → PureState (S i)`, the fidelity of the two product states `⨂ᵢ ψᵢ` and `⨂ᵢ φᵢ`
equals the product over the factors of the per-factor fidelities: `F(⨂ᵢ ψᵢ, ⨂ᵢ φᵢ) = ∏ᵢ F(ψᵢ, φᵢ)`.
Proved from `PureState.overlap_piTensor` (or directly `PiTensorProduct.inner_tprod_tprod`) using
`State.fidelity_toState_toState` (`F = ‖overlap‖`) and multiplicativity of the complex norm. -/
theorem PureState.fidelity_piTensor (ψ φ : (i : ι) → PureState (S i)) :
    (PureState.piTensor ψ).toState.fidelity (PureState.piTensor φ).toState
      = ∏ i, (ψ i).toState.fidelity (φ i).toState := by
  rw [State.fidelity_toState_toState, ← PureState.overlap_def, PureState.overlap_piTensor,
    Complex.norm_prod]
  exact Finset.prod_congr rfl fun i _ => by
    rw [State.fidelity_toState_toState, PureState.overlap_def]

end AxQM
