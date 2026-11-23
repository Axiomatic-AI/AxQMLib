/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SameNonzeroSpectrum
import AxQM.Postulates.API.SchmidtReducedSpectrum

/-!
# AxQM.Postulates.API — a pure ancilla does not change the non-zero spectrum

Adjoining a *pure* ancilla `ω` on the right of a state `ρ` leaves the non-zero spectrum of `ρ`
untouched: `λ_{ρ ⊗ |ω⟩⟨ω|} ≅ λ_ρ`. Since `|ω⟩⟨ω|` has the single non-zero eigenvalue `1`, the
product operator `ρ ⊗ |ω⟩⟨ω|` has exactly the eigenvalues of `ρ` (each carried by the eigenvector
`|eᵢ⟩ ⊗ |ω⟩`), and the padding by an orthonormal ancilla contributes no new non-zero entries.

This is the spectral fact behind the "pure ancilla is free" steps of Nielsen & Chuang's
information-theoretic arguments (e.g. that appending a pure reference does not change the entropy of
a state), stated for the relation `State.SameNonzeroSpectrum`
(`AxQM/Postulates/API/SameNonzeroSpectrum.lean`).

## Main statements

* `State.sameNonzeroSpectrum_tmul_pure_right` — `(ρ ⊗ |ω⟩⟨ω|) ≅ ρ` for a pure ancilla `ω`.
* `State.sameNonzeroSpectrum_evolve_tmul_pure_right` — `U (ρ ⊗ |ω⟩⟨ω|) U† ≅ ρ` for a unitary `U`
  on `S ⊗ T`: the spectrum of the pre-trace state of the dilation `State.dilatedChannel U ω`,
  the necessity (`⟹`) ingredient of Nielsen & Chuang Exercise 12.22.
-/

open scoped TensorProduct
open InnerProductSpace

namespace AxQM

variable {S T : QSystem}

/-- **A pure ancilla does not change the non-zero spectrum.** Adjoining a pure state `ω` on the
right of a state `ρ` leaves the non-zero eigenvalue spectrum of `ρ` unchanged:
`λ_{ρ ⊗ |ω⟩⟨ω|} ≅ λ_ρ`.

Proof: `ρ` has the spectral decomposition `ρ.op = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|` over its canonical orthonormal
eigenbasis `e = ρ.eigenbasis` (`State.op_eq_sum_eigenvalueDist_rankOne`). Tensoring with `|ω⟩⟨ω|`
(`State.tmul_op`, `PureState.toState_op`) and
distributing `TensorProduct.mapL` over the sum turns each rank-one term into
`|eᵢ ⊗ ω⟩⟨eᵢ ⊗ ω|` (`InnerProductSpace.rankOne_tmul_self`), so
`(ρ ⊗ |ω⟩⟨ω|).op = ∑ᵢ λᵢ |eᵢ ⊗ ω⟩⟨eᵢ ⊗ ω|`. The family `i ↦ eᵢ ⊗ ω` is orthonormal (`e`
orthonormal, `‖ω‖ = 1`), so the recognition lemma
`State.sameNonzero_eigenvalueDist_of_orthonormal_rankOne_sum` identifies the weight list `λ` with
the reduced spectrum, giving `λ_ρ ≅ λ_{ρ ⊗ |ω⟩⟨ω|}`; symmetry finishes. -/
theorem State.sameNonzeroSpectrum_tmul_pure_right (ρ : State S) (ω : PureState T) :
    (ρ.tmul ω.toState).SameNonzeroSpectrum ρ := by
  set b := ρ.eigenbasis
  -- The tensored family `i ↦ eᵢ ⊗ ω` is orthonormal.
  have he : Orthonormal ℂ (fun i => b i ⊗ₜ[ℂ] ω.vec) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [TensorProduct.inner_tmul, inner_self_eq_norm_sq_to_K, ω.normalized]
    rw [orthonormal_iff_ite.mp b.orthonormal i j]
    simp
  -- Spectral decomposition of the composite operator.
  have hop_comp : (ρ.tmul ω.toState).op
      = ∑ i, (ρ.eigenvalueDist i : ℂ) •
          (rankOne ℂ (b i ⊗ₜ[ℂ] ω.vec)) (b i ⊗ₜ[ℂ] ω.vec) := by
    rw [State.tmul_op, PureState.toState_op, ρ.op_eq_sum_eigenvalueDist_rankOne]
    simp only [TensorProduct.mapL_sum_left, TensorProduct.mapL_smul_left]
    exact Finset.sum_congr rfl fun i _ => by rw [InnerProductSpace.rankOne_tmul_self]
  exact ((ρ.tmul ω.toState).sameNonzero_eigenvalueDist_of_orthonormal_rankOne_sum he
    ρ.eigenvalueDist hop_comp).symm

/-- **A local unitary on a pure-ancilla-adjoined state preserves the non-zero spectrum.** For a
state `ρ` on `S`, a unitary `U` on `S ⊗ T`, and a pure ancilla `ω` on `T`, the joint state
`U (ρ ⊗ |ω⟩⟨ω|) U†` has the same non-zero spectrum as `ρ`: `λ_{U(ρ ⊗ |ω⟩⟨ω|)U†} ≅ λ_ρ`.

This is the spectrum of the pre-partial-trace state behind Nielsen & Chuang's single-system dilation
`State.dilatedChannel U ω = (U.evolve (ρ ⊗ |ω⟩⟨ω|)).reducedLeft` (whose left marginal is the channel
output `E(ρ)`): unitary conjugation permutes the eigenbasis without changing the eigenvalues
(`State.sameNonzeroSpectrum_evolve`), and the pure ancilla contributes no new non-zero eigenvalue
(`State.sameNonzeroSpectrum_tmul_pure_right`), so the joint state keeps exactly `ρ`'s spectrum.

It is the necessity (`⟹`) ingredient of Nielsen & Chuang Exercise 12.22: presenting Alice's local
channel `E_A` by its dilation `(U_A, ω_A)`, the joint Alice-side state `U_A (ρ_ψ ⊗ |ω_A⟩⟨ω_A|) U_A†`
— which traces down to `ρ_φ = E_A(ρ_ψ)` — carries `ρ_ψ`'s spectrum `λ_ψ`, pinning `λ_ψ` to the
spectrum of that joint state. -/
theorem State.sameNonzeroSpectrum_evolve_tmul_pure_right (ρ : State S) (U : Evolution (S ⊗ T))
    (ω : PureState T) : (U.evolve (ρ.tmul ω.toState)).SameNonzeroSpectrum ρ :=
  (State.sameNonzeroSpectrum_evolve U (ρ.tmul ω.toState)).trans
    (State.sameNonzeroSpectrum_tmul_pure_right ρ ω)

end AxQM
