/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.EntropyExchange
public import ToMathlib.Analysis.InnerProductSpace.VonNeumannEntropyFano

/-! # The quantum Fano inequality

For a state `ρ` (a density operator on a `d`-dimensional complex inner product space `H`, so
`d = finrank ℂ H`) and a trace-preserving quantum operation with operation elements
`E : ι → (H →L[ℂ] H)` (`∑ᵢ Eᵢ† Eᵢ = 1`), the **entropy exchange** `S(ρ, E)` and the **entanglement
fidelity** `F(ρ, E)` obey the **quantum Fano inequality** (Nielsen & Chuang, *Quantum Computation
and Quantum Information*, Theorem 12.9, eq. (12.112)):
`S(ρ, E) ≤ H(F(ρ, E)) + (1 - F(ρ, E)) · log (d² - 1)`,
where `H` is the binary Shannon entropy.

This file is the assembly step of the development spread across
`ToMathlib/Analysis/InnerProductSpace/VonNeumannEntropyFano.lean` (the density-operator Fano bound),
`…/VonNeumannEntropyGram.lean` (the Gram / sum-of-rank-ones entropy equality), and
`…/EntropyExchange.lean` (the entropy exchange `S(ρ, E)`, the reference-plus-system output state
`ρ_{R'Q'}`, and its entanglement-fidelity overlap). It carries out the two observations of N&C's
proof (eqs. (12.113)–(12.115)):

* the reference-plus-system output state `ρ_{R'Q'}` lives on the `d²`-dimensional Hilbert–Schmidt
  space `H ⊗ H` (`Module.finrank_tensorProduct`), with entropy `S(ρ_{R'Q'}) = S(ρ, E)`
  (`entropyExchange_eq_vonNeumannEntropy_entropyExchangeState`) and diagonal entry against the unit
  vector `vec √ρ` (N&C's `|RQ⟩`, `norm_matricize_symm_cfc_sqrt`) equal to the entanglement fidelity
  `⟨√ρ, ρ_{R'Q'} √ρ⟩ = F(ρ, E)` (`re_inner_entropyExchangeState_sqrt_eq_entanglementFidelity`);
* the density-operator Fano bound `S(σ) ≤ H(⟨ψ, σ ψ⟩) + (1 - ⟨ψ, σ ψ⟩) · log (D - 1)`
  (`IsDensityOp.vonNeumannEntropy_le_binEntropy_add`, N&C eqs. (12.113)–(12.115)) applied to
  `σ = ρ_{R'Q'}`, `ψ = vec √ρ`, `D = finrank ℂ (H ⊗ H) = d²`.

Composing these turns the density-operator Fano bound at dimension `d²` into the quantum Fano
inequality. The whole development is stated for operators and Kraus families; the statement of
Nielsen & Chuang Theorem 12.9 is in `AxQM/NC/Ch12/Theorem12_9.lean`.

## Main results

* `ContinuousLinearMap.entropyExchange_le_binEntropy_entanglementFidelity_add` — the quantum Fano
  inequality `S(ρ, E) ≤ H(F(ρ, E)) + (1 - F(ρ, E)) · log (d² - 1)` (N&C Theorem 12.9, eq. (12.112)).

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.4.1 (Theorem 12.9, eqs. (12.107)–(12.115)).
-/

open scoped InnerProductSpace TensorProduct ComplexConjugate
open InnerProductSpace

@[expose] public section

namespace ContinuousLinearMap

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The quantum Fano inequality** (Nielsen & Chuang, *Quantum Computation and Quantum
Information*, Theorem 12.9, eq. (12.112)). For a density operator `ρ` on a `d`-dimensional space
`H` (`d = finrank ℂ H`) and a trace-preserving quantum operation with operation elements
`E : ι → (H →L[ℂ] H)` (`∑ᵢ Eᵢ† Eᵢ = 1`), the entropy exchange is bounded by the binary Shannon
entropy of the entanglement fidelity:
`S(ρ, E) ≤ H(F(ρ, E)) + (1 - F(ρ, E)) · log (d² - 1)`.

The proof realizes the reference-plus-system output state `ρ_{R'Q'} = entropyExchangeState b ρ E`
as a density operator on the `d²`-dimensional Hilbert–Schmidt space `H ⊗ H`
(`entropyExchangeState_isDensityOp`, using trace preservation), applies the density-operator Fano
bound `IsDensityOp.vonNeumannEntropy_le_binEntropy_add` there with the unit vector `vec √ρ`
(N&C's initial `|RQ⟩`, `norm_matricize_symm_cfc_sqrt`), and rewrites the two sides:
`S(ρ_{R'Q'}) = S(ρ, E)` (`entropyExchange_eq_vonNeumannEntropy_entropyExchangeState`) and the
diagonal entry `⟨vec √ρ, ρ_{R'Q'} (vec √ρ)⟩ = F(ρ, E)`
(`re_inner_entropyExchangeState_sqrt_eq_entanglementFidelity`), while the dimension of the space is
`finrank ℂ (H ⊗ H) = d²` (`Module.finrank_tensorProduct`). -/
theorem entropyExchange_le_binEntropy_entanglementFidelity_add
    {ρ : H →L[ℂ] H} (hρ : ρ.IsDensityOp) {E : ι → H →L[ℂ] H}
    (htp : ∑ i, adjoint (E i) * E i = 1) :
    entropyExchange ρ E ≤ Real.binEntropy (entanglementFidelity ρ E)
      + (1 - entanglementFidelity ρ E) * Real.log ((Module.finrank ℂ H : ℝ) ^ 2 - 1) := by
  -- Realize `ρ_{R'Q'}` on the `d²`-dimensional Hilbert–Schmidt space `H ⊗ H`, with the unit
  -- Hilbert–Schmidt vector `vec √ρ`, and apply the density-operator Fano bound there.
  set b := stdOrthonormalBasis ℂ H with hb
  have hM : (entropyExchangeState b ρ E).IsDensityOp := entropyExchangeState_isDensityOp b hρ htp
  have hψ : ‖(TensorProduct.matricize b).symm (cfc Real.sqrt ρ)‖ = 1 :=
    norm_matricize_symm_cfc_sqrt b hρ
  have hbound := hM.vonNeumannEntropy_le_binEntropy_add hψ
  -- `S(ρ_{R'Q'}) = S(ρ, E)` and `⟨vec √ρ, ρ_{R'Q'} (vec √ρ)⟩ = F(ρ, E)`.
  rw [re_inner_entropyExchangeState_sqrt_eq_entanglementFidelity b hρ.nonneg E,
    ← entropyExchange_eq_vonNeumannEntropy_entropyExchangeState b hρ.nonneg E] at hbound
  -- The Hilbert–Schmidt space has dimension `finrank ℂ (H ⊗ H) = d²`.
  rw [show ((Module.finrank ℂ H : ℝ) ^ 2 - 1)
      = ((Module.finrank ℂ (H ⊗[ℂ] H) : ℝ) - 1) by
    rw [Module.finrank_tensorProduct]; push_cast; ring]
  exact hbound

end ContinuousLinearMap
