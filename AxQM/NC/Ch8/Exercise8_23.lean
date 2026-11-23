/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DualRailAmplitudeDamping

/-!
# Nielsen & Chuang, Exercise 8.23 (amplitude damping of dual-rail qubits)

*(N&C p. 381.)*

Show E_AD⊗E_AD on dual-rail |ψ⟩=a|01⟩+b|10⟩ has operation elements E0dr, E1dr (error detection).

## The answer

The dual-rail encoding shares one excitation between two optical modes ("rails"),
`|ψ⟩ = a|01⟩ + b|10⟩`; each rail independently undergoes amplitude damping, so the joint channel is
`E_AD ⊗ E_AD`, with operation elements the four tensor products `Eᵢ ⊗ Eⱼ` (`i, j ∈ {0,1}`) of the
single-qubit operation elements `E₀ = diag(1, √(1-γ))`, `E₁ = √γ|0⟩⟨1|` (eq. 8.108). Applied to the
codeword `|ψ⟩`:

* `E₀ ⊗ E₀ : |ψ⟩ ↦ √(1-γ) |ψ⟩` — nothing is lost; `E₀ ⊗ E₀` is the scalar `√(1-γ)` on the
  codespace, i.e. `E₀ᵈʳ = √(1-γ) I`;
* `E₀ ⊗ E₁ : |ψ⟩ ↦ √γ·a |00⟩` and `E₁ ⊗ E₀ : |ψ⟩ ↦ √γ·b |00⟩` — a photon is lost from one rail,
  sending the state to the vacuum `|00⟩`;
* `E₁ ⊗ E₁ : |ψ⟩ ↦ 0` — both rails cannot lose the single excitation at once.

Every loss branch lands in `|00⟩`, and `⟨00|ψ⟩ = 0`: the error is orthogonal to every codeword, so
"are there zero photons?" is a nondestructive error-detection test.

**Fidelity note.** N&C summarise the two loss branches by a *single* error element
`E₁ᵈʳ = √γ(|00⟩⟨01| + |00⟩⟨10|)` (eq. 8.115). But `E_AD ⊗ E_AD`'s two loss branches `E₀ ⊗ E₁` and
`E₁ ⊗ E₀` leave the environment in the *orthogonal* states `|0⟩⊗|1⟩`, `|1⟩⊗|0⟩`, so they add
**incoherently** (giving `|00⟩` weight `γ(|a|²+|b|²) = γ`), whereas the single `E₁ᵈʳ` sums them
*coherently* to `√γ(a+b)|00⟩` (weight `γ|a+b|²`); for `a = b = 1/√2` that is `2γ ≠ γ`, and
`(E₀ᵈʳ)†E₀ᵈʳ + (E₁ᵈʳ)†E₁ᵈʳ ≠ I`. The faithful reduced error description is thus the *pair*
`√γ|00⟩⟨01|`, `√γ|00⟩⟨10|` (the restrictions of `E₀ ⊗ E₁`, `E₁ ⊗ E₀`), not the single `E₁ᵈʳ`. The
qualitative error-detection content (nothing, or collapse to the orthogonal `|00⟩`) is correct and
is what is formalised; the single-`E₁ᵈʳ` normalization is corrected here rather than repeated.

## The formalisation

The whole development is raw operator algebra on the two-qubit space `H ⊗ H`: bare `LinearMap`s,
`TensorProduct.map`, an `OrthonormalBasis`, and inner products. Compare the rest of the
amplitude-damping exercises 8.20–8.22 (`AxQM/Concrete/AmplitudeDampingChannel.lean`).

The formalisation is in `AxQM/Concrete/DualRailAmplitudeDamping.lean`, the dual-rail development:

* `AxQM.Concrete.dualRailVec` — the codeword `|ψ⟩ = a|01⟩ + b|10⟩` (eq. 8.113);
* `dualRailVec_ampDampMap_zero_zero` / `_zero_one` / `_one_zero` / `_one_one` — the four
  operation-element branches `Eᵢ ⊗ Eⱼ` applied to `|ψ⟩` (√(1-γ)|ψ⟩, √γ·a|00⟩, √γ·b|00⟩, 0);
* `dualRailVec_inner_ketZeroZero` — the error state `|00⟩` is orthogonal to every codeword
  (`⟨00|ψ⟩ = 0`), the error-detection property;
* `dualRailADChannel` / `dualRailADChannel_apply_dualRail` — the error-detection **process** on
  the density operator: `E_AD ⊗ E_AD(|ψ⟩⟨ψ|) = (1-γ)|ψ⟩⟨ψ| + γ|00⟩⟨00|` for a normalised codeword
  (nothing happens, weight `1-γ`; or collapse to `|00⟩`, weight `γ`);
* `dualRailKrausZeroDR`, `dualRailErrZeroOne`, `dualRailErrOneZero` — the **faithful reduced
  operation elements** `E₀ᵈʳ = √(1-γ) I`, `√γ|00⟩⟨01|`, `√γ|00⟩⟨10|`, with
  `dualRailErr*_apply_dualRailVec` tying the pair to the loss branches `E₀ ⊗ E₁`, `E₁ ⊗ E₀`, and
  `dualRailFaithful_completeness` — `Σ (Eᵏ)† Eᵏ = I` on the codespace (trace preservation);
* `dualRailErrCombined` and `dualRailErrCombined_not_completeness` — the **formal refutation** of
  N&C's single `E₁ᵈʳ = √γ(|00⟩⟨01| + |00⟩⟨10|)` (eq. 8.115): the coherent two-element operator sum
  `{E₀ᵈʳ, E₁ᵈʳ}` fails completeness on the codespace (`dualRailErrCombined_completeness_fails`
  exhibits the off-diagonal `γ` leak), so it is not a trace-preserving decomposition of
  `E_AD ⊗ E_AD`; the faithful reduced description is the *pair* above.
-/
