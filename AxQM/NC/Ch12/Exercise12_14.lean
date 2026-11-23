/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.SubsystemErrorCorrectionSufficiency

/-!
# Nielsen & Chuang, Exercise 12.14 (decoupling is sufficient to correct errors on a subsystem)

Show rho^{RQ1}=rho^R tensor rho^{Q1} is sufficient to correct errors on Q1.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, Exercise 12.14 (p. 567).

**Context (N&C §12.4.2).** An `[n, k]` quantum code lives in `Q`, with orthonormal codewords `|x⟩`
and code projector `P`. Purifying the maximally-mixed code state `P/2^k` against a reference `R` of
the same dimension gives the maximally-entangled `|RQ⟩ = (1/√2^k) ∑ₓ |x⟩ ⊗ |x⟩`. Split `Q = Q₁ ⊗ Q₂`
into the subsystem `Q₁` on which errors occur and the remaining qubits `Q₂`. The
information-theoretic reversibility condition `ρ^{R'E'} = ρ^{R'} ⊗ ρ^{E'}` — that after the
noise the reference and the environment are uncorrelated — specialises, for the error that
swaps `Q₁` out into the environment, to `ρ^{RQ1} = ρ^R ⊗ ρ^{Q1}`. N&C's preceding discussion shows
this decoupling is *necessary* for correction; this exercise asks for *sufficiency*.

## Route (Knill–Laflamme)

Rather than N&C's constructive Schmidt-decomposition recovery (Eqs. (12.137)–(12.141)), the
formalisation shows the decoupling condition equivalent to the code **protecting the left factor**
`Q₁` — `∀ A, ∃ c, P (A ⊗ I) P = c • P` — i.e. to the **Knill–Laflamme conditions** for the complete
`Q₁`-error family `{|a⟩⟨b| ⊗ I_{Q₂}}` (which spans every operator on `Q₁`), whence correctability
follows from the already-formalised **Theorem 10.1**. The pivot is the codeword-reduced-operator
family `σᵢⱼ = Tr_{Q₂} |wᵢ⟩⟨wⱼ|`: both the decoupling condition and the protection condition hold
exactly when `σ` is *scalar-diagonal* (`σᵢⱼ = δᵢⱼ ρ₁`), and chaining the two equivalences (threading
`ρ₁ = ρ^{Q1}`) yields `decoupling ⟹ ProtectsLeftFactor ⟹ QEC conditions ⟹ ∃ recovery`.

## The formalisation

Exercise 12.14 is about operators — the code projector
`P : (Q₁ ⊗ Q₂).space →L[ℂ] (Q₁ ⊗ Q₂).space`, the error operation elements `|a⟩⟨b| ⊗ I`, the
partial trace `Tr_{Q₂}`, and the recovery family / `ContinuousLinearMap.Corrects`. As for
Theorem 10.1 (`AxQM/NC/Ch10/Theorem10_1.lean`), they are treated at the level of operators.

The subsystem error-correction development is in `AxQM/Postulates/API/`:

* `SubsystemErrorCorrection.lean` — `leftFactorOp` (`A ↦ A ⊗ I_{Q₂}`), `leftFactorErrorBasis` (the
  complete `Q₁`-error family `{|a⟩⟨c| ⊗ I}`), `ProtectsLeftFactor` (the subsystem protection
  predicate), and `ProtectsLeftFactor.satisfiesQECConditions` — **protection ⟹ Knill–Laflamme
  conditions** for the `Q₁`-error family.
* `SubsystemErrorCorrectionMarginal.lean` — `codePurifyVec` (the maximally-mixed code purification
  `|RQ⟩ = ∑ₓ eₓ ⊗ wₓ`) with its marginals: `ρ^R = I/N` (`codePurifyVec_partialTraceRight_ref_eq_id`)
  and the block form of `ρ^{RQ1}` (`codePurifyVec_partialTraceRight_assoc`).
* `SubsystemErrorCorrectionDecoupling.lean` — `codePurify_decoupledLeftFactor_iff`: the
  **decoupling** `ρ^{RQ1} = ρ^R ⊗ ρ₁ ⟺ σ scalar-diagonal`.
* `SubsystemErrorCorrectionProtection.lean` — `protectsLeftFactor_iff_codewordReducedScalar`:
  **protection** `ProtectsLeftFactor P ⟺ σ scalar-diagonal`.
* `SubsystemErrorCorrectionSufficiency.lean` — the assembly:
  * `decoupledLeftFactor_protectsLeftFactor` — **decoupling ⟹ `ProtectsLeftFactor P`** (chaining the
    two equivalences above);
  * `satisfiesQECConditions_of_decoupledLeftFactor` — **decoupling ⟹ the Knill–Laflamme conditions**
    for the complete `Q₁`-error family;
  * `exists_correction_of_decoupledLeftFactor` — **decoupling ⟹ a trace-preserving recovery
    operation correcting the `Q₁`-errors** (`ContinuousLinearMap.Corrects`, via Theorem 10.1);
  * `exists_correctionChannel_of_decoupledLeftFactor` — **decoupling ⟹ a recovery *channel***
    (`IsChannel`) returning every code state to the same scalar multiple of itself — the physical
    statement of correction. This is the sufficiency the exercise asks for.

The projector helpers (`codewordProj_isSelfAdjoint` / `codewordProj_comp_self` /
`codewordProj_ne_zero`, in `SubsystemErrorCorrectionSufficiency.lean`) supply the self-adjoint,
idempotent, nonzero code projector `P = ∑ᵢ |wᵢ⟩⟨wᵢ|` that Theorem 10.1 consumes.
-/
