/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.StateMajorization

/-!
# Nielsen & Chuang, Exercise 12.20 — removing invertibility from the converse of Theorem 12.15

*(N&C p. 577.)*

Remove the invertibility assumption on rho_psi in converse of Theorem 12.15.

## Context — the invertibility assumption N&C makes

Theorem 12.15 (Nielsen's theorem) is the equivalence "`|ψ⟩ → |φ⟩` by LOCC `⟺ λ_ψ ≺ λ_φ`". In the
**converse** direction (majorization `⟹` LOCC), N&C constructs Alice's measurement from the unitary
mixture `ρ_ψ = ∑ⱼ pⱼ Uⱼ ρ_φ Uⱼ†` supplied by Theorem 12.13 by *defining* operators through
`Mⱼ √ρ_ψ ≡ √pⱼ ρ_φ Uⱼ†`, i.e. `Mⱼ = √pⱼ ρ_φ Uⱼ† ρ_ψ^{-1/2}`. Checking the completeness relation
then reads (N&C eq. (12.165))

`∑ⱼ Mⱼ† Mⱼ = ρ_ψ^{-1/2} (∑ⱼ pⱼ Uⱼ ρ_φ Uⱼ†) ρ_ψ^{-1/2} = ρ_ψ^{-1/2} ρ_ψ ρ_ψ^{-1/2} = I`,

which uses `ρ_ψ^{-1/2}` — hence *assumes `ρ_ψ` is invertible*. This exercise asks to discharge that
assumption; N&C's own remark ("this assumption is easily removed") points at the resolution used
here.

## The formalisation — no invertibility hypothesis

The converse of Theorem 12.15 was already proved **in full generality, with no invertibility
hypothesis on `ρ`**, as the `⟸` half of Nielsen's theorem. The declaration is

* `AxQM.State.LOCCConvertible_of_majorize`
  (in `AxQM/Postulates/API/StateMajorization.lean`) :
  `{ρ σ : State S} (h : ρ.Majorize σ) : ρ.LOCCConvertible σ`.

Its hypothesis is *only* `ρ.Majorize σ` (N&C's `ρ_ψ ≺ ρ_φ`) — there is no rank/invertibility side
condition — so it is exactly the invertibility-free converse this exercise demands. It is the `⟸`
component of Theorem 12.15, `AxQM.State.loccConvertible_iff_majorize`
(`AxQM/NC/Ch12/Theorem12_15.lean`).

## How invertibility is removed — the pseudo-inverse construction

The `ρ_ψ^{-1/2}` of N&C's proof is replaced by the **inverse-square-root pseudo-inverse** `(√ρ)⁺`
(`AxQM.State.sqrtPseudoInverse`): the self-adjoint operator that acts as `1/√·` on the
support of `ρ` and sends `ker ρ` to `0` (spectral, since `1/√x` is discontinuous at `0` — the reason
the honest inverse cannot be used when `ρ` is singular). With
`Mⱼ = √pⱼ · √σ Uⱼ† (√ρ)⁺` (outcomes indexed by `some j`) the completeness sum collapses only to the
**support projector** `Pₛ = (√ρ)⁺ ρ (√ρ)⁺` (`State.supportProjector`), not to `I`. Faithfulness of a
measurement is restored by adjoining **one extra outcome** `M₀ = Pₖ`, the projector onto `ker ρ`
(`State.kernelProjector`, `Pₖ = 1 − Pₛ`), carrying probability `0`. Then:

* **completeness** `∑ᵢ Mᵢ† Mᵢ = Pₛ + Pₖ = 1` (the `Pₛ + Pₖ = 1` identity replacing N&C's
  `ρ^{-1/2} ρ ρ^{-1/2} = I`);
* **support outcomes** `Mⱼ ρ Mⱼ† = pⱼ σ` still hold — since `Pₛ = 1 − Pₖ` and `√σ Uⱼ† Pₖ = 0`
  whenever `pⱼ > 0` (read off from `Pₖ ρ Pₖ = 0`), the kernel correction vanishes;
* **kernel outcome** `M₀ ρ M₀† = Pₖ ρ Pₖ = 0 = 0 · σ`, so the extra outcome never fires on `ρ` and
  changes no physics.

When `ρ` *is* invertible, `Pₖ = 0` and `(√ρ)⁺ = ρ^{-1/2}`, recovering N&C's original construction —
so the general proof specialises to the textbook one, confirming it is a faithful generalisation and
not a different theorem wearing the same name.

The supporting spectral lemmas are in `AxQM/Postulates/API/StateMajorization.lean`:
`State.sqrtPseudoInverse` and its `_apply_eigenbasis` / `isSelfAdjoint_` / `_comp_self` (`si² = ρ⁺`)
/ `_comp_op_comm` lemmas; `State.supportProjector`, `State.kernelProjector` and their
self-adjointness / idempotence / `_comp_op` lemmas.
-/
