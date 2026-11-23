/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.CFCSqrtTraceInequality

/-!
# The Gram-operator trace form of the pretty-good-measurement error estimate

For a continuous linear map `V : F →L[ℂ] G` between finite-dimensional complex Hilbert spaces —
whose columns are the (typical-subspace–compressed) codeword eigenvectors `|Ẽ_c⟩` of Nielsen &
Chuang's Box 12.5 — with **total operator** `S = V ∘ V⋆` on `G` and **Gram operator**
`Γ = V⋆ ∘ V` on `F`, this file evaluates the two "spurs" on the right-hand side of the trace form
of the square-root operator inequality (`CFCSqrtTraceInequality`, N&C eqs. (12.92)–(12.93)) as
**physical traces** of `S` and of the eigenvalue-weighted operator `T = V ∘ Λ ∘ V⋆` on `G`.

Writing `sp = tr_F` for the trace on the index space `F` (Nielsen & Chuang's "spur") and `tr = tr_G`
for the trace on the ambient (physical) space `G`, and `Λ ≥ 0` for the diagonal eigenvalue-weight
operator on `F`, cross-space trace cyclicity (`LinearMap.trace_comp_comm'`) gives

`sp(Λ(1 - Γ))  = tr_F Λ  −  tr(V Λ V⋆)`,
`sp(Λ(1 - Γ)²) = tr_F Λ  −  2·tr(V Λ V⋆)  +  tr(S · V Λ V⋆)`,

so, feeding these into the trace inequality `2·sp(Λ(1 - √Γ)) ≤ sp(Λ(1 - Γ)²) + sp(Λ(1 - Γ))`
(`ContinuousLinearMap.two_mul_re_trace_one_sub_cfc_sqrt_mul_le_add_re_trace`), the decoding deficit
`sp(Λ(1 - √Γ))` of the pretty-good (square-root) POVM is bounded by physical traces:

`2·re sp(Λ(1 - √Γ))  ≤  2·re tr_F Λ  −  3·re tr(V Λ V⋆)  +  re tr(S · V Λ V⋆)`.

This is the operator-trace form of the "calculating the spurs" step of **Nielsen & Chuang's Box
12.5** (eq. (12.94)), the achievability half of the **Holevo–Schumacher–Westmoreland theorem**
(`χ(E) = C⁽¹⁾(E)`, N&C Theorem 12.8): each of the three physical traces `tr_F Λ`, `tr(V Λ V⋆)`,
`tr(S · V Λ V⋆)` becomes — once `V`, `Λ` are instantiated to the concrete codeword-eigenvector
apparatus — one of the physical error terms `tr(σ_M(I − P))`, `tr(P σ_M P P_{M'})`,
`tr(σ_M(I − P_M))` of the random-coding error estimate (12.79).

## What this file provides

* `ContinuousLinearMap.trace_gram_mul` — the cross-space cyclicity core
  `tr_F((V⋆·V)·A) = tr_G(V·A·V⋆)`: pairing the Gram operator `Γ = V⋆·V` against any `A` on `F`
  equals pairing `A` conjugated by `V` (i.e. `V·A·V⋆`) on `G`.
* `ContinuousLinearMap.trace_one_sub_gram_mul` — the **linear spur**
  `tr_F((1 - Γ)·Λ) = tr_F Λ − tr_G(V·Λ·V⋆)` (N&C `sp(Λ(E − Γ))`).
* `ContinuousLinearMap.trace_one_sub_gram_sq_mul` — the **quadratic spur**
  `tr_F((1 - Γ)²·Λ) = tr_F Λ − 2·tr_G(V·Λ·V⋆) + tr_G(S·(V·Λ·V⋆))` (N&C `sp(Λ(E − Γ)²)`).
* `ContinuousLinearMap.two_mul_re_trace_one_sub_cfc_sqrt_gram_le` — the **headline bound**
  `2·re tr_F((1 - √Γ)·Λ) ≤ 2·re tr_F Λ − 3·re tr_G(V·Λ·V⋆) + re tr_G(S·(V·Λ·V⋆))` (N&C eq. (12.94)),
  the trace inequality with its right-hand side evaluated into physical traces.

## Proof

The two spur identities are cross-space trace cyclicity: `Γ·A = V⋆·(V·A)` and
`tr_F(V⋆·(V·A)) = tr_G((V·A)·V⋆) = tr_G(V·A·V⋆)` (`LinearMap.trace_comp_comm'`); expanding
`(1 - Γ)·Λ` and `(1 - Γ)²·Λ` (`noncomm_ring`) and applying this to each `Γ`-power term, together
with the linearity of the trace, gives the identities.  The headline bound rewrites the spurs of the
trace inequality `two_mul_re_trace_one_sub_cfc_sqrt_mul_le_add_re_trace` (whose hypothesis
`0 ≤ Γ = V⋆·V` is automatic, `isPositive_self_comp_adjoint`) and collects the real parts.

-/

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace ContinuousLinearMap

variable {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G]

/-- **Cyclicity against the Gram operator.**  For `V : F →L[ℂ] G` with Gram operator
`Γ = V⋆ ∘ V` on `F`, and any `A : F →L[ℂ] F`,

`tr_F(Γ · A) = tr_G(V · A · V⋆)`,

i.e. pairing the Gram operator against `A` on the index space `F` equals the trace of `A`
conjugated by `V` on the ambient space `G`.  Immediate from the cyclicity identity
`ContinuousLinearMap.trace_conj_adjoint` (`tr_G(V·A·V⋆) = tr_F(V⋆·V·A)`) after folding
`Γ · A = V⋆ · (V · A)`. -/
theorem trace_gram_mul (V : F →L[ℂ] G) (A : F →L[ℂ] F) :
    LinearMap.trace ℂ F ((((adjoint V).comp V) * A : F →L[ℂ] F) : F →ₗ[ℂ] F)
      = LinearMap.trace ℂ G ((V.comp (A.comp (adjoint V)) : G →L[ℂ] G) : G →ₗ[ℂ] G) := by
  have h : (((adjoint V).comp V) * A : F →L[ℂ] F) = (adjoint V).comp (V.comp A) := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  rw [h]
  exact (ContinuousLinearMap.trace_conj_adjoint V A).symm

/-- **The linear spur of the Gram trace form** (Nielsen & Chuang, Box 12.5, `sp(Λ(E − Γ))`).  For
`V : F →L[ℂ] G` with Gram operator `Γ = V⋆ ∘ V`, and `Λ : F →L[ℂ] F`,

`tr_F((1 - Γ)·Λ) = tr_F Λ − tr_G(V·Λ·V⋆)`.

The `1`-term of the trace is `tr_F Λ`; the `Γ`-term is carried to the ambient space by
`trace_gram_mul`. -/
theorem trace_one_sub_gram_mul (V : F →L[ℂ] G) (Λ : F →L[ℂ] F) :
    LinearMap.trace ℂ F (((1 - (adjoint V).comp V) * Λ : F →L[ℂ] F) : F →ₗ[ℂ] F)
      = LinearMap.trace ℂ F (Λ : F →ₗ[ℂ] F)
        - LinearMap.trace ℂ G ((V.comp (Λ.comp (adjoint V)) : G →L[ℂ] G) : G →ₗ[ℂ] G) := by
  have hexp : ((1 - (adjoint V).comp V) * Λ : F →L[ℂ] F)
      = Λ - ((adjoint V).comp V) * Λ := by noncomm_ring
  rw [hexp, ContinuousLinearMap.toLinearMap_sub, map_sub, trace_gram_mul]

/-- **The quadratic spur of the Gram trace form** (Nielsen & Chuang, Box 12.5, `sp(Λ(E − Γ)²)`).
For `V : F →L[ℂ] G` with total operator `S = V ∘ V⋆`, Gram operator `Γ = V⋆ ∘ V`, and
`Λ : F →L[ℂ] F`,

`tr_F((1 - Γ)²·Λ) = tr_F Λ − 2·tr_G(V·Λ·V⋆) + tr_G(S·(V·Λ·V⋆))`.

Expanding `(1 - Γ)²·Λ = Λ − Γ·Λ − Γ·Λ + Γ·(Γ·Λ)` (`noncomm_ring`), the two `Γ·Λ` terms are each
`trace_gram_mul` (giving `tr_G(V·Λ·V⋆)`), and the `Γ·(Γ·Λ)` term is `trace_gram_mul` applied to
`A = Γ·Λ`, whose conjugation `V·(Γ·Λ)·V⋆` folds to `S·(V·Λ·V⋆)`. -/
theorem trace_one_sub_gram_sq_mul (V : F →L[ℂ] G) (Λ : F →L[ℂ] F) :
    LinearMap.trace ℂ F (((1 - (adjoint V).comp V) ^ 2 * Λ : F →L[ℂ] F) : F →ₗ[ℂ] F)
      = LinearMap.trace ℂ F (Λ : F →ₗ[ℂ] F)
        - LinearMap.trace ℂ G ((V.comp (Λ.comp (adjoint V)) : G →L[ℂ] G) : G →ₗ[ℂ] G)
        - LinearMap.trace ℂ G ((V.comp (Λ.comp (adjoint V)) : G →L[ℂ] G) : G →ₗ[ℂ] G)
        + LinearMap.trace ℂ G
            (((V.comp (adjoint V)).comp (V.comp (Λ.comp (adjoint V))) : G →L[ℂ] G)
              : G →ₗ[ℂ] G) := by
  have hexp : ((1 - (adjoint V).comp V) ^ 2 * Λ : F →L[ℂ] F)
      = Λ - ((adjoint V).comp V) * Λ - ((adjoint V).comp V) * Λ
        + ((adjoint V).comp V) * (((adjoint V).comp V) * Λ) := by noncomm_ring
  -- the folding of the conjugated double-Gram term to `S · (V·Λ·V⋆)`
  have hfold : V.comp ((((adjoint V).comp V) * Λ).comp (adjoint V))
      = (V.comp (adjoint V)).comp (V.comp (Λ.comp (adjoint V))) := by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  rw [hexp, ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_sub,
      ContinuousLinearMap.toLinearMap_sub,
    map_add, map_sub, map_sub, trace_gram_mul, trace_gram_mul (A := ((adjoint V).comp V) * Λ),
    hfold]

/-- **The Gram-operator trace form of the pretty-good-measurement error estimate**
(Nielsen & Chuang, Box 12.5, eq. (12.94)).  For `V : F →L[ℂ] G` with total operator `S = V ∘ V⋆`,
Gram operator `Γ = V⋆ ∘ V`, and a positive weight `Λ ≥ 0` on `F`,

`2·re tr_F((1 - √Γ)·Λ)  ≤  2·re tr_F Λ  −  3·re tr_G(V·Λ·V⋆)  +  re tr_G(S·(V·Λ·V⋆))`,

where `√Γ = cfc Real.sqrt Γ`.  This is the trace inequality
`2·re tr_F((1 - √Γ)·Λ) ≤ re tr_F((1 - Γ)²·Λ) + re tr_F((1 - Γ)·Λ)`
(`two_mul_re_trace_one_sub_cfc_sqrt_mul_le_add_re_trace`, whose hypothesis `0 ≤ Γ = V⋆·V` is
automatic) with its right-hand-side spurs evaluated as physical traces of `S` and `T = V·Λ·V⋆`
(`trace_one_sub_gram_sq_mul`, `trace_one_sub_gram_mul`).  The decoding deficit `sp(Λ(1 - √Γ))` of
the pretty-good (square-root) POVM is thereby bounded by physical operator traces, ready for the
concrete codeword-eigenvector instantiation of the random-coding error estimate (12.79). -/
theorem two_mul_re_trace_one_sub_cfc_sqrt_gram_le (V : F →L[ℂ] G) {Λ : F →L[ℂ] F} (hΛ : 0 ≤ Λ) :
    2 * RCLike.re (LinearMap.trace ℂ F
        (((1 - cfc Real.sqrt ((adjoint V).comp V)) * Λ : F →L[ℂ] F) : F →ₗ[ℂ] F))
      ≤ 2 * RCLike.re (LinearMap.trace ℂ F (Λ : F →ₗ[ℂ] F))
        - 3 * RCLike.re (LinearMap.trace ℂ G ((V.comp (Λ.comp (adjoint V)) : G →L[ℂ] G)
            : G →ₗ[ℂ] G))
        + RCLike.re (LinearMap.trace ℂ G
            (((V.comp (adjoint V)).comp (V.comp (Λ.comp (adjoint V))) : G →L[ℂ] G)
              : G →ₗ[ℂ] G)) := by
  have hΓ : 0 ≤ (adjoint V).comp V := by
    have h := isPositive_self_comp_adjoint (adjoint V)
    rw [adjoint_adjoint] at h
    exact nonneg_iff_isPositive.mpr h
  have h := two_mul_re_trace_one_sub_cfc_sqrt_mul_le_add_re_trace hΓ hΛ
  rw [trace_one_sub_gram_sq_mul, trace_one_sub_gram_mul] at h
  simp only [map_add, map_sub] at h
  linarith

end ContinuousLinearMap
