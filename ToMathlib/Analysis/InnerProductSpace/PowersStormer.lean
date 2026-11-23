/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.PosNegPart
public import ToMathlib.Analysis.InnerProductSpace.TraceNorm
public import ToMathlib.Analysis.InnerProductSpace.CFC
public import ToMathlib.Analysis.InnerProductSpace.OperatorSum
public import ToMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.TraceDeriv

/-!
# The Powers–Størmer inequality

For positive operators `A, B` on a finite-dimensional complex Hilbert space, the
Hilbert–Schmidt distance of the operators is controlled by the trace-norm distance of their
squares:
`re tr((A - B)²) ≤ ‖A² - B²‖₁`.
This is the **Powers–Størmer inequality** (Powers–Størmer 1970). Applied to the operator square
roots `A = √ρ`, `B = √σ` of two density operators it upgrades the elementary Hilbert–Schmidt
identity `‖√ρ - √σ‖₂² = 2(1 - tr(√ρ √σ))` into the operational bound
`1 - tr(√ρ √σ) ≤ D(ρ, σ)` relating the quantum **affinity** to the trace distance — the
fidelity-family Fuchs–van de Graaf lower bound.

## Proof

Write `C = A - B` (self-adjoint) and `S = A + B`. Let `J = sgn(C)` be the sign operator (`cfc` of
`SignType.sign`, well-defined here because on a finite-dimensional self-adjoint operator every real
function is continuous on the finite spectrum). Then `‖J‖ ≤ 1` and `J·C = C·J = |C| = C⁺ + C⁻`.
Pairing `M := A² - B² = A·C + C·B` with the contraction `J` in the variational characterisation of
the trace norm (`re_hsPairing_le_traceNorm_of_opNorm_le_one`) gives
`re tr(|C|·S) = re tr(J·M) ≤ ‖M‖₁`. Finally the positive/negative-part decomposition `C = C⁺ - C⁻`
(`CFC.posPart_sub_negPart`) with the orthogonality `C⁺ C⁻ = C⁻ C⁺ = 0` yields
`re tr(C²) = re tr((C⁺)²) + re tr((C⁻)²) ≤ re tr(C⁺·S) + re tr(C⁻·S) = re tr(|C|·S)`,
the two middle inequalities coming from `S - C = 2B ≥ 0` and `S + C = 2A ≥ 0` traced against the
positive parts (`re_trace_mul_nonneg_of_nonneg`). The operator inequality `S ≥ |C|` is *false*, but
its trace form against `|C|` holds precisely because the cross terms `tr(C⁺ C⁻)` vanish — the reason
the proof runs through the parts rather than through `|C|` directly.

## Main results

* `ContinuousLinearMap.re_trace_sub_mul_self_le_traceNorm_mul_self_sub_mul_self` — the
  Powers–Størmer inequality `re tr((A - B)*(A - B)) ≤ ‖A*A - B*B‖₁` for positive operators `A, B`.
-/

open scoped InnerProductSpace

@[expose] public section

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

set_option maxHeartbeats 400000 in
-- The proof composes many operator identities (CFC of the sign function, the positive/negative-part
-- decomposition, trace cyclicity, the trace-norm duality) whose combined elaboration over the
-- heavily-instanced operator algebra `E →L[ℂ] E` exceeds the default heartbeat budget.
/-- **The Powers–Størmer inequality** (Powers–Størmer 1970). For positive operators `A, B` on a
finite-dimensional complex Hilbert space, the Hilbert–Schmidt distance of `A` and `B` is bounded by
the trace-norm distance of their squares:
`re tr((A - B)·(A - B)) ≤ ‖A·A - B·B‖₁`.
The witness in the trace-norm variational characterisation is the sign operator `J = sgn(A - B)`
(`cfc SignType.sign`), a contraction with `J·(A - B) = |A - B|`; the positive/negative parts of
`A - B` then convert the (false) operator inequality `A + B ≥ |A - B|` into its valid trace form
against `|A - B|`, the cross terms vanishing by `C⁺ C⁻ = 0`. -/
theorem re_trace_sub_mul_self_le_traceNorm_mul_self_sub_mul_self {A B : E →L[ℂ] E} (hA : 0 ≤ A)
    (hB : 0 ≤ B) :
    RCLike.re (LinearMap.trace ℂ E (((A - B) * (A - B) : E →L[ℂ] E) : E →ₗ[ℂ] E))
      ≤ (A * A - B * B).traceNorm := by
  have hAsa : IsSelfAdjoint A := .of_nonneg hA
  have hBsa : IsSelfAdjoint B := .of_nonneg hB
  set C := A - B with hCdef
  set M := A * A - B * B with hMdef
  set S := A + B with hSdef
  have hCsa : IsSelfAdjoint C := hAsa.sub hBsa
  set rt := ContinuousLinearMap.reTraceCLM E with hrtdef
  have hrt_apply : ∀ T : E →L[ℂ] E, rt T = RCLike.re (LinearMap.trace ℂ E (T : E →ₗ[ℂ] E)) := by
    intro T; rw [hrtdef]; exact ContinuousLinearMap.reTraceCLM_apply T
  have hcyc : ∀ X Y : E →L[ℂ] E, rt (X * Y) = rt (Y * X) := by
    intro X Y
    rw [hrt_apply, hrt_apply, ContinuousLinearMap.toLinearMap_mul,
        ContinuousLinearMap.toLinearMap_mul,
      LinearMap.trace_mul_comm]
  have hnn : ∀ X Y : E →L[ℂ] E, 0 ≤ X → 0 ≤ Y → 0 ≤ rt (X * Y) := by
    intro X Y hX hY; rw [hrt_apply]; exact re_trace_mul_nonneg_of_nonneg hX hY
  -- The sign operator `J = sgn C`, a self-adjoint contraction with `J·C = C·J = |C|`.
  set J := cfc (fun x : ℝ => (SignType.sign x : ℝ)) C with hJdef
  have hJsa : IsSelfAdjoint J := cfc_predicate _ C
  have hJnorm : ‖J‖ ≤ 1 := by
    apply norm_cfc_le (by norm_num); intro x hx
    rw [Real.norm_eq_abs]
    rcases lt_trichotomy x 0 with h | h | h
    · rw [sign_neg h]; norm_num
    · subst h; simp
    · rw [sign_pos h]; norm_num
  have hQ0 : (0 : E →L[ℂ] E) ≤ C⁺ := CFC.posPart_nonneg C
  have hR0 : (0 : E →L[ℂ] E) ≤ C⁻ := CFC.negPart_nonneg C
  have hQR : C⁺ * C⁻ = 0 := CFC.posPart_mul_negPart C
  have hRQ : C⁻ * C⁺ = 0 := CFC.negPart_mul_posPart C
  have hCQR : C⁺ - C⁻ = C := CFC.posPart_sub_negPart C hCsa
  -- `|C| = C⁺ + C⁻`, identifying the cfc of `|·|` directly through `CFC.abs` (`= cfc ‖·‖`).
  have habs : cfc (fun x : ℝ => |x|) C = C⁺ + C⁻ := by
    rw [CFC.posPart_add_negPart C hCsa, CFC.abs_eq_cfc_norm C hCsa]
    exact cfc_congr fun x hx => (Real.norm_eq_abs x).symm
  have hJC : J * C = C⁺ + C⁻ := by
    rw [hJdef, hCsa.cfc_mul_id fun x : ℝ => (SignType.sign x : ℝ),
      show (fun x : ℝ => (SignType.sign x : ℝ) * x) = (fun x : ℝ => |x|) from
        funext fun x => sign_mul_self x, habs]
  have hCJ : C * J = C⁺ + C⁻ := by
    rw [hJdef, hCsa.cfc_id_mul fun x : ℝ => (SignType.sign x : ℝ),
      show (fun x : ℝ => x * (SignType.sign x : ℝ)) = (fun x : ℝ => |x|) from
        funext fun x => self_mul_sign x, habs]
  -- `M = A·C + C·B`, whence `tr(J·M) = tr(|C|·S)`.
  have hM : M = A * C + C * B := by rw [hMdef, hCdef, mul_sub, sub_mul]; abel
  have htr : rt (J * M) = rt ((C⁺ + C⁻) * S) := by
    have e1 : J * M = J * A * C + J * C * B := by rw [hM, mul_add, ← mul_assoc, ← mul_assoc]
    have e2 : rt (J * A * C) = rt ((C⁺ + C⁻) * A) := by rw [hcyc (J * A) C, ← mul_assoc, hCJ]
    have e3 : rt (J * C * B) = rt ((C⁺ + C⁻) * B) := by rw [hJC]
    rw [e1, map_add, e2, e3, ← map_add, hSdef, mul_add]
  -- `tr(C²) = tr((C⁺)²) + tr((C⁻)²)`, the cross terms vanishing.
  have hCsq : rt (C * C) = rt (C⁺ * C⁺) + rt (C⁻ * C⁻) := by
    have hCC : C * C = C⁺ * C⁺ + C⁻ * C⁻ := by
      conv_lhs => rw [← hCQR]
      rw [sub_mul, mul_sub, mul_sub, hQR, hRQ]; abel
    rw [hCC, map_add]
  have hSCpos : (0 : E →L[ℂ] E) ≤ S - C := by
    rw [hSdef, hCdef, show A + B - (A - B) = B + B by abel]; exact add_nonneg hB hB
  have hSCpos2 : (0 : E →L[ℂ] E) ≤ S + C := by
    rw [hSdef, hCdef, show A + B + (A - B) = A + A by abel]; exact add_nonneg hA hA
  -- `C⁺·C = (C⁺)²` and `C⁻·C = -(C⁻)²`, using `C⁺ C⁻ = C⁻ C⁺ = 0`.
  have hQCeq : C⁺ * C = C⁺ * C⁺ := by
    conv_rhs => rw [← sub_zero (C⁺ * C⁺), ← hQR, ← mul_sub, hCQR]
  have hRCeq : C⁻ * C = -(C⁻ * C⁻) := by
    conv_rhs => rw [← zero_sub (C⁻ * C⁻), ← hRQ, ← mul_sub, hCQR]
  have hb1 : rt (C⁺ * C⁺) ≤ rt (C⁺ * S) := by
    have h0 : 0 ≤ rt (C⁺ * (S - C)) := hnn _ _ hQ0 hSCpos
    rw [mul_sub, hQCeq, map_sub] at h0; linarith
  have hb2 : rt (C⁻ * C⁻) ≤ rt (C⁻ * S) := by
    have h0 : 0 ≤ rt (C⁻ * (S + C)) := hnn _ _ hR0 hSCpos2
    rw [mul_add, hRCeq, map_add, map_neg] at h0; linarith
  have hbound : rt (C * C) ≤ rt ((C⁺ + C⁻) * S) := by
    rw [hCsq, add_mul, map_add]; linarith
  -- The trace-norm duality bound at the contraction `J`.
  have hpair : RCLike.re (M.hsPairing J) = rt (J * M) := by
    rw [ContinuousLinearMap.hsPairing_eq, hJsa.adjoint_eq, hrt_apply]
    rfl
  have hdual : rt (J * M) ≤ M.traceNorm := by
    rw [← hpair]; exact M.re_hsPairing_le_traceNorm_of_opNorm_le_one hJnorm
  calc RCLike.re (LinearMap.trace ℂ E (((A - B) * (A - B) : E →L[ℂ] E) : E →ₗ[ℂ] E))
      = rt (C * C) := by rw [hrt_apply, hCdef]
    _ ≤ rt ((C⁺ + C⁻) * S) := hbound
    _ = rt (J * M) := htr.symm
    _ ≤ M.traceNorm := hdual

end ContinuousLinearMap
