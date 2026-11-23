/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import ToMathlib.Analysis.InnerProductSpace.CFC

/-!
# The square-root operator inequality of the pretty-good-measurement error estimate

For a positive operator `A ≥ 0` on a complex Hilbert space, this file records the
functional-calculus operator inequality

`2 • (1 - √A)  ≤  (1 - A)² + (1 - A)`

(with `√A = cfc Real.sqrt A` the operator square root).  It is the crux operator inequality of the
error estimate for the **pretty-good (square-root) measurement** — Nielsen & Chuang's Box 12.5,
eqs. (12.89)–(12.91), used to bound the average decoding error in the achievability half of the
**Holevo–Schumacher–Westmoreland theorem** (`χ(E) = C⁽¹⁾(E)`, N&C Theorem 12.8).  There it is
applied to the Gram operator `Γ` of the (typical-subspace–compressed) codeword eigenvectors: the
diagonal decoding overlap `α_{(M,K),(M,K)}` is `⟨Ẽ| Γ^{-1/2} |Ẽ⟩`-shaped, and controlling `1 - α`
reduces — via `2(1 - √Γ) ≤ (1 - Γ)² + (1 - Γ)` — to the "false-decoding" cross terms that the
random-coding average then makes decay.

## What this file provides

* `ContinuousLinearMap.two_smul_one_sub_cfc_sqrt_le` — the operator inequality
  `2 • (1 - √A) ≤ (1 - A)² + (1 - A)` for `0 ≤ A`.

## Proof

Both sides are continuous-functional-calculus images of `A`, so the operator inequality follows from
the **scalar** inequality `2(1 - √x) ≤ (1 - x)² + (1 - x)` on the (nonnegative) spectrum of `A` by
`cfc_mono`.  The scalar inequality is the nonnegativity, for `x ≥ 0`, of

`(1 - x)² + (1 - x) - 2(1 - √x)  =  √x · (√x - 1)² · (√x + 2)  =  x² - 3x + 2√x  ≥  0`

(writing `s = √x`, the difference is `s⁴ - 3s² + 2s = s (s - 1)² (s + 2)`).  This sidesteps
Nielsen & Chuang's algebraic route through `(1 + √Γ)⁻²` entirely: `cfc_mono` needs only the
pointwise scalar bound, and continuity on the spectrum is automatic (the functions are continuous
on all of `ℝ`).

-/

@[expose] public section

open ContinuousFunctionalCalculus

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The square-root operator inequality of the pretty-good-measurement error estimate**
(Nielsen & Chuang, Box 12.5, eqs. (12.89)–(12.91)): for a positive operator `A ≥ 0`,

`2 • (1 - √A)  ≤  (1 - A)² + (1 - A)`,

where `√A = cfc Real.sqrt A`.  It is the operator inequality that turns the diagonal decoding
overlap `1 - α` of the pretty-good (square-root) measurement into the "false-decoding" cross terms
of the HSW random-coding error bound.

The proof lifts the scalar inequality `2(1 - √x) ≤ (1 - x)² + (1 - x)` (valid for every `x ≥ 0`,
since the difference is `√x · (√x - 1)² · (√x + 2) = x² - 3x + 2√x ≥ 0`) through `cfc_mono`: the
spectrum of `A ≥ 0` is nonnegative (`spectrum_nonneg_of_nonneg`), and continuity on the spectrum is
free (the functions are continuous on all of `ℝ`).  Both `cfc` images are then rewritten to closed
operator form via the `cfc` ring homomorphism lemmas. -/
theorem two_smul_one_sub_cfc_sqrt_le {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    (2 : ℝ) • (1 - cfc Real.sqrt A) ≤ (1 - A) ^ 2 + (1 - A) := by
  -- The scalar inequality `2(1 - √x) ≤ (1 - x)² + (1 - x)` on the nonnegative spectrum of `A`.
  have hscal : ∀ x ∈ spectrum ℝ A, 2 * (1 - Real.sqrt x) ≤ (1 - x) ^ 2 + (1 - x) := fun x hx => by
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA hx
    have hs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
    have hsnn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    -- The difference is `√x · (√x - 1)² · (√x + 2)`: multiply the hint `(√x - 1)²(√x + 2) ≥ 0`
    -- by `√x ≥ 0`.
    nlinarith [mul_nonneg (sq_nonneg (Real.sqrt x - 1)) (by linarith : (0 : ℝ) ≤ Real.sqrt x + 2),
      hs, hsnn]
  -- Lift to operators by CFC monotonicity; the functions are continuous on all of `ℝ`.
  have key := cfc_mono (a := A) (f := fun x => 2 * (1 - Real.sqrt x))
      (g := fun x => (1 - x) ^ 2 + (1 - x)) hscal
      ((continuous_const.mul (continuous_const.sub Real.continuous_sqrt)).continuousOn)
      (by fun_prop)
  -- Translate both `cfc` images to closed operator form.
  have h1sub : cfc (fun x : ℝ => 1 - x) A = 1 - A := by
    rw [cfc_sub (fun _ => (1 : ℝ)) (fun x => x) A (by fun_prop) (by fun_prop),
      cfc_const 1 A, map_one, cfc_id' ℝ A]
  have hL : cfc (fun x : ℝ => 2 * (1 - Real.sqrt x)) A = (2 : ℝ) • (1 - cfc Real.sqrt A) := by
    rw [cfc_const_mul (2 : ℝ) (fun x => 1 - Real.sqrt x) A
        ((continuous_const.sub Real.continuous_sqrt).continuousOn)]
    congr 1
    rw [cfc_sub (fun _ => (1 : ℝ)) Real.sqrt A (by fun_prop) Real.continuous_sqrt.continuousOn,
      cfc_const 1 A, map_one]
  have hR : cfc (fun x : ℝ => (1 - x) ^ 2 + (1 - x)) A = (1 - A) ^ 2 + (1 - A) := by
    rw [cfc_add A (fun x => (1 - x) ^ 2) (fun x => 1 - x) (by fun_prop) (by fun_prop),
      cfc_pow (fun x => 1 - x) 2 A (by fun_prop), h1sub]
  rw [hL, hR] at key
  exact key

end ContinuousLinearMap
