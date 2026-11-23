/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ApproxError
import AxQM.Postulates.API.QuantumFourierTransform
import AxQM.Postulates.API.QftApproxEvolution
import AxQM.Concrete.QftGateCount

/-!
# Nielsen & Chuang, Exercise 5.6 — the approximate quantum Fourier transform

*(N&C p. 221.)*

Approximate QFT: with R_k precision 1/p(n), error E(U,V)=max||(U-V)|psi>|| is Theta(n^2/p(n)).

## The mechanism, and what is formalised

The error measure `E(U,V) = max_{|ψ⟩} ‖(U−V)|ψ⟩‖` is exactly Box 4.1's gate error
`Evolution.gateError U V = ‖U.op − V.op‖` (`AxQM/Postulates/API/ApproxError.lean`). The exercise's
`Θ` has two halves — an `O` (upper) accuracy guarantee and an order-matching `Ω` (lower) bound —
**both of which are formalised over these declarations, and combined into a fully two-sided
`Θ`-sandwich on the specific coherent realisation** (`qftApprox_gateError_mem_Icc`): the error of
the very transform `V` that N&C describes is pinned on both sides to `Θ(n²·Δ)`.

**Upper bound `O(n²/p(n))` — "polynomial precision suffices" — FORMALISED, via Box 4.1's chaining
bound** (N&C eq. 4.63) `E(∏ⱼ Uⱼ, ∏ⱼ Vⱼ) ≤ ∑ⱼ E(Uⱼ, Vⱼ)` (`Evolution.gateError_prod_le`), whose
uniform-precision reading `E(∏ Uⱼ, ∏ Vⱼ) ≤ (#gates)·Δ` is `Evolution.gateError_prod_le_uniform`.
The QFT circuit's imprecise gates are its controlled-`Rₖ` phase rotations, of which there are
`Concrete.qftControlledRkCount n = n(n-1)/2 = Θ(n²)` (`Concrete.qftControlledRkCount_isTheta_sq`;
the Hadamards and swaps carry no continuous parameter and are exact), so implementing each to
precision `Δ = 1/p(n)` bounds the error by `E(U, V) ≤ qftControlledRkCount n · Δ = O(n²/p(n))`. This
half is **universal** over factorisations, so it covers the real approximate-QFT circuit:

* `qftEvolution_gateError_le_length_mul` — for any gate-circuit factorisation `l` of the QFT
  (`(l.map Prod.fst).prod = qftEvolution (2^n)`) with each gate to precision `Δ`, error
  `≤ (length l)·Δ`.
* `qftApprox_gateError_le` — at the Figure 5.1 count: `E(U, V) ≤ qftControlledRkCount n · Δ`.
* `qftApprox_gateError_le_div` — with `Δ = 1/p(n)`: `E(U, V) ≤ qftControlledRkCount n / p(n)`;
  combined with `Concrete.qftApproxErrorBound_isTheta` this is the `O(n²/p(n))` accuracy guarantee.

**Lower bound `Ω(n²/p(n))` — the bound is order-tight, so the scaling is `Θ` and not merely `O` —
FORMALISED (faithful, coherent `Rₖ` perturbation).** N&C fixes `V` as "the transform which results
if the *controlled-`Rₖ` gates* are performed to precision `Δ`", so a faithful `Ω(n²/p(n))`
lower-bounds the error of the QFT with **its own elementary `Rₖ` gates** perturbed — the errors of
the `Θ(n²)` small-angle rotations adding *coherently* in the worst case. This is exactly what
`qftApproxEvolution n Δ` (`AxQM/Postulates/API/QftApproxEvolution.lean`) is: the gate-level Figure
5.1 circuit `Concrete.qftGateCircuit n` with every controlled-`Rₖ` shifted by `+Δ`
(`Concrete.qftGateCircuitPerturbed`), promoted to an `Evolution`. On the worst-case all-ones input
`|1…1⟩` every controlled-`Rₖ` is active, so the per-wire phase errors `εₛ = (n-1-s)Δ` add coherently
to `∑ₛ εₛ = qftControlledRkCount n · Δ = n(n-1)Δ/2`, and the coherent-accumulation distance bound
(`Concrete.phaseProdVec_scaled_dist_ge` → `Concrete.qftGateCircuitPerturbed_allOnes_dist_ge`, lifted
to the operator norm by `qftApproxEvolution_op_allOnes_dist_ge`) gives, via
`Evolution.gateError_apply_le` at the unit input `|1…1⟩`,

`E(qftEvolution (2^n), qftApproxEvolution n Δ) ≥ qftControlledRkCount n · Δ / π = n(n-1)Δ/(2π)`.

* `qftApprox_gateError_ge` — the faithful `Ω` at the Figure 5.1 count: `E(U, V) ≥ n(n-1)Δ/(2π)`.
* `qftApprox_gateError_ge_div` — with `Δ = 1/p(n)`: `E(U, V) ≥ qftControlledRkCount n / (p(n)·π)`;
  with `Concrete.qftApproxErrorBound_isTheta` this is the `Ω(n²/p(n))` matching lower bound.

Because the gate-level circuit is a *formal* object here, this `Ω` is not a proxy: it perturbs the
QFT's own `Rₖ` gates, and `qftApproxEvolution` is genuinely a decomposition of the QFT into
elementary gates (`Concrete.qftGateCircuit_eq_qftMatrix`). This is why the *abstract*
tightness result (`Evolution.exists_factorisation_gateError_ge`,
`AxQM/Postulates/API/ApproxErrorTight.lean`) — a global-phase witness that holds verbatim with
`qftEvolution` replaced by the identity, and so establishes none of the exercise's `Rₖ`-specific
content — is not used for the `Ω` bound in this file.

**The two-sided `Θ`-sandwich on the specific realisation `V` — FORMALISED.** The universal `O` half
above bounds *every* `Δ`-precision realisation, but N&C's `V` is the *specific* transform with each
controlled-`Rₖ` shifted by `Δ` — namely `qftApproxEvolution`. Applying Box 4.1's chaining bound to
that transform's own Figure 5.1 factorisation gives the **specific-`V` upper bound**
`E(U, qftApproxEvolution n Δ) ≤ qftControlledRkCount n · Δ` directly. The mechanism is the concrete
matrix chaining bound `Concrete.qftGateCircuit_sub_qftGateCircuitPerturbed_norm_le`: both the ideal
circuit `qftGateCircuit n` and the perturbed `qftGateCircuitPerturbed n Δ` are the reverse product
of the *same* gate list except that each controlled-`Rₖ` is shifted by `+Δ`, so
`‖qftGateCircuit n − qftGateCircuitPerturbed n Δ‖ ≤ ∑ᵢ ‖(gate)ᵢ − (gate')ᵢ‖`
(`norm_listProd_sub_listProd_le`) collapses to `qftControlledRkCount n · |Δ|` — the exact Hadamards
and swap drop out, and each of the `Θ(n²)` controlled-`Rₖ` gates is diagonal with operator-norm
error `2|sin(Δ/2)| ≤ |Δ|`. The lemma `qftApproxEvolution_gateError_le` transports this to
`E(U,V) = ‖U.op − V.op‖` (`Matrix.cstar_norm_def`), and the main results are:

* `qftApprox_gateError_le_specific` — the specific-`V` upper bound `E(U, qftApproxEvolution n Δ) ≤
  qftControlledRkCount n · Δ` (`0 ≤ Δ`).
* `qftApprox_gateError_le_specific_div` — with `Δ = 1/p(n)`:
  `E(U, V) ≤ qftControlledRkCount n / p(n) = O(n²/p(n))`, the specific-`V` counterpart of the
  universal `qftApprox_gateError_le_div`.
* `qftApprox_gateError_mem_Icc` — the **two-sided sandwich**: in the regime
  `0 ≤ qftControlledRkCount n · Δ ≤ π`,
  `E(U, qftApproxEvolution n Δ) ∈ [qftControlledRkCount n · Δ / π, qftControlledRkCount n · Δ]`.
  The two bounds differ only by the constant `π`, so `E(U, V) = Θ(n²·Δ)` on the one
  realisation `V`; with `Δ = 1/p(n)` and `Concrete.qftApproxErrorBound_isTheta` this is the
  `Θ(n²/p(n))` scaling of the approximate-QFT error — the conclusion of Exercise 5.6.

Because the gate-level circuit is a *formal* object, both halves of the sandwich are about the QFT's
own `Rₖ` gates (not a proxy): the `Ω` perturbs them coherently, and the `O` chains their individual
precisions.

## Fidelity notes

1. **What the `O` half covers, and how the circuit enters.** The upper bounds are universal over
   factorisations `l` (`hfact`, `hlen`), so they apply to the genuine Figure 5.1 circuit once its
   `Rₖ` gates are within `Δ`. The quadratic gate count is itself a *theorem*
   (`Concrete.qftControlledRkCount = n(n-1)/2` via the Gauss sum
   `Concrete.qftControlledRkCount_eq_sum`), not an assumption.

2. **The `Ω` is faithful, not proxied.** The exercise's `Ω` is inherently about the coherent
   accumulation of the *actual* controlled-`Rₖ` gate errors; a global-phase witness on the
   monolithic `qftEvolution` would be QFT-agnostic and so miss that content. The `Ω` here instead
   perturbs the QFT's own `Rₖ` gates through the gate-level Figure 5.1 circuit
   (`qftApproxEvolution`), so it is the real coherent-accumulation bound.

3. **The universal `O` and the specific-`V` `O`.** Two upper bounds appear, for two purposes. The
   *universal* `O` (`qftApprox_gateError_le` and `_le_div`, N&C's "polynomial precision suffices")
   bounds *every* `Δ`-precision realisation `V` via an arbitrary Figure 5.1 factorisation — it needs
   no gate-level object, only that each gate is within `Δ`. The *specific-`V`* `O`
   (`qftApprox_gateError_le_specific`) instead bounds the one realisation `qftApproxEvolution` for
   which the coherent `Ω` also holds, by chaining that transform's *own* Figure 5.1 factorisation;
   pairing the two on the same `V` is what makes `qftApprox_gateError_mem_Icc` a genuine two-sided
   `Θ` on a single object rather than an `O` over one class and an `Ω` over another.

4. **The `Θ` holds only in the small-error regime.** `E(U,V) = ‖U.op − V.op‖ ≤ ‖U.op‖ + ‖V.op‖
   ≤ 2` for *any* two unitaries, so `E` is bounded by `2` and the literal `Θ(n²/p(n))` can hold only
   where `n²/p(n)` stays bounded — i.e. `p(n) = Ω(n²)`, the regime the exercise operates in
   ("polynomial precision *sufficient to guarantee polynomial accuracy*": one takes `p(n)` large
   enough to make the error small). Accordingly the `Ω` half and the two-sided sandwich
   (`qftApprox_gateError_ge`, `qftApprox_gateError_mem_Icc`) carry the explicit regime hypothesis
   `qftControlledRkCount n · Δ ≤ π`; the `O` half needs no such restriction. This regime restriction
   is inherent to the error measure, not a weakening.

## Where the ingredients are

The gate error `E(U,V)` and its chaining bound, the imperfect transform `qftApproxEvolution` and
its operator-level all-ones distance / specific-`V` upper bounds
(`qftApproxEvolution_op_allOnes_dist_ge`, `qftApproxEvolution_gateError_le`) are in
`AxQM/Postulates/API/QftApproxEvolution.lean` (Box 4.1); the gate-count arithmetic, the coherent
all-ones distance, the matrix chaining bound
`Concrete.qftGateCircuit_sub_qftGateCircuitPerturbed_norm_le`, and their `Θ(n²)`/`Θ(n²/p(n))`
asymptotics are in `AxQM/Concrete/QftGateCount.lean`, `AxQM/Concrete/QftGateCircuitAllOnes.lean`
and `AxQM/Concrete/QftApproxErrorBound.lean`.
-/

open scoped InnerProductSpace

namespace AxQM

open Concrete

/-- **Nielsen & Chuang, Exercise 5.6 — the QFT approximation error accumulates linearly in the gate
count.** For any gate-circuit factorisation `l` of the quantum Fourier transform on `n` qubits
(`(l.map Prod.fst).prod = qftEvolution (2^n)`, the ideal Figure 5.1 circuit) in which every gate is
implemented to precision `Δ` (`p.1.gateError p.2 ≤ Δ`), the transform `V = ∏ⱼ Vⱼ` produced by the
imperfect gates approximates the ideal QFT with error

`E(qftEvolution (2^n), V) ≤ (length l)·Δ`.

This is Box 4.1's chaining bound (`Evolution.gateError_prod_le_uniform`) transported through the
factorisation `hfact`: the whole-circuit error is at most the number of gates times the per-gate
precision. -/
theorem qftEvolution_gateError_le_length_mul (n : ℕ) (Δ : ℝ)
    (l : List (Evolution (qudit (2 ^ n)) × Evolution (qudit (2 ^ n))))
    (hfact : (l.map Prod.fst).prod = qftEvolution (2 ^ n))
    (hΔ : ∀ p ∈ l, p.1.gateError p.2 ≤ Δ) :
    (qftEvolution (2 ^ n)).gateError (l.map Prod.snd).prod ≤ (l.length : ℝ) * Δ := by
  rw [← hfact]
  exact Evolution.gateError_prod_le_uniform l Δ hΔ

/-- **Nielsen & Chuang, Exercise 5.6 — the QFT error bound at the Figure 5.1 gate count.**
Specialising `qftEvolution_gateError_le_length_mul` to the actual QFT circuit — whose imprecise
(controlled-`Rₖ`) gates number `qftControlledRkCount n = n(n-1)/2` (`Concrete.qftControlledRkCount`)
— gives, for each gate implemented to precision `Δ`,

`E(qftEvolution (2^n), V) ≤ qftControlledRkCount n · Δ`.

With `qftControlledRkCount_isTheta_sq` (`qftControlledRkCount n = Θ(n²)`) this is the `Θ(n²)·Δ`
error budget of Exercise 5.6. -/
theorem qftApprox_gateError_le (n : ℕ) (Δ : ℝ)
    (l : List (Evolution (qudit (2 ^ n)) × Evolution (qudit (2 ^ n))))
    (hfact : (l.map Prod.fst).prod = qftEvolution (2 ^ n))
    (hlen : l.length = qftControlledRkCount n)
    (hΔ : ∀ p ∈ l, p.1.gateError p.2 ≤ Δ) :
    (qftEvolution (2 ^ n)).gateError (l.map Prod.snd).prod ≤ (qftControlledRkCount n : ℝ) * Δ := by
  have h := qftEvolution_gateError_le_length_mul n Δ l hfact hΔ
  rwa [hlen] at h

/-- **Nielsen & Chuang, Exercise 5.6 — polynomial precision gives polynomial accuracy.** With each
controlled-`Rₖ` gate of the QFT circuit implemented to precision `Δ = 1/p(n)` for a precision
denominator `p`, the ideal QFT `U = qftEvolution (2^n)` and the realised transform `V = ∏ⱼ Vⱼ`
satisfy

`E(U, V) ≤ qftControlledRkCount n / p(n) = n(n-1)/(2·p(n))`.

Since `qftControlledRkCount n = Θ(n²)` (`Concrete.qftControlledRkCount_isTheta_sq`), this bound is
`O(n²/p(n))` (its exact `Θ(n²/p(n))` scaling is `Concrete.qftApproxErrorBound_isTheta`): polynomial
precision `1/p(n)` in each gate guarantees polynomial accuracy `O(n²/p(n))` in the output state —
the exercise's conclusion. -/
theorem qftApprox_gateError_le_div (n : ℕ) (p : ℕ → ℝ)
    (l : List (Evolution (qudit (2 ^ n)) × Evolution (qudit (2 ^ n))))
    (hfact : (l.map Prod.fst).prod = qftEvolution (2 ^ n))
    (hlen : l.length = qftControlledRkCount n)
    (hΔ : ∀ q ∈ l, q.1.gateError q.2 ≤ 1 / p n) :
    (qftEvolution (2 ^ n)).gateError (l.map Prod.snd).prod
      ≤ (qftControlledRkCount n : ℝ) / p n := by
  have h := qftApprox_gateError_le n (1 / p n) l hfact hlen hΔ
  rwa [mul_one_div] at h

/-- **Nielsen & Chuang, Exercise 5.6 — the faithful `Ω(n²·Δ)` lower bound (order-tightness).** The
imperfect transform `V = qftApproxEvolution n Δ` — the ideal QFT circuit with every controlled-`Rₖ`
performed to precision `Δ` — differs from the ideal QFT `U = qftEvolution (2ⁿ)` by at least

`E(U, V) ≥ qftControlledRkCount n · Δ / π = n(n-1)Δ/(2π)`,

in the small-error regime `0 ≤ qftControlledRkCount n · Δ ≤ π` (`0 ≤ Δ`, `hreg`). On the worst-case
all-ones input `|1…1⟩` every controlled-`Rₖ` is active and the `Θ(n²)` phase errors `εₛ = (n-1-s)Δ`
add *coherently* to `∑ₛ εₛ = qftControlledRkCount n · Δ`; the operator-level distance bound
`qftApproxEvolution_op_allOnes_dist_ge` bounds `‖U.op |1…1⟩ − V.op |1…1⟩‖` below by
`n(n-1)Δ/(2π)`, and `Evolution.gateError_apply_le` at the unit input `|1…1⟩` lifts this to the gate
error `E(U,V)`. Together with the universal `O(n²·Δ)` upper bound (`qftApprox_gateError_le`) this
makes the QFT-approximation error order-tight — the `Ω` half of Exercise 5.6's `Θ`. -/
theorem qftApprox_gateError_ge (n : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hreg : (qftControlledRkCount n : ℝ) * Δ ≤ Real.pi) :
    (qftControlledRkCount n : ℝ) * Δ / Real.pi
      ≤ (qftEvolution (2 ^ n)).gateError (qftApproxEvolution n Δ) := by
  have hle := (qftEvolution (2 ^ n)).gateError_apply_le (qftApproxEvolution n Δ)
    (quditBasis (finFunctionFinEquiv (qftAllOnes n))).vec
  rw [(quditBasis (finFunctionFinEquiv (qftAllOnes n))).normalized, mul_one] at hle
  exact (qftApproxEvolution_op_allOnes_dist_ge n Δ hΔ hreg).trans hle

/-- **Nielsen & Chuang, Exercise 5.6 — the matching `Ω(n²/p(n))` lower bound.** With each
controlled-`Rₖ` gate implemented to precision `Δ = 1/p(n)` for a precision denominator `p` (with
`0 ≤ p(n)`), the ideal QFT `U = qftEvolution (2ⁿ)` and the coherent imperfect realisation
`V = qftApproxEvolution n (1/p(n))` satisfy

`E(U, V) ≥ qftControlledRkCount n / p(n) / π = n(n-1)/(2·p(n)·π)`,

in the regime `qftControlledRkCount n / p(n) ≤ π`. Since `qftControlledRkCount n = Θ(n²)`, this is
`Ω(n²/p(n))` (its exact `Θ(n²/p(n))` scaling is `Concrete.qftApproxErrorBound_isTheta`). Paired
with the `O(n²/p(n))` accuracy guarantee `qftApprox_gateError_le_div`, this is the two-sided
`Θ(n²/p(n))` scaling of the worst-case approximate-QFT error — the conclusion of Exercise 5.6.
Obtained from `qftApprox_gateError_ge` at `Δ = 1/p(n)`. -/
theorem qftApprox_gateError_ge_div (n : ℕ) (p : ℕ → ℝ) (hp : 0 ≤ p n)
    (hreg : (qftControlledRkCount n : ℝ) / p n ≤ Real.pi) :
    (qftControlledRkCount n : ℝ) / p n / Real.pi
      ≤ (qftEvolution (2 ^ n)).gateError (qftApproxEvolution n (1 / p n)) := by
  have h := qftApprox_gateError_ge n (1 / p n) (one_div_nonneg.mpr hp) (by rwa [mul_one_div])
  rwa [mul_one_div] at h

/-- **Nielsen & Chuang, Exercise 5.6 — the specific-`V` upper bound `O(n²·Δ)` (order-tightness, the
`O` half on the coherent realisation).** The very transform `V = qftApproxEvolution n Δ` that the
faithful `Ω` lower-bounds — the ideal QFT circuit with every controlled-`Rₖ` performed to precision
`Δ` — differs from the ideal QFT `U = qftEvolution (2ⁿ)` by at most

`E(U, V) ≤ qftControlledRkCount n · Δ = n(n-1)Δ/2`   (`0 ≤ Δ`),

the imprecise-gate count times the per-gate precision. This is Box 4.1's chaining bound (N&C eq.
4.63) applied to the Figure 5.1 gate factorisation of `V`: the Hadamards and swap are exact (they
carry no continuous parameter), so only the `qftControlledRkCount n = n(n-1)/2` controlled-`Rₖ`
gates contribute, each within `Δ` of its ideal — the boundary lemma
`qftApproxEvolution_gateError_le` (`Postulates/API/QftApproxEvolution.lean`), whose content is the
concrete matrix chaining bound `Concrete.qftGateCircuit_sub_qftGateCircuitPerturbed_norm_le`.
Together with the coherent `Ω` bound `qftApprox_gateError_ge` this two-sidedly pins the error of the
*specific* realisation `V` to `Θ(n²·Δ)` (`qftApprox_gateError_mem_Icc`). -/
theorem qftApprox_gateError_le_specific (n : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    (qftEvolution (2 ^ n)).gateError (qftApproxEvolution n Δ)
      ≤ (qftControlledRkCount n : ℝ) * Δ := by
  have h := qftApproxEvolution_gateError_le n Δ
  rwa [abs_of_nonneg hΔ] at h

/-- **Nielsen & Chuang, Exercise 5.6 — the specific-`V` upper bound with `Δ = 1/p(n)`.** With each
controlled-`Rₖ` gate implemented to precision `Δ = 1/p(n)` (precision denominator `p`, `0 ≤ p(n)`),
the coherent realisation `V = qftApproxEvolution n (1/p(n))` satisfies

`E(U, V) ≤ qftControlledRkCount n / p(n) = n(n-1)/(2·p(n)) = O(n²/p(n))`

(its exact `Θ(n²/p(n))` scaling is `Concrete.qftApproxErrorBound_isTheta`). Obtained from
`qftApprox_gateError_le_specific` at `Δ = 1/p(n)`; the specific-`V` counterpart of the universal
accuracy guarantee `qftApprox_gateError_le_div`, and the upper half matching the lower bound
`qftApprox_gateError_ge_div`. -/
theorem qftApprox_gateError_le_specific_div (n : ℕ) (p : ℕ → ℝ) (hp : 0 ≤ p n) :
    (qftEvolution (2 ^ n)).gateError (qftApproxEvolution n (1 / p n))
      ≤ (qftControlledRkCount n : ℝ) / p n := by
  have h := qftApprox_gateError_le_specific n (1 / p n) (one_div_nonneg.mpr hp)
  rwa [mul_one_div] at h

/-- **Nielsen & Chuang, Exercise 5.6 — the two-sided `Θ(n²·Δ)` sandwich on the coherent
realisation.** The error of the *specific* imperfect transform `V = qftApproxEvolution n Δ` — the
ideal QFT with every controlled-`Rₖ` performed to precision `Δ` — is pinned on **both** sides by the
imprecise-gate count times the per-gate precision:

`qftControlledRkCount n · Δ / π ≤ E(U, V) ≤ qftControlledRkCount n · Δ`,

in the small-error regime `0 ≤ qftControlledRkCount n · Δ ≤ π` (`0 ≤ Δ`, `hreg`). The lower bound is
the coherent-accumulation `Ω` (`qftApprox_gateError_ge`: the `Θ(n²)` per-wire phase errors on the
worst-case input `|1…1⟩` add in phase); the upper bound is Box 4.1's chaining `O`
(`qftApprox_gateError_le_specific`: the errors of the `Θ(n²)` controlled-`Rₖ` gates add at most
linearly). The two bounds differ only by the constant factor `π`, so `E(U, V) = Θ(n²·Δ)` on this one
realisation — a single two-sided statement of Exercise 5.6's `Θ`. With `Δ = 1/p(n)` (via
`qftApprox_gateError_ge_div` / `qftApprox_gateError_le_specific_div`) and
`Concrete.qftApproxErrorBound_isTheta` (`qftControlledRkCount n / p(n) = Θ(n²/p(n))`) this is the
`Θ(n²/p(n))` scaling of the approximate-QFT error, the conclusion of Exercise 5.6. -/
theorem qftApprox_gateError_mem_Icc (n : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hreg : (qftControlledRkCount n : ℝ) * Δ ≤ Real.pi) :
    (qftEvolution (2 ^ n)).gateError (qftApproxEvolution n Δ) ∈
      Set.Icc ((qftControlledRkCount n : ℝ) * Δ / Real.pi) ((qftControlledRkCount n : ℝ) * Δ) :=
  ⟨qftApprox_gateError_ge n Δ hΔ hreg, qftApprox_gateError_le_specific n Δ hΔ⟩

/-- **Nielsen & Chuang, Exercise 5.6 — the `Θ(n²/p(n))` scaling of the approximate-QFT error (the
exercise's conclusion).** With each controlled-`Rₖ` gate implemented to precision `Δ = 1/p(n)`
(precision denominator `p`, `0 ≤ p(n)`), the error of the imperfect transform
`V = qftApproxEvolution n (1/p(n))` — the QFT N&C describes — is pinned on both sides:

`qftControlledRkCount n / p(n) / π ≤ E(U, V) ≤ qftControlledRkCount n / p(n)`,

in the small-error regime `qftControlledRkCount n / p(n) ≤ π`. The two bounds are
`qftControlledRkCount n / p(n) = n(n-1)/(2·p(n))` up to the constant factor `π`, and
`qftControlledRkCount n / p(n) = Θ(n²/p(n))` (`Concrete.qftApproxErrorBound_isTheta`), so
`E(U, V) = Θ(n²/p(n))` — polynomial precision `1/p(n)` in each gate yields error scaling as
`Θ(n²/p(n))`. The `Δ = 1/p(n)` specialisation of `qftApprox_gateError_mem_Icc`. -/
theorem qftApprox_gateError_div_mem_Icc (n : ℕ) (p : ℕ → ℝ) (hp : 0 ≤ p n)
    (hreg : (qftControlledRkCount n : ℝ) / p n ≤ Real.pi) :
    (qftEvolution (2 ^ n)).gateError (qftApproxEvolution n (1 / p n)) ∈
      Set.Icc ((qftControlledRkCount n : ℝ) / p n / Real.pi) ((qftControlledRkCount n : ℝ) / p n) :=
  ⟨qftApprox_gateError_ge_div n p hp hreg, qftApprox_gateError_le_specific_div n p hp⟩

end AxQM
