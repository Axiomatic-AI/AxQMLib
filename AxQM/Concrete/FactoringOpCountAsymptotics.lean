/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic

/-!
# Concrete: the improved `O(L² log L log log L)` factoring cost (N&C Problem 5.4)

Nielsen & Chuang, Problem 5.4 (p. 244): the runtime bound `O(L³)` given for the factoring algorithm
is not tight; a better upper bound of `O(L² log L log log L)` operations can be achieved.

## The mathematical kernel

The factoring algorithm reduces to order-finding, whose dominant cost is *modular exponentiation*.
Box 5.2 (p. 228) gives its structure explicitly on a `t`-qubit exponent register: **stage 1** builds
the chain `x, x², x⁴, …, x^{2^{t-1}}` mod N by repeated squaring — `t − 1` modular multiplications
(one squaring per new element); **stage 2** forms the product `x^z = ∏_j x^{z_j 2^j}` mod N — a
further `t − 1` modular multiplications.  So the circuit performs `modExpMulCount t = (t-1) + (t-1)`
modular multiplications, and order-finding on an `L`-bit modulus uses `t = 2L + 1 + c` qubits
(`orderFindingRegisterSize`, N&C p. 227, `c = ⌈log(2 + 1/(2ε))⌉` a fixed accuracy constant).  Hence
the multiplication count `factoringModExpMulCount c L = 4L + 2c` is `O(L)` — a purely combinatorial
fact **proved** here (`factoringModExpMulCount_isBigO`), needing no operational cost model.

The *only* thing that changes between the textbook `O(L³)` and the improved bound is the
**per-multiplication cost**: naive multiplication is `O(L²)`, whereas fast (Schönhage–Strassen)
multiplication is `O(L log L log log L)`.  This cost is a legitimately-cited external input (N&C
cites Schönhage–Strassen rather than re-deriving it), so it enters as the single explicit `IsBigO`
hypothesis `hMul`.  What is *proved* — the genuine content of the problem — is:

* **the improved bound is achievable** (`factoringOpCount_isBigO_of_fastMul`): the total cost
  `factoringModExpMulCount c L · mulCost L` is `O(L² log L log log L)` when each multiplication is
  `O(L log L log log L)` — the `O(L)·O(L log L log log L)` composition, with the `O(L)` count
  proved;
  the same composition with the naive `O(L²)` per multiplication reproduces the textbook `O(L³)`
  (`factoringOpCount_isBigO_cubic_of_naiveMul`), so the improvement is localised entirely in the
  multiplication subroutine;
* **the improved bound is genuinely better** (`factoringFastOpBound_isLittleO_cubic`):
  `L² log L log log L = o(L³)`, i.e. it is asymptotically *strictly* smaller than the `O(L³)` bound
  N&C says is "not tight" — the crux is that `log L · log log L = o(L)` (powers of `log` are beaten
  by the identity, `Real.isLittleO_pow_log_id_atTop`);
* **the bound holds for the whole factoring algorithm, not just the bottleneck.**  N&C's resource
  summary (p. 232) splits the `O(L³)` count into co-equal parts: the *quantum circuit proper*
  (modular exponentiation + Hadamard/inverse-Fourier, `factoringQftGateBound c L = (2L+1+c)²`,
  `Θ(L²)`) is `O(L² log L log log L)` with fast multiplication
  (`factoringCircuitOpCount_isBigO_of_fastMul`); adding the *continued-fractions* recovery of the
  order (`O(L)` split-and-invert steps, Box 5.3 — a *further* `O(L³)`) and the `O(L²)` classical
  *order→factor reduction* (§5.3.2, Exercise 5.15), the whole algorithm is still
  `O(L² log L log log L)` (`factoringTotalOpCount_isBigO_of_fastMul`), and `O(L³)` with naive
  multiplication (`…_cubic_of_naiveMul`).  So Problem 5.4's claim is discharged for the factoring
  algorithm as a whole, matching N&C's own accounting.

Everything here is `ℕ`/`ℝ` asymptotics (no quantum object at all — only real-valued cost
functions), mirroring `AxQM/Concrete/MultiControlledNotAsymptotics.lean` (the `O(n²)` gate count of
`Cⁿ(X)`).
-/

namespace AxQM.Concrete

open Filter Asymptotics

/-- The Schönhage–Strassen fast-multiplication operation count `O(L log L log log L)` for
multiplying two `L`-bit integers — the per-multiplication cost that replaces the naive `O(L²)` in
the factoring algorithm (N&C Problem 5.4). -/
noncomputable def fastMulOpBound (L : ℕ) : ℝ :=
  (L : ℝ) * Real.log L * Real.log (Real.log L)

/-- The improved total operation-count bound `O(L² log L log log L)` for factoring an `L`-bit
integer, achieved by using fast (Schönhage–Strassen) multiplication in the modular exponentiation
step (N&C Problem 5.4): `L` modular multiplications, each of cost `fastMulOpBound L`. -/
noncomputable def factoringFastOpBound (L : ℕ) : ℝ :=
  (L : ℝ) ^ 2 * Real.log L * Real.log (Real.log L)

/-- The number of modular multiplications performed by the Box 5.2 modular-exponentiation circuit on
a `t`-qubit exponent register (N&C p. 228): `t − 1` squarings to build `x, x², x⁴, …, x^{2^{t-1}}`
mod N by repeated squaring (stage 1), plus `t − 1` modular multiplications to form the product
`x^z = ∏_j x^{z_j 2^j}` mod N (stage 2). -/
def modExpMulCount (t : ℕ) : ℕ := (t - 1) + (t - 1)

/-- The exponent-register size `t = 2L + 1 + c` used by order-finding on an `L`-bit modulus (N&C
p. 227); `c = ⌈log(2 + 1/(2ε))⌉` is a fixed accuracy-dependent constant (independent of `L`). -/
def orderFindingRegisterSize (c L : ℕ) : ℕ := 2 * L + 1 + c

/-- The number of modular multiplications the order-finding modular-exponentiation circuit performs
when factoring an `L`-bit modulus, at accuracy constant `c`: `modExpMulCount` on the register size
`orderFindingRegisterSize c L` (N&C Box 5.2).  It equals `4L + 2c`. -/
def factoringModExpMulCount (c L : ℕ) : ℕ := modExpMulCount (orderFindingRegisterSize c L)

/-- The factoring modular-exponentiation multiplication count is `O(L)`: the combinatorial Box 5.2
count `factoringModExpMulCount c L = 4L + 2c` grows linearly in the bit-length `L` (for any fixed
accuracy constant `c`).  This is the multiplication-count analysis discharged here — no operational
cost model is needed — leaving only the per-multiplication cost as an external input. -/
theorem factoringModExpMulCount_isBigO (c : ℕ) :
    (fun L : ℕ => (factoringModExpMulCount c L : ℝ)) =O[atTop] fun L : ℕ => (L : ℝ) := by
  refine IsBigO.of_bound (4 + 2 * (c : ℝ)) ?_
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hL' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hcount : factoringModExpMulCount c L = 4 * L + 2 * c := by
    unfold factoringModExpMulCount orderFindingRegisterSize modExpMulCount
    omega
  rw [hcount, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  push_cast
  nlinarith [hL', Nat.cast_nonneg (α := ℝ) c]

/-- `log (log x)` is `O(log x)` at infinity: for `x ≥ e` one has `0 ≤ log (log x) ≤ log x − 1`.
This is the bound that lets `log L · log log L` be absorbed into `(log L)²` in
`factoringFastOpBound_isLittleO_cubic`. -/
theorem isBigO_log_log_atTop :
    (fun x : ℝ => Real.log (Real.log x)) =O[atTop] Real.log := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have h1 : (1 : ℝ) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hpos : (0 : ℝ) < Real.log x := lt_of_lt_of_le one_pos h1
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg hpos.le]
  linarith [Real.log_le_sub_one_of_pos hpos]

/-- **N&C Problem 5.4 — the improved bound is genuinely better than `O(L³)`.**
`L² log L log log L = o(L³)`: the improved factoring bound is asymptotically *strictly* smaller than
the cubic bound N&C says is "not tight".  Equivalently `log L · log log L = o(L)`, which reduces to
`(log L)² = o(L)` (`Real.isLittleO_pow_log_id_atTop`) after absorbing `log log L` into `log L`
(`isBigO_log_log_atTop`). -/
theorem factoringFastOpBound_isLittleO_cubic :
    factoringFastOpBound =o[atTop] fun L : ℕ => (L : ℝ) ^ 3 := by
  have hsq : (fun x : ℝ => Real.log x * Real.log x) =o[atTop] (id : ℝ → ℝ) := by
    have h := Real.isLittleO_pow_log_id_atTop (n := 2)
    simp only [pow_two] at h
    exact h
  have hbaseR : (fun x : ℝ => Real.log x * Real.log (Real.log x)) =o[atTop] (id : ℝ → ℝ) :=
    ((isBigO_refl Real.log atTop).mul isBigO_log_log_atTop).trans_isLittleO hsq
  have hbaseN : (fun L : ℕ => Real.log (L : ℝ) * Real.log (Real.log (L : ℝ))) =o[atTop]
      fun L : ℕ => (L : ℝ) := by
    have h := hbaseR.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def] using h
  refine ((isBigO_refl (fun L : ℕ => (L : ℝ) ^ 2) atTop).mul_isLittleO hbaseN).congr
    (fun L => ?_) (fun L => ?_)
  · unfold factoringFastOpBound; ring
  · ring

/-- **N&C Problem 5.4 — the improved bound is achievable.**  With fast (Schönhage–Strassen)
multiplication, each modular multiplication costs `O(L log L log log L)` (`hMul`); the order-finding
modular exponentiation performs `factoringModExpMulCount c L = O(L)` of them (proved,
`factoringModExpMulCount_isBigO`), so the total operation count is `O(L² log L log log L)`.  This is
the `O(L)·O(L log L log log L) = O(L² log L log log L)` reduction, via `IsBigO.mul`. -/
theorem factoringOpCount_isBigO_of_fastMul (c : ℕ) {mulCost : ℕ → ℝ}
    (hMul : mulCost =O[atTop] fastMulOpBound) :
    (fun L : ℕ => (factoringModExpMulCount c L : ℝ) * mulCost L) =O[atTop]
      factoringFastOpBound := by
  refine ((factoringModExpMulCount_isBigO c).mul hMul).congr_right fun L => ?_
  unfold fastMulOpBound factoringFastOpBound
  ring

/-- **N&C Problem 5.4 — the naive multiplication reproduces the textbook `O(L³)`.**  With the same
`factoringModExpMulCount c L = O(L)` modular multiplications but the naive `O(L²)`
per-multiplication cost, the total is `O(L³)` — the runtime N&C starts from.  Together with
`factoringOpCount_isBigO_of_fastMul` this shows the improvement is localised entirely in the
multiplication subroutine. -/
theorem factoringOpCount_isBigO_cubic_of_naiveMul (c : ℕ) {mulCost : ℕ → ℝ}
    (hMul : mulCost =O[atTop] fun L : ℕ => (L : ℝ) ^ 2) :
    (fun L : ℕ => (factoringModExpMulCount c L : ℝ) * mulCost L) =O[atTop]
      fun L : ℕ => (L : ℝ) ^ 3 := by
  refine ((factoringModExpMulCount_isBigO c).mul hMul).congr_right fun L => ?_
  ring

/-! ### From the modular-exponentiation bottleneck to the whole factoring algorithm

The theorems above bound the *modular exponentiation* alone.  N&C's own resource summary (p. 232)
splits the factoring algorithm's `O(L³)` operation count into co-equal parts, and Problem 5.4 asks
to improve the **whole** count, so we assemble it in the same layers:

* the **quantum circuit proper** — modular exponentiation (`O(L³)` gates, the bottleneck) together
  with the Hadamard and inverse Fourier transforms (`O(L²)` gates), N&C p. 232;
* the **continued-fractions** post-processing that recovers the order `r` from the measured phase —
  `O(L)` "split and invert" steps, each one elementary `O(L)`-bit integer arithmetic operation
  (Box 5.3, p. 230), which N&C counts as a *further* `O(L³)`, co-equal with the circuit proper;
* the classical **order→factor reduction** — the `gcd`/`lcm` bookkeeping of §5.3.2 and
  Exercise 5.15, `O(L²)` operations.

The improvement lives entirely in the per-operation arithmetic cost `mulCost` (a single `O(L)`-bit
multiply/divide): naive `O(L²)` makes every arithmetic-bound part `O(L³)`, while fast
(Schönhage–Strassen) `O(L log L log log L)` makes them `O(L² log L log log L)`; the two `O(L²)`
parts (Fourier transform, reduction) are dominated either way.  The same `hMul` drives the modular
multiplications and the continued-fractions divisions, since division of `L`-bit integers has the
same asymptotic cost as multiplication (Newton iteration over fast multiplication). -/

/-- `L² = O(L³)`: the naive quadratic per-operation contribution is dominated by the cubic bound.
Used to fold the `Θ(L²)` Fourier transform and the `O(L²)` reduction into the textbook `O(L³)`
totals.  This is the canonical `Asymptotics.IsBigO.pow_of_le_right`
(`1 ≤ᶠ[l] f → n ≤ m → fⁿ =O[l] fᵐ`), applied to `f = fun L => (L : ℝ)` and `2 ≤ 3`. -/
theorem sq_isBigO_cube :
    (fun L : ℕ => (L : ℝ) ^ 2) =O[atTop] fun L : ℕ => (L : ℝ) ^ 3 := by
  have hf : (1 : ℕ → ℝ) ≤ᶠ[atTop] fun L => (L : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with L hL
    simp only [Pi.one_apply]; exact_mod_cast hL
  exact Asymptotics.IsBigO.pow_of_le_right hf (by norm_num : 2 ≤ 3)

/-- `L² = O(L² log L log log L)`: the `Θ(L²)` cost of the parts *other than* the arithmetic
(the Fourier transform and the order→factor reduction) is dominated by the improved
`factoringFastOpBound`.  The crux is that `log L · log log L → ∞`, so `1 ≤ log L · log log L`
eventually; hence `L² ≤ L² · log L · log log L`.  This is what lets the whole-algorithm total keep
the modular-exponentiation bound (`factoringTotalOpCount_isBigO_of_fastMul`). -/
theorem sq_isBigO_factoringFastOpBound :
    (fun L : ℕ => (L : ℝ) ^ 2) =O[atTop] factoringFastOpBound := by
  have hg1 : ∀ᶠ L : ℕ in atTop, (1 : ℝ) ≤ Real.log L := by
    have : Tendsto (fun L : ℕ => Real.log (L : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact this.eventually_ge_atTop 1
  have hg2 : ∀ᶠ L : ℕ in atTop, (1 : ℝ) ≤ Real.log (Real.log L) := by
    have : Tendsto (fun L : ℕ => Real.log (Real.log (L : ℝ))) atTop atTop :=
      Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact this.eventually_ge_atTop 1
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hg1, hg2] with L hL1 hL2
  have hprod : (1 : ℝ) ≤ Real.log L * Real.log (Real.log L) := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Real.log L * Real.log (Real.log L) :=
          mul_le_mul hL1 hL2 zero_le_one (le_trans zero_le_one hL1)
  have hL2pos : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hval_nonneg : (0 : ℝ) ≤ factoringFastOpBound L := by
    unfold factoringFastOpBound; rw [mul_assoc]
    exact mul_nonneg hL2pos (le_trans zero_le_one hprod)
  rw [Real.norm_of_nonneg hL2pos, one_mul, Real.norm_of_nonneg hval_nonneg]
  unfold factoringFastOpBound; rw [mul_assoc]
  exact le_mul_of_one_le_right hL2pos hprod

/-- An upper bound on the operations of the order-finding circuit *other than* the modular
exponentiation: the quantum Fourier transform on the `t = orderFindingRegisterSize c L` qubit
register uses `Θ(t²)` gates (N&C §5.1) — Hadamards and controlled phase rotations — which we bound
above by `t²`.  For an `L`-bit modulus this is `(2L + 1 + c)²`, i.e. `Θ(L²)`
(`factoringQftGateBound_isBigO`), so it is dominated by the improved modular-exponentiation
bound. -/
def factoringQftGateBound (c L : ℕ) : ℕ := orderFindingRegisterSize c L ^ 2

/-- The quantum Fourier transform gate bound is `O(L²)`: on the `t = 2L + 1 + c` qubit order-finding
register the count `(2L + 1 + c)²` grows quadratically in the bit-length `L` (for any fixed accuracy
constant `c`). -/
theorem factoringQftGateBound_isBigO (c : ℕ) :
    (fun L : ℕ => (factoringQftGateBound c L : ℝ)) =O[atTop] fun L : ℕ => (L : ℝ) ^ 2 := by
  refine IsBigO.of_bound ((3 + (c : ℝ)) ^ 2) ?_
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hcount : factoringQftGateBound c L = (2 * L + 1 + c) ^ 2 := rfl
  rw [hcount, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  push_cast
  have hcnn : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hb : (2 * (L : ℝ) + 1 + c) ≤ (3 + c) * L := by nlinarith [hL1, hcnn]
  have hb0 : (0 : ℝ) ≤ 2 * (L : ℝ) + 1 + c := by positivity
  nlinarith [hb, hb0, mul_le_mul hb hb hb0 (by positivity : (0 : ℝ) ≤ (3 + (c : ℝ)) * L)]

/-- **N&C Problem 5.4 — the quantum circuit proper achieves `O(L² log L log log L)`.**  N&C's
"quantum circuit proper" (p. 232) is the modular exponentiation (`factoringModExpMulCount c L`
modular multiplications, each of cost `mulCost L`) together with the Hadamard and inverse Fourier
transforms (`factoringQftGateBound c L` gates, `Θ(L²)`).  With fast (Schönhage–Strassen)
multiplication (`hMul`) the modular exponentiation is `O(L² log L log log L)`
(`factoringOpCount_isBigO_of_fastMul`) and the `Θ(L²)` Fourier transform is dominated by it
(`factoringQftGateBound_isBigO` with `sq_isBigO_factoringFastOpBound`), so the circuit proper is
`O(L² log L log log L)`.  The whole algorithm — adding the continued-fractions and reduction costs —
is `factoringTotalOpCount_isBigO_of_fastMul`. -/
theorem factoringCircuitOpCount_isBigO_of_fastMul (c : ℕ) {mulCost : ℕ → ℝ}
    (hMul : mulCost =O[atTop] fastMulOpBound) :
    (fun L : ℕ => (factoringModExpMulCount c L : ℝ) * mulCost L
        + (factoringQftGateBound c L : ℝ)) =O[atTop] factoringFastOpBound :=
  (factoringOpCount_isBigO_of_fastMul c hMul).add
    ((factoringQftGateBound_isBigO c).trans sq_isBigO_factoringFastOpBound)

/-- **N&C Problem 5.4 — with naive multiplication the quantum circuit proper is the textbook
`O(L³)`.**  The same circuit proper (modular exponentiation + Fourier transform) with the naive
`O(L²)` per-multiplication cost (`hMul`) is `O(L³)` — the bound N&C p. 232 gives for the circuit
proper — since the modular exponentiation is `O(L³)` (`factoringOpCount_isBigO_cubic_of_naiveMul`)
and the `Θ(L²)` Fourier transform is dominated by it (`factoringQftGateBound_isBigO` with
`sq_isBigO_cube`). -/
theorem factoringCircuitOpCount_isBigO_cubic_of_naiveMul (c : ℕ) {mulCost : ℕ → ℝ}
    (hMul : mulCost =O[atTop] fun L : ℕ => (L : ℝ) ^ 2) :
    (fun L : ℕ => (factoringModExpMulCount c L : ℝ) * mulCost L
        + (factoringQftGateBound c L : ℝ)) =O[atTop] fun L : ℕ => (L : ℝ) ^ 3 :=
  (factoringOpCount_isBigO_cubic_of_naiveMul c hMul).add
    ((factoringQftGateBound_isBigO c).trans sq_isBigO_cube)

/-- **N&C Problem 5.4 — the whole factoring algorithm achieves `O(L² log L log log L)`.**  On top of
the quantum circuit proper, N&C's resource summary (p. 232) counts a *further* `O(L³)` for the
continued-fractions recovery of the order and an `O(L²)` classical order→factor reduction; Problem
5.4 asks to improve this whole count.  The two arithmetic-bound parts share one per-operation cost
`mulCost` (one `O(L)`-bit multiply/divide): the modular exponentiation
(`factoringModExpMulCount c L` multiplications) and the continued-fractions post-processing
(`cfStepCount L` split-and-invert steps, `O(L)` by Box 5.3, `hCF`).  The other two parts — the
Fourier transform (`Θ(L²)`) and the reduction (`reductionCost L`, `O(L²)`, `hRed`; §5.3.2,
Exercise 5.15) — are dominated either way.
With fast (Schönhage–Strassen) multiplication (`hMul`) every arithmetic-bound part is
`O(L² log L log log L)`, so the whole algorithm is `O(L² log L log log L)` — Problem 5.4's bound for
the algorithm as a whole, not merely its dominant subroutine. -/
theorem factoringTotalOpCount_isBigO_of_fastMul (c : ℕ)
    {mulCost cfStepCount reductionCost : ℕ → ℝ}
    (hMul : mulCost =O[atTop] fastMulOpBound)
    (hCF : cfStepCount =O[atTop] fun L : ℕ => (L : ℝ))
    (hRed : reductionCost =O[atTop] fun L : ℕ => (L : ℝ) ^ 2) :
    (fun L : ℕ => (factoringModExpMulCount c L : ℝ) * mulCost L + (factoringQftGateBound c L : ℝ)
        + cfStepCount L * mulCost L + reductionCost L) =O[atTop] factoringFastOpBound := by
  have hCFcost : (fun L : ℕ => cfStepCount L * mulCost L) =O[atTop] factoringFastOpBound := by
    refine (hCF.mul hMul).congr_right fun L => ?_
    unfold fastMulOpBound factoringFastOpBound; ring
  exact ((factoringCircuitOpCount_isBigO_of_fastMul c hMul).add hCFcost).add
    (hRed.trans sq_isBigO_factoringFastOpBound)

/-- **N&C Problem 5.4 — with naive multiplication the whole algorithm is the textbook `O(L³)`.**
The same whole algorithm (circuit proper + continued fractions + reduction) with the naive `O(L²)`
per-operation cost (`hMul`) is `O(L³)`: the modular exponentiation and the continued fractions are
each `O(L³)`, and the Fourier transform and the reduction are `O(L²)`.  Contrasting with
`factoringTotalOpCount_isBigO_of_fastMul`, the entire improvement from `O(L³)` to
`O(L² log L log log L)` is localised in the per-operation arithmetic cost `mulCost`. -/
theorem factoringTotalOpCount_isBigO_cubic_of_naiveMul (c : ℕ)
    {mulCost cfStepCount reductionCost : ℕ → ℝ}
    (hMul : mulCost =O[atTop] fun L : ℕ => (L : ℝ) ^ 2)
    (hCF : cfStepCount =O[atTop] fun L : ℕ => (L : ℝ))
    (hRed : reductionCost =O[atTop] fun L : ℕ => (L : ℝ) ^ 2) :
    (fun L : ℕ => (factoringModExpMulCount c L : ℝ) * mulCost L + (factoringQftGateBound c L : ℝ)
        + cfStepCount L * mulCost L + reductionCost L) =O[atTop] fun L : ℕ => (L : ℝ) ^ 3 := by
  have hCFcost : (fun L : ℕ => cfStepCount L * mulCost L) =O[atTop] fun L : ℕ => (L : ℝ) ^ 3 := by
    refine (hCF.mul hMul).congr_right fun L => ?_
    ring
  exact ((factoringCircuitOpCount_isBigO_cubic_of_naiveMul c hMul).add hCFcost).add
    (hRed.trans sq_isBigO_cube)

end AxQM.Concrete
