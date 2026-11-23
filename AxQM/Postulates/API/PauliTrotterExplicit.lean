/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliTrotterStep
import AxQM.Postulates.API.PauliTrotter
import AxQM.Postulates.API.PauliCoefficientOpNorm
import AxQM.Postulates.API.ApproxError
import ToMathlib.Analysis.InnerProductSpace.Uhlmann

/-!
# The `k`-fold Trotter circuit approximates `U` with an explicit `O(4ⁿ)` constant (Problem 4.3(6))

Nielsen & Chuang, Problem 4.3(6) claims a **literal** `O(n·16ⁿ/ε)` gate count for approximating an
arbitrary `n`-qubit unitary `U` by the `k`-fold Trotter circuit `[∏_g exp(-i h_g g /k)]ᵏ`. The
part-(5) theorem `Evolution.exists_pauliString_trotter_approximation`
(`Postulates/API/PauliTrotter.lean`) already proves the accuracy bound
`‖[∏_g exp(-i h_g g /k)]ᵏ - U‖ ≤ C/k` — but with `C` the **general** Banach-algebra Lie–Trotter
constant of `NormedSpace.exists_norm_prod_exp_inv_smul_pow_sub_exp_sum_le`, which is existential
and, built from the non-unitary two-factor estimate, carries a crude `exp(∑|h_g|)` factor. That
is *not* pinned to `O(4ⁿ)`, so that theorem does **not** yet reach N&C's `16ⁿ`.

This file sharpens the constant. It uses two ingredients:

* **bound α** — the unitarity-aware `k`-fold Lie–Trotter bound with an **explicit** numerical
  constant and a clean `Λ²` dependence, `NormedSpace.norm_prod_exp_inv_smul_pow_sub_exp_sum_le_sq`
  (`ToMathlib/Analysis/Normed/Algebra/LieTrotter.lean`): for **contraction** generators
  (`‖exp(s•gᵢ)‖ ≤ 1`, `‖exp(s•∑g)‖ ≤ 1`), `‖(∏ᵢ exp(k⁻¹•gᵢ))ᵏ - exp(∑gᵢ)‖ ≤ (2e+e²·eᵉ)·Λ²·k⁻¹`
  with `Λ = ∑ᵢ‖gᵢ‖` — **no** exponential prefactor;
* **bound β** — the total Pauli weight is `O(2ⁿ)`,
  `Observable.sum_abs_pauliCoeff_le_of_spectrum_Icc` (`Postulates/API/PauliCoefficientOpNorm.lean`):
  `∑_g |h_g| ≤ 2ⁿ·c` for a Hamiltonian with `spectrum ⊆ [0, c]`, so with `c = 2π` (part (1b),
  the generator of a unitary) `Λ = ∑_g |h_g| ≤ 2ⁿ·2π`, whence `Λ² = O(4ⁿ)`.

The physics that makes α fire is that the generators `gᵢ = -i • Hᵢ.op` are **skew-adjoint**, so
`exp(s • gᵢ) = (Hᵢ.propagator 1 0 s).op` is *unitary* — a genuine `Evolution` — and every unitary is
a contraction (`Evolution.norm_op_le_one`). The contraction hypotheses of α are therefore automatic
for propagators; no case split on skew-adjointness is needed.

## What this file provides

The explicit numerical constant of the bounds is `NormedSpace.trotterProductConst` (`= 2e + e²·eᵉ`),
defined beside the α bounds in `ToMathlib/Analysis/Normed/Algebra/LieTrotter.lean`.

* `Observable.norm_exp_smul_neg_I_op_le_one` — the **contraction lemma**: for any Hamiltonian `H`,
  `‖exp(s • (-i • H.op))‖ ≤ 1` for **every** real `s`, because that exponential is the unitary
  propagator `(H.propagator 1 0 s).op`. This discharges α's contraction hypotheses.
* `norm_pauliStringHamiltonian_op_le` — `‖(pauliStringHamiltonian g c).op‖ ≤ |c|`: a Pauli string is
  a self-adjoint involution, hence unitary, hence `‖·‖ ≤ 1`, so scaling by `c` gives `≤ |c|`. This
  turns `Λ = ∑‖Hᵢ.op‖` into `∑|h_g|`, the quantity bound β bounds. (Part (2)'s explicit-`h`
  operator decomposition, `Observable.op_eq_sum_pauliStringHamiltonian_of_expansion`, so
  that bound β consumes the *same* `h`, is in `AxQM/Postulates/API/PauliTrotter.lean`.)
* `Observable.norm_prod_propagator_op_pow_sub_propagator_op_le_sq` — the **general explicit
  constant** Trotter bound: for a Hamiltonian sum `H = Σᵢ Hᵢ`,
  `‖(∏ᵢ (Hᵢ.propagator 1 0 (1/k)).op)ᵏ - (H.propagator 1 0 1).op‖ ≤
  trotterProductConst·(∑ᵢ‖Hᵢ.op‖)²·k⁻¹`. The sharpening of
  `Observable.exists_norm_prod_propagator_op_pow_sub_propagator_op_le`: same shape, but a
  *numerical* constant and an explicit `(∑‖Hᵢ.op‖)²` (Λ²) weight, using α + the automatic
  contraction of propagators.
* `Evolution.exists_pauliString_trotter_approximation_explicit` — the **main theorem**,
  explicit form: every `U : Evolution (qudit (2ⁿ))` satisfies
  `‖[∏_g exp(-i h_g g /k)]ᵏ - U‖ ≤ trotterProductConst·(2ⁿ·2π)²·k⁻¹` — an `O(4ⁿ)/k` bound with a
  fully explicit constant. Assembles part (1b) (generator with `spectrum ⊆ [0,2π]`), part (2) (Pauli
  expansion), the general α bound above, `norm_pauliStringHamiltonian_op_le`, and bound β.
* `Evolution.exists_pauliTrotterStep_pow_op_sub_le_explicit` — the same bound transferred onto the
  countable circuit `pauliTrotterStep n h (1/k)`, via `Evolution.op_pow` + `pauliTrotterStep_op`.
  This accuracy bound is combined with the `O(n·4ⁿ)`-per-step `CircuitBudget` to reach N&C's
  literal `O(n·16ⁿ/ε)` in Problem 4.3 (`AxQM/NC/Ch4/Problem4_3.lean`).

## Design notes

* **Why the constant is now explicit.** The general `exists_...` bounds return `∃ C, 0 ≤ C ∧ …` — an
  existential with no handle on `C`'s size. N&C's `16ⁿ` is a *quantitative* claim, so the constant
  must be exhibited. `trotterProductConst · (2ⁿ·2π)²` is that constant: `(2ⁿ·2π)² = 4ⁿ · (2π)²`, so
  it is manifestly `O(4ⁿ)`, and `trotterProductConst = 2e+e²·eᵉ` is a fixed number. Nothing here is
  existential except the coefficients `h` (which are determined by `H = i ln U`, not a free
  parameter of the bound).
* **Contraction comes for free.** Piece α needs `‖exp(s•gᵢ)‖ ≤ 1`. Rather than invoke
  skew-adjointness abstractly, this file observes `exp(s • (-i • Hᵢ.op)) = (Hᵢ.propagator 1 0 s).op`
  (`Observable.propagator_op_one_zero`) — a propagator, i.e. an `Evolution`, whose operator norm is
  `≤ 1` (`Evolution.norm_op_le_one`, valid in every system including the trivial one). So the
  contraction hypotheses are discharged by the propagators themselves.
* **`Λ = ∑‖Hᵢ.op‖` vs. `∑|h_g|`.** α's weight is `∑‖gᵢ‖ = ∑‖Hᵢ.op‖`; β bounds `∑|h_g|`. The
  bridge is `norm_pauliStringHamiltonian_op_le`: `‖(pauliStringHamiltonian g c).op‖ ≤ |c|`, as the
  unit
  Pauli string `(pauliStringHamiltonian g 1).op` is a self-adjoint involution
  (`pauliStringHamiltonian_op_mul_self`), hence a unitary of the C⋆-algebra
  `S.space →L[ℂ] S.space`, hence a contraction (`ContinuousLinearMap.opNorm_le_one_of_mem_unitary`).
  So `Λ ≤ ∑|h_g|`, and the bound is monotone in `Λ` (it is `C·Λ²·k⁻¹`), so `Λ ≤ 2ⁿ·2π` suffices.
-/

open scoped InnerProductSpace

open Matrix

noncomputable section

namespace AxQM

variable {n : ℕ}

-- `NormedSpace.trotterProductConst` (`= 2e + e²·eᵉ`) is the numerical constant of the
-- unitarity-aware Trotter bounds `NormedSpace.norm_prod_exp_inv_smul_pow_sub_exp_sum_le_sq` etc.;
-- open it (and its nonnegativity) so the statements below refer to it by name.
open NormedSpace (trotterProductConst trotterProductConst_nonneg)

/-- **The Lie–Trotter generators of a Hamiltonian generate contractions.** For any Hamiltonian
`H : Observable S` and any real `s`, `‖exp(s • (-i • H.op))‖ ≤ 1`: that exponential is exactly the
propagator operator `(H.propagator 1 0 s).op` (`Observable.propagator_op_one_zero`), a *unitary*
`Evolution` whose operator norm is `≤ 1` (`Evolution.norm_op_le_one`). This discharges — for every
`s`, in particular `s ≥ 0` — the contraction hypotheses of the unitarity-aware Trotter bound
`NormedSpace.norm_prod_exp_inv_smul_pow_sub_exp_sum_le_sq`, so no explicit appeal to
skew-adjointness is needed: propagators are unitary because they are `Evolution`s. -/
theorem Observable.norm_exp_smul_neg_I_op_le_one {S : QSystem} (H : Observable S) (s : ℝ) :
    ‖NormedSpace.exp (s • (-Complex.I) • H.op)‖ ≤ 1 := by
  rw [← H.propagator_op_one_zero s]
  exact (H.propagator 1 0 s).norm_op_le_one

/-- **A scaled Pauli string has operator norm at most `|c|`.** `‖(pauliStringHamiltonian g c).op‖ ≤
|c|`: the unit Pauli string `(pauliStringHamiltonian g 1).op` is a self-adjoint involution
(`pauliStringHamiltonian_op_mul_self`, `Observable.selfAdjoint`), hence a unitary element of the
C⋆-algebra of operators, hence a contraction `‖·‖ ≤ 1`
(`ContinuousLinearMap.opNorm_le_one_of_mem_unitary`); scaling by the real `c` multiplies the norm by
`|c|`. This turns the Trotter weight `Λ = ∑_g ‖(pauliStringHamiltonian g (h g)).op‖` into
`∑_g |h_g|`, the quantity bounded by bound β. -/
theorem norm_pauliStringHamiltonian_op_le (g : Fin n → Fin 4) (c : ℝ) :
    ‖(pauliStringHamiltonian g c).op‖ ≤ |c| := by
  have : CompleteSpace (qudit (2 ^ n)).space := FiniteDimensional.completeSpace ℂ _
  set T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 ^ n)) (Concrete.pauliStringStd g) with hTdef
  -- `‖(pauliStringHamiltonian g d).op‖ = |d| · ‖T‖` for every real `d`: the operator is `d • T`,
  -- and `norm_smul` computes the norm of a scalar multiple (the `show` moves the scalar action to
  -- the `NormedSpace` instance `norm_smul` expects, matching the one carried by `.op`).
  have hnorm : ∀ d : ℝ, ‖(pauliStringHamiltonian g d).op‖ = |d| * ‖T‖ := by
    intro d
    rw [pauliStringHamiltonian_op]
    change ‖(d : ℂ) • T‖ = |d| * ‖T‖
    rw [show ‖(d : ℂ) • T‖ = ‖(d : ℂ)‖ * ‖T‖ from norm_smul _ _, Complex.norm_real,
      Real.norm_eq_abs]
  -- the unit Pauli string is a self-adjoint involution, hence unitary, hence a contraction
  have hunit : (pauliStringHamiltonian g 1).op ∈
      unitary ((qudit (2 ^ n)).space →L[ℂ] (qudit (2 ^ n)).space) := by
    have hsa : star (pauliStringHamiltonian g 1).op = (pauliStringHamiltonian g 1).op :=
      (pauliStringHamiltonian g 1).selfAdjoint
    rw [Unitary.mem_iff, hsa]
    exact ⟨pauliStringHamiltonian_op_mul_self g, pauliStringHamiltonian_op_mul_self g⟩
  -- `‖T‖ ≤ 1` is the `c = 1` case (`|1| · ‖T‖ = ‖T‖`) of the unitary contraction bound
  have hT : ‖T‖ ≤ 1 := by
    have h1 : ‖(pauliStringHamiltonian g 1).op‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_one_of_mem_unitary hunit
    rwa [hnorm 1, abs_one, one_mul] at h1
  rw [hnorm c]
  exact mul_le_of_le_one_right (abs_nonneg c) hT

/-- **Nielsen & Chuang, Problem 4.3(5) with an explicit `O(Λ²)` constant.** If a Hamiltonian `H` is
a sum `H = Σᵢ Hᵢ` of Hamiltonians (`H.op = (Hs.map Observable.op).sum`), then the `k`-fold Trotter
splitting error carries the **numerical** constant `trotterProductConst` and the explicit weight
`Λ² = (∑ᵢ ‖Hᵢ.op‖)²`: `‖(∏ᵢ (Hᵢ.propagator 1 0 (1/k)).op)ᵏ - (H.propagator 1 0 1).op‖ ≤
trotterProductConst·(∑ᵢ‖Hᵢ.op‖)²·k⁻¹` for every `k ≥ 1`.

This sharpens `Observable.exists_norm_prod_propagator_op_pow_sub_propagator_op_le` (whose constant
is existential and carries an `exp(Λ)` factor) by using the unitarity-aware bound
`NormedSpace.norm_prod_exp_inv_smul_pow_sub_exp_sum_le_sq`. Its contraction hypotheses hold because
each generator `gᵢ = -i • Hᵢ.op` exponentiates to the *unitary* propagator
`(Hᵢ.propagator 1 0 s).op` (and likewise for `∑ gᵢ = -i • H.op`), so `‖exp(s•gᵢ)‖ ≤ 1` and
`‖exp(s•∑g)‖ ≤ 1` are the norm-`≤ 1` of an `Evolution`
(`Observable.norm_exp_smul_neg_I_op_le_one`). The weight `Λ = ∑ᵢ‖-i•Hᵢ.op‖ = ∑ᵢ‖Hᵢ.op‖`. -/
theorem Observable.norm_prod_propagator_op_pow_sub_propagator_op_le_sq {S : QSystem}
    (H : Observable S) (Hs : List (Observable S)) (hH : H.op = (Hs.map Observable.op).sum)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖((Hs.map fun Hᵢ => (Hᵢ.propagator 1 0 (k : ℝ)⁻¹).op).prod) ^ k - (H.propagator 1 0 1).op‖
      ≤ trotterProductConst * ((Hs.map fun Hᵢ => ‖Hᵢ.op‖).sum) ^ 2 * (k : ℝ)⁻¹ := by
  by_cases hnt : Nontrivial S.space
  · have := hnt
    have : CompleteSpace S.space := FiniteDimensional.completeSpace ℂ S.space
    -- contraction hypotheses: each generator and their sum exponentiate to unitaries. They are
    -- stated by the lemma itself, so its instances on `S.space →L[ℂ] S.space` need no unification.
    have key := NormedSpace.norm_prod_exp_inv_smul_pow_sub_exp_sum_le_sq
      (𝔸 := S.space →L[ℂ] S.space) (Hs.map fun Hᵢ => (-Complex.I) • Hᵢ.op) ?_ ?_ hk
    rotate_left
    · intro x hx s _
      rw [List.mem_map] at hx
      obtain ⟨Hᵢ, _, rfl⟩ := hx
      exact Hᵢ.norm_exp_smul_neg_I_op_le_one s
    · intro s _
      rw [Observable.sum_map_neg_I_smul_op hH]
      exact H.norm_exp_smul_neg_I_op_le_one s
    -- the weight `Λ = ∑‖-i•Hᵢ.op‖` equals `∑‖Hᵢ.op‖`
    have hΛ : ((Hs.map fun Hᵢ => (-Complex.I) • Hᵢ.op).map fun x => ‖x‖).sum
        = (Hs.map fun Hᵢ => ‖Hᵢ.op‖).sum := by
      rw [List.map_map]
      refine congrArg List.sum (List.map_congr_left fun Hᵢ _ => ?_)
      simp [norm_smul, norm_neg, Complex.norm_I]
    rw [hΛ] at key
    rw [Observable.map_propagator_op_eq_map_exp_smul, Observable.propagator_op_one_zero, one_smul,
      ← Observable.sum_map_neg_I_smul_op hH]
    exact key
  · rw [not_nontrivial_iff_subsingleton] at hnt
    have := hnt
    rw [Subsingleton.elim (((Hs.map fun Hᵢ => (Hᵢ.propagator 1 0 (k : ℝ)⁻¹).op).prod) ^ k)
      (H.propagator 1 0 1).op, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg trotterProductConst_nonneg (sq_nonneg _)) (by positivity)

/-- **Nielsen & Chuang, Problem 4.3(6), operator form with an explicit `O(4ⁿ)` constant.** *Every*
unitary `U` on the `n`-qubit register `qudit (2ⁿ)` is approximated to `O(4ⁿ)/k` by the `k`-fold
Pauli–Trotter product, with a **fully explicit** constant: there are real coefficients `h_g` with
`‖(∏_g exp(-i h_g g /k))ᵏ - U‖ ≤ trotterProductConst · (2ⁿ · 2π)² · k⁻¹` for every `k ≥ 1`.

Since `(2ⁿ · 2π)² = 4ⁿ · (2π)²`, the constant `trotterProductConst · (2ⁿ · 2π)²` is manifestly
`O(4ⁿ)` — N&C's `k = O(4ⁿ/ε)` step count. This is the sharpening of the part-(5) theorem
`Evolution.exists_pauliString_trotter_approximation` (whose `C` is existential with a crude
`exp(∑|h_g|)` factor). It assembles part (1b) (the generator `H = i ln U` with `spectrum ⊆ [0, 2π]`,
`Evolution.exists_hamiltonian_generator_spectrum_Icc`), part (2)
(`Observable.op_eq_sum_pauliStringHamiltonian_of_expansion`), the explicit general bound
`Observable.norm_prod_propagator_op_pow_sub_propagator_op_le_sq`, the Pauli-string norm bound
`norm_pauliStringHamiltonian_op_le`, and bound β `Observable.sum_abs_pauliCoeff_le_of_spectrum_Icc`
(`Λ = ∑_g |h_g| ≤ 2ⁿ · 2π`). -/
theorem Evolution.exists_pauliString_trotter_approximation_explicit
    (U : Evolution (qudit (2 ^ n))) :
    ∃ h : (Fin n → Fin 4) → ℝ, ∀ k : ℕ, 1 ≤ k →
      ‖(Finset.univ.toList.map fun g =>
            ((pauliStringHamiltonian g (h g)).propagator 1 0 (k : ℝ)⁻¹).op).prod ^ k - U.op‖
        ≤ trotterProductConst * (2 ^ n * (2 * Real.pi)) ^ 2 * (k : ℝ)⁻¹ := by
  obtain ⟨H, hU, hspec⟩ := U.exists_hamiltonian_generator_spectrum_Icc
  obtain ⟨h, hexp⟩ := H.exists_real_pauliString_expansion
  refine ⟨h, fun k hk => ?_⟩
  have hH : H.op = ((Finset.univ.toList.map fun g => pauliStringHamiltonian g (h g)).map
      Observable.op).sum := H.op_eq_sum_pauliStringHamiltonian_of_expansion hexp
  have key := H.norm_prod_propagator_op_pow_sub_propagator_op_le_sq
    (Finset.univ.toList.map fun g => pauliStringHamiltonian g (h g)) hH k hk
  rw [← hU] at key
  -- the Trotter weight `Λ = ∑_g ‖(pauliStringHamiltonian g (h g)).op‖ ≤ ∑_g |h_g| ≤ 2ⁿ·2π`
  have hΛnonneg : 0 ≤ ((Finset.univ.toList.map fun g => pauliStringHamiltonian g (h g)).map
      fun Hᵢ => ‖Hᵢ.op‖).sum :=
    List.sum_nonneg fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨Hᵢ, _, rfl⟩ := hx; exact norm_nonneg _
  have hΛbound : ((Finset.univ.toList.map fun g => pauliStringHamiltonian g (h g)).map
      fun Hᵢ => ‖Hᵢ.op‖).sum ≤ 2 ^ n * (2 * Real.pi) := by
    rw [List.map_map, Finset.sum_map_toList]
    calc ∑ g, ‖(pauliStringHamiltonian g (h g)).op‖
        ≤ ∑ g, |h g| :=
          Finset.sum_le_sum fun g _ => norm_pauliStringHamiltonian_op_le g (h g)
      _ ≤ 2 ^ n * (2 * Real.pi) :=
          H.sum_abs_pauliCoeff_le_of_spectrum_Icc (by positivity) hspec hexp
  -- monotonicity in `Λ²`, then collapse the double `List.map` on the left to match the goal
  have hstep := le_trans key
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΛnonneg hΛbound 2) trotterProductConst_nonneg)
      (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹))
  rwa [List.map_map] at hstep

/-- **Nielsen & Chuang, Problem 4.3(6), circuit form with an explicit `O(4ⁿ)` constant.** For every
`U : Evolution (qudit (2ⁿ))` there are real coefficients `h_g` such that for every `k ≥ 1` the
circuit `(pauliTrotterStep n h (1/k))ᵏ` — the `k`-fold power of one Trotter step
`∏_g exp(-i h_g g /k)`, a single `Evolution` — approximates `U` with the fully explicit constant
`‖((pauliTrotterStep n h (k)⁻¹)ᵏ).op - U.op‖ ≤ trotterProductConst · (2ⁿ · 2π)² · k⁻¹`.

The sharpened circuit-level bound, obtained from the operator form
`Evolution.exists_pauliString_trotter_approximation_explicit` exactly as
`Evolution.exists_pauliTrotterStep_pow_op_sub_le` is obtained from the crude operator form:
`Evolution.op_pow` turns `((pauliTrotterStep …)ᵏ).op` into `(pauliTrotterStep …).op ^ k`, and the
faithfulness `pauliTrotterStep_op` rewrites the base into the ordered propagator product. This is
the accuracy bound that Problem 4.3 (`AxQM/NC/Ch4/Problem4_3.lean`) combines with the
`O(n·4ⁿ)`-per-step `CircuitBudget` to reach N&C's literal `O(n·16ⁿ/ε)`:
`k = O(4ⁿ/ε)` steps × `O(n·4ⁿ)` gates/step. -/
theorem Evolution.exists_pauliTrotterStep_pow_op_sub_le_explicit
    (U : Evolution (qudit (2 ^ n))) :
    ∃ h : (Fin n → Fin 4) → ℝ, ∀ k : ℕ, 1 ≤ k →
      ‖((pauliTrotterStep n h (k : ℝ)⁻¹) ^ k).op - U.op‖
        ≤ trotterProductConst * (2 ^ n * (2 * Real.pi)) ^ 2 * (k : ℝ)⁻¹ := by
  obtain ⟨h, hbd⟩ := U.exists_pauliString_trotter_approximation_explicit
  refine ⟨h, fun k hk => ?_⟩
  rw [Evolution.op_pow, pauliTrotterStep_op]
  exact hbd k hk

end AxQM
