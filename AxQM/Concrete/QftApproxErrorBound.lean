/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QftGateCircuitPerturbed
import AxQM.Concrete.QftGateCircuitCorrectness
import ToMathlib.Analysis.Normed.Ring.ProductTelescope

/-!
# Concrete: the operator-norm distance between the ideal and perturbed Figure 5.1 circuits

The **specific-`V` upper bound** of Nielsen & Chuang, Exercise 5.6, at the matrix level. The ideal
gate-level QFT circuit `Concrete.qftGateCircuit n` and its `Δ`-perturbed twin
`Concrete.qftGateCircuitPerturbed n Δ` (every controlled-`Rₖ` gate shifted by `+Δ`) differ, in the
`L²`-operator (`C⋆`) matrix norm, by at most the number of imprecise gates times the per-gate
precision:

`‖qftGateCircuit n − qftGateCircuitPerturbed n Δ‖ ≤ qftControlledRkCount n · |Δ| = n(n-1)|Δ|/2`.

This is **Box 4.1's chaining bound** (N&C eq. 4.63) `‖∏ⱼ Uⱼ − ∏ⱼ Vⱼ‖ ≤ ∑ⱼ ‖Uⱼ − Vⱼ‖` for
products of unitaries (`Mathlib`'s `norm_listProd_sub_listProd_le`), applied to the Figure 5.1 gate
factorisations of the two circuits. Both circuits are the reverse product of the *same* gate
sequence except that each controlled-`Rₖ` gate `qftControlledGate n t c` is replaced by its
perturbed counterpart `qftControlledGatePerturbed n Δ t c`; the Hadamards and the wire-reversal swap
are identical in both, so they contribute `0` to the chaining sum. The only nonzero terms are the
`qftControlledRkCount n = n(n-1)/2` controlled-`Rₖ` gates, and each contributes at most `|Δ|`
because the perturbation multiplies one diagonal phase by `e^{iΔ}` and
`‖diagonal d‖ = ‖d‖_∞ = 2|sin(Δ/2)| ≤ |Δ|` (`Matrix.l2_opNorm_diagonal`,
`Concrete.norm_qftRkPerturbed_sub_qftRk_le`).

## What is formalised

* `Concrete.qftGatePairs n Δ` — the Figure 5.1 gate factorisation as a list of `(ideal, perturbed)`
  matrix pairs: the swap gate paired with itself, then, per target `t`, the Hadamard paired with
  itself followed by each controlled-`Rₖ` paired with its perturbed counterpart.
* `Concrete.qftGatePairs_map_fst` / `_map_snd` — projecting the pairs recovers the ideal
  `qftGateSequence n` / perturbed `qftGateSequencePerturbed n Δ` gate lists.
* `Concrete.qftControlledGate_sub_perturbed_norm_le` — the per-gate precision: each perturbed
  controlled-`Rₖ` gate is within `|Δ|` of its ideal (via the diagonal operator norm).
* `Concrete.qftGateCircuit_sub_qftGateCircuitPerturbed_norm_le` — **the headline**: the
  whole-circuit operator-norm distance `≤ qftControlledRkCount n · |Δ|`.

This concrete distance is the matrix form of Exercise 5.6's specific-`V` upper bound; the boundary
wrapper `qftApproxEvolution_gateError_le` (`Postulates/API/QftApproxEvolution.lean`) transports it
to the gate error `E(U, V) = ‖U.op − V.op‖` via `Matrix.cstar_norm_def`.
-/

open scoped Matrix.Norms.L2Operator

namespace AxQM.Concrete

open Matrix

/-- **The Figure 5.1 gate factorisation as a list of `(ideal, perturbed)` matrix pairs.** In
circuit/time order: the wire-reversal swap paired with itself (it is exact), then for each target
`t = 0, …, n-1` the Hadamard on wire `t` paired with itself (also exact) followed by target `t`'s
controlled-`Rₖ` cascade, each ideal gate `qftControlledGate n t c` paired with its precision-`Δ`
counterpart `qftControlledGatePerturbed n Δ t c`. Projecting the first / second components recovers
`qftGateSequence n` / `qftGateSequencePerturbed n Δ` (`qftGatePairs_map_fst` / `_map_snd`), so this
is Box 4.1's `(target gate, approximating gate)` list for the two circuits. -/
noncomputable def qftGatePairs (n : ℕ) (Δ : ℝ) :
    List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ × Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  (permGate finFunctionFinEquiv (qftBitReversal n),
      permGate finFunctionFinEquiv (qftBitReversal n))
    :: (List.finRange n).flatMap (fun t =>
        (qftHadamardGate n t, qftHadamardGate n t)
          :: (qftTargetControls n t).map
              (fun c => (qftControlledGate n t c, qftControlledGatePerturbed n Δ t c)))

/-- The first components of `qftGatePairs n Δ` are the ideal Figure 5.1 gate sequence
`qftGateSequence n` (the swap, then each target's Hadamard and controlled-`Rₖ` cascade). -/
theorem qftGatePairs_map_fst (n : ℕ) (Δ : ℝ) :
    (qftGatePairs n Δ).map Prod.fst = qftGateSequence n := by
  rw [qftGatePairs, qftGateSequence, List.map_cons, List.map_flatMap]
  refine congrArg _ (List.flatMap_congr fun t _ => ?_)
  rw [qftBlock, qftBlockControlledGates, List.map_cons, List.map_map]; rfl

/-- The second components of `qftGatePairs n Δ` are the perturbed Figure 5.1 gate sequence
`qftGateSequencePerturbed n Δ` (the same swap and Hadamards, with each controlled-`Rₖ` shifted by
`+Δ`). -/
theorem qftGatePairs_map_snd (n : ℕ) (Δ : ℝ) :
    (qftGatePairs n Δ).map Prod.snd = qftGateSequencePerturbed n Δ := by
  rw [qftGatePairs, qftGateSequencePerturbed, List.map_cons, List.map_flatMap]
  refine congrArg _ (List.flatMap_congr fun t _ => ?_)
  rw [qftBlockPerturbed, qftBlockControlledGatesPerturbed, List.map_cons, List.map_map]; rfl

/-- **Per-gate precision (Nielsen & Chuang, Exercise 5.6).** For distinct wires `t ≠ c`, the
precision-`Δ` controlled-`Rₖ` gate is within `|Δ|` of the ideal one in operator norm:
`‖qftControlledGate n t c − qftControlledGatePerturbed n Δ t c‖ ≤ |Δ|`. Both gates are diagonal
(`qftControlledGate_eq_diagonal`, `qftControlledGatePerturbed_eq_diagonal`), so their operator norm
difference is the supremum of the entrywise differences (`Matrix.l2_opNorm_diagonal`); the only
nonzero entries are where both control and target wires are `1`, where the difference is
`e^{2πi/2^{c-t+1}} − e^{2πi/2^{c-t+1}+iΔ}`, of modulus `2|sin(Δ/2)| ≤ |Δ|`
(`norm_qftRkPerturbed_sub_qftRk_le`). -/
theorem qftControlledGate_sub_perturbed_norm_le (n : ℕ) (Δ : ℝ) (t c : Fin n) (htc : t ≠ c) :
    ‖qftControlledGate n t c - qftControlledGatePerturbed n Δ t c‖ ≤ |Δ| := by
  rw [qftControlledGate_eq_diagonal n t c htc, qftControlledGatePerturbed_eq_diagonal n Δ t c htc,
      Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (abs_nonneg _)]
  intro i
  by_cases h : finFunctionFinEquiv.symm i c = 1 ∧ finFunctionFinEquiv.symm i t = 1
  · simp only [ite_eq_left h]
    have hl := norm_qftRkPerturbed_sub_qftRk_le ((c : ℕ) - (t : ℕ) + 1) Δ
    simp only [qftRk, qftRkPerturbed, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hl ⊢
    rwa [norm_sub_rev] at hl
  · simp only [ite_eq_right h, sub_self, norm_zero]
    exact abs_nonneg _

/-- **Nielsen & Chuang, Exercise 5.6 — the specific-`V` upper bound (matrix form).** The ideal
gate-level QFT circuit and its precision-`Δ` perturbation differ, in `L²`-operator norm, by at most
the imprecise-gate count times the per-gate precision:

`‖qftGateCircuit n − qftGateCircuitPerturbed n Δ‖ ≤ qftControlledRkCount n · |Δ| = n(n-1)|Δ|/2`.

Both circuits are the reverse product of the paired gate list `qftGatePairs n Δ`
(`qftGatePairs_map_fst` / `_map_snd`), so Box 4.1's chaining bound (`norm_listProd_sub_listProd_le`,
each unitary factor of norm `1`) bounds the distance by the sum of the per-gate errors. The swap and
Hadamard pairs are equal, contributing `0`; the `qftControlledRkCount n` controlled-`Rₖ` pairs each
contribute at most `|Δ|` (`qftControlledGate_sub_perturbed_norm_le`), and target `t` contributes its
`n-1-t` controls, so the total is `∑_{t<n} (n-1-t)·|Δ| = qftControlledRkCount n · |Δ|` (the
reflected Gauss sum, `qftControlledRkCount_eq_sum`). -/
theorem qftGateCircuit_sub_qftGateCircuitPerturbed_norm_le (n : ℕ) (Δ : ℝ) :
    ‖qftGateCircuit n - qftGateCircuitPerturbed n Δ‖ ≤ (qftControlledRkCount n : ℝ) * |Δ| := by
  have hfst : ((qftGatePairs n Δ).reverse.map Prod.fst).prod = qftGateCircuit n := by
    rw [List.map_reverse, qftGatePairs_map_fst, qftGateCircuit]
  have hsnd : ((qftGatePairs n Δ).reverse.map Prod.snd).prod = qftGateCircuitPerturbed n Δ := by
    rw [List.map_reverse, qftGatePairs_map_snd, qftGateCircuitPerturbed]
  rw [← hfst, ← hsnd]
  refine (norm_listProd_sub_listProd_le _ ?_ ?_).trans ?_
  · intro p hp
    rw [List.mem_reverse] at hp
    refine le_of_eq (CStarRing.norm_of_mem_unitary
      (qftGateSequence_forall_mem_unitaryGroup n _ ?_))
    rw [← qftGatePairs_map_fst n Δ]
    exact List.mem_map_of_mem hp
  · intro p hp
    rw [List.mem_reverse] at hp
    refine le_of_eq (CStarRing.norm_of_mem_unitary
      (qftGateSequencePerturbed_forall_mem_unitaryGroup n Δ _ ?_))
    rw [← qftGatePairs_map_snd n Δ]
    exact List.mem_map_of_mem hp
  · rw [List.map_reverse, List.sum_reverse, qftGatePairs, List.map_cons, List.sum_cons, sub_self,
        norm_zero, zero_add, List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]
    refine (List.sum_le_sum (l := List.finRange n)
      (g := fun t => ((n - 1 - (t : ℕ) : ℕ) : ℝ) * |Δ|) ?_).trans (le_of_eq ?_)
    · intro t _
      rw [Function.comp_apply, List.map_cons, List.sum_cons, sub_self, norm_zero, zero_add,
          List.map_map]
      refine (List.sum_le_length_nsmul _ |Δ| ?_).trans ?_
      · intro x hx
        rw [List.mem_map] at hx
        obtain ⟨c, hc, rfl⟩ := hx
        exact qftControlledGate_sub_perturbed_norm_le n Δ t c
          (Fin.ne_of_val_ne (ne_of_lt (qftTargetControls_lt hc)))
      · rw [List.length_map, length_qftTargetControls, nsmul_eq_mul]
    · rw [List.sum_map_mul_right]
      congr 1
      rw [← List.ofFn_eq_map, List.sum_ofFn, ← Nat.cast_sum]
      congr 1
      rw [qftControlledRkCount_eq_sum, Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n,
          Finset.sum_range_reflect (fun i => i) n]

end AxQM.Concrete
