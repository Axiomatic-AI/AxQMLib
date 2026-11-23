/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QftGateCircuitEqMatrix
import AxQM.Concrete.QftGateCircuitPerturbed

/-!
# Concrete: state propagation through the *perturbed* Figure 5.1 QFT circuit blocks

Toward the faithful `Ω(n²/p(n))` lower bound of Nielsen & Chuang, Exercise 5.6, this file computes
the **block-by-block action of the imperfect transform `V = qftGateCircuitPerturbed n Δ`** (each
controlled-`Rₖ` gate phase-shifted by `+Δ`, `QftGateCircuitPerturbed.lean`) on a computational-basis
input — the perturbed twin of the ideal propagation `QftGateCircuitState.lean`.

## The mirror

The perturbed circuit shares the exact Hadamard/swap structure of the ideal `qftGateCircuit` and
differs only in the cascade phase (`qftRk ↦ qftRkPerturbed`), so its state propagation mirrors
`QftGateCircuitState.lean` verbatim with the phase `e^{2πi/2^{c-t+1}}` shifted to
`e^{2πi/2^{c-t+1} + iΔ}` and `qftBlockPhase ↦ qftBlockPhasePerturbed`:

* `qftBlockPhasePerturbed`, `qftPartialStatePerturbed` — the perturbed block phase and the invariant
  register state after the first `m` blocks (the perturbed twins of `qftBlockPhase`,
  `qftPartialState`).
* `qftPartialStatePerturbed_zero`, `qftBlockPerturbed_reverse_prod`,
  `qftPartialStatePerturbed_succ`, `qftBlocksProdPerturbed_mulVec_basis` — the perturbed
  input-state, single-block operator, single-block step (Hadamard frees a wire, perturbed cascade
  applies its phase), and full block induction, each the perturbed twin of the corresponding ideal
  lemma. The headline `qftBlocksProdPerturbed_mulVec_basis` is: the perturbed block sequence
  (without the wire reversal) maps `|enc a⟩` to `qftPartialStatePerturbed n a Δ n`.
* `qftGateCircuitPerturbed_eq_blocks_mul_perm`, `qftPartialStatePerturbed_full` — the swap-first
  factorisation of the perturbed circuit and the `m = n` amplitude form, the two structure hooks the
  all-ones `Ω` specialisation consumes.

## Why this file exists (Exercise 5.6)

The faithful `Ω(n²/p(n))` half needs the perturbed circuit's output on the all-ones input `|1…1⟩` in
closed form. This file supplies the reusable heart: the block-by-block propagation to the perturbed
product state `qftPartialStatePerturbed n a Δ n`. The all-ones specialisation (the swap fixing
`|1…1⟩`, and reading the output off the coherent-phase `phaseProdVec` of `QftCoherentError.lean`) is
in `QftGateCircuitAllOnes.lean`; the coherent-accumulation distance bound is
`phaseProdVec_scaled_dist_ge` in `QftCoherentError.lean`.
-/

namespace AxQM.Concrete

open Matrix

/-- **The perturbed block phase of wire `t`**: the perturbed twin of `qftBlockPhase`, with each
controlled-`Rₖ'` cascade factor shifted by `+Δ` — the Hadamard sign `(-1)^{a_t}` times
`∏_{c > t, a_c = 1} e^{2πi/2^{c-t+1} + iΔ}`. It is the phase wire `t`'s `|1⟩`
amplitude picks up in its block of the imperfect circuit `qftGateCircuitPerturbed`. -/
noncomputable def qftBlockPhasePerturbed (n : ℕ) (a : Fin n → Fin 2) (Δ : ℝ) (t : Fin n) : ℂ :=
  (-1) ^ (a t : ℕ) *
    ((qftTargetControls n t).map fun c =>
      if a c = 1
      then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1) + ↑Δ * Complex.I)
      else 1).prod

/-- **The register state after the first `m` perturbed Figure 5.1 blocks act on `|enc a⟩`** — the
perturbed twin of `qftPartialState`: wires `s ≥ m` stay pinned to the input bits `a`, the
normalisation is `(1/√2)^m`, and each processed wire `s < m` carries
`qftBlockPhasePerturbed n a Δ s` raised to its output bit. -/
noncomputable def qftPartialStatePerturbed (n : ℕ) (a : Fin n → Fin 2) (Δ : ℝ) (m : ℕ) :
    Fin (2 ^ n) → ℂ :=
  fun i =>
    if ∀ s : Fin n, m ≤ (s : ℕ) → finFunctionFinEquiv.symm i s = a s then
      (Real.sqrt 2 : ℂ)⁻¹ ^ m *
        ∏ s ∈ Finset.univ.filter (fun s : Fin n => (s : ℕ) < m),
          qftBlockPhasePerturbed n a Δ s ^ (finFunctionFinEquiv.symm i s : ℕ)
    else 0

/-- Both bits of `Fin 2` are `0` or `1` — the case split used in the block phase algebra. -/
private theorem fin_two_cases (x : Fin 2) : x = 0 ∨ x = 1 := by decide +revert

/-- **The input state** (perturbed twin of `qftPartialState_zero`): before any block acts (`m = 0`),
`qftPartialStatePerturbed n a Δ 0 = |enc a⟩`. -/
theorem qftPartialStatePerturbed_zero (n : ℕ) (a : Fin n → Fin 2) (Δ : ℝ) :
    qftPartialStatePerturbed n a Δ 0 = Pi.single (finFunctionFinEquiv a) 1 := by
  funext i
  have hfil : (Finset.univ.filter (fun s : Fin n => (s : ℕ) < 0)) = ∅ := by simp
  have key : (∀ s : Fin n, (0 : ℕ) ≤ (s : ℕ) → finFunctionFinEquiv.symm i s = a s)
      ↔ i = finFunctionFinEquiv a := by
    constructor
    · intro h
      rw [← Equiv.symm_apply_eq]
      funext s; exact h s (Nat.zero_le _)
    · intro h s _; rw [h, Equiv.symm_apply_apply]
  rw [qftPartialStatePerturbed, hfil, Finset.prod_empty, mul_one, pow_zero, Pi.single_apply]
  by_cases h : i = finFunctionFinEquiv a
  · rw [ite_eq_left (key.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hh => h (key.mp hh)), ite_eq_right h]

/-- **The perturbed block's controlled-`Rₖ'` cascade, product in reverse, is the diagonal phase
gate** (perturbed twin of `qftBlockControlledGates_reverse_prod_eq_diagonal`): the perturbed cascade
gates are diagonal (`qftControlledGatePerturbed_eq_diagonal`), so the reverse product is the same
diagonal, now with the shifted phase `e^{2πi/2^{c-t+1} + iΔ}`. -/
theorem qftBlockControlledGatesPerturbed_reverse_prod_eq_diagonal (n : ℕ) (Δ : ℝ) (t : Fin n) :
    (qftBlockControlledGatesPerturbed n Δ t).reverse.prod = Matrix.diagonal fun i =>
      ((qftTargetControls n t).map fun c =>
        if finFunctionFinEquiv.symm i c = 1 ∧ finFunctionFinEquiv.symm i t = 1
        then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1) + ↑Δ * Complex.I)
        else 1).prod := by
  rw [qftBlockControlledGatesPerturbed, ← List.map_reverse,
    List.map_congr_left fun c hc => qftControlledGatePerturbed_eq_diagonal n Δ t c
      (Fin.ne_of_val_ne (ne_of_lt (qftTargetControls_lt (List.mem_reverse.mp hc)))),
    diagonal_map_prod]
  refine congrArg Matrix.diagonal (funext fun i => ?_)
  rw [List.map_reverse, List.prod_reverse]

/-- **One perturbed Figure 5.1 block as an operator** (perturbed twin of `qftBlock_reverse_prod`):
`(qftBlockPerturbed n Δ t).reverse.prod = D'_t · H_t`, the exact Hadamard `H_t` followed by the
perturbed diagonal cascade `D'_t`. -/
theorem qftBlockPerturbed_reverse_prod (n : ℕ) (Δ : ℝ) (t : Fin n) :
    (qftBlockPerturbed n Δ t).reverse.prod
      = (Matrix.diagonal fun i => ((qftTargetControls n t).map fun c =>
          if finFunctionFinEquiv.symm i c = 1 ∧ finFunctionFinEquiv.symm i t = 1
          then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1) + ↑Δ * Complex.I)
          else 1).prod)
        * qftHadamardGate n t := by
  rw [qftBlockPerturbed, List.reverse_cons, List.prod_append, List.prod_singleton,
    qftBlockControlledGatesPerturbed_reverse_prod_eq_diagonal]

/-- **The perturbed block phase collapses the perturbed diagonal cascade against the Hadamard sign**
(perturbed twin of the ideal `cascade_mul_hadamardC`): for a fixed output bit `kt`, the perturbed
cascade phase times the Hadamard coefficient is `(1/√2)·(qftBlockPhasePerturbed n a Δ t)^{kt}`. -/
private theorem cascadePerturbed_mul_hadamardC (n : ℕ) (a : Fin n → Fin 2) (Δ : ℝ) (t : Fin n)
    (kt : Fin 2) :
    ((qftTargetControls n t).map fun c =>
        if a c = 1 ∧ kt = 1
        then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1) + ↑Δ * Complex.I)
        else 1).prod
      * hadamardC kt (a t)
      = (Real.sqrt 2 : ℂ)⁻¹ * qftBlockPhasePerturbed n a Δ t ^ (kt : ℕ) := by
  have hH := hadamardC_apply kt (a t)
  have hD : ((qftTargetControls n t).map fun c =>
        if a c = 1 ∧ kt = 1
        then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1) + ↑Δ * Complex.I)
        else 1).prod
      = ((qftTargetControls n t).map fun c =>
        if a c = 1
        then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1) + ↑Δ * Complex.I)
        else 1).prod
        ^ (kt : ℕ) := by
    rcases fin_two_cases kt with h | h <;> subst h
    · simp only [Fin.val_zero, pow_zero]
      refine List.prod_eq_one fun x hx => ?_
      simp only [List.mem_map] at hx
      obtain ⟨c, _, rfl⟩ := hx
      simp
    · rw [Fin.val_one, pow_one]
      refine congrArg _ (List.map_congr_left fun c _ => ?_)
      simp
  rw [hD, hH, qftBlockPhasePerturbed, mul_pow, ← pow_mul]
  ring

/-- **The perturbed single-block step** (perturbed twin of `qftPartialState_succ`): applying the
perturbed block `m` to the state after `m` blocks gives the state after `m+1` blocks. The Hadamard
frees wire `m` and the perturbed diagonal cascade multiplies its `|1⟩` by
`∏_{c > m, a_c = 1} e^{2πi/2^{c-m+1} + iΔ}`, the two combining into
`qftBlockPhasePerturbed n a Δ ⟨m⟩` on the freed wire. -/
theorem qftPartialStatePerturbed_succ (n : ℕ) (a : Fin n → Fin 2) (Δ : ℝ) (m : ℕ) (hm : m < n) :
    (qftBlockPerturbed n Δ ⟨m, hm⟩).reverse.prod *ᵥ qftPartialStatePerturbed n a Δ m
      = qftPartialStatePerturbed n a Δ (m + 1) := by
  set t : Fin n := ⟨m, hm⟩ with ht
  have htv : (t : ℕ) = m := by rw [ht]
  rw [qftBlockPerturbed_reverse_prod, ← Matrix.mulVec_mulVec]
  funext i
  rw [Matrix.mulVec_diagonal, qftHadamardGate, singleQubitOnWire_mulVec]
  set k := finFunctionFinEquiv.symm i with hk
  set Φ := ∏ s ∈ Finset.univ.filter (fun s : Fin n => (s : ℕ) < m),
    qftBlockPhasePerturbed n a Δ s ^ (k s : ℕ) with hΦ
  have hval : ∀ b : Fin 2,
      qftPartialStatePerturbed n a Δ m (finFunctionFinEquiv (Function.update k t b))
      = if b = a t ∧ (∀ s : Fin n, m + 1 ≤ (s : ℕ) → k s = a s)
        then (Real.sqrt 2 : ℂ)⁻¹ ^ m * Φ else 0 := by
    intro b
    have hcond : (∀ s : Fin n, m ≤ (s : ℕ) → Function.update k t b s = a s)
        ↔ (b = a t ∧ ∀ s : Fin n, m + 1 ≤ (s : ℕ) → k s = a s) := by
      constructor
      · intro h
        refine ⟨?_, fun s hs => ?_⟩
        · have := h t (le_of_eq htv.symm)
          rwa [Function.update_self] at this
        · have hst : s ≠ t := Fin.ne_of_val_ne (by rw [htv]; omega)
          rw [← Function.update_of_ne hst b k]
          exact h s (by omega)
      · rintro ⟨hb, hab⟩ s hs
        rcases eq_or_lt_of_le hs with heq | hlt
        · have hst : s = t := Fin.ext (by rw [htv]; omega)
          rw [hst, Function.update_self]; exact hb
        · rw [Function.update_of_ne (Fin.ne_of_val_ne (by rw [htv]; omega))]
          exact hab s (by omega)
    simp only [qftPartialStatePerturbed, Equiv.symm_apply_apply]
    by_cases hc : b = a t ∧ (∀ s : Fin n, m + 1 ≤ (s : ℕ) → k s = a s)
    · rw [ite_eq_left (hcond.mpr hc), ite_eq_left hc, hΦ]
      congr 1
      refine Finset.prod_congr rfl fun s hs => ?_
      have hsm : (s : ℕ) < m := (Finset.mem_filter.mp hs).2
      rw [Function.update_of_ne (Fin.ne_of_val_ne (by rw [htv]; omega))]
    · rw [ite_eq_right (fun h => hc (hcond.mp h)), ite_eq_right hc]
  have hnotmem : t ∉ Finset.univ.filter (fun s : Fin n => (s : ℕ) < m) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [htv]; omega
  have hfilsucc : Finset.univ.filter (fun s : Fin n => (s : ℕ) < m + 1)
      = insert t (Finset.univ.filter (fun s : Fin n => (s : ℕ) < m)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hs; rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext (by rw [htv]; exact h))
    · rintro (rfl | h)
      · rw [htv]; omega
      · omega
  have hrhs : qftPartialStatePerturbed n a Δ (m + 1) i
      = if (∀ s : Fin n, m + 1 ≤ (s : ℕ) → k s = a s)
        then (Real.sqrt 2 : ℂ)⁻¹ ^ (m + 1) * (qftBlockPhasePerturbed n a Δ t ^ (k t : ℕ) * Φ)
        else 0 := by
    simp only [qftPartialStatePerturbed, ← hk]
    rw [hfilsucc, Finset.prod_insert hnotmem, hΦ]
  rw [hval 0, hval 1, hrhs]
  by_cases hp : ∀ s : Fin n, m + 1 ≤ (s : ℕ) → k s = a s
  · rw [ite_eq_left hp]
    have hpin : ∀ c ∈ qftTargetControls n t, k c = a c := fun c hc =>
      hp c (by have := qftTargetControls_lt hc; rw [htv] at this; omega)
    have hDeq : ((qftTargetControls n t).map fun c =>
          if k c = 1 ∧ k t = 1
          then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1) + ↑Δ * Complex.I)
          else 1).prod
        = ((qftTargetControls n t).map fun c =>
          if a c = 1 ∧ k t = 1
          then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1) + ↑Δ * Complex.I)
          else 1).prod := by
      congr 1
      exact List.map_congr_left fun c hc => by rw [hpin c hc]
    rw [hDeq]
    simp only [and_iff_left hp]
    have hsum : hadamardC (k t) 0 * (if (0 : Fin 2) = a t then (Real.sqrt 2 : ℂ)⁻¹ ^ m * Φ else 0)
          + hadamardC (k t) 1 * (if (1 : Fin 2) = a t then (Real.sqrt 2 : ℂ)⁻¹ ^ m * Φ else 0)
        = hadamardC (k t) (a t) * ((Real.sqrt 2 : ℂ)⁻¹ ^ m * Φ) := by
      rcases fin_two_cases (a t) with hat | hat <;> rw [hat]
      · rw [ite_eq_left rfl, ite_eq_right (by decide)]; ring
      · rw [ite_eq_right (by decide), ite_eq_left rfl]; ring
    rw [hsum, ← mul_assoc, cascadePerturbed_mul_hadamardC, pow_succ]
    ring
  · rw [ite_eq_right hp, ite_eq_right (fun h => hp h.2), ite_eq_right (fun h => hp h.2)]
    ring

/-- **The perturbed block sequence maps a basis input to the perturbed product state** (perturbed
twin of `qftBlocksProd_mulVec_basis`): the whole perturbed Figure 5.1 block sequence (without the
wire reversal) applied to `|enc a⟩` is `qftPartialStatePerturbed n a Δ n`, by induction on the
number of blocks with the single-block step `qftPartialStatePerturbed_succ`. -/
theorem qftBlocksProdPerturbed_mulVec_basis (n : ℕ) (a : Fin n → Fin 2) (Δ : ℝ) :
    ((List.finRange n).flatMap (qftBlockPerturbed n Δ)).reverse.prod
        *ᵥ Pi.single (finFunctionFinEquiv a) 1
      = qftPartialStatePerturbed n a Δ n := by
  have H : ∀ m, m ≤ n →
      (((List.finRange n).take m).flatMap (qftBlockPerturbed n Δ)).reverse.prod
          *ᵥ Pi.single (finFunctionFinEquiv a) 1
        = qftPartialStatePerturbed n a Δ m := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [List.take_zero, List.flatMap_nil, List.reverse_nil, List.prod_nil, Matrix.one_mulVec,
        qftPartialStatePerturbed_zero]
    | succ m ih =>
      intro hm1
      have hm : m < n := hm1
      have hlen : m < (List.finRange n).length := by rw [List.length_finRange]; exact hm
      have hget : (List.finRange n)[m]'hlen = (⟨m, hm⟩ : Fin n) := by simp [List.getElem_finRange]
      have htk : (List.finRange n).take (m + 1)
          = (List.finRange n).take m ++ [(⟨m, hm⟩ : Fin n)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlen, hget]; rfl
      rw [htk, List.flatMap_append, List.reverse_append, List.prod_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, ← Matrix.mulVec_mulVec, ih (le_of_lt hm),
        qftPartialStatePerturbed_succ n a Δ m hm]
  have hfull := H n (le_refl n)
  rwa [List.take_of_length_le (le_of_eq List.length_finRange)] at hfull

/-- **The perturbed circuit factors as blocks-then-swap** (perturbed twin of
`qftGateCircuit_eq_blocks_mul_perm`): `qftGateCircuitPerturbed n Δ = (∏ perturbed blocks) · P`, the
same wire-reversal `P` as the ideal circuit (only the blocks carry the perturbed gates). A structure
hook for the all-ones `Ω` specialisation. -/
theorem qftGateCircuitPerturbed_eq_blocks_mul_perm (n : ℕ) (Δ : ℝ) :
    qftGateCircuitPerturbed n Δ
      = ((List.finRange n).flatMap (qftBlockPerturbed n Δ)).reverse.prod
        * permGate finFunctionFinEquiv (qftBitReversal n) := by
  rw [qftGateCircuitPerturbed, qftGateSequencePerturbed, List.reverse_cons, List.prod_append,
    List.prod_singleton]

/-- **The full perturbed product state at `m = n`** (perturbed twin of `qftPartialState_full`): once
every block has acted the pinned condition is vacuous, so
`qftPartialStatePerturbed n a Δ n i = (1/√2)ⁿ · ∏ₛ (qftBlockPhasePerturbed n a Δ s)^{kₛ}`. -/
theorem qftPartialStatePerturbed_full (n : ℕ) (a : Fin n → Fin 2) (Δ : ℝ) (i : Fin (2 ^ n)) :
    qftPartialStatePerturbed n a Δ n i
      = (Real.sqrt 2 : ℂ)⁻¹ ^ n
        * ∏ s : Fin n, qftBlockPhasePerturbed n a Δ s ^ (finFunctionFinEquiv.symm i s : ℕ) := by
  rw [qftPartialStatePerturbed, ite_eq_left (fun s hs => absurd hs (Nat.not_le.mpr s.isLt)),
    Finset.filter_true_of_mem (fun s _ => s.isLt)]

end AxQM.Concrete
