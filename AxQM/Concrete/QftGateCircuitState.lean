/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.QftGateCircuitCorrectness

/-!
# Concrete: state propagation through the Figure 5.1 QFT circuit blocks (N&C eqs. 5.5–5.10)

Building toward the correctness of the gate-level Figure 5.1 circuit
(`Concrete.qftGateCircuit n = qftMatrix 2ⁿ`, N&C eqs. 5.12–5.18), this file computes the **action of
the block sequence on a computational-basis input** — the state-vector propagation N&C run in eqs.
5.5–5.10. The circuit `qftGateCircuit n = ((qftGateSequence n)).reverse.prod` is the wire-reversal
`permGate` followed (in circuit/time order) by each target's block
`qftBlock n t = H_t ::` (its controlled-`Rₖ` cascade). Feeding a basis state `|enc a⟩` through the
blocks (the reversal is handled separately, in the final assembly), the state after the first
`m` blocks is the explicit superposition tracked here.

## The invariant

`qftPartialState n a m` is the register state after processing blocks `0, …, m-1` on the input
`|enc a⟩`: wires `≥ m` are still pinned to the input bits `a`, while each processed wire `s < m`
has been Hadamard-freed and carries the block phase `qftBlockPhase n a s` on its `|1⟩` component. At
index `i` with bits `k = enc.symm i`,

`qftPartialState n a m i = ⟦∀ s ≥ m, kₛ = aₛ⟧ · (1/√2)^m · ∏_{s < m} (qftBlockPhase n a s)^{kₛ}`.

The **block phase** `qftBlockPhase n a t` is the phase wire `t`'s `|1⟩` amplitude acquires in its
block: the Hadamard sign `(-1)^{a_t}` times the controlled-`Rₖ` cascade
`∏_{c > t, a_c = 1} e^{2πi/2^{c-t+1}}` from the (still pinned) higher wires — N&C's map appending
the binary fraction `0.a_t…a_{n-1}` to wire `t`.

## What is formalised

* `qftBlockPhase`, `qftPartialState` — the phase and the invariant state above.
* `qftPartialState_zero` — the input state: `qftPartialState n a 0 = |enc a⟩` (`Pi.single`).
* `qftBlockControlledGates_reverse_prod_eq_diagonal`, `qftBlock_reverse_prod` — the operator form of
  one block: `(qftBlock n t).reverse.prod = D_t · H_t`, the diagonal cascade `D_t` after the
  Hadamard `H_t`.
* `qftPartialState_succ` — **the single-block step**: applying block `m` to
  `qftPartialState n a m` gives `qftPartialState n a (m+1)`; the Hadamard frees wire `m` off the
  pinned set and the diagonal cascade multiplies its `|1⟩` by `qftBlockPhase`, the phase algebra
  `D_t · (-1)^{k_t a_t} = qftBlockPhase^{k_t}` closing the step.
* `qftBlocksProd_mulVec_basis` — **the block induction**: the whole block sequence maps `|enc a⟩` to
  the product state `qftPartialState n a n = (1/√2^n) ∏_t (qftBlockPhase n a t)^{k_t}` (the product
  representation, up to the input reversal — matched to `qftMatrix` in the final assembly).

## Why this file exists (Exercise 5.6)

The faithful `Ω(n²/p(n))` half of Exercise 5.6 needs the Figure 5.1 circuit as a formal object whose
controlled-`Rₖ` gates one can perturb, and the identification `qftGateCircuit n = qftMatrix 2ⁿ`.
This file supplies the reusable heart of that identification — the block-by-block state propagation,
and the single-block step is itself reusable for the *perturbed* circuit of the `Ω` argument (the
Hadamard-plus-cascade shape, with each `Rₖ` phase shifted). The final matrix equality (reversal
identity + match to `qftMatrix_apply_eq_prod_wirePhase`) is proved in `QftGateCircuitEqMatrix.lean`.
-/

namespace AxQM.Concrete

open Matrix

/-- **The block phase of wire `t`** (Nielsen & Chuang eqs. 5.5–5.6): the phase acquired by wire
`t`'s `|1⟩` amplitude as its Figure 5.1 block acts on the input-pinned state — the Hadamard sign
`(-1)^{a_t}` times the controlled-`Rₖ` cascade `∏_{c > t, a_c = 1} e^{2πi/2^{c-t+1}}` from the
higher wires (still holding the input bits `a`). This is N&C's map appending the binary fraction
`0.a_t a_{t+1} … a_{n-1}` to the phase of wire `t`. -/
noncomputable def qftBlockPhase (n : ℕ) (a : Fin n → Fin 2) (t : Fin n) : ℂ :=
  (-1) ^ (a t : ℕ) *
    ((qftTargetControls n t).map fun c =>
      if a c = 1 then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1))
      else 1).prod

/-- **The register state after the first `m` Figure 5.1 blocks act on `|enc a⟩`** (Nielsen & Chuang
eqs. 5.5–5.10). At basis index `i` with bit string `k = enc.symm i`: wires `s ≥ m` are still pinned
to the input bits `a` (the indicator `⟦∀ s ≥ m, kₛ = aₛ⟧`), the normalisation is `(1/√2)^m`, and
each processed wire `s < m` carries the block phase `qftBlockPhase n a s` raised to its output bit
`kₛ`.
`qftPartialState n a 0 = |enc a⟩` and `qftPartialState n a n` is the full product-representation
state. -/
noncomputable def qftPartialState (n : ℕ) (a : Fin n → Fin 2) (m : ℕ) : Fin (2 ^ n) → ℂ :=
  fun i =>
    if ∀ s : Fin n, m ≤ (s : ℕ) → finFunctionFinEquiv.symm i s = a s then
      (Real.sqrt 2 : ℂ)⁻¹ ^ m *
        ∏ s ∈ Finset.univ.filter (fun s : Fin n => (s : ℕ) < m),
          qftBlockPhase n a s ^ (finFunctionFinEquiv.symm i s : ℕ)
    else 0

/-- Both bits of `Fin 2` are `0` or `1` — the case split used in the block phase algebra. -/
private theorem fin_two_eq_zero_or_one (x : Fin 2) : x = 0 ∨ x = 1 := by
  decide +revert

/-- **The input state**: before any block acts (`m = 0`), the state is the basis vector `|enc a⟩`,
`qftPartialState n a 0 = Pi.single (finFunctionFinEquiv a) 1`. The pinned condition `∀ s, 0 ≤ s →
kₛ = aₛ` says `enc.symm i = a`, i.e. `i = enc a`; the empty phase product and `(1/√2)^0 = 1` leave
the amplitude `1`. -/
theorem qftPartialState_zero (n : ℕ) (a : Fin n → Fin 2) :
    qftPartialState n a 0 = Pi.single (finFunctionFinEquiv a) 1 := by
  funext i
  have hfil : (Finset.univ.filter (fun s : Fin n => (s : ℕ) < 0)) = ∅ := by simp
  have key : (∀ s : Fin n, (0 : ℕ) ≤ (s : ℕ) → finFunctionFinEquiv.symm i s = a s)
      ↔ i = finFunctionFinEquiv a := by
    constructor
    · intro h
      rw [← Equiv.symm_apply_eq]
      funext s; exact h s (Nat.zero_le _)
    · intro h s _; rw [h, Equiv.symm_apply_apply]
  rw [qftPartialState, hfil, Finset.prod_empty, mul_one, pow_zero, Pi.single_apply]
  by_cases h : i = finFunctionFinEquiv a
  · rw [ite_eq_left (key.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hh => h (key.mp hh)), ite_eq_right h]

/-- **A block's controlled-`Rₖ` cascade, product in reverse, is the same diagonal phase gate.** The
cascade gates are diagonal (`qftBlockControlledGates_prod_eq_diagonal`), so their product is
independent of order; the reverse product (which appears when reading `qftBlock.reverse.prod`) is
the same diagonal. -/
theorem qftBlockControlledGates_reverse_prod_eq_diagonal (n : ℕ) (t : Fin n) :
    (qftBlockControlledGates n t).reverse.prod = Matrix.diagonal fun i =>
      ((qftTargetControls n t).map fun c =>
        if finFunctionFinEquiv.symm i c = 1 ∧ finFunctionFinEquiv.symm i t = 1
        then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1)) else 1).prod := by
  rw [qftBlockControlledGates, ← List.map_reverse,
    List.map_congr_left fun c hc => qftControlledGate_eq_diagonal n t c
      (Fin.ne_of_val_ne (ne_of_lt (qftTargetControls_lt (List.mem_reverse.mp hc)))),
    diagonal_map_prod]
  refine congrArg Matrix.diagonal (funext fun i => ?_)
  rw [List.map_reverse, List.prod_reverse]

/-- **One Figure 5.1 block as an operator**: `(qftBlock n t).reverse.prod = D_t · H_t`, the Hadamard
`H_t = qftHadamardGate n t` on wire `t` followed by the diagonal cascade `D_t`. The block list
`H_t :: cascade` read as `.reverse.prod` is the operator
`cascade.reverse.prod · H_t = D_t · H_t`. -/
theorem qftBlock_reverse_prod (n : ℕ) (t : Fin n) :
    (qftBlock n t).reverse.prod
      = (Matrix.diagonal fun i => ((qftTargetControls n t).map fun c =>
          if finFunctionFinEquiv.symm i c = 1 ∧ finFunctionFinEquiv.symm i t = 1
          then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1)) else 1).prod)
        * qftHadamardGate n t := by
  rw [qftBlock, List.reverse_cons, List.prod_append, List.prod_singleton,
    qftBlockControlledGates_reverse_prod_eq_diagonal]

/-- **The block phase collapses the diagonal cascade against the Hadamard sign.** For a fixed output
bit `kt` on the target wire (its controls holding the input bits `a`), the diagonal cascade phase
times the Hadamard coefficient `hadamardC kt (a t)` is `(1/√2) · (qftBlockPhase n a t)^{kt}`: when
`kt = 0` the cascade is trivial and both sides are `(1/√2)`; when `kt = 1` the cascade
`∏_{c, a_c=1} e^{…}` times the sign `(-1)^{a_t}` is exactly `qftBlockPhase`. -/
private theorem cascade_mul_hadamardC (n : ℕ) (a : Fin n → Fin 2) (t : Fin n) (kt : Fin 2) :
    ((qftTargetControls n t).map fun c =>
        if a c = 1 ∧ kt = 1
        then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1)) else 1).prod
      * hadamardC kt (a t)
      = (Real.sqrt 2 : ℂ)⁻¹ * qftBlockPhase n a t ^ (kt : ℕ) := by
  have hH := hadamardC_apply kt (a t)
  have hD : ((qftTargetControls n t).map fun c =>
        if a c = 1 ∧ kt = 1
        then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1)) else 1).prod
      = ((qftTargetControls n t).map fun c =>
        if a c = 1
        then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1)) else 1).prod
        ^ (kt : ℕ) := by
    rcases fin_two_eq_zero_or_one kt with h | h <;> subst h
    · simp only [Fin.val_zero, pow_zero]
      refine List.prod_eq_one fun x hx => ?_
      simp only [List.mem_map] at hx
      obtain ⟨c, _, rfl⟩ := hx
      simp
    · rw [Fin.val_one, pow_one]
      refine congrArg _ (List.map_congr_left fun c _ => ?_)
      simp
  rw [hD, hH, qftBlockPhase, mul_pow, ← pow_mul]
  ring

/-- **The single-block step** (Nielsen & Chuang eqs. 5.5–5.10, one wire): applying block `m` to the
state after the first `m` blocks gives the state after `m+1` blocks. The Hadamard `H_m` frees wire
`m` off the pinned set (its `|1⟩`/`|0⟩` amplitudes get the sign `(-1)^{a_m}`), and the diagonal
cascade `D_m` multiplies wire `m`'s `|1⟩` by `∏_{c > m, a_c = 1} e^{2πi/2^{c-m+1}}`; the two combine
into `qftBlockPhase n a ⟨m⟩` on the freed wire, extending the phase product by one factor and the
normalisation by `1/√2`. -/
theorem qftPartialState_succ (n : ℕ) (a : Fin n → Fin 2) (m : ℕ) (hm : m < n) :
    (qftBlock n ⟨m, hm⟩).reverse.prod *ᵥ qftPartialState n a m = qftPartialState n a (m + 1) := by
  set t : Fin n := ⟨m, hm⟩ with ht
  have htv : (t : ℕ) = m := by rw [ht]
  rw [qftBlock_reverse_prod, ← Matrix.mulVec_mulVec]
  funext i
  rw [Matrix.mulVec_diagonal, qftHadamardGate, singleQubitOnWire_mulVec]
  set k := finFunctionFinEquiv.symm i with hk
  set Φ := ∏ s ∈ Finset.univ.filter (fun s : Fin n => (s : ℕ) < m),
    qftBlockPhase n a s ^ (k s : ℕ) with hΦ
  -- The invariant state at the two wire-`t` updates of `i`.
  have hval : ∀ b : Fin 2, qftPartialState n a m (finFunctionFinEquiv (Function.update k t b))
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
    simp only [qftPartialState, Equiv.symm_apply_apply]
    by_cases hc : b = a t ∧ (∀ s : Fin n, m + 1 ≤ (s : ℕ) → k s = a s)
    · rw [ite_eq_left (hcond.mpr hc), ite_eq_left hc, hΦ]
      congr 1
      refine Finset.prod_congr rfl fun s hs => ?_
      have hsm : (s : ℕ) < m := (Finset.mem_filter.mp hs).2
      rw [Function.update_of_ne (Fin.ne_of_val_ne (by rw [htv]; omega))]
    · rw [ite_eq_right (fun h => hc (hcond.mp h)), ite_eq_right hc]
  -- The state at `m+1`, with the phase product split off wire `t`.
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
  have hrhs : qftPartialState n a (m + 1) i
      = if (∀ s : Fin n, m + 1 ≤ (s : ℕ) → k s = a s)
        then (Real.sqrt 2 : ℂ)⁻¹ ^ (m + 1) * (qftBlockPhase n a t ^ (k t : ℕ) * Φ) else 0 := by
    simp only [qftPartialState, ← hk]
    rw [hfilsucc, Finset.prod_insert hnotmem, hΦ]
  rw [hval 0, hval 1, hrhs]
  by_cases hp : ∀ s : Fin n, m + 1 ≤ (s : ℕ) → k s = a s
  · rw [ite_eq_left hp]
    have hpin : ∀ c ∈ qftTargetControls n t, k c = a c := fun c hc =>
      hp c (by have := qftTargetControls_lt hc; rw [htv] at this; omega)
    have hDeq : ((qftTargetControls n t).map fun c =>
          if k c = 1 ∧ k t = 1
          then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1)) else 1).prod
        = ((qftTargetControls n t).map fun c =>
          if a c = 1 ∧ k t = 1
          then Complex.exp (2 * Real.pi * Complex.I / 2 ^ ((c : ℕ) - (t : ℕ) + 1))
          else 1).prod := by
      congr 1
      exact List.map_congr_left fun c hc => by rw [hpin c hc]
    rw [hDeq]
    simp only [and_iff_left hp]
    have hsum : hadamardC (k t) 0 * (if (0 : Fin 2) = a t then (Real.sqrt 2 : ℂ)⁻¹ ^ m * Φ else 0)
          + hadamardC (k t) 1 * (if (1 : Fin 2) = a t then (Real.sqrt 2 : ℂ)⁻¹ ^ m * Φ else 0)
        = hadamardC (k t) (a t) * ((Real.sqrt 2 : ℂ)⁻¹ ^ m * Φ) := by
      rcases fin_two_eq_zero_or_one (a t) with hat | hat <;> rw [hat]
      · rw [ite_eq_left rfl, ite_eq_right (by decide)]; ring
      · rw [ite_eq_right (by decide), ite_eq_left rfl]; ring
    rw [hsum, ← mul_assoc, cascade_mul_hadamardC, pow_succ]
    ring
  · rw [ite_eq_right hp, ite_eq_right (fun h => hp h.2), ite_eq_right (fun h => hp h.2)]
    ring

/-- **The block sequence maps a basis input to the product state** (Nielsen & Chuang eqs. 5.5–5.10).
The whole Figure 5.1 block sequence (all `qftBlock`s, without the wire reversal) applied to
`|enc a⟩` is the product-representation state `qftPartialState n a n`, i.e. `(1/√2^n) ∏_t
(qftBlockPhase n a t)^{k_t}`. By induction on the number of blocks processed, peeling the last block
with the single-block step `qftPartialState_succ`. -/
theorem qftBlocksProd_mulVec_basis (n : ℕ) (a : Fin n → Fin 2) :
    ((List.finRange n).flatMap (qftBlock n)).reverse.prod *ᵥ Pi.single (finFunctionFinEquiv a) 1
      = qftPartialState n a n := by
  have H : ∀ m, m ≤ n →
      (((List.finRange n).take m).flatMap (qftBlock n)).reverse.prod
          *ᵥ Pi.single (finFunctionFinEquiv a) 1
        = qftPartialState n a m := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [List.take_zero, List.flatMap_nil, List.reverse_nil, List.prod_nil, Matrix.one_mulVec,
        qftPartialState_zero]
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
        qftPartialState_succ n a m hm]
  have hfull := H n (le_refl n)
  rwa [List.take_of_length_le (le_of_eq List.length_finRange)] at hfull

end AxQM.Concrete
