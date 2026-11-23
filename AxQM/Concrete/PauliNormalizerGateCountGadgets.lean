/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliNormalizerGateCount

/-!
# Concrete: constant gate-count bounds for the single-qubit / single-wire synthesis gadgets

*(The `O(n²)` gate-count clause of Nielsen & Chuang Theorem 10.6 / Exercise 10.40, N&C §10.5.2,
pp. 461–462.)*

The `O(n²)` gate-count bound of Theorem 10.6 is proved by bounding the `CliffordCircuit` length
(`= List.length`, its gate count) through the Figure 10.9 reduction. The circuit arithmetic of the
building **definitions** is in `AxQM/Concrete/PauliNormalizerGateCount.lean`; this file gives the
base case: the *existence* lemmas for single-qubit and single-wire gadgets, strengthened to also
bound the gadget's length by a **constant**.

Each lemma here repeats the construction of its `PauliNormalizer*.lean` counterpart while also
tracking the gate count. The bounds are the small explicit constants read off the finite word
lists:

* `exists_cliffordCircuit_singleQubit_act_length_le` — a single-qubit permutation word (one of the
  six words of `S₃` on `{X, Y, Z}`) has `≤ 3` gates.
* `exists_cliffordCircuit_singleQubit_signFix_length_le` — a single-qubit sign-fix word (`I`, `X`,
  `Z`, `Y`-type Pauli-conjugation words) has `≤ 6` gates.
* `exists_cliffordCircuit_singleQubit_act_sign_length_le` — the glued single-qubit synthesis
  `permutation ++ sign-fix` has `≤ 9` gates.
* `exists_cliffordCircuit_onWire_act_sign_length_le` — running that gadget on one wire `j` of an
  `n`-qubit register (a wire relabeling, which preserves the gate count, `length_onWire`) still has
  `≤ 9` gates.

The last is the per-wire "sign gadget" the pair reduction and the first-wire reduction invoke a
bounded number of times; its constant length keeps their contribution to the level-cost `O(1)`.
-/

open Matrix

noncomputable section

namespace AxQM.Concrete

variable {n : ℕ}

/-- **A single-qubit permutation word has at most three gates.** Strengthens
`exists_cliffordCircuit_singleQubit_act` with a gate-count bound: each of the six explicit words
realising a permutation of `{X, Y, Z}` (`[]`, `[H]`, `[S]`, `[H, S, H]`, `[H, S]`, `[S, H]`) has at
most three gates. Same `fin_cases` case split as the base lemma, with the length checked by
`decide`. -/
theorem exists_cliffordCircuit_singleQubit_act_length_le {aX aZ : Fin 4}
    (h0X : aX ≠ 0) (h0Z : aZ ≠ 0) (hne : aX ≠ aZ) :
    ∃ p : CliffordCircuit 1, CliffordCircuit.act p (fun _ => 1) = (fun _ => aX) ∧
      CliffordCircuit.act p (fun _ => 3) = (fun _ => aZ) ∧ p.length ≤ 3 := by
  fin_cases aX <;> fin_cases aZ <;>
    first
      | exact absurd rfl h0X
      | exact absurd rfl h0Z
      | exact absurd rfl hne
      | exact ⟨[], by decide, by decide, by decide⟩
      | exact ⟨[.had 0], by decide, by decide, by decide⟩
      | exact ⟨[.phase 0], by decide, by decide, by decide⟩
      | exact ⟨[.had 0, .phase 0, .had 0], by decide, by decide, by decide⟩
      | exact ⟨[.had 0, .phase 0], by decide, by decide, by decide⟩
      | exact ⟨[.phase 0, .had 0], by decide, by decide, by decide⟩

/-- **A single-qubit sign-fix word has at most six gates.** Strengthens
`exists_cliffordCircuit_singleQubit_signFix` with a gate-count bound: the four trivial-action
sign-correction words (`[]`; the `Z`-flip `H S² H`; the `X`-flip `S²`; and their both-flip
composite) have at most six gates. Same split on the target signs, length checked by `decide`. -/
theorem exists_cliffordCircuit_singleQubit_signFix_length_le {sX sZ : ℂ}
    (hsX : sX = 1 ∨ sX = -1) (hsZ : sZ = 1 ∨ sZ = -1) :
    ∃ f : CliffordCircuit 1, CliffordCircuit.act f (fun _ => 1) = (fun _ => 1) ∧
      CliffordCircuit.act f (fun _ => 3) = (fun _ => 3) ∧
      CliffordCircuit.sign f (fun _ => 1) = sX ∧ CliffordCircuit.sign f (fun _ => 3) = sZ ∧
      f.length ≤ 6 := by
  rcases hsX with rfl | rfl <;> rcases hsZ with rfl | rfl
  · exact ⟨[], by decide, by decide, by simp [CliffordCircuit.sign],
      by simp [CliffordCircuit.sign], by decide⟩
  · exact ⟨[.had 0, .phase 0, .phase 0, .had 0], by decide, by decide,
      by simp [CliffordCircuit.sign, CliffordCircuit.act, CliffordGate.sign, CliffordGate.act,
        hadamardPauli, hadamardPauliSign, phasePauli, phasePauliSign, Function.update],
      by simp [CliffordCircuit.sign, CliffordCircuit.act, CliffordGate.sign, CliffordGate.act,
        hadamardPauli, hadamardPauliSign, phasePauli, phasePauliSign, Function.update],
      by decide⟩
  · exact ⟨[.phase 0, .phase 0], by decide, by decide,
      by simp [CliffordCircuit.sign, CliffordCircuit.act, CliffordGate.sign, CliffordGate.act,
        phasePauli, phasePauliSign, Function.update],
      by simp [CliffordCircuit.sign, CliffordCircuit.act, CliffordGate.sign, CliffordGate.act,
        phasePauli, phasePauliSign, Function.update],
      by decide⟩
  · exact ⟨[.had 0, .phase 0, .phase 0, .had 0, .phase 0, .phase 0], by decide, by decide,
      by simp [CliffordCircuit.sign, CliffordCircuit.act, CliffordGate.sign, CliffordGate.act,
        hadamardPauli, hadamardPauliSign, phasePauli, phasePauliSign, Function.update],
      by simp [CliffordCircuit.sign, CliffordCircuit.act, CliffordGate.sign, CliffordGate.act,
        hadamardPauli, hadamardPauliSign, phasePauli, phasePauliSign, Function.update],
      by decide⟩

/-- **The single-qubit synthesis has at most nine gates.** Strengthens
`exists_cliffordCircuit_singleQubit_act_sign` with a gate-count bound. The synthesised circuit is a
permutation word (`≤ 3` gates, `exists_cliffordCircuit_singleQubit_act_length_le`) appended with a
sign-fix word (`≤ 6` gates, `exists_cliffordCircuit_singleQubit_signFix_length_le`), so appending
gives `≤ 3 + 6 = 9` gates. The action/sign facts are proved exactly as in the base lemma. -/
theorem exists_cliffordCircuit_singleQubit_act_sign_length_le {aX aZ : Fin 4} {zX zZ : ℂ}
    (h0X : aX ≠ 0) (h0Z : aZ ≠ 0) (hne : aX ≠ aZ)
    (hzX : zX = 1 ∨ zX = -1) (hzZ : zZ = 1 ∨ zZ = -1) :
    ∃ C : CliffordCircuit 1,
      CliffordCircuit.act C (fun _ => 1) = (fun _ => aX) ∧
        CliffordCircuit.sign C (fun _ => 1) = zX ∧
      CliffordCircuit.act C (fun _ => 3) = (fun _ => aZ) ∧
        CliffordCircuit.sign C (fun _ => 3) = zZ ∧
      C.length ≤ 9 := by
  obtain ⟨p, hpX, hpZ, hplen⟩ := exists_cliffordCircuit_singleQubit_act_length_le h0X h0Z hne
  have hpXpm := CliffordCircuit.sign_eq_one_or_neg_one p (fun _ => 1)
  have hpZpm := CliffordCircuit.sign_eq_one_or_neg_one p (fun _ => 3)
  obtain ⟨f, hfaX, hfaZ, hfsX, hfsZ, hflen⟩ :=
    exists_cliffordCircuit_singleQubit_signFix_length_le
      (sX := zX * CliffordCircuit.sign p (fun _ => 1))
      (sZ := zZ * CliffordCircuit.sign p (fun _ => 3))
      (by rcases hzX with h | h <;> rcases hpXpm with h' | h' <;> rw [h, h'] <;> norm_num)
      (by rcases hzZ with h | h <;> rcases hpZpm with h' | h' <;> rw [h, h'] <;> norm_num)
  refine ⟨p ++ f, ?_, ?_, ?_, ?_, ?_⟩
  · rw [CliffordCircuit.act_append, hfaX, hpX]
  · rw [CliffordCircuit.sign_append, hfaX, hfsX]; rcases hpXpm with h | h <;> rw [h] <;> ring
  · rw [CliffordCircuit.act_append, hfaZ, hpZ]
  · rw [CliffordCircuit.sign_append, hfaZ, hfsZ]; rcases hpZpm with h | h <;> rw [h] <;> ring
  · rw [List.length_append]; omega

/-- **The single-wire sign gadget on wire `j` has at most nine gates.** Strengthens
`exists_cliffordCircuit_onWire_act_sign` with a gate-count bound. The gadget runs the single-qubit
synthesis (`≤ 9` gates, `exists_cliffordCircuit_singleQubit_act_sign_length_le`) on wire `j` via
`CliffordCircuit.onWire`, a wire relabeling that preserves the gate count
(`CliffordCircuit.length_onWire`), so the bound is unchanged. This is the per-wire sign gadget the
pair reduction and the first-wire reduction invoke a bounded number of times per induction level. -/
theorem exists_cliffordCircuit_onWire_act_sign_length_le (j : Fin n) {aX aZ : Fin 4} {zX zZ : ℂ}
    (h0X : aX ≠ 0) (h0Z : aZ ≠ 0) (hne : aX ≠ aZ)
    (hzX : zX = 1 ∨ zX = -1) (hzZ : zZ = 1 ∨ zZ = -1) :
    ∃ C : CliffordCircuit n,
      CliffordCircuit.act C (xGenPauli j) = Function.update (0 : Fin n → Fin 4) j aX ∧
        CliffordCircuit.sign C (xGenPauli j) = zX ∧
      CliffordCircuit.act C (zGenPauli j) = Function.update (0 : Fin n → Fin 4) j aZ ∧
        CliffordCircuit.sign C (zGenPauli j) = zZ ∧
      (∀ (g : Fin n → Fin 4) (k : Fin n), k ≠ j → CliffordCircuit.act C g k = g k) ∧
      C.length ≤ 9 := by
  obtain ⟨C₀, hCaX, hCsX, hCaZ, hCsZ, hC0len⟩ :=
    exists_cliffordCircuit_singleQubit_act_sign_length_le h0X h0Z hne hzX hzZ
  have hXj : (fun _ : Fin 1 => xGenPauli j j) = (fun _ => (1 : Fin 4)) := by
    funext _; simp [xGenPauli]
  have hZj : (fun _ : Fin 1 => zGenPauli j j) = (fun _ => (3 : Fin 4)) := by
    funext _; simp [zGenPauli]
  refine ⟨CliffordCircuit.onWire j C₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show xGenPauli j = Function.update (0 : Fin n → Fin 4) j 1 from rfl,
      CliffordCircuit.onWire_act_update, hCaX]
  · rw [CliffordCircuit.onWire_sign, hXj, hCsX]
  · rw [show zGenPauli j = Function.update (0 : Fin n → Fin 4) j 3 from rfl,
      CliffordCircuit.onWire_act_update, hCaZ]
  · rw [CliffordCircuit.onWire_sign, hZj, hCsZ]
  · intro g k hk
    exact CliffordCircuit.onWire_act_of_ne _ _ _ hk
  · rw [CliffordCircuit.length_onWire]; exact hC0len

end AxQM.Concrete

end
