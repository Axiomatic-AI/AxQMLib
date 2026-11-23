/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliNormalizerGateCount

/-!
# Concrete: the `O(n)` gate-count of the single-generator reduction (N&C Theorem 10.6)

*(Supporting material for Theorem 10.6, N&C §10.5.2, p. 461.)*

Nielsen & Chuang **Theorem 10.6** asserts a normalizer `U ∈ N(Gₙ)` may be composed, up to a global
phase, from **`O(n²)`** Hadamard/phase/CNOT gates. The structural converse
(`isPauliNormalizer_eq_smul_cliffordCircuit`) is discharged; what remains is the quantitative gate
count, which is threaded bottom-up through the Figure 10.9
synthesis: the **length calculus of the circuit-building *definitions***
(`PauliNormalizerGateCount.lean`), then a **per-level linear bound** `|B| ≤ O(n)` on the first-wire
reduction circuit (this cascade), then the `O(n²)` headline.

This file is the **first step**: it bounds the length of the **single-generator
reduction** — the sweep that collapses a normalizer's generator image `U X₁ U†` to a standard
`X_c`/`Z_c` (`exists_cliffordCircuit_reduceToXGen`/`…ZGen`). Each such reduction is a
diagonalising single-qubit *layer* (`O(n)` gates: one bounded word on each of `n` wires), then a
CNOT *fan* (`O(n)` gates: at most one gate per support wire), then a constant-size sign gadget, so
it costs `O(n)` gates in total.

## Length-annotated companions

The length-of-definition lemmas (`length_singleQubitLayer_le`, `length_cnotFan_le`, …) are in
`AxQM/Concrete/PauliNormalizerGateCount.lean`. The quantitative refinement is stated here as
length-annotated **companions** `…_length_le` of the existence lemmas, which re-exhibit each
circuit and additionally bound its `List.length`. The action/phase content is carried entirely by
the shared building-block lemmas (`singleQubitLayer_act`, `act_cnotFan_collapse`,
`onWire_act_update`, …), so each companion is a thin assembly that pairs the original construction
with a length bound, not a re-proof of the tableau algebra.

Contents:

* `exists_singleQubitLayer_act_diagX_length_le` / `…diagZ_length_le` — the diagonalising layers
  cost `≤ n` (resp. `≤ 2·n`) gates: one `rotateToX` (`≤ 1`) resp. `rotateToZ` (`≤ 2`) word on each
  of the `n` wires (`length_singleQubitLayer_le`).
* `exists_cliffordCircuit_cnotClear_toSingleX_length_le` / `…toSingleZ_length_le` — the CNOT
  clearing fans cost `≤ n` gates: at most one CNOT per support wire
  (`length_cnotFan_le`/`…FanInto_le`), and the support is a `Finset.filter` of `Fin n`, so its
  size is `≤ n`.
* `exists_cliffordCircuit_xGen_signFlip_length_le` (`≤ 2`) / `…zGen_signFlip_length_le` (`≤ 4`) —
  the sign-flip gadgets are single-wire Pauli conjugations (`Z = S²`, `X = H S² H`) on one wire.
* `exists_cliffordCircuit_reduceToXGen_length_le` (`≤ 2·n + 2`) / `…reduceToZGen_length_le`
  (`≤ 3·n + 4`) — the exact single-generator reduction costs `O(n)` gates, the per-generator atom
  of the linear per-level bound `|B| ≤ O(n)`.
* `exists_cliffordCircuit_reduceFirstOfPair_length_le` (`≤ 2·n + 2`) — the
  symplectic first move of the anticommuting-pair reduction (reduce `p` to `X_c` while its partner
  `q` keeps a `Z` factor on the pivot `c`) is exactly `reduceToXGen` applied to `p`, so it inherits
  the `≤ 2·n + 2` bound. This is the `O(n)` entry point of the pair-reduction cascade toward the
  first-wire reduction `fixFirstPair`.

-/
open Matrix

noncomputable section

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The diagonalising single-qubit layers cost `O(n)` gates -/

/-- **The all-`X` diagonalising layer costs `≤ n` gates.** The length-annotated companion of
`exists_singleQubitLayer_act_diagX`: for any Pauli string `a` there is a per-wire family `f` whose
layer sends `a` to its all-`X`-on-support form *and* whose gate count is `≤ n`. Take
`f k = rotateToX (a k)`; each per-wire word has `≤ 1` gate (`length_rotateToX_le`), so the layer —
one word on each of the `n` wires — has `≤ n · 1 = n` gates (`length_singleQubitLayer_le`). -/
theorem exists_singleQubitLayer_act_diagX_length_le (a : Fin n → Fin 4) :
    ∃ f : Fin n → CliffordCircuit 1,
      (∀ k, CliffordCircuit.act (CliffordCircuit.singleQubitLayer f) a k
          = if a k = 0 then 0 else 1) ∧
        (CliffordCircuit.singleQubitLayer f).length ≤ n := by
  refine ⟨fun k => CliffordCircuit.rotateToX (a k), fun k => ?_, ?_⟩
  · rw [CliffordCircuit.singleQubitLayer_act]; exact CliffordCircuit.rotateToX_act (a k)
  · calc (CliffordCircuit.singleQubitLayer fun k => CliffordCircuit.rotateToX (a k)).length
        ≤ n * 1 :=
          CliffordCircuit.length_singleQubitLayer_le _
            fun i => CliffordCircuit.length_rotateToX_le _
      _ = n := Nat.mul_one n

/-- **The all-`Z` diagonalising layer costs `≤ 2·n` gates.** The `Z`-basis mirror of
`exists_singleQubitLayer_act_diagX_length_le`: `f k = rotateToZ (a k)`, each per-wire word `≤ 2`
gates (`H` for `X`, `H S` for `Y`; `length_rotateToZ_le`), so the layer has `≤ n · 2 = 2·n` gates.
-/
theorem exists_singleQubitLayer_act_diagZ_length_le (a : Fin n → Fin 4) :
    ∃ f : Fin n → CliffordCircuit 1,
      (∀ k, CliffordCircuit.act (CliffordCircuit.singleQubitLayer f) a k
          = if a k = 0 then 0 else 3) ∧
        (CliffordCircuit.singleQubitLayer f).length ≤ 2 * n := by
  refine ⟨fun k => CliffordCircuit.rotateToZ (a k), fun k => ?_, ?_⟩
  · rw [CliffordCircuit.singleQubitLayer_act]; exact CliffordCircuit.rotateToZ_act (a k)
  · calc (CliffordCircuit.singleQubitLayer fun k => CliffordCircuit.rotateToZ (a k)).length
        ≤ n * 2 :=
          CliffordCircuit.length_singleQubitLayer_le _
            fun i => CliffordCircuit.length_rotateToZ_le _
      _ = 2 * n := Nat.mul_comm n 2

/-! ### The CNOT-clearing fans cost `O(n)` gates -/

/-- **The all-`X` CNOT-clearing fan costs `≤ n` gates.** The length-annotated companion of
`exists_cliffordCircuit_cnotClear_toSingleX`: the witness is the CNOT fan `cnotFan c ts` over the
support `ts = {k | a k = 1, k ≠ c}`, which has at most one gate per target
(`length_cnotFan_le`, `≤ |ts|`), and `ts` is a `Finset.filter` of `Fin n` so `|ts| ≤ n`
(`card_filter_le`). The action/phase proof is that of the original (`act_cnotFan_collapse`,
`sign_cnotFan_collapse`). -/
theorem exists_cliffordCircuit_cnotClear_toSingleX_length_le (a : Fin n → Fin 4) (c : Fin n)
    (hc : a c = 1) (hX : ∀ k, a k = 0 ∨ a k = 1) :
    ∃ C : CliffordCircuit n,
      CliffordCircuit.act C a = xGenPauli c ∧ CliffordCircuit.sign C a = 1 ∧ C.length ≤ n := by
  set ts := (Finset.univ.filter (fun k => a k = 1 ∧ k ≠ c)).toList with hts
  have hmem : ∀ k, k ∈ ts ↔ (a k = 1 ∧ k ≠ c) := by
    intro k
    rw [hts, Finset.mem_toList, Finset.mem_filter]
    simp
  have hnd : ts.Nodup := Finset.nodup_toList _
  have hcnotin : c ∉ ts := fun h => ((hmem c).mp h).2 rfl
  have hall : ∀ t ∈ ts, a t = 1 := fun t ht => ((hmem t).mp ht).1
  have hlen : ts.length ≤ n := by
    rw [hts, Finset.length_toList]
    calc (Finset.univ.filter fun k => a k = 1 ∧ k ≠ c).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
      _ = n := by simp
  refine ⟨cnotFan c ts, ?_, sign_cnotFan_collapse c ts hcnotin hnd a hc hall,
    le_trans (length_cnotFan_le c ts) hlen⟩
  funext k
  rw [act_cnotFan_collapse c ts hcnotin hnd a hc hall k, xGenPauli_apply]
  rcases eq_or_ne k c with rfl | hkc
  · simp
  · simp only [ite_eq_right hkc]
    by_cases hk1 : a k = 1
    · rw [ite_eq_left ((hmem k).mpr ⟨hk1, hkc⟩)]
    · rw [ite_eq_right (fun h => hk1 ((hmem k).mp h).1)]
      exact (hX k).resolve_right hk1

/-- **The all-`Z` reverse CNOT-clearing fan costs `≤ n` gates.** The `Z`-basis mirror of
`exists_cliffordCircuit_cnotClear_toSingleX_length_le`: the witness is the reverse fan
`cnotFanInto c ts` over the support `ts = {k | a k = 3, k ≠ c}` (`length_cnotFanInto_le`, `≤ |ts|`),
again `|ts| ≤ n`. Action/phase from `act_cnotFanInto_collapse`, `sign_cnotFanInto_collapse`. -/
theorem exists_cliffordCircuit_cnotClear_toSingleZ_length_le (a : Fin n → Fin 4) (c : Fin n)
    (hc : a c = 3) (hZ : ∀ k, a k = 0 ∨ a k = 3) :
    ∃ C : CliffordCircuit n,
      CliffordCircuit.act C a = zGenPauli c ∧ CliffordCircuit.sign C a = 1 ∧ C.length ≤ n := by
  set ts := (Finset.univ.filter (fun k => a k = 3 ∧ k ≠ c)).toList with hts
  have hmem : ∀ k, k ∈ ts ↔ (a k = 3 ∧ k ≠ c) := by
    intro k
    rw [hts, Finset.mem_toList, Finset.mem_filter]
    simp
  have hnd : ts.Nodup := Finset.nodup_toList _
  have hcnotin : c ∉ ts := fun h => ((hmem c).mp h).2 rfl
  have hall : ∀ t ∈ ts, a t = 3 := fun t ht => ((hmem t).mp ht).1
  have hlen : ts.length ≤ n := by
    rw [hts, Finset.length_toList]
    calc (Finset.univ.filter fun k => a k = 3 ∧ k ≠ c).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
      _ = n := by simp
  refine ⟨cnotFanInto c ts, ?_, sign_cnotFanInto_collapse c ts hcnotin hnd a hc hall,
    le_trans (length_cnotFanInto_le c ts) hlen⟩
  funext k
  rw [act_cnotFanInto_collapse c ts hcnotin hnd a hc hall k, zGenPauli_apply]
  rcases eq_or_ne k c with rfl | hkc
  · simp
  · simp only [ite_eq_right hkc]
    by_cases hk3 : a k = 3
    · rw [ite_eq_left ((hmem k).mpr ⟨hk3, hkc⟩)]
    · rw [ite_eq_right (fun h => hk3 ((hmem k).mp h).1)]
      exact (hZ k).resolve_right hk3

/-! ### The single-wire sign-flip gadgets are constant-length -/

/-- **The `X_c` sign-flip gadget costs `≤ 2` gates.** The length-annotated companion of
`exists_cliffordCircuit_xGen_signFlip`, with the explicit construction `onWire c [S, S]`: a `Z_c`
conjugation (`Z = S²`, `Z X Z = -X`, `Z Z Z = Z`) placed on wire `c`. It fixes `X_c`'s index while
negating its phase (`act = X_c`, `sign = -1`), and has `2` gates (`length_onWire`). -/
theorem exists_cliffordCircuit_xGen_signFlip_length_le (c : Fin n) :
    ∃ C : CliffordCircuit n,
      CliffordCircuit.act C (xGenPauli c) = xGenPauli c ∧
        CliffordCircuit.sign C (xGenPauli c) = -1 ∧ C.length ≤ 2 := by
  refine ⟨CliffordCircuit.onWire c [CliffordGate.phase 0, CliffordGate.phase 0], ?_, ?_, ?_⟩
  · rw [show xGenPauli c = Function.update (0 : Fin n → Fin 4) c 1 from rfl,
      CliffordCircuit.onWire_act_update,
      show CliffordCircuit.act [CliffordGate.phase 0, CliffordGate.phase 0]
          (fun _ => (1 : Fin 4)) 0 = 1 from by decide]
  · have hcc : xGenPauli c c = 1 := by rw [xGenPauli_apply, ite_eq_left rfl]
    rw [CliffordCircuit.onWire_sign, hcc]
    simp [CliffordCircuit.sign, CliffordCircuit.act, CliffordGate.sign, CliffordGate.act,
      phasePauli, phasePauliSign, Function.update]
  · simp [CliffordCircuit.length_onWire]

/-- **The `Z_c` sign-flip gadget costs `≤ 4` gates.** The length-annotated companion of
`exists_cliffordCircuit_zGen_signFlip`, with the explicit construction `onWire c [H, S, S, H]`: an
`X_c` conjugation (`X = H S² H`, `X Z X = -Z`, `X X X = X`) placed on wire `c`. It fixes `Z_c`'s
index while negating its phase (`act = Z_c`, `sign = -1`), and has `4` gates (`length_onWire`). -/
theorem exists_cliffordCircuit_zGen_signFlip_length_le (c : Fin n) :
    ∃ C : CliffordCircuit n,
      CliffordCircuit.act C (zGenPauli c) = zGenPauli c ∧
        CliffordCircuit.sign C (zGenPauli c) = -1 ∧ C.length ≤ 4 := by
  refine ⟨CliffordCircuit.onWire c
      [CliffordGate.had 0, CliffordGate.phase 0, CliffordGate.phase 0, CliffordGate.had 0],
    ?_, ?_, ?_⟩
  · rw [show zGenPauli c = Function.update (0 : Fin n → Fin 4) c 3 from rfl,
      CliffordCircuit.onWire_act_update,
      show CliffordCircuit.act [CliffordGate.had 0, CliffordGate.phase 0, CliffordGate.phase 0,
          CliffordGate.had 0] (fun _ => (3 : Fin 4)) 0 = 3 from by decide]
  · have hcc : zGenPauli c c = 3 := by rw [zGenPauli_apply, ite_eq_left rfl]
    rw [CliffordCircuit.onWire_sign, hcc]
    simp [CliffordCircuit.sign, CliffordCircuit.act, CliffordGate.sign, CliffordGate.act,
      hadamardPauli, hadamardPauliSign, phasePauli, phasePauliSign, Function.update]
  · simp [CliffordCircuit.length_onWire]

/-! ### The single-generator reduction costs `O(n)` gates -/

/-- **Exact reduction to a standard `X` generator costs `≤ 2·n + 2` gates.** The length-annotated
companion of `exists_cliffordCircuit_reduceToXGen`: the reducing circuit is
`[sign gadget] ++ cnotClear ++ layer`, whose diagonalising layer costs `≤ n`
(`…diagX_length_le`), CNOT clear `≤ n` (`…cnotClear_toSingleX_length_le`) and sign gadget `≤ 2`
(`…xGen_signFlip_length_le`), so `≤ 2·n + 2` gates. This is the per-generator `O(n)` atom of the
linear per-level bound the Figure 10.9 induction needs. -/
theorem exists_cliffordCircuit_reduceToXGen_length_le (a : Fin n → Fin 4) (c : Fin n)
    (hc : a c ≠ 0) :
    ∃ C : CliffordCircuit n,
      CliffordCircuit.act C a = xGenPauli c ∧ CliffordCircuit.sign C a = 1 ∧
        C.length ≤ 2 * n + 2 := by
  obtain ⟨f, hf, hLlen⟩ := exists_singleQubitLayer_act_diagX_length_le a
  have ha'c : CliffordCircuit.act (CliffordCircuit.singleQubitLayer f) a c = 1 := by
    rw [hf c, ite_eq_right hc]
  have ha'X : ∀ k, CliffordCircuit.act (CliffordCircuit.singleQubitLayer f) a k = 0 ∨
      CliffordCircuit.act (CliffordCircuit.singleQubitLayer f) a k = 1 := by
    intro k; rw [hf k]; split
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨K, hKact, hKsign, hKlen⟩ :=
    exists_cliffordCircuit_cnotClear_toSingleX_length_le
      (CliffordCircuit.act (CliffordCircuit.singleQubitLayer f) a) c ha'c ha'X
  set L := CliffordCircuit.singleQubitLayer f with hLdef
  have hrest_act : CliffordCircuit.act (K ++ L) a = xGenPauli c := by
    rw [CliffordCircuit.act_append]; exact hKact
  have hrest_sign : CliffordCircuit.sign (K ++ L) a = CliffordCircuit.sign L a := by
    rw [CliffordCircuit.sign_append, hKsign, mul_one]
  have hrest_len : (K ++ L).length ≤ 2 * n := by
    rw [List.length_append]; omega
  rcases CliffordCircuit.sign_eq_one_or_neg_one L a with hs | hs
  · exact ⟨K ++ L, hrest_act, by rw [hrest_sign]; exact hs, by omega⟩
  · obtain ⟨D, hDact, hDsign, hDlen⟩ := exists_cliffordCircuit_xGen_signFlip_length_le c
    refine ⟨D ++ (K ++ L), ?_, ?_, ?_⟩
    · rw [CliffordCircuit.act_append, hrest_act, hDact]
    · rw [CliffordCircuit.sign_append, hrest_sign, hs, hrest_act, hDsign]; norm_num
    · rw [List.length_append]; omega

/-- **Exact reduction to a standard `Z` generator costs `≤ 3·n + 4` gates.** The `Z`-basis mirror of
`exists_cliffordCircuit_reduceToXGen_length_le`: the diagonalising layer costs `≤ 2·n`
(`…diagZ_length_le`), CNOT clear `≤ n` (`…cnotClear_toSingleZ_length_le`) and sign gadget `≤ 4`
(`…zGen_signFlip_length_le`), so `≤ 3·n + 4` gates. -/
theorem exists_cliffordCircuit_reduceToZGen_length_le (a : Fin n → Fin 4) (c : Fin n)
    (hc : a c ≠ 0) :
    ∃ C : CliffordCircuit n,
      CliffordCircuit.act C a = zGenPauli c ∧ CliffordCircuit.sign C a = 1 ∧
        C.length ≤ 3 * n + 4 := by
  obtain ⟨f, hf, hLlen⟩ := exists_singleQubitLayer_act_diagZ_length_le a
  have ha'c : CliffordCircuit.act (CliffordCircuit.singleQubitLayer f) a c = 3 := by
    rw [hf c, ite_eq_right hc]
  have ha'Z : ∀ k, CliffordCircuit.act (CliffordCircuit.singleQubitLayer f) a k = 0 ∨
      CliffordCircuit.act (CliffordCircuit.singleQubitLayer f) a k = 3 := by
    intro k; rw [hf k]; split
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨K, hKact, hKsign, hKlen⟩ :=
    exists_cliffordCircuit_cnotClear_toSingleZ_length_le
      (CliffordCircuit.act (CliffordCircuit.singleQubitLayer f) a) c ha'c ha'Z
  set L := CliffordCircuit.singleQubitLayer f with hLdef
  have hrest_act : CliffordCircuit.act (K ++ L) a = zGenPauli c := by
    rw [CliffordCircuit.act_append]; exact hKact
  have hrest_sign : CliffordCircuit.sign (K ++ L) a = CliffordCircuit.sign L a := by
    rw [CliffordCircuit.sign_append, hKsign, mul_one]
  have hrest_len : (K ++ L).length ≤ 3 * n := by
    rw [List.length_append]; omega
  rcases CliffordCircuit.sign_eq_one_or_neg_one L a with hs | hs
  · exact ⟨K ++ L, hrest_act, by rw [hrest_sign]; exact hs, by omega⟩
  · obtain ⟨D, hDact, hDsign, hDlen⟩ := exists_cliffordCircuit_zGen_signFlip_length_le c
    refine ⟨D ++ (K ++ L), ?_, ?_, ?_⟩
    · rw [CliffordCircuit.act_append, hrest_act, hDact]
    · rw [CliffordCircuit.sign_append, hrest_sign, hs, hrest_act, hDsign]; norm_num
    · rw [List.length_append]; omega

/-! ### The symplectic first move of the pair reduction costs `O(n)` gates -/

/-- **The symplectic first move of the pair reduction costs `≤ 2·n + 2` gates.** The
length-annotated companion of `exists_cliffordCircuit_reduceFirstOfPair`: for an anticommuting pair
`p, q`, the
reducing circuit `C` is exactly an `exists_cliffordCircuit_reduceToXGen_length_le` applied to `p`
(reducing `p` to `X_c`), so it inherits that reduction's `≤ 2·n + 2` gate count. The pivot wire `c`,
the exact reduction of `p`, and the `Y`/`Z` factor of `act C q` on `c` are established exactly as in
the base lemma (via the symplectic invariance `act_pauliAnticommCount_even_iff`). This is the first
move whose `O(n)` cost feeds the per-level overhead of the Figure 10.9 recurrence. -/
theorem exists_cliffordCircuit_reduceFirstOfPair_length_le (p q : Fin n → Fin 4)
    (hpq : Odd (pauliAnticommCount p q)) :
    ∃ (C : CliffordCircuit n) (c : Fin n),
      CliffordCircuit.act C p = xGenPauli c ∧ CliffordCircuit.sign C p = 1 ∧
        (CliffordCircuit.act C q c = 2 ∨ CliffordCircuit.act C q c = 3) ∧
          C.length ≤ 2 * n + 2 := by
  obtain ⟨c, hc⟩ := exists_support_of_odd_pauliAnticommCount p q hpq
  obtain ⟨C, hCact, hCsign, hClen⟩ := exists_cliffordCircuit_reduceToXGen_length_le p c hc
  refine ⟨C, c, hCact, hCsign, ?_, hClen⟩
  have hpreserve : Odd (pauliAnticommCount (C.act p) (C.act q)) := by
    rw [← Nat.not_even_iff_odd] at hpq ⊢
    rwa [CliffordCircuit.act_pauliAnticommCount_even_iff]
  rw [← odd_pauliAnticommCount_xGenPauli_iff, pauliAnticommCount_symm, ← hCact]
  exact hpreserve

end AxQM.Concrete

end
