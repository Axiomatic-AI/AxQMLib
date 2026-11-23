/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliNormalizerGateCountGadgets
import AxQM.Concrete.PauliNormalizerGateCountReduce

/-!
# Concrete: the `O(n)` gate-count of the anticommuting-pair reduction (N&C Theorem 10.6)

*(Theorem 10.6, N&C §10.5.2, p. 461.)*

Nielsen & Chuang **Theorem 10.6** asserts that a Pauli normalizer `U ∈ N(Gₙ)` may be composed, up to
a global phase, from **`O(n²)`** Hadamard/phase/CNOT gates. The structural converse
(`isPauliNormalizer_eq_smul_cliffordCircuit`) gives the circuit; the quantitative part is the gate
count, bounded through the Figure 10.9 synthesis. This file bounds the length of the first-qubit
reduction `exists_cliffordCircuit_reducePair` — the move that carries a normalizer's
anticommuting generator image pair `(U X₁ U†, U Z₁ U†)` to the canonical `(X_c, Z_c)` on a common
pivot wire — by `O(n)` gates. It composes three sub-moves, each `O(n)`:

* the symplectic first move (reduce `p` to `X_c` via `reduceToXGen`, `≤ 2·n + 2` — reused
  inline here);
* the `X_c`-preserving `Z`-reduction of the partner image (`reduceSecondFixingX`: a diagonalising
  single-qubit layer, `≤ 3·n`, then a reverse CNOT fan, `≤ n`, so `≤ 4·n`);
* the two `±1` sign corrections (`fixPairSigns`: at most two constant-length `onWire` gadgets, `≤ 9`
  each, so `+ 18`).

So the pair reduction costs `≤ (2·n + 2) + 4·n + 18 = 6·n + 20` gates — the per-pair `O(n)` atom of
the first-wire-reduction bound `|B| ≤ O(n)` the Figure 10.9 induction needs.


Contents:

* `exists_cnotFanInto_toSingleZ_fixingX_length_le` (`≤ n`) — the reverse CNOT-clearing fan that
  collapses an all-`Z` string to `Z_c` while fixing `X_c` costs at most one CNOT per support wire.
* `exists_cliffordCircuit_reduceSecondFixingX_length_le` (`≤ 4·n`) — the `X_c`-preserving
  `Z`-reduction of the partner image: a diagonalising layer (`≤ 3·n`, per-wire words `rotateToZ ≤ 2`
  and the pivot `rotateToZFixingX ≤ 3`) then the fan above (`≤ n`).
* `exists_cliffordCircuit_fixPairSigns_length_le` (`≤ input + 18`) — sign normalisation with at most
  two constant-length `onWire` sign gadgets (`≤ 9` each).
* `exists_cliffordCircuit_reducePair_length_le` (`≤ 6·n + 20`) — the
  first-qubit reduction of an anticommuting pair costs `O(n)` gates.
-/

open Matrix

noncomputable section

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The `X_c`-preserving reverse CNOT-clearing fan costs `O(n)` gates -/

/-- **The reverse CNOT-clearing fan collapsing an all-`Z` string to `Z_c` while fixing `X_c` costs
`≤ n` gates.** The length-annotated companion of `exists_cnotFanInto_toSingleZ_fixingX`
(the `X_c`-preserving strengthening of `exists_cliffordCircuit_cnotClear_toSingleZ`): the witness is
the reverse fan `cnotFanInto c ts` over the support `ts = {k | a k = 3, k ≠ c}`, which has at most
one gate per control (`length_cnotFanInto_le`, `≤ |ts|`), and `ts` is a `Finset.filter` of `Fin n`
so `|ts| ≤ n` (`card_filter_le`). The collapse and `X_c`-preservation are those of the original
(`act_cnotFanInto_collapse`, `act_cnotFanInto_xGenPauli`); signs are not tracked (they are corrected
by the pair reduction). -/
theorem exists_cnotFanInto_toSingleZ_fixingX_length_le (a : Fin n → Fin 4) (c : Fin n)
    (hc : a c = 3) (hZ : ∀ k, a k = 0 ∨ a k = 3) :
    ∃ C : CliffordCircuit n,
      CliffordCircuit.act C a = zGenPauli c ∧
        CliffordCircuit.act C (xGenPauli c) = xGenPauli c ∧ C.length ≤ n := by
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
  refine ⟨cnotFanInto c ts, ?_, act_cnotFanInto_xGenPauli c ts hcnotin,
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

/-! ### The `X_c`-preserving `Z`-reduction of the partner image costs `O(n)` gates -/

/-- **The `X_c`-preserving `Z`-reduction of a Pauli string costs `≤ 4·n` gates.** The
length-annotated companion of `exists_cliffordCircuit_reduceSecondFixingX`: for a string `q` with a
`Z` factor on wire `c` (`q c ∈ {Y, Z}`), a Clifford circuit `D` collapsing `q` to `Z_c` while fixing
`X_c` (index level), with `≤ 4·n` gates. The reducing circuit is `cnotFanInto ++ layer`, whose
`X_c`-preserving diagonalising layer costs `≤ 3·n` (each per-wire word is `rotateToZ ≤ 2`, except
the pivot's `rotateToZFixingX ≤ 3`, so `≤ n·3`; `length_singleQubitLayer_le`) and whose reverse CNOT
fan
costs `≤ n` (`exists_cnotFanInto_toSingleZ_fixingX_length_le`). The action/phase content is that of
the original (diagonalise-to-all-`Z`-fixing-`X_c`, then `X_c`-preserving CNOT collapse). -/
theorem exists_cliffordCircuit_reduceSecondFixingX_length_le (q : Fin n → Fin 4) (c : Fin n)
    (hq : q c = 2 ∨ q c = 3) :
    ∃ D : CliffordCircuit n,
      CliffordCircuit.act D q = zGenPauli c ∧
        CliffordCircuit.act D (xGenPauli c) = xGenPauli c ∧ D.length ≤ 4 * n := by
  set f : Fin n → CliffordCircuit 1 :=
    Function.update (fun k => CliffordCircuit.rotateToZ (q k)) c
      (CliffordCircuit.rotateToZFixingX (q c)) with hf
  set L := CliffordCircuit.singleQubitLayer f with hL
  -- the layer diagonalises `q` to an all-`Z` string with pivot `c`, fixing `X_c`
  have hLqc : CliffordCircuit.act L q c = 3 := by
    rw [hL, CliffordCircuit.singleQubitLayer_act, hf, Function.update_self]
    exact CliffordCircuit.rotateToZFixingX_act_self hq
  have hLqZ : ∀ k, CliffordCircuit.act L q k = 0 ∨ CliffordCircuit.act L q k = 3 := by
    intro k
    rw [hL, CliffordCircuit.singleQubitLayer_act, hf]
    by_cases hkc : k = c
    · rw [hkc, Function.update_self]
      exact Or.inr (CliffordCircuit.rotateToZFixingX_act_self hq)
    · simp only [Function.update_of_ne hkc, CliffordCircuit.rotateToZ_act]
      split
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hLx : CliffordCircuit.act L (xGenPauli c) = xGenPauli c := by
    funext k
    rw [hL, CliffordCircuit.singleQubitLayer_act, hf]
    by_cases hkc : k = c
    · rw [hkc, Function.update_self, xGenPauli_apply, ite_eq_left rfl]
      exact CliffordCircuit.rotateToZFixingX_act_one _
    · simp only [Function.update_of_ne hkc, xGenPauli_apply, ite_eq_right hkc]
      exact CliffordCircuit.rotateToZ_act_zero _
  -- the layer costs `≤ 3·n` gates: each per-wire word has `≤ 3` gates
  have hLlen : L.length ≤ 3 * n := by
    have hb : L.length ≤ n * 3 :=
      CliffordCircuit.length_singleQubitLayer_le f fun i => by
        by_cases hic : i = c
        · rw [hf, hic, Function.update_self]
          exact CliffordCircuit.length_rotateToZFixingX_le _
        · rw [hf, Function.update_of_ne hic]
          exact le_trans (CliffordCircuit.length_rotateToZ_le _) (by norm_num)
    omega
  -- collapse the all-`Z` image to `Z_c`, keeping `X_c` fixed, in `≤ n` gates
  obtain ⟨K, hKq, hKx, hKlen⟩ :=
    exists_cnotFanInto_toSingleZ_fixingX_length_le (CliffordCircuit.act L q) c hLqc hLqZ
  refine ⟨K ++ L, ?_, ?_, ?_⟩
  · rw [CliffordCircuit.act_append]; exact hKq
  · rw [CliffordCircuit.act_append, hLx]; exact hKx
  · rw [List.length_append]; omega

/-! ### Sign normalisation of a reduced pair is constant overhead -/

/-- **Normalising the signs of a reduced pair costs `≤ input + 18` gates.** The length-annotated
companion of `exists_cliffordCircuit_fixPairSigns`: given a Clifford circuit `E` already sending
`p ↦ X_c` and `q ↦ Z_c` at the index level, two single-wire `onWire` sign gadgets pin the two
independent residual `±1` phases to `+1`, each with `≤ 9` gates
(`exists_cliffordCircuit_onWire_act_sign_length_le`), so at most `18` gates are prepended. In every
branch (zero, one or two corrections) the total is `≤ E.length + 18`. -/
theorem exists_cliffordCircuit_fixPairSigns_length_le (E : CliffordCircuit n) (c : Fin n)
    {p q : Fin n → Fin 4} (hp : CliffordCircuit.act E p = xGenPauli c)
    (hq : CliffordCircuit.act E q = zGenPauli c) :
    ∃ E' : CliffordCircuit n, CliffordCircuit.act E' p = xGenPauli c ∧
      CliffordCircuit.sign E' p = 1 ∧ CliffordCircuit.act E' q = zGenPauli c ∧
        CliffordCircuit.sign E' q = 1 ∧ E'.length ≤ E.length + 18 := by
  -- correct `p`'s sign with an `X_c`-sign-flip gadget (fixing `Z_c`) if needed
  obtain ⟨E1, hE1p, hE1q, hE1ps, hE1qs, hE1len⟩ :
      ∃ E1 : CliffordCircuit n, CliffordCircuit.act E1 p = xGenPauli c ∧
        CliffordCircuit.act E1 q = zGenPauli c ∧
        CliffordCircuit.sign E1 p = 1 ∧ CliffordCircuit.sign E1 q = CliffordCircuit.sign E q ∧
        E1.length ≤ E.length + 9 := by
    rcases CliffordCircuit.sign_eq_one_or_neg_one E p with hs | hs
    · exact ⟨E, hp, hq, hs, rfl, by omega⟩
    · obtain ⟨A, hAx, hAxs, hAz, hAzs, -, hAlen⟩ :=
        exists_cliffordCircuit_onWire_act_sign_length_le c (aX := 1) (aZ := 3) (zX := -1) (zZ := 1)
          (by decide) (by decide) (by decide) (Or.inr rfl) (Or.inl rfl)
      refine ⟨A ++ E, ?_, ?_, ?_, ?_, ?_⟩
      · rw [CliffordCircuit.act_append, hp]; exact hAx
      · rw [CliffordCircuit.act_append, hq]; exact hAz
      · rw [CliffordCircuit.sign_append, hp, hs, hAxs]; norm_num
      · rw [CliffordCircuit.sign_append, hq, hAzs, mul_one]
      · rw [List.length_append]; omega
  -- correct `q`'s sign with a `Z_c`-sign-flip gadget (fixing `X_c`) if needed
  rcases CliffordCircuit.sign_eq_one_or_neg_one E1 q with hs | hs
  · exact ⟨E1, hE1p, hE1ps, hE1q, hs, by omega⟩
  · obtain ⟨B, hBx, hBxs, hBz, hBzs, -, hBlen⟩ :=
      exists_cliffordCircuit_onWire_act_sign_length_le c (aX := 1) (aZ := 3) (zX := 1) (zZ := -1)
        (by decide) (by decide) (by decide) (Or.inl rfl) (Or.inr rfl)
    refine ⟨B ++ E1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [CliffordCircuit.act_append, hE1p]; exact hBx
    · rw [CliffordCircuit.sign_append, hE1p, hE1ps, hBxs]; norm_num
    · rw [CliffordCircuit.act_append, hE1q]; exact hBz
    · rw [CliffordCircuit.sign_append, hE1q, hs, hBzs]; norm_num
    · rw [List.length_append]; omega

/-! ### The first-qubit reduction of an anticommuting pair costs `O(n)` gates -/

/-- **The first-qubit reduction of an anticommuting pair costs `≤ 6·n + 20` gates.** The
length-annotated companion of `exists_cliffordCircuit_reducePair` (N&C Exercise 10.40, first-qubit
reduction): for an anticommuting pair `p, q` (`Odd (pauliAnticommCount p q)`), a Clifford circuit
`E` and pivot wire `c` reducing the pair to the canonical generators exactly — `act E p =
xGenPauli c`,
`sign E p = 1`, `act E q = zGenPauli c`, `sign E q = 1` — with `E.length ≤ 6·n + 20`.

A three-move composition, each `O(n)`:

1. the symplectic first move — `p` is non-identity (an anticommuting partner), so it has a support
   wire `c`, and `exists_cliffordCircuit_reduceToXGen_length_le` reduces `p` to `X_c` with
   `≤ 2·n + 2` gates; the Clifford action is symplectic
   (`act_pauliAnticommCount_even_iff`), so the partner image `act C q` still anticommutes with `X_c`
   (`act C q c ∈ {Y, Z}`). (Reconstructed inline from `reduceToXGen_length_le`.)
2. the `X_c`-preserving `Z`-reduction `D` of `act C q`
   (`exists_cliffordCircuit_reduceSecondFixingX_length_le`, `≤ 4·n`), so `D ++ C` realises
   `p ↦ X_c`, `q ↦ Z_c` on the index level in `≤ 6·n + 2` gates;
3. `exists_cliffordCircuit_fixPairSigns_length_le` pins the two residual `±1` phases to `+1` with at
   most `18` further gates.

Total `≤ (2·n + 2) + 4·n + 18 = 6·n + 20`. This is the per-pair `O(n)` bound used once per induction
level of the first-wire reduction (`fixFirstPair`) in the `O(n²)` bound. -/
theorem exists_cliffordCircuit_reducePair_length_le (p q : Fin n → Fin 4)
    (hpq : Odd (pauliAnticommCount p q)) :
    ∃ (E : CliffordCircuit n) (c : Fin n),
      CliffordCircuit.act E p = xGenPauli c ∧ CliffordCircuit.sign E p = 1 ∧
        CliffordCircuit.act E q = zGenPauli c ∧ CliffordCircuit.sign E q = 1 ∧
        E.length ≤ 6 * n + 20 := by
  -- the symplectic first move, inlined: reduce `p` to `X_c` with `≤ 2·n + 2` gates
  obtain ⟨c, hc⟩ : ∃ c, p c ≠ 0 := by
    by_contra hall
    have hp0 : ∀ k, p k = 0 := fun k => by
      by_contra hk; exact hall ⟨k, hk⟩
    have hz : pauliAnticommCount p q = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hp0 k]
      simp [singlePauliAnticomm, pauliXBit, pauliZBit]
    rw [hz] at hpq
    exact absurd hpq (by decide)
  obtain ⟨C, hCp, hCsp, hClen⟩ := exists_cliffordCircuit_reduceToXGen_length_le p c hc
  have hCqc : CliffordCircuit.act C q c = 2 ∨ CliffordCircuit.act C q c = 3 := by
    have hpreserve : Odd (pauliAnticommCount (C.act p) (C.act q)) := by
      rw [← Nat.not_even_iff_odd] at hpq ⊢
      rwa [CliffordCircuit.act_pauliAnticommCount_even_iff]
    rw [← odd_pauliAnticommCount_xGenPauli_iff, pauliAnticommCount_symm, ← hCp]
    exact hpreserve
  -- the `X_c`-preserving `Z`-reduction of the partner image, `≤ 4·n` gates
  obtain ⟨D, hDq, hDx, hDlen⟩ :=
    exists_cliffordCircuit_reduceSecondFixingX_length_le (CliffordCircuit.act C q) c hCqc
  set E0 := D ++ C with hE0
  have hE0p : CliffordCircuit.act E0 p = xGenPauli c := by
    rw [hE0, CliffordCircuit.act_append, hCp]; exact hDx
  have hE0q : CliffordCircuit.act E0 q = zGenPauli c := by
    rw [hE0, CliffordCircuit.act_append]; exact hDq
  have hE0len : E0.length ≤ 6 * n + 2 := by
    rw [hE0, List.length_append]; omega
  -- pin the two residual ±1 phases to +1, `≤ 18` further gates
  obtain ⟨E, hEp, hEps, hEq, hEqs, hElen⟩ :=
    exists_cliffordCircuit_fixPairSigns_length_le E0 c hE0p hE0q
  exact ⟨E, c, hEp, hEps, hEq, hEqs, by omega⟩

end AxQM.Concrete

end
