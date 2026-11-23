/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliNormalizerGateCountFirstPair

/-!
# Concrete: the `O(n²)` gate-count headline of the normalizer synthesis (N&C Theorem 10.6 /
Exercise 10.40, Fig 10.9)

*(Supporting material for Theorem 10.6 and Exercise 10.40, N&C
§10.5.2, pp. 461–462.)*

Nielsen & Chuang **Theorem 10.6** (and its worked proof, **Exercise 10.40**) asserts that a Pauli
normalizer `U ∈ N(Gₙ)` may be composed, up to a global phase, from **`O(n²)`** Hadamard/phase/CNOT
gates. The structural *existence* content — that H/S/CNOT generate `N(Gₙ)` — is
`isPauliNormalizer_eq_smul_cliffordCircuit` (`PauliNormalizerInduction.lean`), which gives a
Clifford circuit `C` with `U = c • C.toMatrix` (`‖c‖ = 1`) but **no** bound on `C.length`. This file
supplies the missing **quantitative** clause: the *same* Figure 10.9 synthesis, re-run with a
length-tracking invariant, produces a circuit of length `≤ 9·n² + 105·n`.

## The recurrence

Threading the per-move `O(n)` bounds of the gate-count cascade
(`PauliNormalizerGateCount*.lean`) through the two structural steps of the induction:

* **First-wire reduction** (`exists_cliffordCircuit_fixFirstPair_length_le`, in
  `PauliNormalizerGateCountFirstPair.lean`). The circuit `B` that brings `U` to a normalizer fixing
  `X₀, Z₀` is `G ++ (swapWires c 0 ++ E)` with `E` the anticommuting-pair reduction
  (`≤ 6·(n+1)+20`), a wire swap (`≤ 3`) and a single-wire sign gadget `G` (`≤ 9`), so
  `|B| ≤ 6·(n+1) + 32` — linear in the wire count.
* **Inductive step.** At level `n + 1` the synthesised circuit is `inverse B ++ C'.relabel succ`,
  where `C'` is the sub-register circuit from the inductive hypothesis. By
  `length_inverse_append_relabel_le` this costs `≤ 3·|B| + |C'|`. With `|B| ≤ 6·(n+1) + 32` and the
  inductive bound `|C'| ≤ 9·n² + 105·n`, the recurrence is
  `L(n+1) ≤ 3·(6·(n+1) + 32) + (9·n² + 105·n) = 9·(n+1)² + 105·(n+1)`,
  an *equality* in the arithmetic, so the quadratic closed form
  `L(n) ≤ 9·n² + 105·n` (`= O(n²)`) propagates exactly. The base `L(0) = 0` is the empty circuit.

`9·n² + 105·n` is a concrete quadratic bound; it is manifestly `O(n²)`, matching the textbook claim.

## Relation to the existence statement

`isPauliNormalizer_eq_smul_cliffordCircuit` is an `∃`-statement, so its witness circuit is opaque: a
length bound cannot be recovered *post hoc*. The length-tracking statement is therefore proved as a
**companion** — the existence proof is repeated and
augmented with the length conjunct. The action / phase / normalizer content is unchanged;
only the `List.length` arithmetic is new. The per-level `O(n)` first-wire atom
(`exists_cliffordCircuit_fixFirstPair_length_le`) is the analogous companion of
`exists_cliffordCircuit_fixFirstPair`; it is proved separately
in `AxQM/Concrete/PauliNormalizerGateCountFirstPair.lean`.

## The `O(n²)` headline and the qualitative characterization

`isPauliNormalizer_eq_smul_cliffordCircuit_bigO` restates the bound in the textbook `O(n²)` form: a
*single universal* constant `K` (here `114`) with `C.length ≤ K·n²` for every `n` and every
`n`-qubit normalizer — the constant is uniform in `n` (a per-`n` `∃ K` would be vacuous), so this is
the faithful reading of "composed from `O(n²)` gates". Immediate from the polynomial bound via
`9·n² + 105·n ≤ 114·n²`.

With both inclusions available — the synthesis (converse) and the easy direction
(`cliffordCircuit_isPauliNormalizer`, every Clifford circuit is a normalizer) —
`isPauliNormalizer_iff_eq_smul_cliffordCircuit` records the biconditional
`IsPauliNormalizer U ↔ ∃ C c, ‖c‖ = 1 ∧ U = c • C.toMatrix`: the normalizer `N(Gₙ)` is *exactly*
the Clifford circuits up to a global phase. The reverse implication uses `IsPauliNormalizer.smul`
— a unit global phase times a normalizer is again a normalizer (`|c|² = 1` cancels in the
conjugation, and `c • V` stays unitary).

-/

open Matrix

noncomputable section

namespace AxQM.Concrete

/-- **Nielsen & Chuang, Theorem 10.6 (converse), with the `O(n²)` gate count.** Every `n`-qubit
Pauli normalizer `U` equals a global phase times a Clifford (`H`/`S`/`CNOT`) circuit `C` of length
**at most `9·n² + 105·n`**: `∃ C c, ‖c‖ = 1 ∧ U = c • C.toMatrix ∧ C.length ≤ 9·n² + 105·n`. This is
the length-tracking companion of `isPauliNormalizer_eq_smul_cliffordCircuit`, and completes the
quantitative clause of Exercise 10.40 (parts 2–3): the concrete quadratic bound is `O(n²)`, exactly
the textbook count. Proved by `Nat.rec` on the wire count; the base `n = 0` is the empty circuit
(`0 ≤ 0`), and the step threads `exists_cliffordCircuit_fixFirstPair_length_le`
(`|B| ≤ 6·(n+1) + 32`) and `length_inverse_append_relabel_le`
(`|inverse B ++ relabel C'| ≤ 3·|B| + |C'|`) into the exact
recurrence `L(n+1) ≤ 3·(6·(n+1)+32) + L(n) = 9·(n+1)² + 105·(n+1)`. -/
theorem isPauliNormalizer_eq_smul_cliffordCircuit_length_le {n : ℕ}
    {U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ} (hU : IsPauliNormalizer U) :
    ∃ (C : CliffordCircuit n) (c : ℂ),
      ‖c‖ = 1 ∧ U = c • CliffordCircuit.toMatrix C ∧ C.length ≤ 9 * n ^ 2 + 105 * n := by
  induction n with
  | zero =>
      -- `Fin 0 → Fin 2` is a singleton: `U` is a `1×1` unitary, the empty circuit's matrix is `1`.
      refine ⟨[], U default default, ?_, ?_, ?_⟩
      · have hUU : Uᴴ * U = 1 := by
          have h := mem_unitaryGroup_iff'.mp hU.1
          rwa [star_eq_conjTranspose] at h
        have h1 := congrFun (congrFun hUU default) default
        simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h1
        rw [Finset.sum_eq_single default] at h1
        · rw [Matrix.conjTranspose_apply] at h1
          have hnn : ‖U default default‖ * ‖U default default‖ = 1 := by
            have := congrArg norm h1
            rwa [norm_mul, norm_star, norm_one] at this
          nlinarith [norm_nonneg (U default default), hnn]
        · intro b _ hb; exact absurd (Subsingleton.elim b default) hb
        · intro h; exact absurd (Finset.mem_univ default) h
      · funext i j
        rw [Subsingleton.elim i default, Subsingleton.elim j default]
        simp [CliffordCircuit.toMatrix, Matrix.one_apply_eq]
      · simp
  | succ n ih =>
      -- Step 1: reduce `U` to a normalizer `M = B U` fixing `X₀, Z₀`, with `|B| ≤ 6·(n+1) + 32`.
      obtain ⟨B, hM, hMX, hMZ, hBlen⟩ := hU.exists_cliffordCircuit_fixFirstPair_length_le
      set M := B.toMatrix * U with hMdef
      -- Step 2: the restriction `M' = firstWireRestrict M` is an `n`-qubit normalizer.
      have hM' : IsPauliNormalizer (firstWireRestrict M) :=
        firstWireRestrict_isPauliNormalizer hM hMX hMZ
      set M' := firstWireRestrict M with hM'def
      -- Step 3: apply the IH to `M'` (carrying its length bound `|C'| ≤ 9n²+105n`).
      obtain ⟨C', c', hc', hC'eq, hC'len⟩ := ih hM'
      -- Step 4: embed `C'` onto the last `n` wires.
      set B' := C'.relabel ⟨Fin.succ, Fin.succ_injective n⟩ with hB'def
      -- Step 5: `M` matches `B'` on every generator, so `M = c • B'.toMatrix`.
      have hM'conj : ∀ g : Fin n → Fin 4,
          M' * pauliString g * M'ᴴ
            = CliffordCircuit.sign C' g • pauliString (CliffordCircuit.act C' g) := by
        intro g
        rw [hC'eq, smul_conjTranspose_conj_cancel hc', CliffordCircuit.conj_pauliString]
      have hgenX : ∀ i, M * pauliString (xGenPauli i) * Mᴴ
          = CliffordCircuit.sign B' (xGenPauli i)
            • pauliString (CliffordCircuit.act B' (xGenPauli i)) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · rw [hMX, xGenPauli_zero_eq_cons, hB'def, CliffordCircuit.relabelSucc_act_cons,
            CliffordCircuit.relabelSucc_sign_cons, CliffordCircuit.act_const_zero,
            CliffordCircuit.sign_const_zero, one_smul, ← xGenPauli_zero_eq_cons]
        · intro j
          rw [xGenPauli_succ_eq_cons, hM.conj_pauliString_cons hMX hMZ, hM'conj,
            embedLast_smul, ← pauliString_cons_zero, hB'def,
            CliffordCircuit.relabelSucc_act_cons, CliffordCircuit.relabelSucc_sign_cons]
      have hgenZ : ∀ i, M * pauliString (zGenPauli i) * Mᴴ
          = CliffordCircuit.sign B' (zGenPauli i)
            • pauliString (CliffordCircuit.act B' (zGenPauli i)) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · rw [hMZ, zGenPauli_zero_eq_cons, hB'def, CliffordCircuit.relabelSucc_act_cons,
            CliffordCircuit.relabelSucc_sign_cons, CliffordCircuit.act_const_zero,
            CliffordCircuit.sign_const_zero, one_smul, ← zGenPauli_zero_eq_cons]
        · intro j
          rw [zGenPauli_succ_eq_cons, hM.conj_pauliString_cons hMX hMZ, hM'conj,
            embedLast_smul, ← pauliString_cons_zero, hB'def,
            CliffordCircuit.relabelSucc_act_cons, CliffordCircuit.relabelSucc_sign_cons]
      obtain ⟨c, hc, hMeq⟩ :=
        unitary_eq_smul_cliffordCircuit_of_conj_generators hM.1 B' hgenX hgenZ
      -- Step 6: left-cancel `B` with its inverse; the length is `|inverse B ++ B'| ≤ 3|B| + |C'|`.
      refine ⟨B.inverse ++ B', c, hc, ?_, ?_⟩
      · have hUeq : U = B.inverse.toMatrix * M := by
          rw [hMdef, ← Matrix.mul_assoc, CliffordCircuit.toMatrix_inverse_mul, Matrix.one_mul]
        rw [hUeq, hMeq, CliffordCircuit.toMatrix_append, Matrix.mul_smul]
      · -- `L(n+1) ≤ 3·|B| + |C'| ≤ 3·(6·(n+1)+32) + (9n²+105n) = 9·(n+1)² + 105·(n+1)`.
        rw [hB'def]
        have hrec := CliffordCircuit.length_inverse_append_relabel_le B C'
          ⟨Fin.succ, Fin.succ_injective n⟩
        nlinarith [hrec, hBlen, hC'len]

/-! ### A unit global phase times a normalizer is a normalizer -/

/-- **A unit global phase times a Pauli normalizer is a Pauli normalizer**: if `V ∈ N(Gₙ)` and
`‖c‖ = 1` then `c • V ∈ N(Gₙ)`. Unitarity is preserved (`(c • V)(c • V)† = |c|²·VV† = 1`), and the
global phase cancels in every conjugation (`(c • V) p (c • V)† = |c|²·V p V† = V p V†`), so `c • V`
sends the Pauli group into itself exactly as `V` does. -/
theorem IsPauliNormalizer.smul {n : ℕ} {V : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ}
    (hV : IsPauliNormalizer V) {c : ℂ} (hc : ‖c‖ = 1) : IsPauliNormalizer (c • V) := by
  have hcc : c * star c = 1 := by simp [RCLike.mul_conj, hc]
  refine ⟨?_, fun p => ?_⟩
  · -- `c • V` is unitary: `(c • V) * (c • V)⋆ = (c * star c) • (V * V⋆) = 1 • 1 = 1`.
    rw [Matrix.mem_unitaryGroup_iff, star_smul, smul_mul_smul_comm,
      Matrix.mem_unitaryGroup_iff.mp hV.1, hcc, one_smul]
  · -- The conjugation is `V`'s, since the unit phase cancels.
    rw [smul_conjTranspose_conj_cancel hc]; exact hV.2 p

/-! ### The `O(n²)` headline (Theorem 10.6 proper) -/

/-- **Nielsen & Chuang, Theorem 10.6.** There is a *universal* constant `K` (here `114`) such that
every `n`-qubit Pauli normalizer `U` is a global phase times a Clifford circuit of `O(n²)` gates:
`∃ K, ∀ n U, IsPauliNormalizer U → ∃ C c, ‖c‖ = 1 ∧ U = c • C.toMatrix ∧ C.length ≤ K · n²`. This is
the faithful formalisation of N&C's "up to a global phase `U` may be composed from `O(n²)`
Hadamard/phase/CNOT gates" — the constant `K` is uniform in `n`. It follows from the explicit
polynomial bound `isPauliNormalizer_eq_smul_cliffordCircuit_length_le` (`≤ 9·n² + 105·n`) via
`9·n² + 105·n ≤ 114·n²` (using `n ≤ n²`). -/
theorem isPauliNormalizer_eq_smul_cliffordCircuit_bigO :
    ∃ K : ℕ, ∀ (n : ℕ) (U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
      IsPauliNormalizer U →
        ∃ (C : CliffordCircuit n) (c : ℂ),
          ‖c‖ = 1 ∧ U = c • CliffordCircuit.toMatrix C ∧ C.length ≤ K * n ^ 2 := by
  refine ⟨114, fun n U hU => ?_⟩
  obtain ⟨C, c, hc, hUeq, hlen⟩ := isPauliNormalizer_eq_smul_cliffordCircuit_length_le hU
  have hnn : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
  exact ⟨C, c, hc, hUeq, hlen.trans (by nlinarith [hnn])⟩

/-! ### The qualitative characterization: `N(Gₙ)` is exactly the Clifford circuits up to phase -/

/-- **`N(Gₙ)` is exactly the Clifford circuits, up to a global phase.** A matrix `U` is a Pauli
normalizer iff it equals a unit global phase times a Clifford (`H`/`S`/`CNOT`) circuit:
`IsPauliNormalizer U ↔ ∃ C c, ‖c‖ = 1 ∧ U = c • C.toMatrix`. The forward direction is the inductive
synthesis (Theorem 10.6's converse, `isPauliNormalizer_eq_smul_cliffordCircuit`); the reverse is the
easy direction — every Clifford circuit is a normalizer (`cliffordCircuit_isPauliNormalizer`) and a
unit global phase preserves the normalizer property (`IsPauliNormalizer.smul`). This packages the
two inclusions of Theorem 10.6 as a single characterization of the normalizer group. -/
theorem isPauliNormalizer_iff_eq_smul_cliffordCircuit {n : ℕ}
    {U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ} :
    IsPauliNormalizer U ↔
      ∃ (C : CliffordCircuit n) (c : ℂ), ‖c‖ = 1 ∧ U = c • CliffordCircuit.toMatrix C := by
  refine ⟨isPauliNormalizer_eq_smul_cliffordCircuit, ?_⟩
  rintro ⟨C, c, hc, rfl⟩
  exact (cliffordCircuit_isPauliNormalizer C).smul hc

end AxQM.Concrete

end
