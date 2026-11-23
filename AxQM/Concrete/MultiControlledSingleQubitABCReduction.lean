/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledSingleQubit
import AxQM.Concrete.ABCDecomposition

/-!
# Concrete: the controlled-`ABC` reduction of a *subset*-controlled single-qubit gate (N&C §4.3)

(Nielsen & Chuang §4.3, p. 176–182 — Corollary 4.2, for an arbitrary control set.)

The Barenco tight-register recursion (`Concrete/MultiControlledSingleQubitBarenco.lean`) factors
`Cⁿ(X)` into *subset*-controlled single-qubit gates `mcCtrlSingleQubit enc S j Ũ` — a `2 × 2` gate
`Ũ` on wire `j`, controlled on the wires in `S`. To bottom the recursion out over
`H, S, CNOT, Toffoli`, each such factor must in turn be reduced to uncontrolled single-qubit gates
and multiply-controlled `NOT`s. This file supplies that reduction — the subset-controlled
generalisation of the all-`1`-controlled `ctrlSingleQubit_one_eq_abc` /
`exists_abc_reduction_ctrlSingleQubit_one` (`Concrete/ControlledSingleQubitABCReduction.lean`, its
`S = univ \ {j}` case) — together with the *peel* that discharges the ABC phase residual.

## The ABC reduction

* `AxQM.Concrete.mcCtrlSingleQubit_eq_abc` — **the controlled-`ABC` identity** (N&C
  Corollary 4.2, subset-controlled): for any `2 × 2` matrices `A, B, C, X` with `A B C = I`,
  `mcCtrlSingleQubit enc S j (A X B X C)
      = singleQubitOnWire enc j A · N · singleQubitOnWire enc j B · N · singleQubitOnWire enc j C`,
  where `N = mcCtrlSingleQubit enc S j X` is the subset-controlled gate with block `X`. On the
  `S`-controlled fibres both `N`s fire (as `X`), so wire `j` sees `A X B X C`; off them both `N`s
  are the identity, so wire `j` sees `A B C = I` and the gate is trivial — the mechanism by which
  two subset-controlled-`NOT`s and three *uncontrolled* single-qubit gates realise a controlled
  gate.
* `AxQM.Concrete.exists_abc_reduction_mcCtrlSingleQubit` — **the reduction of a general
  subset-controlled single-qubit gate**: for any `Ũ ∈ U(2)`, the ABC decomposition
  (`exists_abc_decomposition`, `Ũ = e^{iα} A X B X C`, `A B C = I`) gives
  `mcCtrlSingleQubit enc S j Ũ = mcCtrlSingleQubit enc S j (e^{iα} • 1) ·
  (singleQubitOnWire enc j A · N · singleQubitOnWire enc j B · N · singleQubitOnWire enc j C)` with
  `N = mcCtrlSingleQubit enc S j pauliX`. This exhibits the gate as three uncontrolled single-qubit
  gates on wire `j`, two subset-controlled-`NOT`s, and one subset-controlled *phase* gate.

## The phase-residual peel

The residual `mcCtrlSingleQubit enc S j (e^{iα} • 1)` applies the global phase `e^{iα}` to the
target fibre exactly when every control in `S` is set — a phase applied to the whole `S`-controlled
subspace, *independent of the target value*. N&C realises it by peeling one control: the same
diagonal gate is a controlled **phase-block** gate `diag(1, e^{iα})` on one of the former control
wires, with one fewer control.

* `AxQM.Concrete.phaseGate z` — the `2 × 2` phase-block gate `diag(1, z)`; unitary for
  `z̄ z = 1` (`phaseGate_mem_unitaryGroup`), so `phaseGate (e^{iα})` is a legitimate single-qubit
  gate.
* `AxQM.Concrete.mcCtrlSingleQubit_phase_peel` — **the phase peel**: for `c ∈ S`, `j ∉ S`,
  `mcCtrlSingleQubit enc S j (z • 1) = mcCtrlSingleQubit enc (S.erase c) c (phaseGate z)`. The
  target moves from `j` to the former control wire `c`, and the control set shrinks by one.
  Iterating bottoms the phase out at the uncontrolled `singleQubitOnWire enc c (phaseGate z)` (via
  `mcCtrlSingleQubit_empty`), and the phase-block gate itself, being a single-qubit unitary,
  recurses through the ABC reduction above — so the ABC reduction and this peel together are the
  "recurse into smaller multiply-controlled gates" step of the §4.3 reduction. Both sides are proved
  equal to the common diagonal matrix `diag(fun i => if all of S set then z else 1)`
  (`mcCtrlSingleQubit_smul_one_eq_diagonal`, `mcCtrlSingleQubit_phaseGate_eq_diagonal`).

## Use

These results are reused by the tight-register `Cⁿ(X)` reduction of Exercise 4.43
(`AxQM/NC/Ch4/Exercise4_43.lean`).
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- **The controlled-`ABC` identity for a subset-controlled single-qubit gate** (Nielsen & Chuang,
Corollary 4.2, for an arbitrary control set `S`). For any `2 × 2` matrices `A, B, C, X` with
`A B C = I`, `mcCtrlSingleQubit enc S j (A X B X C) = singleQubitOnWire enc j A · N ·
singleQubitOnWire enc j B · N · singleQubitOnWire enc j C`, where `N = mcCtrlSingleQubit enc S j X`.
On the `S`-controlled fibres both `N`s fire (as `X`), so wire `j` sees `A X B X C`; off them both
`N`s are the identity, so wire `j` sees `A B C = I` and nothing happens. The all-`1`-controlled
`ctrlSingleQubit_one_eq_abc` is the `S = univ \ {j}` case. -/
theorem mcCtrlSingleQubit_eq_abc (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m)) (j : Fin m)
    (A B C X : Matrix (Fin 2) (Fin 2) ℂ) (hABC : A * B * C = 1) :
    mcCtrlSingleQubit enc S j (A * X * B * X * C)
      = singleQubitOnWire enc j A * mcCtrlSingleQubit enc S j X
        * singleQubitOnWire enc j B * mcCtrlSingleQubit enc S j X
        * singleQubitOnWire enc j C := by
  simp only [singleQubitOnWire_eq_wireGate, mcCtrlSingleQubit, wireGate_mul]
  congr 1
  funext y
  by_cases h : ∀ k ∈ S, y k = 1
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h, mul_one, hABC]

/-- **The reduction of a general subset-controlled single-qubit gate** (Nielsen & Chuang §4.3). For
any single-qubit unitary `Ũ`, the ABC decomposition (`exists_abc_decomposition`) yields real phase
`α` and unitaries `A, B, C` with `A B C = I` such that `mcCtrlSingleQubit enc S j Ũ =
mcCtrlSingleQubit enc S j (e^{iα} • 1) · (singleQubitOnWire enc j A · N · singleQubitOnWire enc j B
· N · singleQubitOnWire enc j C)`, with `N = mcCtrlSingleQubit enc S j pauliX`. This exhibits the
gate as three uncontrolled single-qubit gates on wire `j`, two subset-controlled-`NOT`s, and one
subset-controlled phase gate — the §4.3 reduction step the Barenco recursion factors feed into. -/
theorem exists_abc_reduction_mcCtrlSingleQubit (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m))
    (j : Fin m) {Ũ : Matrix (Fin 2) (Fin 2) ℂ} (hŨ : Ũ ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (α : ℝ) (A B C : Matrix (Fin 2) (Fin 2) ℂ),
      A ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ B ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        C ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        mcCtrlSingleQubit enc S j Ũ
          = mcCtrlSingleQubit enc S j (Complex.exp ((α : ℂ) * Complex.I) • 1)
            * (singleQubitOnWire enc j A * mcCtrlSingleQubit enc S j pauliX
              * singleQubitOnWire enc j B * mcCtrlSingleQubit enc S j pauliX
              * singleQubitOnWire enc j C) := by
  obtain ⟨α, A, B, C, hA, hB, hC, hABC, hU⟩ := exists_abc_decomposition Ũ hŨ
  refine ⟨α, A, B, C, hA, hB, hC, ?_⟩
  rw [hU, ← smul_one_mul, ← mcCtrlSingleQubit_mul,
    mcCtrlSingleQubit_eq_abc enc S j A B C pauliX hABC]

/-- **The `2 × 2` phase-block gate** `diag(1, z)`. For `z = e^{iα}` (`z̄ z = 1`) it is a unitary
single-qubit gate (`phaseGate_mem_unitaryGroup`); it is the block the subset-controlled *phase*
residual of the ABC reduction peels one control off into (`mcCtrlSingleQubit_phase_peel`). -/
def phaseGate (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, z]

/-- The phase-block gate as a diagonal matrix, `diag(1, z) = Matrix.diagonal ![1, z]`. -/
theorem phaseGate_eq_diagonal (z : ℂ) : phaseGate z = Matrix.diagonal ![1, z] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [phaseGate, Matrix.diagonal]

/-- The diagonal entries of the phase-block gate: `diag(1, z) 0 0 = 1`, `diag(1, z) 1 1 = z`. -/
theorem phaseGate_apply_diag (z : ℂ) (a : Fin 2) : phaseGate z a a = if a = 0 then 1 else z := by
  fin_cases a <;> simp [phaseGate]

/-- The phase-block gate is diagonal: off-diagonal entries vanish. -/
theorem phaseGate_apply_of_ne (z : ℂ) {a b : Fin 2} (h : a ≠ b) : phaseGate z a b = 0 := by
  fin_cases a <;> fin_cases b <;> simp_all [phaseGate]

/-- **The phase-block gate is unitary when `z̄ z = 1`** (e.g. `z = e^{iα}`): `(diag(1, z))ᴴ
diag(1, z) = diag(1, z̄ z) = I`. -/
theorem phaseGate_mem_unitaryGroup {z : ℂ} (hz : star z * z = 1) :
    phaseGate z ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, phaseGate_eq_diagonal,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  fin_cases a
  · simp
  · simpa using hz

/-- **The subset-controlled global-phase gate is diagonal.** `mcCtrlSingleQubit enc S j (z • 1)`
(with `j ∉ S`) multiplies `|enc x⟩` by `z` exactly when every control in `S` is set — the diagonal
matrix `diag(fun i => if all of S set then z else 1)`, independent of the target value at `j`. The
`w = fun _ => z` case of the general diagonal-block lemma `mcCtrlSingleQubit_diagonal`, via
`Matrix.smul_one_eq_diagonal` (`z • 1 = diagonal (fun _ => z)`). -/
theorem mcCtrlSingleQubit_smul_one_eq_diagonal (enc : (Fin m → Fin 2) ≃ Fin d)
    {S : Finset (Fin m)} {j : Fin m} (hj : j ∉ S) (z : ℂ) :
    mcCtrlSingleQubit enc S j (z • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = Matrix.diagonal (fun i => if ∀ k ∈ S, enc.symm i k = 1 then z else 1) := by
  rw [Matrix.smul_one_eq_diagonal, mcCtrlSingleQubit_diagonal enc hj]

/-- **The subset-controlled phase-block gate is the same diagonal.** For `c ∈ S`,
`mcCtrlSingleQubit enc (S.erase c) c (phaseGate z)` multiplies `|enc x⟩` by `z` exactly when wire
`c` and every control in `S.erase c` are set — i.e. when every control in `S` is set (`c ∈ S`) —
the same `diag(fun i => if all of S set then z else 1)` as
`mcCtrlSingleQubit_smul_one_eq_diagonal`. -/
theorem mcCtrlSingleQubit_phaseGate_eq_diagonal (enc : (Fin m → Fin 2) ≃ Fin d)
    {S : Finset (Fin m)} {c : Fin m} (hc : c ∈ S) (z : ℂ) :
    mcCtrlSingleQubit enc (S.erase c) c (phaseGate z)
      = Matrix.diagonal (fun i => if ∀ k ∈ S, enc.symm i k = 1 then z else 1) := by
  have hsplit : ∀ i : Fin d, (∀ k ∈ S, enc.symm i k = 1)
      ↔ (enc.symm i c = 1 ∧ ∀ k ∈ S.erase c, enc.symm i k = 1) := fun i =>
    ⟨fun h => ⟨h c hc, fun k hk => h k (Finset.mem_of_mem_erase hk)⟩,
      fun ⟨hc1, h⟩ k hk => by
        rcases eq_or_ne k c with rfl | hkc
        · exact hc1
        · exact h k (Finset.mem_erase.mpr ⟨hkc, hk⟩)⟩
  ext i i'
  rw [mcCtrlSingleQubit, wireGate_apply]
  simp only [Matrix.diagonal_apply, ctrl_update_iff (Finset.notMem_erase c S)]
  by_cases hii : i = i'
  · subst hii
    rw [ite_eq_left rfl, ite_eq_left (fun _ _ => rfl)]
    by_cases hall : ∀ k ∈ S, enc.symm i k = 1
    · rw [ite_eq_left hall, ite_eq_left (fun k hk => hall k (Finset.mem_of_mem_erase hk)),
        hall c hc, phaseGate_apply_diag, ite_eq_right (by decide)]
    · rw [ite_eq_right hall]
      by_cases he : ∀ k ∈ S.erase c, enc.symm i k = 1
      · have hc0 : enc.symm i c = 0 := by
          rcases (by omega : enc.symm i c = 0 ∨ enc.symm i c = 1) with h0 | h1
          · exact h0
          · exact absurd ((hsplit i).mpr ⟨h1, he⟩) hall
        rw [ite_eq_left he, hc0, phaseGate_apply_diag, ite_eq_left rfl]
      · rw [ite_eq_right he, Matrix.one_apply_eq]
  · rw [ite_eq_right hii]
    by_cases hoff : ∀ k, k ≠ c → enc.symm i k = enc.symm i' k
    · rw [ite_eq_left hoff]
      have hne : enc.symm i c ≠ enc.symm i' c := enc_symm_ne_of_off enc hii hoff
      split_ifs with h
      · rw [phaseGate_apply_of_ne z hne]
      · rw [Matrix.one_apply_ne hne]
    · rw [ite_eq_right hoff]

/-- **The phase peel** (Nielsen & Chuang §4.3): the subset-controlled global-phase residual of the
ABC reduction is a controlled *phase-block* gate on **one fewer control**. For `c ∈ S`, `j ∉ S`,
`mcCtrlSingleQubit enc S j (z • 1) = mcCtrlSingleQubit enc (S.erase c) c (phaseGate z)`: the target
moves from `j` to the former control wire `c`, and the control set shrinks by one. Iterating bottoms
the phase out at the uncontrolled `singleQubitOnWire enc c (phaseGate z)` (via
`mcCtrlSingleQubit_empty`), and the phase-block gate, being a single-qubit unitary, recurses through
`exists_abc_reduction_mcCtrlSingleQubit` — so the ABC reduction and this peel are the "recurse into
smaller multiply-controlled gates" step of the §4.3 reduction. Proved by writing both sides as the
common diagonal matrix. -/
theorem mcCtrlSingleQubit_phase_peel (enc : (Fin m → Fin 2) ≃ Fin d) {S : Finset (Fin m)}
    {c j : Fin m} (hc : c ∈ S) (hj : j ∉ S) (z : ℂ) :
    mcCtrlSingleQubit enc S j (z • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = mcCtrlSingleQubit enc (S.erase c) c (phaseGate z) := by
  rw [mcCtrlSingleQubit_smul_one_eq_diagonal enc hj,
    mcCtrlSingleQubit_phaseGate_eq_diagonal enc hc]

end AxQM.Concrete
