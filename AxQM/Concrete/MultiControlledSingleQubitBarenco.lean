/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.MultiControlledSingleQubit
import AxQM.Concrete.SqrtNot

/-!
# Concrete: the Barenco tight-register `Cⁿ(X)` recursion (N&C §4.3 / Barenco Lemma 7.5)

The §4.3 reduction of a controlled single-qubit gate to `H, S, CNOT, Toffoli` bottoms out at the
**tight-register** multiply-controlled `NOT` `Cⁿ(X)` — controls *all* `n` wires but the target, no
spare/work wire. By a parity obstruction (`Concrete/SqrtNot.lean`) that gate is **not** a product of
`Toffoli`/`CNOT`/`NOT` permutation gates; Nielsen & Chuang's *no-work-qubit* construction (Exercise
4.30 / Barenco *et al.* Lemma 7.5) resolves it with a genuine single-qubit gate `V = √X`
(`sqrtNot`). Writing `Cⁿ(X) = Cⁿ(V²)`, the construction peels one control:

`Cⁿ(V²) = C(V) · Cⁿ⁻¹(X) · C(V†) · Cⁿ⁻¹(X) · Cⁿ⁻¹(V)`,

where — distinguishing one control wire `c` from the other `n − 1` controls `S'` and the target `j`
— the factors are

* `C(V)`, `C(V†)` — single-qubit `V`, `V†` on wire `j`, controlled on the *one* wire `c`;
* `Cⁿ⁻¹(X)` (twice) — a `NOT` on wire `c`, controlled on the `n − 1` wires `S'`;
* `Cⁿ⁻¹(V)` — single-qubit `V` on wire `j`, controlled on the `n − 1` wires `S'`.

Each factor lives in the interpolating gate `mcCtrlSingleQubit`
(`Concrete/MultiControlledSingleQubit.lean`). This file proves the identity at the matrix level.

## The proof shape

All five factors are fibrewise (`wireGate`) — three on wire `j` (`C(V)`, `C(V†)`, `Cⁿ⁻¹(V)`) and two
on wire `c` (the `Cⁿ⁻¹(X)`s). The two `Cⁿ⁻¹(X) = P` factors are the *same* permutation gate,
sandwiching `C(V†)`; conjugating collapses that sandwich back to a **single wire-`j` gate**, so the
whole right-hand side becomes a product of three wire-`j` `wireGate`s, which multiply blockwise
(`wireGate_mul`). The identity then reduces to a per-off-`j`-pattern `2 × 2` check: on the four
cases of `(c-bit, all-S'-controls-set)` the block products are `1`, `V†V = 1`, `VV† = 1`, `V·V` —
the
Barenco truth table.

The conjugation collapse is `mcNotGate_conj_wireGate`: conjugating a wire-`j` `wireGate enc j f` by
`P = mcCtrlSingleQubit enc S' c pauliX` reindexes the block family by the classical `mcNot S' c`,
`P · wireGate enc j f · P = wireGate enc j (fun y => f (mcNot S' c y))`. It is proved from the
general **conjugation-is-reindexing** fact `mcNotGate_conj`
(`P · M · P = M.submatrix (flipCtrl …) (flipCtrl …)`, the analogue of
`singleQubitOnWire_swap_conj`), since `P` is the `0/1` permutation matrix of the involution
`flipCtrl` (the basis-index incarnation of `mcNot S' c`).

## Use

These results are reused by the tight-register `Cⁿ(X)` reduction of Exercise 4.43
(`AxQM/NC/Ch4/Exercise4_43.lean`).
-/

open Matrix

namespace AxQM.Concrete

variable {m d : ℕ}

/-- **The basis-index incarnation of the classical `mcNot S t`.** Relative to an encoding
`enc : (Fin m → Fin 2) ≃ Fin d`, `flipCtrl enc S t` sends `|enc x⟩` to `|enc (mcNot S t x)⟩`: it
flips bit `t` of the encoded bit-string exactly when every control wire in `S` is set. It is the
permutation the multiply-controlled `NOT` gate `mcCtrlSingleQubit enc S t pauliX` realises. -/
def flipCtrl (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m)) (t : Fin m) (i : Fin d) : Fin d :=
  enc (mcNot S t (enc.symm i))

/-- The bit-string underlying `flipCtrl enc S t i` is `mcNot S t (enc.symm i)`. -/
theorem enc_symm_flipCtrl (enc : (Fin m → Fin 2) ≃ Fin d) (S : Finset (Fin m)) (t : Fin m)
    (i : Fin d) : enc.symm (flipCtrl enc S t i) = mcNot S t (enc.symm i) := by
  rw [flipCtrl, Equiv.symm_apply_apply]

/-- **`flipCtrl enc S t` is an involution** (when the target `t` is not a control): applying
`mcNot S t` twice restores the bit-string (`mcNot_involutive`), hence the basis index. -/
theorem flipCtrl_involutive (enc : (Fin m → Fin 2) ≃ Fin d) {S : Finset (Fin m)} {t : Fin m}
    (ht : t ∉ S) : Function.Involutive (flipCtrl enc S t) := by
  intro i
  rw [flipCtrl, enc_symm_flipCtrl, mcNot_involutive S ht, Equiv.apply_symm_apply]

/-- **The multiply-controlled `NOT` gate is the `0/1` permutation matrix of `flipCtrl`.** Its entry
at `(i, a)` is `1` exactly when `a = flipCtrl enc S t i` (and `0` otherwise). This is the
column-indexed form of `mcCtrlSingleQubit_pauliX_eq_permGate`, the analogue of
`singleQubitOnWire_swap_apply`, and the engine behind the conjugation-is-reindexing lemma. -/
theorem mcNotGate_apply (enc : (Fin m → Fin 2) ≃ Fin d) {S : Finset (Fin m)} {t : Fin m}
    (ht : t ∉ S) (i a : Fin d) :
    mcCtrlSingleQubit enc S t pauliX i a = if a = flipCtrl enc S t i then 1 else 0 := by
  rw [mcCtrlSingleQubit_pauliX_eq_permGate enc S ht, permGate_apply, mcNotPerm_apply]
  exact if_congr (eq_comm.trans (flipCtrl_involutive enc ht).eq_iff) rfl rfl

/-- **Conjugation by the multiply-controlled `NOT` reindexes both matrix indices by `flipCtrl`.**
For any `d × d` matrix `M`, `P · M · P = M.submatrix (flipCtrl enc S t) (flipCtrl enc S t)`,
where
`P = mcCtrlSingleQubit enc S t pauliX`. Since `P` is the `0/1` permutation matrix
(`mcNotGate_apply`) of the involution `flipCtrl enc S t` (`flipCtrl_involutive`), sandwiching `M`
between two copies permutes rows and columns by that flip — the analogue of
`singleQubitOnWire_swap_conj`. -/
theorem mcNotGate_conj (enc : (Fin m → Fin 2) ≃ Fin d) {S : Finset (Fin m)} {t : Fin m}
    (ht : t ∉ S) (M : Matrix (Fin d) (Fin d) ℂ) :
    mcCtrlSingleQubit enc S t pauliX * M * mcCtrlSingleQubit enc S t pauliX
      = M.submatrix (flipCtrl enc S t) (flipCtrl enc S t) := by
  ext i i'
  rw [Matrix.submatrix_apply, Matrix.mul_apply]
  have hb0 : ∀ b ∈ (Finset.univ : Finset (Fin d)), b ≠ flipCtrl enc S t i' →
      (mcCtrlSingleQubit enc S t pauliX * M) i b
        * mcCtrlSingleQubit enc S t pauliX b i' = 0 := by
    intro b _ hb
    have hbne : ¬ (i' = flipCtrl enc S t b) := by
      intro h; exact hb (by rw [h, flipCtrl_involutive enc ht])
    rw [mcNotGate_apply enc ht, ite_eq_right hbne, mul_zero]
  rw [Finset.sum_eq_single (flipCtrl enc S t i') hb0 (fun h => absurd (Finset.mem_univ _) h),
    mcNotGate_apply enc ht, flipCtrl_involutive enc ht, ite_eq_left rfl, mul_one, Matrix.mul_apply]
  have ha0 : ∀ a ∈ (Finset.univ : Finset (Fin d)), a ≠ flipCtrl enc S t i →
      mcCtrlSingleQubit enc S t pauliX i a * M a (flipCtrl enc S t i') = 0 := by
    intro a _ ha
    rw [mcNotGate_apply enc ht, ite_eq_right ha, zero_mul]
  rw [Finset.sum_eq_single (flipCtrl enc S t i) ha0 (fun h => absurd (Finset.mem_univ _) h),
    mcNotGate_apply enc ht, ite_eq_left rfl, one_mul]

/-- Updating bit `j` of `mcNot S c x` (with `j ≠ c` and `j ∉ S`) commutes past the gate: bit `j` is
neither the target nor a control, so `(mcNot S c x)[j ↦ v] = mcNot S c (x[j ↦ v])`. -/
theorem update_mcNot_comm {S : Finset (Fin m)} {c j : Fin m} (hjc : j ≠ c) (hjS : j ∉ S)
    (x : Fin m → Fin 2) (v : Fin 2) :
    Function.update (mcNot S c x) j v = mcNot S c (Function.update x j v) := by
  rw [mcNot, mcNot, ctrlBit_update_of_notMem S hjS x v, Function.update_of_ne (Ne.symm hjc),
    Function.update_comm hjc]

/-- Two bit-strings agree off wire `j` iff their `mcNot S c`-images do (for `j ≠ c`, `j ∉ S`):
`mcNot S c` preserves each `j`-fibre. The `→` direction propagates agreement (`mcNot` reads only
the off-`j` control and `c` bits); the `←` direction is the same run through the involution. -/
theorem forall_ne_mcNot_iff {S : Finset (Fin m)} {c j : Fin m} (hc : c ∉ S) (hjc : j ≠ c)
    (hjS : j ∉ S) (x x' : Fin m → Fin 2) :
    (∀ l, l ≠ j → mcNot S c x l = mcNot S c x' l) ↔ (∀ l, l ≠ j → x l = x' l) := by
  have key : ∀ u v : Fin m → Fin 2, (∀ l, l ≠ j → u l = v l) →
      (∀ l, l ≠ j → mcNot S c u l = mcNot S c v l) := by
    intro u v h l hl
    rcases eq_or_ne l c with rfl | hlc
    · rw [mcNot_apply_self, mcNot_apply_self, h l hl]
      congr 1
      simp only [ctrlBit, forall_mem_eq_one_congr fun k hk => h k fun e => hjS (e ▸ hk)]
    · rw [mcNot_apply_of_ne S c u hlc, mcNot_apply_of_ne S c v hlc]
      exact h l hl
  refine ⟨fun h l hl => ?_, key x x'⟩
  have h2 := key _ _ h l hl
  rwa [mcNot_involutive S hc, mcNot_involutive S hc] at h2

/-- **Conjugating a wire-`j` gate by the multiply-controlled `NOT` reindexes its block by `mcNot`.**
For `c ∉ S`, `j ≠ c`, `j ∉ S`,
`P · wireGate enc j f · P = wireGate enc j (fun y => f (mcNot S c y))`, where
`P = mcCtrlSingleQubit enc S c pauliX`. Combined with the two extreme `Cⁿ⁻¹(X)` factors of the
Barenco recursion sandwiching `C(V†)`, this collapses the sandwich to a single wire-`j` gate. -/
theorem mcNotGate_conj_wireGate (enc : (Fin m → Fin 2) ≃ Fin d) {S : Finset (Fin m)} {c j : Fin m}
    (hc : c ∉ S) (hjc : j ≠ c) (hjS : j ∉ S)
    (f : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) :
    mcCtrlSingleQubit enc S c pauliX * wireGate enc j f * mcCtrlSingleQubit enc S c pauliX
      = wireGate enc j (fun y => f (mcNot S c y)) := by
  rw [mcNotGate_conj enc hc]
  ext i i'
  rw [Matrix.submatrix_apply, wireGate_apply, wireGate_apply, enc_symm_flipCtrl, enc_symm_flipCtrl,
    mcNot_apply_of_ne S c (enc.symm i) hjc, mcNot_apply_of_ne S c (enc.symm i') hjc,
    update_mcNot_comm hjc hjS (enc.symm i) 0]
  exact if_congr (forall_ne_mcNot_iff hc hjc hjS _ _) rfl rfl

/-- **The Barenco tight-register recursion** (N&C §4.3 / Barenco Lemma 7.5), at the matrix level.
For a distinguished control wire `c`, the remaining controls `S` (`c ∉ S`), and a target `j`
(`j ≠ c`, `j ∉ S`), and any single-qubit unitary `V`, the multiply-controlled gate `Cⁿ(V²)` on the
control set `insert c S` factors as
`C(V) · Cⁿ⁻¹(X) · C(V†) · Cⁿ⁻¹(X) · Cⁿ⁻¹(V)`:
one control is peeled by inserting two `NOT`s on wire `c` (controlled on `S`) around a
controlled-`V†`, plus a controlled-`V` on `c` and a controlled-`V` on the remaining controls `S`.
On the four cases of `(c-bit, all-of-S-set)` the wire-`j` block products are `1`, `V†V`, `VV†`, and
`V²`, matching `mcCtrlSingleQubit enc (insert c S) j (V * V)` since `V` is unitary. -/
theorem mcCtrlSingleQubit_barenco_recursion (enc : (Fin m → Fin 2) ≃ Fin d) {S : Finset (Fin m)}
    {c j : Fin m} (hc : c ∉ S) (hjc : j ≠ c) (hjS : j ∉ S) {V : Matrix (Fin 2) (Fin 2) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    mcCtrlSingleQubit enc (insert c S) j (V * V)
      = mcCtrlSingleQubit enc {c} j V * mcCtrlSingleQubit enc S c pauliX
        * mcCtrlSingleQubit enc {c} j Vᴴ * mcCtrlSingleQubit enc S c pauliX
        * mcCtrlSingleQubit enc S j V := by
  have hVdV : Vᴴ * V = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hV
  have hVVd : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hV
  -- collapse the `Cⁿ⁻¹(X) · C(V†) · Cⁿ⁻¹(X)` sandwich to a single wire-`j` gate
  have hconj : mcCtrlSingleQubit enc S c pauliX * mcCtrlSingleQubit enc {c} j Vᴴ
        * mcCtrlSingleQubit enc S c pauliX
      = wireGate enc j
          (fun y => if ∀ k ∈ ({c} : Finset (Fin m)), mcNot S c y k = 1 then Vᴴ else 1) :=
    mcNotGate_conj_wireGate enc hc hjc hjS _
  -- reassociate `A * B * C * B * E` to `A * (B * C * B) * E` and rewrite the sandwich
  rw [mul_assoc (mcCtrlSingleQubit enc {c} j V) (mcCtrlSingleQubit enc S c pauliX)
      (mcCtrlSingleQubit enc {c} j Vᴴ),
    mul_assoc (mcCtrlSingleQubit enc {c} j V) _ (mcCtrlSingleQubit enc S c pauliX), hconj,
    mcCtrlSingleQubit, mcCtrlSingleQubit, mcCtrlSingleQubit, wireGate_mul, wireGate_mul]
  congr 1
  funext y
  simp only [Finset.mem_singleton, Finset.mem_insert, forall_eq, forall_eq_or_imp,
    mcNot_apply_self]
  by_cases hcS : ∀ k ∈ S, y k = 1
  · have hcb : ctrlBit S y = 1 := ite_eq_left hcS
    rw [hcb]
    rcases (by omega : y c = 0 ∨ y c = 1) with hyc | hyc <;> rw [hyc]
    · rw [ite_eq_right (fun h => absurd h.1 (by decide)), ite_eq_right (by decide),
          ite_eq_left (by decide),
        ite_eq_left hcS, one_mul, hVdV]
    · rw [ite_eq_left ⟨rfl, hcS⟩, ite_eq_left rfl, ite_eq_right (by decide), ite_eq_left hcS,
          mul_one]
  · have hcb : ctrlBit S y = 0 := ite_eq_right hcS
    rw [hcb]
    rcases (by omega : y c = 0 ∨ y c = 1) with hyc | hyc <;> rw [hyc]
    · rw [ite_eq_right (fun h => absurd h.1 (by decide)), ite_eq_right (by decide),
          ite_eq_right (by decide),
        ite_eq_right hcS, mul_one, mul_one]
    · rw [ite_eq_right (fun h => hcS h.2), ite_eq_left rfl, ite_eq_left (by decide),
          ite_eq_right hcS, mul_one, hVVd]

/-- **The Barenco tight-register `Cⁿ(X)` recursion** — the `V = √X` specialisation of
`mcCtrlSingleQubit_barenco_recursion`. Since `sqrtNot² = X` (`sqrtNot_mul_self`) and `sqrtNot` is
unitary (`sqrtNot_mem_unitaryGroup`), the tight multiply-controlled `NOT` `Cⁿ(X)` on control set
`insert c S` factors as `C(√X) · Cⁿ⁻¹(X) · C(√X†) · Cⁿ⁻¹(X) · Cⁿ⁻¹(√X)`, peeling one control at the
cost of a genuine single-qubit `√X` gate — the no-work-qubit reduction of Exercise 4.30. Each
`Cⁿ⁻¹(X)`/`Cⁿ⁻¹(√X)` factor uses `n − 1` controls, so on the tight `n + 1`-wire register it now has
a spare wire, feeding the permutation-gate / controlled-`ABC` machinery. -/
theorem mcCtrlSingleQubit_pauliX_barenco_recursion (enc : (Fin m → Fin 2) ≃ Fin d)
    {S : Finset (Fin m)} {c j : Fin m} (hc : c ∉ S) (hjc : j ≠ c) (hjS : j ∉ S) :
    mcCtrlSingleQubit enc (insert c S) j pauliX
      = mcCtrlSingleQubit enc {c} j sqrtNot * mcCtrlSingleQubit enc S c pauliX
        * mcCtrlSingleQubit enc {c} j sqrtNotᴴ * mcCtrlSingleQubit enc S c pauliX
        * mcCtrlSingleQubit enc S j sqrtNot := by
  nth_rewrite 1 [← sqrtNot_mul_self]
  exact mcCtrlSingleQubit_barenco_recursion enc hc hjc hjS sqrtNot_mem_unitaryGroup

end AxQM.Concrete
