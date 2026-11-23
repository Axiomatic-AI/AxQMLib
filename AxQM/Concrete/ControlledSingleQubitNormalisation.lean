/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ControlledSingleQubitConjugation

/-!
# Concrete: control-pattern normalisation, folded to all-`1` controls (N&C §4.3)

(Nielsen & Chuang §4.3, p. 182 — the reduction of a controlled gate to single-qubit and `CNOT`
gates.)

`Concrete/ControlledSingleQubitConjugation.lean` supplied the **one-wire** step of Nielsen &
Chuang's §4.3 control-pattern normalisation: conjugating a controlled single-qubit gate
`ctrlSingleQubit enc j c Ũ` by the `X`-on-wire gate
`Wₖ = singleQubitOnWire enc k (Matrix.swap ℂ 0 1)` (for a control wire `k ≠ j`) flips the value the
control is conditioned on,
`Wₖ * ctrlSingleQubit enc j c Ũ * Wₖ = ctrlSingleQubit enc j (c[k ↦ ¬c k]) Ũ`
(`ctrlSingleQubit_conj_singleQubitOnWire_swap`). This file **folds that step over a list of wires**,
so an *arbitrary* control pattern is normalised to the all-`1` pattern by conjugation with a product
of `X`-on-wire gates — the state N&C's §4.3 reduction starts from before realising the resulting
`Cⁿ(Ũ)` over `H, S, CNOT, Toffoli`.

## The construction

Fix an encoding `enc : (Fin m → Fin 2) ≃ Fin d` of the `m`-bit strings as the `d = 2 ^ m` basis
indices.

* `AxQM.Concrete.wireFlipProd enc L` — the product `∏ₖ Wₖ` of `X`-on-wire gates over a list
  `L` of wires (head outermost). It is a product of uncontrolled single-qubit gates, hence unitary
  (`wireFlipProd_mem_unitaryGroup`), and `wireFlipProd enc L * wireFlipProd enc L.reverse = 1`
  (`wireFlipProd_mul_reverse`), so the reversed list gives its inverse (each `Wₖ` is an involution,
  telescoping from the inside out with no need for the `Wₖ` to commute).
* `AxQM.Concrete.flipPattern L c` — the control pattern `c` with every bit listed in `L`
  negated in turn. For a duplicate-free `L`, `flipPattern L c l = ¬c l` on `l ∈ L` and `c l`
  elsewhere (`flipPattern_apply_of_nodup`).
* `AxQM.Concrete.wireFlipProd_conj_ctrlSingleQubit` — **the fold**: for a list `L` of wires
  all distinct from the target `j`,
  `wireFlipProd enc L * ctrlSingleQubit enc j c Ũ * wireFlipProd enc L.reverse
      = ctrlSingleQubit enc j (flipPattern L c) Ũ`, iterating the one-wire step along `L`. No
  commutativity of the `Wₖ` is used — each induction step peels one `Wₖ` off each side and applies
  the single-wire lemma to the conjugated remainder.
* `AxQM.Concrete.exists_wireFlipProd_conj_ctrlSingleQubit_one` — **the headline**: for any
  control pattern `c`, there is a list `L` of control wires with
  `ctrlSingleQubit enc j c Ũ
      = wireFlipProd enc L.reverse * ctrlSingleQubit enc j 1 Ũ * wireFlipProd enc L`
  — every controlled single-qubit gate is, up to conjugation by a product of `X`-on-wire gates, the
  gate with **all controls conditioned on `1`** (the constant pattern `1`). `L` is taken to be the
  wires `≠ j` on which `c` is `0`; folding the one-wire flip over them turns those `0`-controls into
  `1`-controls, and the wires already carrying a `1`-control are left untouched.

It is used in the §4.3 reduction of Exercise 4.43's `n`-qubit lift; the statement of
Exercise 4.43 is in `AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- **The product of `X`-on-wire gates over a list of wires** (head outermost):
`wireFlipProd enc [k₁, …, kₙ] = W_{k₁} ⋯ W_{kₙ}` with
`Wₖ = singleQubitOnWire enc k (Matrix.swap ℂ 0 1)`
the `NOT` gate on wire `k`. It is the operator that conjugates a control pattern into its
normalised form. -/
noncomputable def wireFlipProd (enc : (Fin m → Fin 2) ≃ Fin d) (L : List (Fin m)) :
    Matrix (Fin d) (Fin d) ℂ :=
  (L.map fun k => singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1)).prod

@[simp] theorem wireFlipProd_nil (enc : (Fin m → Fin 2) ≃ Fin d) :
    wireFlipProd enc [] = 1 := rfl

/-- `wireFlipProd` peels its first wire off the outside. -/
theorem wireFlipProd_cons (enc : (Fin m → Fin 2) ≃ Fin d) (k : Fin m) (L : List (Fin m)) :
    wireFlipProd enc (k :: L)
      = singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1) * wireFlipProd enc L := by
  simp [wireFlipProd]

/-- `wireFlipProd` on a singleton is the single `X`-on-wire gate. -/
@[simp] theorem wireFlipProd_singleton (enc : (Fin m → Fin 2) ≃ Fin d) (k : Fin m) :
    wireFlipProd enc [k] = singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1) := by
  simp [wireFlipProd]

/-- `wireFlipProd` turns list concatenation into matrix multiplication. -/
theorem wireFlipProd_append (enc : (Fin m → Fin 2) ≃ Fin d) (L₁ L₂ : List (Fin m)) :
    wireFlipProd enc (L₁ ++ L₂) = wireFlipProd enc L₁ * wireFlipProd enc L₂ := by
  simp [wireFlipProd, List.map_append, List.prod_append]

/-- **The reversed list gives the inverse product**:
`wireFlipProd enc L * wireFlipProd enc L.reverse = 1`.
Proved by peeling one wire off each end and cancelling the two innermost copies of `Wₖ`
(an involution, `singleQubitOnWire_swap_mul_self`); the cancellation telescopes from the inside out,
so the `Wₖ` need not commute. -/
theorem wireFlipProd_mul_reverse (enc : (Fin m → Fin 2) ≃ Fin d) (L : List (Fin m)) :
    wireFlipProd enc L * wireFlipProd enc L.reverse = 1 := by
  induction L with
  | nil => simp
  | cons k L ih =>
    rw [wireFlipProd_cons, List.reverse_cons, wireFlipProd_append, wireFlipProd_singleton,
      mul_assoc, ← mul_assoc (wireFlipProd enc L), ih, one_mul, singleQubitOnWire_swap_mul_self]

/-- **`wireFlipProd enc L` is unitary** — it is a product of the uncontrolled single-qubit gates
`Wₖ = singleQubitOnWire enc k (Matrix.swap ℂ 0 1)`, each unitary (`swapTwo_mem_unitaryGroup`). -/
theorem wireFlipProd_mem_unitaryGroup (enc : (Fin m → Fin 2) ≃ Fin d) (L : List (Fin m)) :
    wireFlipProd enc L ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  refine list_prod_mem ?_
  intro M hM
  rw [List.mem_map] at hM
  obtain ⟨k, _, rfl⟩ := hM
  exact singleQubitOnWire_mem_unitaryGroup enc k swapTwo_mem_unitaryGroup

/-- **The control pattern `c` with every bit listed in `L` negated in turn**
(`Equiv.swap 0 1`, applied one wire at a time, head first). It is the pattern
`wireFlipProd enc L` conjugates `c` into (`wireFlipProd_conj_ctrlSingleQubit`). -/
def flipPattern (L : List (Fin m)) (c : Fin m → Fin 2) : Fin m → Fin 2 :=
  L.foldr (fun k c' => Function.update c' k (Equiv.swap (0 : Fin 2) 1 (c' k))) c

@[simp] theorem flipPattern_nil (c : Fin m → Fin 2) : flipPattern [] c = c := rfl

/-- `flipPattern` on a cons negates the head wire on top of the tail's fold. -/
theorem flipPattern_cons (k : Fin m) (L : List (Fin m)) (c : Fin m → Fin 2) :
    flipPattern (k :: L) c
      = Function.update (flipPattern L c) k (Equiv.swap (0 : Fin 2) 1 (flipPattern L c k)) := rfl

/-- **On a duplicate-free list, `flipPattern` negates exactly the listed wires.**
`flipPattern L c l = ¬c l` (i.e. `Equiv.swap 0 1 (c l)`) for `l ∈ L`, and `c l` otherwise — each
listed wire is flipped exactly once. -/
theorem flipPattern_apply_of_nodup {L : List (Fin m)} (hL : L.Nodup) (c : Fin m → Fin 2)
    (l : Fin m) :
    flipPattern L c l = if l ∈ L then Equiv.swap (0 : Fin 2) 1 (c l) else c l := by
  induction L with
  | nil => simp
  | cons k L ih =>
    rw [List.nodup_cons] at hL
    rw [flipPattern_cons]
    rcases eq_or_ne l k with rfl | hlk
    · rw [Function.update_self, ih hL.2, ite_eq_right hL.1, ite_eq_left (List.mem_cons_self ..)]
    · rw [Function.update_of_ne hlk, ih hL.2]
      by_cases hlL : l ∈ L
      · rw [ite_eq_left hlL, ite_eq_left (List.mem_cons_of_mem k hlL)]
      · rw [ite_eq_right hlL, ite_eq_right (by simp [List.mem_cons, hlk, hlL])]

/-- **`ctrlSingleQubit` depends on the control pattern only off the target wire.** If `c` and `c'`
agree on every wire `≠ j`, they give the same controlled single-qubit gate: the control condition
`∀ k ≠ j, x k = c k` reads `c` only away from `j`. -/
theorem ctrlSingleQubit_congr (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m) {c c' : Fin m → Fin 2}
    (h : ∀ l, l ≠ j → c l = c' l) (Ũ : Matrix (Fin 2) (Fin 2) ℂ) :
    ctrlSingleQubit enc j c Ũ = ctrlSingleQubit enc j c' Ũ := by
  ext i i'
  simp only [ctrlSingleQubit, Matrix.of_apply]
  have hc : (∀ k, k ≠ j → enc.symm i k = c k) ↔ (∀ k, k ≠ j → enc.symm i k = c' k) :=
    forall_congr' fun k => imp_congr_right fun hk => by rw [h k hk]
  exact if_congr Iff.rfl (if_congr hc rfl rfl) rfl

/-- **The fold of the one-wire control-bit flip along a list of control wires.** For a list `L` of
wires all distinct from the target `j`,
`wireFlipProd enc L * ctrlSingleQubit enc j c Ũ * wireFlipProd enc L.reverse
    = ctrlSingleQubit enc j (flipPattern L c) Ũ`: conjugating by the product of `X`-on-wire gates
negates the control values on exactly the wires of `L`. Each induction step peels one `Wₖ` off each
side and applies `ctrlSingleQubit_conj_singleQubitOnWire_swap` to the conjugated remainder, so no
commutativity of the wire gates is needed. -/
theorem wireFlipProd_conj_ctrlSingleQubit (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (c : Fin m → Fin 2) (Ũ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ (L : List (Fin m)), (∀ k ∈ L, k ≠ j) →
      wireFlipProd enc L * ctrlSingleQubit enc j c Ũ * wireFlipProd enc L.reverse
        = ctrlSingleQubit enc j (flipPattern L c) Ũ := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons k L ih =>
    intro hL
    have hk : k ≠ j := hL k (List.mem_cons_self ..)
    have hL' : ∀ k' ∈ L, k' ≠ j := fun k' hk' => hL k' (List.mem_cons_of_mem k hk')
    calc wireFlipProd enc (k :: L) * ctrlSingleQubit enc j c Ũ * wireFlipProd enc (k :: L).reverse
        = singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1)
            * (wireFlipProd enc L * ctrlSingleQubit enc j c Ũ * wireFlipProd enc L.reverse)
            * singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1) := by
          rw [wireFlipProd_cons, List.reverse_cons, wireFlipProd_append, wireFlipProd_singleton]
          simp only [mul_assoc]
      _ = singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1)
            * ctrlSingleQubit enc j (flipPattern L c) Ũ
            * singleQubitOnWire enc k (Matrix.swap ℂ (0 : Fin 2) 1) := by rw [ih hL']
      _ = ctrlSingleQubit enc j (flipPattern (k :: L) c) Ũ := by
          rw [ctrlSingleQubit_conj_singleQubitOnWire_swap enc hk, flipPattern_cons]

/-- **Every controlled single-qubit gate normalises, up to conjugation by `X`-on-wire gates, to the
all-`1`-controlled gate** (N&C §4.3, control-pattern normalisation). For any control pattern `c`
there is a list `L` of control wires (all `≠ j`) with
`ctrlSingleQubit enc j c Ũ
    = wireFlipProd enc L.reverse * ctrlSingleQubit enc j 1 Ũ * wireFlipProd enc L`,
where `1` is the constant pattern that conditions every control wire on `1`. `L` is the set of wires
`≠ j` on which `c` is `0`; folding the one-wire flip over them turns those `0`-controls into
`1`-controls while leaving the wires already carrying `1` untouched. This is the state from which
the resulting `Cⁿ(Ũ)` is realised over `H, S, CNOT, Toffoli`. -/
theorem exists_wireFlipProd_conj_ctrlSingleQubit_one (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (c : Fin m → Fin 2) (Ũ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ L : List (Fin m), (∀ k ∈ L, k ≠ j) ∧
      ctrlSingleQubit enc j c Ũ
        = wireFlipProd enc L.reverse * ctrlSingleQubit enc j 1 Ũ * wireFlipProd enc L := by
  set L : List (Fin m) :=
    (Finset.univ.filter fun l => l ≠ j ∧ c l = 0).toList with hLdef
  have hmem : ∀ l, l ∈ L ↔ (l ≠ j ∧ c l = 0) := by
    intro l; rw [hLdef, Finset.mem_toList, Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ l)
  have hLne : ∀ k ∈ L, k ≠ j := fun k hk => ((hmem k).1 hk).1
  have hLnodup : L.Nodup := Finset.nodup_toList _
  have hflip : ∀ l, l ≠ j → flipPattern L c l = (1 : Fin m → Fin 2) l := by
    intro l hlj
    rw [flipPattern_apply_of_nodup hLnodup, Pi.one_apply]
    by_cases h0 : c l = 0
    · rw [ite_eq_left ((hmem l).2 ⟨hlj, h0⟩), h0, Equiv.swap_apply_left]
    · rw [ite_eq_right (fun hl => h0 ((hmem l).1 hl).2)]
      omega
  have key : wireFlipProd enc L * ctrlSingleQubit enc j c Ũ * wireFlipProd enc L.reverse
      = ctrlSingleQubit enc j 1 Ũ := by
    rw [wireFlipProd_conj_ctrlSingleQubit enc j c Ũ L hLne, ctrlSingleQubit_congr enc j hflip Ũ]
  have hBA : wireFlipProd enc L.reverse * wireFlipProd enc L = 1 := by
    have h := wireFlipProd_mul_reverse enc L.reverse
    rwa [List.reverse_reverse] at h
  refine ⟨L, hLne, ?_⟩
  rw [← key]; simp only [mul_assoc]; rw [hBA, mul_one, ← mul_assoc, hBA, one_mul]

end AxQM.Concrete
