/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.DeutschDoublyControlledReachable
import AxQM.Concrete.MultiControlledSingleQubit

/-!
# Concrete: the doubly-controlled `Fin 8` matrix is a three-wire `mcCtrlSingleQubit` placement
(matrix level, N&C Ex 4.44)

Every statement is about matrices — the doubly-controlled `Fin 8` gate `ccontrolledMatFin8` and
the multiply-controlled single-qubit wire gate `mcCtrlSingleQubit`.

## Bridging the two matrix forms of the doubly-controlled gate

The universality development of the Deutsch gate `G = C²(iR_x(πα))` (Nielsen & Chuang, Exercise
4.44) carries **two** matrix representations of the doubly-controlled gate `C²(g)`:

* `ccontrolledMatFin8 g` — the `Fin 8 × Fin 8` matrix `C²(g)` obtained by nesting the
  once-controlled construction, `reindex`ed to `Fin 8` along the big-endian packing
  `threeQubitIndex`. This is the
  form in which `deutschGate_congr_threeQuditIso_op` reads the physical gate: the
  Deutsch gate `deutschGate α` transported to the eight-level register `qudit 8` is
  `toEuclideanCLM (ccontrolledMatFin8 (iRxMat (πα)))` (`Postulates/API/DeutschGateMatrix.lean`).
* `mcCtrlSingleQubit enc S j g` — the wire-addressed placement that applies `g` to wire `j` of an
  `m`-qubit register when every control wire in `S` is `1`. This is the form from which
  `Concrete/DeutschWirePlacement.lean`, `…DeutschCompressedReachable.lean` and
  `…DeutschCompressedUniversality.lean` are built — a `G`-placement on register wires.

These are the *same* gate written over two index conventions, but no lemma related them. This file
supplies the bridge for the **base register** (three wires, `d = 8`): with the canonical three-wire
encoding `finThreeRegEnc` — bit `k` of the string is register wire `k`, packed big-endian into
`Fin 8` exactly as `threeQubitIndex` packs `(c₁, c₂, t)` — the doubly-controlled `Fin 8` gate *is*
the two-control placement with controls `{0, 1}` and target `2`:

  `ccontrolledMatFin8 g = mcCtrlSingleQubit finThreeRegEnc {0, 1} 2 g`.

This is the register-model counterpart of `deutschGate_congr_threeQuditIso_op`: it lets the physical
Deutsch gate (read as `ccontrolledMatFin8`) be named as the reachability family's
`mcCtrlSingleQubit` placement on the base three-wire register.

## The construction and results

* `finThreeRegEnc : (Fin 3 → Fin 2) ≃ Fin 8` — the canonical three-wire register encoding
  `x ↦ 4·x 0 + 2·x 1 + x 2`, the composite of `finThreeArrowProd` (reading a `Fin 3`-string as the
  triple `(x 0, x 1, x 2)`) with `threeQubitIndex`.
* `ccontrolledMatFin8_eq_mcCtrlSingleQubit` — the bridge identity
  `ccontrolledMatFin8 g = mcCtrlSingleQubit finThreeRegEnc {0, 1} 2 g`, proved by matching the
  entrywise formulas `ccontrolledMat_apply` and `wireGate_apply` on the control-diagonal block.
-/

namespace AxQM.Concrete

open Matrix

/-- **A `Fin 3`-indexed bit string as an ordered triple.** The equivalence
`(Fin 3 → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2` reading a three-bit string `x` as the triple
`(x 0, x 1, x 2)` (and back via `![·, ·, ·]`). Composed with `threeQubitIndex` it gives the
canonical three-wire register encoding. -/
def finThreeArrowProd : (Fin 3 → Fin 2) ≃ (Fin 2 × Fin 2 × Fin 2) where
  toFun x := (x 0, x 1, x 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv x := by
    funext k
    fin_cases k <;> rfl
  right_inv p := rfl

/-- **The canonical three-wire register encoding** `(Fin 3 → Fin 2) ≃ Fin 8`. Reads a three-bit
string as the register index `4·x 0 + 2·x 1 + x 2` — bit `k` of the string is register wire `k`,
packed big-endian exactly as `threeQubitIndex` packs the control/control/target triple
`(c₁, c₂, t)`.
The encoding against which the doubly-controlled `Fin 8` gate is a two-control `mcCtrlSingleQubit`
placement. -/
def finThreeRegEnc : (Fin 3 → Fin 2) ≃ Fin 8 :=
  finThreeArrowProd.trans threeQubitIndex

@[simp] theorem finThreeArrowProd_symm_apply (p : Fin 2 × Fin 2 × Fin 2) :
    finThreeArrowProd.symm p = ![p.1, p.2.1, p.2.2] := rfl

/-- **The doubly-controlled `Fin 8` gate is the base three-wire `mcCtrlSingleQubit` placement.**
For any single-qubit block `g`, the `Fin 8` matrix `C²(g)` equals the two-control single-qubit wire
gate placing `g` on wire `2` with controls `{0, 1}`, relative to the canonical three-wire encoding
`finThreeRegEnc`:

  `ccontrolledMatFin8 g = mcCtrlSingleQubit finThreeRegEnc {0, 1} 2 g`.

The `((a,b,s), (c,d,t))` entry of `ccontrolledMatFin8 g` (indices read off `threeQubitIndex.symm`)
is `0` off the control-diagonal `a = c ∧ b = d`, and on it is `g s t` when both controls are `1`,
else
`δ_{s,t}` (`ccontrolledMat_apply`). The `mcCtrlSingleQubit` entry (via `wireGate_apply`) fires the
block `g` on wire `2` exactly when register wires `0, 1` are `1`, requiring wires `0, 1` to agree —
the very same control-diagonal condition — and reads the target fibre `(s, t)`; the two entrywise
formulas coincide. -/
theorem ccontrolledMatFin8_eq_mcCtrlSingleQubit (g : Matrix (Fin 2) (Fin 2) ℂ) :
    ccontrolledMatFin8 g = mcCtrlSingleQubit finThreeRegEnc {0, 1} 2 g := by
  ext I I'
  rw [ccontrolledMatFin8, Matrix.reindex_apply, Matrix.submatrix_apply, mcCtrlSingleQubit,
    wireGate_apply]
  have hE : ∀ J : Fin 8, finThreeRegEnc.symm J = finThreeArrowProd.symm (threeQubitIndex.symm J) :=
    fun J => by rw [finThreeRegEnc, Equiv.symm_trans_apply]
  rw [hE I, hE I']
  generalize threeQubitIndex.symm I = p
  generalize threeQubitIndex.symm I' = q
  obtain ⟨a, b, s⟩ := p
  obtain ⟨c, d, t⟩ := q
  rw [ccontrolledMat_apply, finThreeArrowProd_symm_apply, finThreeArrowProd_symm_apply]
  have e2 : (![a, b, s] : Fin 3 → Fin 2) 2 = s := rfl
  have e2' : (![c, d, t] : Fin 3 → Fin 2) 2 = t := rfl
  have hc : (∀ k : Fin 3, k ≠ 2 → (![a, b, s] : Fin 3 → Fin 2) k = ![c, d, t] k)
      ↔ (a = c ∧ b = d) := by
    constructor
    · intro h
      exact ⟨h 0 (by decide), h 1 (by decide)⟩
    · rintro ⟨hac, hbd⟩ k hk
      fin_cases k
      · exact hac
      · exact hbd
      · exact absurd rfl hk
  have hctrl : (∀ k ∈ ({0, 1} : Finset (Fin 3)),
        Function.update (![a, b, s] : Fin 3 → Fin 2) 2 0 k = 1) ↔ (a = 1 ∧ b = 1) := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have := h 0 (by decide); rwa [Function.update_of_ne (by decide)] at this
      · have := h 1 (by decide); rwa [Function.update_of_ne (by decide)] at this
    · rintro ⟨ha, hb⟩ k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · rwa [Function.update_of_ne (by decide)]
      · rwa [Function.update_of_ne (by decide)]
  dsimp only
  rw [e2, e2']
  simp only [hc, hctrl]
  by_cases h : a = c ∧ b = d
  · rw [ite_eq_left h, ite_eq_left h]
    obtain ⟨rfl, rfl⟩ := h
    by_cases hab : a = 1 ∧ b = 1
    · rw [ite_eq_left hab, ite_eq_left hab]
    · rw [ite_eq_right hab, ite_eq_right hab, Matrix.one_apply]
  · rw [ite_eq_right h, ite_eq_right h]

end AxQM.Concrete
