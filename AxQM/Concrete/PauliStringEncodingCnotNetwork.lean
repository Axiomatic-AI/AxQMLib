/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringEncodingCnotLayer

/-!
# Concrete: the multi-control CNOT network of the stabilizer encoding circuit (N&C, Problem 10.3)

This file continues the **synthesis** half
of Nielsen & Chuang **Problem 10.3** ("encoding stabilizer codes"). The CNOT layer of
`Concrete/PauliStringEncodingCnotLayer.lean` gave, for a **single** control fan `cnotFan i ts`, its
action on the two *seed* generators `Xᵢ` and `Z_m`. The encoding circuit, however, applies a whole
**network** of such fans — one per top (pivot) control wire — to *every* row of the check matrix at
once, and building `[I A₁ A₂]` (and the coupled transposed `Z`-blocks) requires knowing how each fan
acts on the arbitrary intermediate Pauli string produced by the earlier fans, not just on a lone
seed. This file supplies exactly that missing generality:

* `checkRow_act_cnotFan` — the **general symplectic column action of a CNOT fan on an arbitrary
  check row**. It packages the two column operations of every `CNOT_{i→t}` (`x_t += x_c`,
  `z_c += z_t`; Figure 10.7) into one closed form `cnotFanCol i ts` acting on `checkRow g` — for
  any Pauli string `g`, not merely a seed. Because a CNOT's action on the check matrix depends on
  `g` only through its check bits (`pauliBit`), the fan's action factors through `checkRow`, so
  successive fans compose at the check-row level.
* `checkRow_act_cnotNetwork` — the **multi-control CNOT network** `cnotNetwork controls tgt` (a fan
  per control `c ∈ controls`, onto its targets `tgt c`) acts on the check matrix by the
  **composition (right fold) of the per-control fan column operations**. This is the operational
  content of "the encoding circuit acts on the check matrix by a sequence of column operations": the
  network's effect on any row is `controls.foldr (cnotFanCol c (tgt c)) (checkRow g)`.

The single-generator lemmas of the CNOT layer are recovered as instances of `checkRow_act_cnotFan`
(the general column op applied to `checkRow (xGenPauli i)` / `checkRow (zGenPauli m)` reproduces the
X-spread / coupled-transpose rows); the general lemma is what the assembly evaluates on the seed
rows of `G` (10.124) — with the pivot controls disjoint from their non-pivot targets — to build the
`X`-blocks `[I A₁ A₂]` and their transposes. Together with the phase/`CZ` network (`Z`-blocks
`B, C₂`) this carries `G` (10.124) to the standard form (10.125).

## Design notes

* The single-qubit check-bit tableaux `pauliBit_cnotCtrlPauli` / `pauliBit_cnotTgtPauli` are the
  `ZMod 2`-valued forms of the `ℕ`-valued symplectic bit laws (`pauliXBit_cnot…` /
  `pauliZBit_cnot…` of `Concrete/PauliStringCnotConjugation.lean`); a `16`-case `decide` lifts them
  to the `pauliBit` pair, from which the whole-string single-CNOT column op
  `checkRow_cnotPauliString` and then the fan column op follow by the wire-by-wire and
  target-by-target inductions.
* `cnotFanCol i ts` reads the *original* control `X`-bit `r.1 i` (a control's `X`-bit is untouched
  by its own fan) and sums the *original* target `Z`-bits `r.2 t` over `ts` into the control's
  `Z`-bit — both valid because the fan changes only target `X`-bits and the control `Z`-bit, never a
  control `X`-bit or a target `Z`-bit; hence the closed form is order-independent and reads solely
  from the input row.
* `cnotFanCol_fixed` (a fan fixes a row whose control `X`-bit and target `Z`-bits all vanish) is the
  "no interference" fact that lets the assembly conclude that the fans other than a row's own leave
  it unchanged.
* `cnotNetwork` and the fold `checkRow_act_cnotNetwork` require only per-control freshness
  (`c ∉ tgt c`, `(tgt c).Nodup`) — the *cross*-control disjointness (controls vs. targets) that
  collapses the fold to the standard-form blocks is supplied by the assembly, not here, keeping this
  file about the network's generic column action.
-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The single-CNOT check-matrix column operation on an arbitrary row -/

/-- The `ZMod 2` check-bit form of the CNOT **control** tableau: `CNOT_{c→t}` fixes the control's
`X`-bit and adds the target's `Z`-bit to the control's `Z`-bit,
`pauliBit (cnotCtrlPauli a b) = (x_a, z_a + z_b)`. A `16`-case check against the `ℕ`-valued laws
`pauliXBit_cnotCtrlPauli` / `pauliZBit_cnotCtrlPauli`. -/
theorem pauliBit_cnotCtrlPauli (a b : Fin 4) :
    pauliBit (cnotCtrlPauli a b) = ((pauliBit a).1, (pauliBit a).2 + (pauliBit b).2) := by
  fin_cases a <;> fin_cases b <;> decide

/-- The `ZMod 2` check-bit form of the CNOT **target** tableau: `CNOT_{c→t}` adds the control's
`X`-bit to the target's `X`-bit and fixes the target's `Z`-bit,
`pauliBit (cnotTgtPauli a b) = (x_b + x_a, z_b)`. A `16`-case check against the `ℕ`-valued laws
`pauliXBit_cnotTgtPauli` / `pauliZBit_cnotTgtPauli`. -/
theorem pauliBit_cnotTgtPauli (a b : Fin 4) :
    pauliBit (cnotTgtPauli a b) = ((pauliBit b).1 + (pauliBit a).1, (pauliBit b).2) := by
  fin_cases a <;> fin_cases b <;> decide

/-- **The single-CNOT check-matrix column operation** (control `c`, target `t`, `c ≠ t`) on an
*arbitrary* Pauli string `g`: conjugating by `CNOT_{c→t}` adds the control's `X`-column into the
target's (`x_t += x_c`) and the target's `Z`-column into the control's (`z_c += z_t`), leaving every
other bit fixed (Figure 10.7). Since a CNOT changes only wires `c, t`, this reads off
`cnotPauliString_ctrl` / `_tgt` / `_of_ne` and the check-bit tableaux `pauliBit_cnot…`. -/
theorem checkRow_cnotPauliString {c t : Fin n} (h : c ≠ t) (g : Fin n → Fin 4) :
    checkRow (cnotPauliString g c t)
      = (fun k => (checkRow g).1 k + (if k = t then (checkRow g).1 c else 0),
         fun k => (checkRow g).2 k + (if k = c then (checkRow g).2 t else 0)) := by
  ext k
  · change (pauliBit (cnotPauliString g c t k)).1 = _
    rcases eq_or_ne k c with rfl | hkc
    · rw [cnotPauliString_ctrl, pauliBit_cnotCtrlPauli]; simp [ite_eq_right h, checkRow]
    · rcases eq_or_ne k t with rfl | hkt
      · rw [cnotPauliString_tgt g h, pauliBit_cnotTgtPauli]; simp [checkRow]
      · rw [cnotPauliString_of_ne g c t hkc hkt]; simp [ite_eq_right hkt, checkRow]
  · change (pauliBit (cnotPauliString g c t k)).2 = _
    rcases eq_or_ne k c with rfl | hkc
    · rw [cnotPauliString_ctrl, pauliBit_cnotCtrlPauli]; simp [checkRow]
    · rcases eq_or_ne k t with rfl | hkt
      · rw [cnotPauliString_tgt g h, pauliBit_cnotTgtPauli]; simp [ite_eq_right (Ne.symm h),
            checkRow]
      · rw [cnotPauliString_of_ne g c t hkc hkt]; simp [ite_eq_right hkc, checkRow]

/-! ### The CNOT-fan check-matrix column operation on an arbitrary row -/

/-- The **closed-form column operation of a CNOT fan** `cnotFan i ts` on a check row
`r = (x | z)`: fan out the control `X`-bit `x_i` onto every target (`x_t += x_i` for `t ∈ ts`) and
accumulate the target `Z`-bits back onto the control (`z_i += Σ_{t ∈ ts} z_t`), fixing all other
bits. The control's own `X`-bit and every target's `Z`-bit are read from the *input* `r` (the fan
never changes them), so the operation is order-independent and depends on the string only through
its check row. This is the check-row realization of `act (cnotFan i ts)`
(`checkRow_act_cnotFan`). -/
def cnotFanCol (i : Fin n) (ts : List (Fin n))
    (r : (Fin n → ZMod 2) × (Fin n → ZMod 2)) : (Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  (fun k => r.1 k + (if k ∈ ts then r.1 i else 0),
   fun k => r.2 k + (if k = i then (ts.map (fun t => r.2 t)).sum else 0))

/-- **The general symplectic column action of a CNOT fan** (N&C Problem 10.3): for distinct targets
`ts` none equal to the control `i`, conjugating an *arbitrary* Pauli string `g` by the fan
`cnotFan i ts` acts on its check row by the closed-form column operation `cnotFanCol i ts`
(`x_t += x_i` for `t ∈ ts`; `z_i += Σ_{t ∈ ts} z_t`). Proved by induction on `ts`: the head
`CNOT_{i→t}` (which, `t ∉ ts`, acts last on the already-fanned string) contributes one more
`checkRow_cnotPauliString` step, reading the still-original `x_i` (a control is never retargeted)
and `z_t` (a target's `Z`-bit is never changed), which telescopes into the sum. This is the reusable
column op the encoding circuit composes over its pivot controls; it subsumes the single-generator
lemmas `checkRow_act_cnotFan_xGenPauli` / `checkRow_act_cnotFan_zGenPauli_of_mem` of the CNOT
layer (their right-hand sides are `cnotFanCol i ts` evaluated at `checkRow (xGenPauli i)` /
`checkRow (zGenPauli m)`). -/
theorem checkRow_act_cnotFan (i : Fin n) :
    ∀ (ts : List (Fin n)), i ∉ ts → ts.Nodup → ∀ (g : Fin n → Fin 4),
      checkRow (CliffordCircuit.act (cnotFan i ts) g) = cnotFanCol i ts (checkRow g)
  | [], _, _, g => by
      simp only [cnotFan_nil, CliffordCircuit.act, cnotFanCol, List.not_mem_nil, ite_false,
        List.map_nil, List.sum_nil]
      ext k <;> simp
  | t :: ts, hi, hnd, g => by
      rw [List.mem_cons, not_or] at hi
      obtain ⟨hit, hits⟩ := hi
      obtain ⟨htnotin, hnd'⟩ := List.nodup_cons.mp hnd
      rw [act_cnotFan_cons_of_ne hit, checkRow_cnotPauliString hit,
        checkRow_act_cnotFan i ts hits hnd' g]
      have hti : t ≠ i := fun e => hit e.symm
      have hinner : (if i ∈ ts then (checkRow g).1 i else 0) = 0 := ite_eq_right hits
      ext k
      · simp only [cnotFanCol, hinner, add_zero, List.mem_cons]
        by_cases h1 : k = t
        · subst h1; simp only [htnotin, ite_false, ite_true, true_or, add_zero]
        · by_cases h2 : k ∈ ts <;>
            simp only [h1, h2, ite_false, ite_true, or_true, or_false, add_zero]
      · simp only [cnotFanCol, List.map_cons, List.sum_cons, ite_eq_right hti, add_zero]
        by_cases hk : k = i
        · subst hk; simp only [ite_true]; abel
        · simp only [hk, ite_false, add_zero]

/-- **A CNOT fan fixes a check row it cannot act on**: if the control `X`-bit `r.1 i` vanishes and
every target `Z`-bit `r.2 t` (`t ∈ ts`) vanishes, then `cnotFanCol i ts r = r`. Nothing is fanned
out (`x_t += 0`) and nothing is accumulated back (`z_i += 0`). This is the "no interference" fact
the assembly uses to conclude that the fans of the other pivot controls leave a given row
unchanged. -/
theorem cnotFanCol_fixed (i : Fin n) (ts : List (Fin n))
    {r : (Fin n → ZMod 2) × (Fin n → ZMod 2)} (hx : r.1 i = 0)
    (hz : ∀ t ∈ ts, r.2 t = 0) : cnotFanCol i ts r = r := by
  ext k
  · simp only [cnotFanCol, hx, ite_self, add_zero]
  · simp only [cnotFanCol]
    have hsum : (ts.map (fun t => r.2 t)).sum = 0 := by
      rw [List.sum_eq_zero]
      intro x hx'
      simp only [List.mem_map] at hx'
      obtain ⟨t, ht, rfl⟩ := hx'
      exact hz t ht
    rw [hsum]; simp

/-! ### The multi-control CNOT network -/

/-- The **multi-control CNOT network**: a CNOT fan from each control `c ∈ controls` onto its own
target list `tgt c` (`controls.flatMap (fun c => cnotFan c (tgt c))`). With `controls` the pivot
wires `{1, …, r}` and `tgt c` the support of row `c` of `[A₁ | A₂]`, this is the CNOT stage of the
stabilizer encoding circuit of N&C Problem 10.3. -/
def cnotNetwork (controls : List (Fin n)) (tgt : Fin n → List (Fin n)) : CliffordCircuit n :=
  controls.flatMap (fun c => cnotFan c (tgt c))

/-- The network is built one control at a time:
`cnotNetwork (c :: cs) tgt = cnotFan c (tgt c) ++ cnotNetwork cs tgt`. -/
theorem cnotNetwork_cons (c : Fin n) (cs : List (Fin n)) (tgt : Fin n → List (Fin n)) :
    cnotNetwork (c :: cs) tgt = cnotFan c (tgt c) ++ cnotNetwork cs tgt := by
  simp only [cnotNetwork, List.flatMap_cons]

/-- **The multi-control CNOT network acts on the check matrix by a fold of fan column operations.**
For per-control freshness (each control absent from and each target list free of duplicates in its
own fan, `c ∉ tgt c` and `(tgt c).Nodup`), conjugating any Pauli string `g` by `cnotNetwork controls
tgt` transforms its check row by the right fold of the per-control column operations,
`controls.foldr (fun c r => cnotFanCol c (tgt c) r) (checkRow g)` — the latest control's fan is
innermost (it transforms `checkRow g` first) and the earliest (head) is outermost (it acts last),
matching `act_append` and the right-to-left `CliffordCircuit.act` convention. This is the
operational statement that "the encoding
circuit acts on the check matrix by a sequence of column operations"; the assembly evaluates this
fold on the seed rows of `G` (10.124), using the cross-control disjointness of pivots and non-pivot
targets, to read off the standard-form `X`-blocks and their transposes. Proved by induction on
`controls` from `act_append` and the general fan column action `checkRow_act_cnotFan`. -/
theorem checkRow_act_cnotNetwork (tgt : Fin n → List (Fin n)) :
    ∀ (controls : List (Fin n)), (∀ c ∈ controls, c ∉ tgt c ∧ (tgt c).Nodup) →
      ∀ (g : Fin n → Fin 4),
        checkRow (CliffordCircuit.act (cnotNetwork controls tgt) g)
          = controls.foldr (fun c r => cnotFanCol c (tgt c) r) (checkRow g)
  | [], _, g => by simp [cnotNetwork, CliffordCircuit.act]
  | c :: cs, hyp, g => by
      have hc := hyp c (List.mem_cons_self ..)
      have hcs : ∀ c' ∈ cs, c' ∉ tgt c' ∧ (tgt c').Nodup :=
        fun c' hc' => hyp c' (List.mem_cons_of_mem _ hc')
      rw [cnotNetwork_cons, act_append, checkRow_act_cnotFan c (tgt c) hc.1 hc.2,
        checkRow_act_cnotNetwork tgt cs hcs g, List.foldr_cons]

end AxQM.Concrete
