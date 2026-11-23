/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringEncodingLayers

/-!
# Concrete: the CNOT layer of the stabilizer encoding circuit (Nielsen & Chuang, Problem 10.3)

This file continues the **synthesis** half of Nielsen & Chuang **Problem 10.3** ("encoding
stabilizer codes"): after the Hadamard layer (`Concrete/PauliStringEncodingLayers.lean`) has turned
the top `r` rows of the trivial check matrix `G` of Eq. (10.124) from `Z`-type (`Zᵢ`) into `X`-type
(`Xᵢ`), the second layer is a **network of CNOT gates**, all controlled on those top `X`-rows, that
builds the `X`-blocks `A₁, A₂` of the standard form (10.125) — and, by the coupled column
operations of a CNOT, simultaneously builds the transposed `Z`-blocks `A₁ᵀ` (into the middle
generator rows) and `A₂ᵀ` (into the bottom encoded-`Z` rows). This file delivers the reusable unit
of that network: the **fan of CNOTs from one control**.

## The CNOT fan

`cnotFan i ts` is the circuit applying a CNOT from control wire `i` to each target `t` in a list
`ts` (a self-target `t = i` is dropped, so the fan is total: `cnotStep i t`). With `ts` the
support of row `i` of `[A₁ | A₂]`, `cnotFan i ts` is exactly the CNOT network attached to the
`i`-th top generator. The two column operations of `CNOT_{i→t}` (`x_t += x_c`, `z_c += z_t`;
Figure 10.7) drive the two effects:

* `act_cnotFan_xGenPauli` — the **X-spread** (building row `i` of `A₁, A₂`): applied to the
  `X`-seed `Xᵢ`, the fan produces the Pauli string with an `X` on wire `i` and on every wire in
  `ts` (`xSetPauli (i :: ts)`). Each `CNOT_{i→t}` copies the control's `X` onto the target
  (`x_t += x_c`), so the seed's single `X` fans out to the whole target set. On the check matrix
  this is row `i` becoming `(eᵢ + Σ_{t∈ts} e_t | 0)` — the `I` diagonal entry plus the row's
  `A₁, A₂` entries.
* `act_cnotFan_zGenPauli_of_mem` — the **coupled transpose** (building `A₂ᵀ` / `A₁ᵀ`): applied
  to a pure-`Z` generator `Z_m` with `m ∈ ts`, the fan produces `Z_i Z_m` (`zPairPauli i m`).
  The single gate `CNOT_{i→m}` copies the target's `Z` back onto the control (`z_i += z_m`), so
  a `Z` on a target wire `m` deposits a `Z` on the control wire `i`. Iterated over the top
  controls `i`, this is precisely how a `Z` in the identity block of a bottom (encoded-`Z`) or
  middle row is transposed into column `i` — the blocks `A₂ᵀ` (bottom) and `A₁ᵀ` (middle) of
  (10.125).
* `act_cnotFan_zGenPauli_of_not_mem` — the fan leaves a pure-`Z` generator `Z_m` **unchanged**
  when `m ∉ ts`: a `Z` on a wire the fan neither controls nor targets is untouched, and a `Z` on
  the control itself is preserved (no target carries a `Z` to add). This is what keeps the layer
  from disturbing rows outside its support.

The check-matrix readings (`checkRow_act_cnotFan_xGenPauli`,
`checkRow_act_cnotFan_zGenPauli_of_mem`) and the operator-level readings through the backbone
`CliffordCircuit.conj_pauliString` (`cnotFan_conj_xGenPauli`, `cnotFan_conj_zGenPauli_of_mem`)
record the same facts as check-matrix column operations and as unitary conjugations up to a
nonzero `±1` phase.

## Design notes

* `cnotFan i ts = ts.flatMap (cnotStep i)`, so it composes with the other layers as list
  concatenation and its `act`/`sign`/`toMatrix` are the existing `CliffordCircuit` folds —
  nothing new about circuits is introduced, only the specific gate list. The helper
  `cnotStep i t` (`if i = t then [] else [CNOT_{i→t}]`) makes the fan **total** — a self-target
  is simply skipped — which sidesteps carrying a `i ∉ ts` proof through the gate list; the
  action lemmas re-supply `i ∉ ts` and `ts.Nodup` as hypotheses where they are actually needed
  (freshness of each target).
* Both action lemmas need `ts.Nodup`: a target hit twice would have its column operation applied
  twice and, `X`/`Z` bits living in `ZMod 2`, cancel — the clean "spread over exactly the wires
  in `ts`" statement is the one the encoding circuit uses (each `1` of `A` gives one CNOT).
* The single-gate facts `cnotPauliString_fixed` (a fan leaves a control/target pair fixed when
  the control is `I`/`Z` and the target is `I`) and `cnotPauliString_zGenPauli_couple`
  (`CNOT_{i→m} : Z_m ↦ Z_i Z_m`) are read off the tableau of
  `Concrete/PauliStringCnotConjugation.lean`; the layer lemmas are inductions over `ts` on top
  of them.
-/

open Matrix

noncomputable section

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### Multi-wire generators (rows of the check matrix) -/

/-- The **multi-`X` Pauli string** on a wire list `S`: `X` on every wire in `S`, `I` elsewhere.
The image of the `X`-seed `Xᵢ` under a CNOT fan (`act_cnotFan_xGenPauli`); its check row is
`(1_S | 0)` — a `1` in each `X`-column of `S`. -/
def xSetPauli (S : List (Fin n)) : Fin n → Fin 4 := fun k => if k ∈ S then 1 else 0

/-- The **two-wire `Z` Pauli string** `Z_i Z_m`: `Z` on wires `i` and `m`, `I` elsewhere. The
image of the pure-`Z` generator `Z_m` under a CNOT fan controlled on `i` with `m` a target
(`act_cnotFan_zGenPauli_of_mem`); its check row is `(0 | e_i + e_m)`. -/
def zPairPauli (i m : Fin n) : Fin n → Fin 4 := fun k => if k = i ∨ k = m then 3 else 0

@[simp] theorem xSetPauli_apply (S : List (Fin n)) (k : Fin n) :
    xSetPauli S k = if k ∈ S then 1 else 0 := rfl

@[simp] theorem zPairPauli_apply (i m k : Fin n) :
    zPairPauli i m k = if k = i ∨ k = m then 3 else 0 := rfl

/-! ### The CNOT fan -/

/-- A **single CNOT step** from control `i` to target `t`: the one-gate circuit `[CNOT_{i→t}]`,
or the empty circuit if `t = i` (a self-target is skipped). This keeps the CNOT fan total. -/
def cnotStep (i t : Fin n) : CliffordCircuit n :=
  if h : i = t then [] else [CliffordGate.cnot i t h]

/-- The **CNOT fan** from control wire `i` onto the target wires `ts`: apply a CNOT from `i` to
each `t ∈ ts` (`ts.flatMap (cnotStep i)`). With `ts` the support of row `i` of the `X`-block
`[A₁ | A₂]`, this is the CNOT network attached to the `i`-th top generator in the encoding
circuit of Nielsen & Chuang Problem 10.3. -/
def cnotFan (i : Fin n) (ts : List (Fin n)) : CliffordCircuit n := ts.flatMap (cnotStep i)

/-- The fan on no targets is the empty circuit. -/
@[simp] theorem cnotFan_nil (i : Fin n) : cnotFan i [] = [] := rfl

/-- The fan is built one target at a time: `cnotFan i (t :: ts) = cnotStep i t ++ cnotFan i ts`. -/
theorem cnotFan_cons (i t : Fin n) (ts : List (Fin n)) :
    cnotFan i (t :: ts) = cnotStep i t ++ cnotFan i ts := by
  simp only [cnotFan, List.flatMap_cons]

/-- **The row action factors over `++`**: conjugating by `U ++ V` applies `V` first, then `U`
(`act (U ++ V) g = act U (act V g)`), since `act` composes gates right-to-left. -/
theorem act_append (U V : CliffordCircuit n) (g : Fin n → Fin 4) :
    CliffordCircuit.act (U ++ V) g = CliffordCircuit.act U (CliffordCircuit.act V g) := by
  induction U with
  | nil => rfl
  | cons γ U ih => simp only [List.cons_append, CliffordCircuit.act, ih]

/-- The row action of a single CNOT step with `i ≠ t` is the CNOT column operation
`cnotPauliString g i t`. -/
theorem act_cnotStep_of_ne {i t : Fin n} (hit : i ≠ t) (g : Fin n → Fin 4) :
    CliffordCircuit.act (cnotStep i t) g = cnotPauliString g i t := by
  rw [cnotStep, dite_eq_right hit]
  simp only [CliffordCircuit.act, CliffordGate.act]

/-- Peeling the head of a CNOT fan (with `i ≠ t`): the head CNOT `i → t` acts last, on the result
of the rest of the fan. -/
theorem act_cnotFan_cons_of_ne {i t : Fin n} (hit : i ≠ t) (ts : List (Fin n))
    (g : Fin n → Fin 4) :
    CliffordCircuit.act (cnotFan i (t :: ts)) g
      = cnotPauliString (CliffordCircuit.act (cnotFan i ts) g) i t := by
  rw [cnotFan_cons, act_append, act_cnotStep_of_ne hit]

/-! ### Single-CNOT tableau facts -/

/-- With an identity target, the control Pauli is unchanged: `cnotCtrlPauli a 0 = a` (a `CNOT`
whose target carries no `Z` does not touch the control's `Z`-bit). -/
theorem cnotCtrlPauli_zero_right (a : Fin 4) : cnotCtrlPauli a 0 = a := by fin_cases a <;> rfl

/-- **A CNOT `i → t` fixes a string whose target wire is `I` and whose control wire is `I` or
`Z`.** Since `x_c ∈ {0}` (control is `I` or `Z`), the target keeps its `I` (`x_t += x_c` adds
nothing), and since `z_t = 0` (target is `I`) the control keeps its `Z`-bit (`z_c += z_t` adds
nothing). This is why the fan leaves untouched every row on which the control and the current
target are inactive. -/
theorem cnotPauliString_fixed {g : Fin n → Fin 4} {i t : Fin n} (hit : i ≠ t)
    (ht0 : g t = 0) (hi : g i = 0 ∨ g i = 3) : cnotPauliString g i t = g := by
  funext k
  rcases eq_or_ne k i with rfl | hki
  · rw [cnotPauliString_ctrl, ht0, cnotCtrlPauli_zero_right]
  · rcases eq_or_ne k t with rfl | hkt
    · rw [cnotPauliString_tgt g hit, ht0]
      rcases hi with h | h <;> rw [h] <;> decide
    · rw [cnotPauliString_of_ne g i t hki hkt]

/-- **The coupling of a single CNOT** `CNOT_{i→m} : Z_m ↦ Z_i Z_m` (`i ≠ m`). The target's `Z`
is copied back onto the control (`z_i += z_m`), depositing a `Z` on the control wire while
leaving the `Z` on `m`. This is the elementary transpose operation building the `A₂ᵀ` / `A₁ᵀ`
blocks. -/
theorem cnotPauliString_zGenPauli_couple {i m : Fin n} (him : i ≠ m) :
    cnotPauliString (zGenPauli m) i m = zPairPauli i m := by
  have hi : zGenPauli m i = 0 := by simp [zGenPauli_apply, him]
  have hm : zGenPauli m m = 3 := by simp [zGenPauli_apply]
  funext k
  rcases eq_or_ne k i with rfl | hki
  · rw [cnotPauliString_ctrl, hi, hm, zPairPauli_apply, ite_eq_left (Or.inl rfl)]; decide
  · rcases eq_or_ne k m with rfl | hkm
    · rw [cnotPauliString_tgt _ him, hi, hm, zPairPauli_apply, ite_eq_left (Or.inr rfl)]; decide
    · rw [cnotPauliString_of_ne _ i m hki hkm, zGenPauli_apply, ite_eq_right hkm, zPairPauli_apply,
        ite_eq_right (not_or.mpr ⟨hki, hkm⟩)]

/-! ### The CNOT layer acting on the seed generators -/

/-- **The X-spread of the CNOT layer** (Nielsen & Chuang Problem 10.3, building `A₁, A₂`):
applying the fan `cnotFan i ts` (distinct targets `ts`, none equal to `i`) to the `X`-seed `Xᵢ`
returns the multi-`X` string with an `X` on wire `i` and on every target — `xSetPauli (i :: ts)`.
Each `CNOT_{i→t}` copies the control's `X` onto the target (`x_t += x_c`), so the seed's single
`X` fans out; on the check matrix this makes row `i` equal to `(eᵢ + Σ_{t∈ts} e_t | 0)`, the `I`
diagonal entry plus row `i` of the `X`-blocks. Proved by induction on `ts`. -/
theorem act_cnotFan_xGenPauli (i : Fin n) : ∀ (ts : List (Fin n)), i ∉ ts → ts.Nodup →
    CliffordCircuit.act (cnotFan i ts) (xGenPauli i) = xSetPauli (i :: ts)
  | [], _, _ => by
      funext k
      simp only [cnotFan_nil, CliffordCircuit.act, xGenPauli_apply, xSetPauli_apply,
        List.mem_singleton]
  | t :: ts, h, hnd => by
      rw [List.mem_cons, not_or] at h
      obtain ⟨hit, hts⟩ := h
      obtain ⟨htnotin, hnd'⟩ := List.nodup_cons.mp hnd
      rw [act_cnotFan_cons_of_ne hit, act_cnotFan_xGenPauli i ts hts hnd']
      have hgi : xSetPauli (i :: ts) i = 1 := by simp [xSetPauli_apply]
      have htmem : t ∉ i :: ts := by
        simp only [List.mem_cons, not_or]; exact ⟨Ne.symm hit, htnotin⟩
      have hgt : xSetPauli (i :: ts) t = 0 := by simp [xSetPauli_apply, htmem]
      funext k
      rcases eq_or_ne k i with rfl | hki
      · rw [cnotPauliString_ctrl, hgi, hgt, xSetPauli_apply, ite_eq_left (by simp)]; decide
      · rcases eq_or_ne k t with rfl | hkt
        · rw [cnotPauliString_tgt _ hit, hgi, hgt, xSetPauli_apply, ite_eq_left (by simp)]; decide
        · rw [cnotPauliString_of_ne _ i t hki hkt, xSetPauli_apply, xSetPauli_apply]
          have hmem : (k ∈ i :: t :: ts) ↔ (k ∈ i :: ts) := by simp [List.mem_cons, hkt]
          simp only [hmem]

/-- **The CNOT layer fixes a pure-`Z` generator off its target set** (`m ∉ ts`): a `Z` on a wire
the fan neither controls (`m` may be `i`) nor targets is left unchanged. Every target of the fan
is `I` in `Z_m`, so no `Z` is ever copied onto the control, and the control's `Z`-bit is likewise
undisturbed. Proved by induction on `ts` via `cnotPauliString_fixed`. -/
theorem act_cnotFan_zGenPauli_of_not_mem (i : Fin n) :
    ∀ (ts : List (Fin n)), i ∉ ts → ts.Nodup →
      ∀ (m : Fin n), m ∉ ts → CliffordCircuit.act (cnotFan i ts) (zGenPauli m) = zGenPauli m
  | [], _, _, _, _ => rfl
  | t :: ts, h, hnd, m, hm => by
      rw [List.mem_cons, not_or] at h hm
      obtain ⟨hit, hts⟩ := h
      obtain ⟨hmt, hmts⟩ := hm
      obtain ⟨_, hnd'⟩ := List.nodup_cons.mp hnd
      rw [act_cnotFan_cons_of_ne hit, act_cnotFan_zGenPauli_of_not_mem i ts hts hnd' m hmts]
      apply cnotPauliString_fixed hit
      · rw [zGenPauli_apply, ite_eq_right (Ne.symm hmt)]
      · rcases eq_or_ne i m with rfl | hh
        · exact Or.inr (by simp [zGenPauli_apply])
        · exact Or.inl (by simp [zGenPauli_apply, hh])

/-- **The coupled transpose of the CNOT layer** (Nielsen & Chuang Problem 10.3, building `A₂ᵀ` /
`A₁ᵀ`): applying the fan `cnotFan i ts` (distinct targets, none equal to `i`) to a pure-`Z`
generator `Z_m` with `m ∈ ts` returns `Z_i Z_m` (`zPairPauli i m`). The one gate `CNOT_{i→m}`
copies the target's `Z` back onto the control (`z_i += z_m`), depositing a `Z` on wire `i`; the
other gates of the fan leave it fixed. On the check matrix this puts a `1` in column `i` of row
`m`'s `Z`-part — the transposed entry. Iterated over the top controls `i`, this builds the whole
`A₂ᵀ` block of the bottom encoded-`Z` rows (and `A₁ᵀ` of the middle rows). Proved by induction on
`ts` via the single-gate coupling and `act_cnotFan_zGenPauli_of_not_mem`. -/
theorem act_cnotFan_zGenPauli_of_mem (i : Fin n) :
    ∀ (ts : List (Fin n)), i ∉ ts → ts.Nodup →
      ∀ (m : Fin n), m ∈ ts →
        CliffordCircuit.act (cnotFan i ts) (zGenPauli m) = zPairPauli i m
  | [], _, _, m, hm => by simp at hm
  | t :: ts, h, hnd, m, hm => by
      rw [List.mem_cons, not_or] at h
      obtain ⟨hit, hts⟩ := h
      obtain ⟨htnotin, hnd'⟩ := List.nodup_cons.mp hnd
      rw [act_cnotFan_cons_of_ne hit]
      rcases List.mem_cons.mp hm with rfl | hmts
      · rw [act_cnotFan_zGenPauli_of_not_mem i ts hts hnd' m htnotin]
        exact cnotPauliString_zGenPauli_couple hit
      · have hmt : m ≠ t := fun e => htnotin (e ▸ hmts)
        rw [act_cnotFan_zGenPauli_of_mem i ts hts hnd' m hmts]
        apply cnotPauliString_fixed hit
        · rw [zPairPauli_apply, ite_eq_right (not_or.mpr ⟨Ne.symm hit, Ne.symm hmt⟩)]
        · exact Or.inr (by rw [zPairPauli_apply, ite_eq_left (Or.inl rfl)])

/-! ### Check-matrix readings -/

/-- The check row of a multi-`X` string is `(1_S | 0)`: a `1` in each `X`-column of `S`, no
`Z`-part. -/
theorem checkRow_xSetPauli (S : List (Fin n)) :
    checkRow (xSetPauli S) = (fun k => if k ∈ S then (1 : ZMod 2) else 0, 0) := by
  ext k <;> by_cases hk : k ∈ S <;>
    simp [checkRow, xSetPauli, pauliBit, pauliXBit, pauliZBit, hk]

/-- The check row of `Z_i Z_m` is `(0 | 1_{i} + 1_{m})`: no `X`-part, a `1` in `Z`-columns `i`
and `m`. -/
theorem checkRow_zPairPauli (i m : Fin n) :
    checkRow (zPairPauli i m) = (0, fun k => if k = i ∨ k = m then (1 : ZMod 2) else 0) := by
  ext k <;> by_cases hk : k = i ∨ k = m <;>
    simp [checkRow, zPairPauli, pauliBit, pauliXBit, pauliZBit, hk]

/-- **The X-spread in check-matrix terms.** After the CNOT fan, row `i` of the check matrix is
`(1_{i :: ts} | 0)` — the `X`-part carries a `1` in column `i` (the `I` diagonal) and in each
column of the target set (the `A₁, A₂` entries of row `i`), and there is no `Z`-part. -/
theorem checkRow_act_cnotFan_xGenPauli (i : Fin n) (ts : List (Fin n)) (h : i ∉ ts)
    (hnd : ts.Nodup) :
    checkRow (CliffordCircuit.act (cnotFan i ts) (xGenPauli i))
      = (fun k => if k ∈ i :: ts then (1 : ZMod 2) else 0, 0) := by
  rw [act_cnotFan_xGenPauli i ts h hnd, checkRow_xSetPauli]

/-- **The coupled transpose in check-matrix terms.** After the CNOT fan, the row of the
encoded-`Z` generator `Z_m` (`m ∈ ts`) is `(0 | 1_i + 1_m)` — the identity-block `1` in
`Z`-column `m` plus the transposed `1` deposited in `Z`-column `i` (an entry of `A₂ᵀ` / `A₁ᵀ`). -/
theorem checkRow_act_cnotFan_zGenPauli_of_mem (i : Fin n) (ts : List (Fin n)) (h : i ∉ ts)
    (hnd : ts.Nodup) (m : Fin n) (hm : m ∈ ts) :
    checkRow (CliffordCircuit.act (cnotFan i ts) (zGenPauli m))
      = (0, fun k => if k = i ∨ k = m then (1 : ZMod 2) else 0) := by
  rw [act_cnotFan_zGenPauli_of_mem i ts h hnd m hm, checkRow_zPairPauli]

/-! ### Operator-level readings (through the backbone) -/

/-- **Operator-level X-spread**, through `CliffordCircuit.conj_pauliString`: the CNOT fan is a
unitary Clifford circuit conjugating the Pauli operator `P_{Xᵢ}` to a nonzero (`±1`,
`CliffordCircuit.sign_ne_zero`) scalar multiple of the multi-`X` operator
`P_{xSetPauli (i :: ts)}` — the physical content of `act_cnotFan_xGenPauli`. -/
theorem cnotFan_conj_xGenPauli (i : Fin n) (ts : List (Fin n)) (h : i ∉ ts) (hnd : ts.Nodup) :
    CliffordCircuit.toMatrix (cnotFan i ts) * pauliString (xGenPauli i)
        * (CliffordCircuit.toMatrix (cnotFan i ts))ᴴ
      = CliffordCircuit.sign (cnotFan i ts) (xGenPauli i)
        • pauliString (xSetPauli (i :: ts)) := by
  rw [CliffordCircuit.conj_pauliString, act_cnotFan_xGenPauli i ts h hnd]

/-- **Operator-level coupled transpose**, through `CliffordCircuit.conj_pauliString`: for
`m ∈ ts` the CNOT fan conjugates `P_{Z_m}` to a nonzero (`±1`) scalar multiple of `P_{Z_i Z_m}` —
the physical content of `act_cnotFan_zGenPauli_of_mem`. -/
theorem cnotFan_conj_zGenPauli_of_mem (i : Fin n) (ts : List (Fin n)) (h : i ∉ ts)
    (hnd : ts.Nodup) (m : Fin n) (hm : m ∈ ts) :
    CliffordCircuit.toMatrix (cnotFan i ts) * pauliString (zGenPauli m)
        * (CliffordCircuit.toMatrix (cnotFan i ts))ᴴ
      = CliffordCircuit.sign (cnotFan i ts) (zGenPauli m) • pauliString (zPairPauli i m) := by
  rw [CliffordCircuit.conj_pauliString, act_cnotFan_zGenPauli_of_mem i ts h hnd m hm]

end AxQM.Concrete

end
