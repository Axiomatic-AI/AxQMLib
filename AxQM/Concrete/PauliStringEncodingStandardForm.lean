/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringEncodingStandardFormCore
import AxQM.Concrete.PauliStringEncodingPhaseCZNetwork

/-!
# Concrete: the stabilizer encoding circuit `G (10.124) → standard form (10.125)`
(N&C, Problem 10.3)

This file completes the **synthesis** half of Nielsen & Chuang **Problem 10.3** ("encoding
stabilizer codes"): a Clifford circuit that carries the *trivial* check matrix `G` of Eq. (10.124)
— a listing of the single-qubit generators `Z₁, …, Zₙ`, i.e. every row `(0 | eᵢ)`, the stabilizer
of `|0⟩⊗ⁿ` — to the **standard form** of Eq. (10.125),

```
      r     n-k-r   k  |  r     n-k-r  k
   ┌  I     A₁     A₂  |  B      0     C₂ ┐   ← r      pivot (top) generator rows
   │  0     0      0   |  D      I     E  │   ← n-k-r  middle generator rows
   └  0     0      0   |  A₂ᵀ    0     I  ┘   ← k      encoded-Z rows
```

The circuit is the three composed layers introduced across this sub-project:

  `encodingCircuit D ws pairs = phaseCZNetwork ws pairs ++ encodingCnotHad D`,

read right-to-left (`CliffordCircuit.act_append`): the **CNOT + Hadamard core** `encodingCnotHad D`
(`PauliStringEncodingStandardFormCore.lean`) acts first, then the **phase / controlled-`Z` network**
`phaseCZNetwork ws pairs` (`PauliStringEncodingPhaseCZNetwork.lean`) acts last.

## What the two stages contribute

The core `encodingCnotHad D` already deposits every `X`-block and every *coupled* `Z`-block of
(10.125): the top rows' `X`-part `[I A₁ A₂]` (with `Z`-part still `0`), the middle rows `[D I E]`
with the standard-form coupling `D = A₁ᵀ + E A₂ᵀ`, and the encoded-`Z` rows `[A₂ᵀ 0 I]`. The only
blocks left are the **top rows' residual `Z`-blocks `B`, `C₂`**, which the phase/`CZ` network
deposits. Crucially the phase and `CZ` gates only *add* a `Z` reading `X`-bits they never change
(`z += x`), so:

* on the **middle** and **encoded-`Z`** rows, whose `X`-part is identically `0`, the whole
  phase/`CZ`
  network is the identity (`phaseCZ_fix`): those rows are left exactly as the core produced them —
  `[0 | D I E]` and `[0 | A₂ᵀ 0 I]`;
* on the **pivot** rows, whose `X`-part is `[I A₁ A₂]`, the network deposits the top `Z`-blocks
  `B` (diagonal via the phase layer `sLayer`, off-diagonal via `CZ` between two pivots) and `C₂`
  (via
  `CZ` between a pivot and an encoded wire). Restricting the phase/`CZ` data to the pivot and
  encoded
  wires (`ws`, `pairs` avoid the middle wires) keeps the middle `Z`-block of the top rows `0`
  (`phaseCZZ_middle_eq_zero`) — the `0` of `[B 0 C₂]`.

## What is proved

For any partition data `D : StdFormData n` and phase/`CZ` data `ws`, `pairs`:

* `checkRow_encodingCircuit_middle` / `_data` — the middle / encoded-`Z` rows equal the ones the
  core
  produced (the phase/`CZ` layer fixes them): `[0 | D I E]`, `[0 | A₂ᵀ 0 I]`.
* `checkRow_encodingCircuit_pivot` — a pivot row `p` becomes
  `(eₚ + 𝟙_{tgt p} | phaseCZZ ws pairs …)`:
  the `X`-blocks `[I A₁ A₂]` unchanged and the top `Z`-blocks `B`, `C₂` deposited as the explicit
  symmetric phase/`CZ` form `phaseCZZ`.
* `phaseCZZ_middle_eq_zero` — the deposited `Z`-block vanishes on the middle columns when `ws`,
  `pairs`
  avoid the middle wires: the top rows are `[I A₁ A₂ | B 0 C₂]`, the standard form (10.125).
* `encodingCircuit_conj_pauliString` — the **operator (unitary) reading**: the encoding circuit's
  unitary conjugates each trivial generator `P_{Zᵢ}` to `± P_{row i}`, i.e. maps the `|0⟩⊗ⁿ`
  stabilizer to the code's standard-form stabilizer up to sign (`CliffordCircuit.conj_pauliString`,
  the phase nonzero by `sign_ne_zero`).
* `phaseCZZ_of_symm` / `encodingCircuit_standardForm_achievable` — the **achievability** (pinnacle
  claim): the phase/`CZ` deposit realizes every symmetric `𝔽₂`-bilinear form (`phaseCZZ_of_symm`),
  so
  for **any** standard-form code (`A₁, A₂, E` via `D`, and `B`, `C₂` with the top-row
  commutation
  relation) there *exists* phase/`CZ` data whose encoding circuit carries `G` (10.124) to that
  code's
  (10.125) with **exactly** its blocks. The witness `ws = phaseWires G`, `pairs = czPairs G` is read
  off the symmetric phase matrix `G` built from `B`, `C₂`, `A₂`.

The three blocks `A₁, A₂, E` (hence `D`) are already general in the core (`tgt` arbitrary), and the
**achievability** theorem `encodingCircuit_standardForm_achievable` proves the remaining blocks `B`,
`C₂` are too: for any code in standard form — `B` (pivot × pivot), `C₂` (pivot × data) satisfying
the
top-row commutation relation `B + Bᵀ = A₂ C₂ᵀ + C₂ A₂ᵀ` — *some* choice of `ws`, `pairs` (avoiding
the
middle wires) makes the encoding circuit carry `G` (10.124) to exactly its (10.125). The witness is
the symmetric phase matrix `G` with `G_{PΔ} = C₂`, `G_{PP} = B + A₂ C₂ᵀ` (symmetric by the relation)
and `G_{ΔΔ} = 0`: `phaseCZZ_of_symm` shows the phase/`CZ` deposit is then the bilinear form
`k ↦ Σₗ G k l xₗ`, and the `A₂ C₂ᵀ` contamination the pivot–data `CZ`s inject into the `B`-block
cancels mod `2`.

Everything is stated for raw index / matrix data (`Concrete.CliffordCircuit`, `Fin n → Fin 4`,
`ZMod 2`). The statement of Problem 10.3 is in
`AxQM/NC/Ch10/Problem10_3_EncodingStabilizer.lean`.

## Design notes

* `ws`, `pairs` are taken as explicit arguments alongside `D : StdFormData n` (which is frozen)
  rather
  than bundled: the two families are the free data (`B`, `C₂`), and keeping them separate lets the
  read-offs and the middle-vanishing lemma quantify over them cleanly.
* The phase/`CZ` deposit is packaged once as `phaseCZZ ws pairs x` — evaluated on the pivot `X`-row
  it
  is the top `Z`-block. Its closed form is obtained from the fold `sCol ws (foldr czCol …)` of
  `checkRow_act_phaseCZNetwork` via the single closed-form fold lemma `czCol_foldr`, which rewrites
  the
  whole right fold to one pair `(r.1, …)`: the `X`-part is invariant (so every `CZ` reads the
  *same*
  `X`-row) and the `Z`-part accumulates the per-pair contributions.
* `phaseCZ_fix` (the network fixes an `X`-free row) is the "no interference" fact for the middle /
  encoded rows; it is `czCol_foldr_fixed` (each `CZ` fixes an `X`-free row, `czCol_fixed`) then
  `sCol_fix` (the phase layer likewise).
-/

namespace AxQM.Concrete

open Matrix

variable {n : ℕ}

/-! ### Folding the phase / controlled-`Z` column operations -/

/-- **The controlled-`Z` fold in closed form**: the right fold of `czCol` over `pairs` starting from
`r` keeps the `X`-part `r.1` (every `CZ` reads it and never changes it) and adds to each `Z`-bit
`r.2 k` the sum over pairs `(c, t)` of `[k = c] x_t + [k = t] x_c`, every `X`-bit read against the
input `r.1`. Since the whole fold is rewritten to an explicit pair, the `X`-invariance and the
`Z`-accumulation are one lemma. -/
theorem czCol_foldr (pairs : List (Fin n × Fin n)) (r : (Fin n → ZMod 2) × (Fin n → ZMod 2)) :
    pairs.foldr (fun p r => czCol p.1 p.2 r) r
      = (r.1, fun k => r.2 k + (pairs.map
          (fun p => (if k = p.1 then r.1 p.2 else 0) + (if k = p.2 then r.1 p.1 else 0))).sum) := by
  induction pairs with
  | nil => ext k <;> simp
  | cons p ps ih =>
      rw [List.foldr_cons, ih]
      refine Prod.ext rfl ?_
      funext k
      simp only [czCol, List.map_cons, List.sum_cons]
      ring

/-- **A controlled-`Z` fold fixes an `X`-free row**: if `r.1 = 0` then the right fold of `czCol`
over
any `pairs` is `r` (each `CZ` fixes an `X`-free row, `czCol_fixed`). -/
theorem czCol_foldr_fixed (pairs : List (Fin n × Fin n))
    {r : (Fin n → ZMod 2) × (Fin n → ZMod 2)} (hr : r.1 = 0) :
    pairs.foldr (fun p r => czCol p.1 p.2 r) r = r := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
      rw [List.foldr_cons, ih]
      exact czCol_fixed p.1 p.2 (by rw [hr]; rfl) (by rw [hr]; rfl)

/-- **The phase layer fixes an `X`-free row**: if `r.1 = 0` then `sCol ws r = r` (nothing is added
to
any `Z`-bit). -/
theorem sCol_fix (ws : List (Fin n)) {r : (Fin n → ZMod 2) × (Fin n → ZMod 2)} (hr : r.1 = 0) :
    sCol ws r = r := by
  ext k <;> simp [sCol, hr]

/-- **The phase / controlled-`Z` network fixes an `X`-free row** (N&C Problem 10.3): if `r.1 = 0`
then
`sCol ws (foldr czCol r) = r`. This is the "no interference" fact used on the middle and encoded-`Z`
rows of (10.125), whose `X`-part vanishes, so the phase/`CZ` layer leaves them exactly as the CNOT +
Hadamard core produced them. -/
theorem phaseCZ_fix (ws : List (Fin n)) (pairs : List (Fin n × Fin n))
    {r : (Fin n → ZMod 2) × (Fin n → ZMod 2)} (hr : r.1 = 0) :
    sCol ws (pairs.foldr (fun p r => czCol p.1 p.2 r) r) = r := by
  rw [czCol_foldr_fixed pairs hr, sCol_fix ws hr]

/-! ### The deposited top-row `Z`-block -/

/-- **The top-row `Z`-block deposited by the phase / controlled-`Z` network** on a check row with
`X`-part `x` (N&C Problem 10.3): a diagonal phase contribution `[k ∈ ws] x_k` (the diagonal of `B`)
plus the symmetric off-diagonal contribution of each `CZ` pair `(c, t)`, `[k = c] x_t + [k = t] x_c`
(off-diagonal `B` between two pivots, `C₂` between a pivot and an encoded wire). Evaluated on a
pivot
row's `X`-part `[I A₁ A₂]` it is the top rows' `Z`-block `[B 0 C₂]`. -/
def phaseCZZ (ws : List (Fin n)) (pairs : List (Fin n × Fin n)) (x : Fin n → ZMod 2) :
    Fin n → ZMod 2 :=
  fun k => (if k ∈ ws then x k else 0)
    + (pairs.map (fun p => (if k = p.1 then x p.2 else 0) + (if k = p.2 then x p.1 else 0))).sum

/-- The phase / controlled-`Z` network acting on a check row with `X`-part `x` and zero `Z`-part
deposits exactly `phaseCZZ ws pairs x`, keeping the `X`-part `x`. Combining the closed-form fold
`czCol_foldr` (the invariant `X`-part and the accumulated `Z`-part) with the phase-layer column
operation `sCol`. -/
theorem phaseCZ_apply (ws : List (Fin n)) (pairs : List (Fin n × Fin n)) (x : Fin n → ZMod 2) :
    sCol ws (pairs.foldr (fun p r => czCol p.1 p.2 r) (x, (0 : Fin n → ZMod 2)))
      = (x, phaseCZZ ws pairs x) := by
  rw [czCol_foldr]
  refine Prod.ext rfl ?_
  funext k
  simp only [sCol, phaseCZZ, Pi.zero_apply, zero_add]
  ring

/-! ### The stabilizer encoding circuit and its standard-form action -/

/-- **The stabilizer encoding circuit** (N&C Problem 10.3): the CNOT + Hadamard core followed
(acting last) by the phase / controlled-`Z` network, `phaseCZNetwork ws pairs ++ encodingCnotHad D`.
Read right-to-left, the Hadamards convert `Zₚ ↦ Xₚ` on the pivots, the CNOT network builds the
`X`-blocks and the coupled `Z`-blocks (`A₁, A₂, D, E, A₂ᵀ`), and the phase/`CZ` network deposits the
residual top-row `Z`-blocks `B`, `C₂`. Applied to the trivial check matrix `G` (10.124) it produces
the standard form (10.125). -/
def encodingCircuit (D : StdFormData n) (ws : List (Fin n)) (pairs : List (Fin n × Fin n)) :
    CliffordCircuit n :=
  phaseCZNetwork ws pairs ++ encodingCnotHad D

/-- **The encoding circuit fixes the middle rows** `[0 | D I E]` (N&C (10.125)): for a middle wire
`m`, the phase/`CZ` layer leaves the core's output unchanged (that row has zero `X`-part), so the
whole circuit gives the same row as the CNOT + Hadamard core. -/
theorem checkRow_encodingCircuit_middle (D : StdFormData n) (ws : List (Fin n))
    (pairs : List (Fin n × Fin n)) (hws : ws.Nodup) (hpairs : ∀ p ∈ pairs, p.1 ≠ p.2)
    {m : Fin n} (hm : m ∈ D.middle) :
    checkRow (CliffordCircuit.act (encodingCircuit D ws pairs) (zGenPauli m))
      = checkRow (CliffordCircuit.act (encodingCnotHad D) (zGenPauli m)) := by
  rw [encodingCircuit, CliffordCircuit.act_append, checkRow_act_phaseCZNetwork ws pairs hws hpairs]
  exact phaseCZ_fix ws pairs (by rw [checkRow_encodingCnotHad_middle D hm])

/-- **The encoding circuit fixes the encoded-`Z` rows** `[0 | A₂ᵀ 0 I]` (N&C (10.125)): for an
encoded wire `d`, the phase/`CZ` layer leaves the core's output unchanged (that row has zero
`X`-part), so the whole circuit gives the same row as the CNOT + Hadamard core. -/
theorem checkRow_encodingCircuit_data (D : StdFormData n) (ws : List (Fin n))
    (pairs : List (Fin n × Fin n)) (hws : ws.Nodup) (hpairs : ∀ p ∈ pairs, p.1 ≠ p.2)
    {d : Fin n} (hd : d ∈ D.dataWires) :
    checkRow (CliffordCircuit.act (encodingCircuit D ws pairs) (zGenPauli d))
      = checkRow (CliffordCircuit.act (encodingCnotHad D) (zGenPauli d)) := by
  rw [encodingCircuit, CliffordCircuit.act_append, checkRow_act_phaseCZNetwork ws pairs hws hpairs]
  exact phaseCZ_fix ws pairs (by rw [checkRow_encodingCnotHad_data D hd])

/-- **The encoding circuit builds the top rows' `Z`-blocks `[B 0 C₂]`** (N&C (10.125)): for a pivot
wire `p`, the circuit carries the seed row `Zₚ` of `G` (10.124) to the check row
`(eₚ + 𝟙_{tgt p} | phaseCZZ ws pairs (eₚ + 𝟙_{tgt p}))`. The CNOT + Hadamard core built the
`X`-blocks `[I A₁ A₂]` with `Z`-part `0`; the phase/`CZ` network reads that `X`-part and deposits
the
top `Z`-blocks `B`, `C₂` as `phaseCZZ`. (Their middle columns vanish once `ws`, `pairs` avoid the
middle wires — `phaseCZZ_middle_eq_zero` — giving the `0` of `[B 0 C₂]`.) -/
theorem checkRow_encodingCircuit_pivot (D : StdFormData n) (ws : List (Fin n))
    (pairs : List (Fin n × Fin n)) (hws : ws.Nodup) (hpairs : ∀ p ∈ pairs, p.1 ≠ p.2)
    {p : Fin n} (hp : p ∈ D.pivots) :
    checkRow (CliffordCircuit.act (encodingCircuit D ws pairs) (zGenPauli p))
      = (fun k => (if k = p then (1 : ZMod 2) else 0) + (if k ∈ D.tgt p then 1 else 0),
         phaseCZZ ws pairs
           (fun k => (if k = p then (1 : ZMod 2) else 0) + (if k ∈ D.tgt p then 1 else 0))) := by
  rw [encodingCircuit, CliffordCircuit.act_append, checkRow_act_phaseCZNetwork ws pairs hws hpairs,
    checkRow_encodingCnotHad_pivot D hp, phaseCZ_apply]

/-- **The deposited top-row `Z`-block vanishes on the middle columns** (the `0` of `[B 0 C₂]`, N&C
(10.125)): if the phase/`CZ` data `ws`, `pairs` avoid the middle wires, then `phaseCZZ ws pairs x`
is `0` on every middle wire. Together with `checkRow_encodingCircuit_pivot` this exhibits the top
rows as `[I A₁ A₂ | B 0 C₂]` — the middle `Z`-block is `0`. -/
theorem phaseCZZ_middle_eq_zero (D : StdFormData n) (ws : List (Fin n))
    (pairs : List (Fin n × Fin n)) (x : Fin n → ZMod 2)
    (hws : ∀ w ∈ ws, w ∉ D.middle)
    (hpairs : ∀ p ∈ pairs, p.1 ∉ D.middle ∧ p.2 ∉ D.middle)
    {m : Fin n} (hm : m ∈ D.middle) : phaseCZZ ws pairs x m = 0 := by
  have hmws : m ∉ ws := fun h => hws m h hm
  simp only [phaseCZZ]
  rw [ite_eq_right hmws, zero_add]
  apply List.sum_eq_zero
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  obtain ⟨h1, h2⟩ := hpairs p hp
  have hp1 : m ≠ p.1 := by rintro rfl; exact h1 hm
  have hp2 : m ≠ p.2 := by rintro rfl; exact h2 hm
  rw [ite_eq_right hp1, ite_eq_right hp2, add_zero]

/-- **The operator (unitary) reading of the encoding circuit** (N&C Problem 10.3): the unitary
`(encodingCircuit D ws pairs).toMatrix` conjugates each trivial stabilizer generator `P_{Zᵢ}` of `G`
(10.124) to `± P_{row i}`, the Pauli operator whose check row is the standard-form row `i` of
(10.125) (given by `checkRow_encodingCircuit_pivot` / `_middle` / `_data`). The `±1` phase
`(encodingCircuit D ws pairs).sign (zGenPauli i)` is nonzero (`CliffordCircuit.sign_ne_zero`),
so this
is a genuine unitary encoding taking the `|0⟩⊗ⁿ` stabilizer to the code's standard-form stabilizer
up
to sign. Specializes the Clifford backbone `CliffordCircuit.conj_pauliString`. -/
theorem encodingCircuit_conj_pauliString (D : StdFormData n) (ws : List (Fin n))
    (pairs : List (Fin n × Fin n)) (i : Fin n) :
    (encodingCircuit D ws pairs).toMatrix * pauliString (zGenPauli i)
        * (encodingCircuit D ws pairs).toMatrix.conjTranspose
      = (encodingCircuit D ws pairs).sign (zGenPauli i)
        • pauliString ((encodingCircuit D ws pairs).act (zGenPauli i)) :=
  CliffordCircuit.conj_pauliString _ _

/-! ### Realizing an arbitrary symmetric phase form — achievability of every top `Z`-block

The read-offs above compute the action of `encodingCircuit D ws pairs` for *given* phase/`CZ` data.
This last section proves the **achievability** direction of N&C Problem 10.3: for an arbitrary valid
standard form, *some* member of the circuit family carries `G` (10.124) to it with **exactly** the
prescribed blocks. The pivot deposit `phaseCZZ ws pairs` is `𝔽₂`-linear in the `X`-row, and choosing
`(ws, pairs)` from a symmetric matrix `G` realizes the symmetric bilinear form `k ↦ ∑ₗ G k l · xₗ`
(`phaseCZZ_of_symm`); a code's `(B, C₂)` (with the top-row commutation relation
`B + Bᵀ = A₂C₂ᵀ + C₂A₂ᵀ`) is then hit by `G` with `G_{PΔ} = C₂`, `G_{PP} = B + A₂C₂ᵀ` (symmetric
by the
relation) and `G_{ΔΔ} = 0` — the `A₂C₂ᵀ` contamination the pivot–data `CZ`s inject into the
`B`-block
cancels mod `2` (`encodingCircuit_standardForm_achievable`). -/

/-- Every element of `ZMod 2` is `0` or `1`. -/
theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

/-- In `ZMod 2`, `if a = 1 then x else 0` is `a * x`. -/
theorem zmod2_ite_eq_one_mul (a x : ZMod 2) : (if a = 1 then x else 0) = a * x := by
  rcases zmod2_eq_zero_or_one a with h | h <;> subst h <;> simp

/-- **The phase wires realizing a phase matrix `G`**: the wires carrying a diagonal `1` of `G`
(one `S` gate each, depositing the diagonal of the top `Z`-block). -/
noncomputable def phaseWires (G : Fin n → Fin n → ZMod 2) : List (Fin n) :=
  (Finset.univ.filter (fun k => G k k = 1)).toList

/-- **The controlled-`Z` pairs realizing a phase matrix `G`**: the strictly-ordered pairs `(c, t)`,
`c < t`, carrying an off-diagonal `1` of `G` (one `CZ` each; every unordered pair listed once). -/
noncomputable def czPairs (G : Fin n → Fin n → ZMod 2) : List (Fin n × Fin n) :=
  (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G p.1 p.2 = 1)).toList

theorem mem_phaseWires {G : Fin n → Fin n → ZMod 2} {k : Fin n} : k ∈ phaseWires G ↔ G k k = 1 := by
  simp [phaseWires]

theorem phaseWires_nodup (G : Fin n → Fin n → ZMod 2) : (phaseWires G).Nodup :=
  Finset.nodup_toList _

theorem mem_czPairs {G : Fin n → Fin n → ZMod 2} {p : Fin n × Fin n} :
    p ∈ czPairs G ↔ p.1 < p.2 ∧ G p.1 p.2 = 1 := by
  simp [czPairs]

theorem czPairs_nodup (G : Fin n → Fin n → ZMod 2) : (czPairs G).Nodup :=
  Finset.nodup_toList _

theorem czPairs_ne {G : Fin n → Fin n → ZMod 2} {p : Fin n × Fin n} (hp : p ∈ czPairs G) :
    p.1 ≠ p.2 := ne_of_lt (mem_czPairs.mp hp).1

open Finset in
/-- **The controlled-`Z` pair contribution of `czPairs G` is a symmetric matrix row.** For symmetric
`G`, the per-pair `CZ` deposit at wire `k` — `Σ_{(c,t)∈czPairs G} ([k=c] x_t + [k=t] x_c)` — equals
`Σ_{l≠k} G k l · x l`: each unordered pair `{k, l}` with `G k l = 1` contributes `x l` exactly
once. -/
theorem czPairs_sum (G : Fin n → Fin n → ZMod 2) (hsymm : ∀ a b, G a b = G b a)
    (x : Fin n → ZMod 2) (k : Fin n) :
    ((czPairs G).map
        (fun p => (if k = p.1 then x p.2 else 0) + (if k = p.2 then x p.1 else 0))).sum
      = ∑ l ∈ univ.filter (fun l => l ≠ k), G k l * x l := by
  classical
  rw [czPairs, Finset.sum_map_toList]
  -- RHS: restrict to `G k l = 1` (where the summand is nonzero)
  rw [show (∑ l ∈ univ.filter (fun l => l ≠ k), G k l * x l)
        = ∑ l ∈ univ.filter (fun l => l ≠ k ∧ G k l = 1), x l from by
      conv_rhs => rw [← Finset.filter_filter, Finset.sum_filter]
      exact Finset.sum_congr rfl (fun l _ => (zmod2_ite_eq_one_mul (G k l) (x l)).symm)]
  -- LHS: restrict to pairs touching `k` (the only ones contributing)
  rw [show (∑ p ∈ univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G p.1 p.2 = 1),
          ((if k = p.1 then x p.2 else 0) + (if k = p.2 then x p.1 else 0)))
        = ∑ p ∈ (univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G p.1 p.2 = 1)).filter
            (fun p => p.1 = k ∨ p.2 = k),
            ((if k = p.1 then x p.2 else 0) + (if k = p.2 then x p.1 else 0)) from by
      symm
      apply Finset.sum_filter_of_ne
      intro p _ hfp
      by_contra hcon
      exact hfp (by rw [ite_eq_right (fun h => hcon (Or.inl h.symm)),
        ite_eq_right (fun h => hcon (Or.inr h.symm)), add_zero])]
  -- bijection: a touching pair ↦ its non-`k` endpoint
  refine Finset.sum_bij'
    (fun p _ => if p.1 = k then p.2 else p.1)
    (fun l _ => if k < l then (k, l) else (l, k)) ?_ ?_ ?_ ?_ ?_
  · -- forward maps into the endpoint set
    rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    obtain ⟨⟨hlt, hG⟩, htouch⟩ := hp
    rcases htouch with h | h
    · subst h; rw [ite_eq_left rfl]
      exact ⟨(ne_of_lt hlt).symm, hG⟩
    · subst h
      have hak : a ≠ b := ne_of_lt hlt
      rw [ite_eq_right hak]
      exact ⟨hak, by rw [hsymm]; exact hG⟩
  · -- backward maps into the pair set
    intro l hl
    simp only [mem_filter, mem_univ, true_and] at hl ⊢
    obtain ⟨hne, hG⟩ := hl
    rcases lt_or_gt_of_ne (Ne.symm hne) with h | h
    · rw [ite_eq_left h]; exact ⟨⟨h, hG⟩, Or.inl rfl⟩
    · rw [ite_eq_right (not_lt.mpr (le_of_lt h))]; exact ⟨⟨h, by rw [hsymm]; exact hG⟩, Or.inr rfl⟩
  · -- left inverse
    rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_univ, true_and] at hp
    obtain ⟨⟨hlt, _⟩, htouch⟩ := hp
    rcases htouch with h | h
    · subst h; simp [hlt]
    · subst h; simp [ne_of_lt hlt, not_lt.mpr hlt.le]
  · -- right inverse
    intro l hl
    simp only [mem_filter, mem_univ, true_and] at hl
    obtain ⟨hne, _⟩ := hl
    rcases lt_or_gt_of_ne (Ne.symm hne) with h | h <;>
      simp [h, not_lt.mpr h.le, ne_of_lt h]
  · -- value equality
    rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_univ, true_and] at hp
    obtain ⟨⟨hlt, _⟩, htouch⟩ := hp
    rcases htouch with h | h
    · subst h; simp [ne_of_lt hlt]
    · subst h; simp [ne_of_lt hlt, (ne_of_lt hlt).symm]

open Finset in
/-- **The phase / controlled-`Z` deposit realizes any symmetric matrix as a bilinear form.** For
symmetric `G`, choosing `ws = phaseWires G` and `pairs = czPairs G` makes the top-row deposit
`phaseCZZ` at wire `k` the matrix row `Σₗ G k l · xₗ`. Thus the family of phase/`CZ` deposits is
exactly the symmetric `𝔽₂`-bilinear forms — the surjectivity that yields achievability of every
standard form. The diagonal `[k ∈ ws] xₖ` supplies the `k = l` term `G k k · xₖ`
(`zmod2_ite_eq_one_mul`); the off-diagonal `CZ` sum supplies `Σ_{l≠k} G k l · xₗ`
(`czPairs_sum`). -/
theorem phaseCZZ_of_symm (G : Fin n → Fin n → ZMod 2) (hsymm : ∀ a b, G a b = G b a)
    (x : Fin n → ZMod 2) (k : Fin n) :
    phaseCZZ (phaseWires G) (czPairs G) x k = ∑ l, G k l * x l := by
  simp only [phaseCZZ]
  rw [czPairs_sum G hsymm x k,
    show (if k ∈ phaseWires G then x k else 0) = G k k * x k from by
      by_cases h : G k k = 1
      · rw [ite_eq_left (mem_phaseWires.mpr h), h, one_mul]
      · rw [ite_eq_right (fun hm => h (mem_phaseWires.mp hm))]
        rcases zmod2_eq_zero_or_one (G k k) with h0 | h1
        · rw [h0, zero_mul]
        · exact absurd h1 h]
  conv_rhs => rw [← Finset.add_sum_erase univ (fun l => G k l * x l) (Finset.mem_univ k)]
  rw [Finset.filter_ne']

open Finset in
/-- **Achievability of every standard form** (N&C Problem 10.3, the pinnacle claim). For an
arbitrary
standard-form code — partition and `X`-blocks `A₁, A₂, E` fixed by `D : StdFormData n`, and top-row
`Z`-blocks `B` (pivot × pivot) and `C₂` (pivot × data) satisfying the top-row commutation relation
`B + Bᵀ = A₂C₂ᵀ + C₂A₂ᵀ` (`hcomm`, with `A₂ p d = [d ∈ tgt p]`) — there is a choice of phase/`CZ`
data `ws`, `pairs` (avoiding the middle wires) whose encoding circuit carries `G` (10.124) to
**exactly** the standard form (10.125): every pivot row `p` becomes
`(eₚ + 𝟙_{tgt p} | B_p, 0, C₂_p)`,
i.e. `[I A₁ A₂ | B 0 C₂]`. The witness is the symmetric phase matrix with `G_{PΔ} = C₂`,
`G_{PP} = B + A₂C₂ᵀ` (symmetric by `hcomm`) and `G_{ΔΔ} = 0`; the `A₂C₂ᵀ` contamination the
pivot–data
`CZ`s inject into the `B`-block cancels mod `2`. -/
theorem encodingCircuit_standardForm_achievable
    (D : StdFormData n) (B C₂ : Fin n → Fin n → ZMod 2)
    (hC₂ : ∀ q d, C₂ q d ≠ 0 → d ∈ D.dataWires)
    (hcomm : ∀ p ∈ D.pivots, ∀ q ∈ D.pivots,
        B p q + B q p
          = (∑ d, (if d ∈ D.tgt p then (1 : ZMod 2) else 0) * C₂ q d)
            + (∑ d, (if d ∈ D.tgt q then (1 : ZMod 2) else 0) * C₂ p d)) :
    ∃ ws pairs, ws.Nodup ∧ (∀ pr ∈ pairs, pr.1 ≠ pr.2)
      ∧ (∀ w ∈ ws, w ∉ D.middle)
      ∧ (∀ pr ∈ pairs, pr.1 ∉ D.middle ∧ pr.2 ∉ D.middle)
      ∧ ∀ p ∈ D.pivots,
        checkRow (CliffordCircuit.act (encodingCircuit D ws pairs) (zGenPauli p))
          = (fun k => (if k = p then (1 : ZMod 2) else 0) + (if k ∈ D.tgt p then 1 else 0),
             fun k => (if k ∈ D.pivots then B p k else 0)
               + (if k ∈ D.dataWires then C₂ p k else 0)) := by
  classical
  -- the accumulated `A₂C₂ᵀ` term and the symmetric phase matrix
  set Acc : Fin n → Fin n → ZMod 2 :=
    fun l k => ∑ d, (if d ∈ D.tgt l then (1 : ZMod 2) else 0) * C₂ k d with hAccdef
  set G : Fin n → Fin n → ZMod 2 := fun k l =>
    (if k ∈ D.pivots ∧ l ∈ D.pivots then B l k + Acc l k else 0)
    + (if k ∈ D.pivots ∧ l ∈ D.dataWires then C₂ k l else 0)
    + (if k ∈ D.dataWires ∧ l ∈ D.pivots then C₂ l k else 0) with hGdef
  -- `G` vanishes when either index is a middle wire
  have hGmid : ∀ k l, k ∈ D.middle ∨ l ∈ D.middle → G k l = 0 := by
    intro k l h
    simp only [hGdef]
    rcases h with h | h
    · have h1 : k ∉ D.pivots := fun hp => D.pivot_not_middle k hp h
      have h2 : k ∉ D.dataWires := fun hd => D.data_not_middle k hd h
      simp [h1, h2]
    · have h1 : l ∉ D.pivots := fun hp => D.pivot_not_middle l hp h
      have h2 : l ∉ D.dataWires := fun hd => D.data_not_middle l hd h
      simp [h1, h2]
  -- `G` is symmetric (the only nontrivial block uses `hcomm`)
  have hGsymm : ∀ k l, G k l = G l k := by
    intro k l
    simp only [hGdef]
    by_cases hkp : k ∈ D.pivots <;> by_cases hlp : l ∈ D.pivots
    · have hknd : k ∉ D.dataWires := D.pivot_not_data k hkp
      have hlnd : l ∉ D.dataWires := D.pivot_not_data l hlp
      simp only [hkp, hlp, hknd, hlnd, and_true, and_false, ite_true, ite_false, add_zero]
      -- goal: `B l k + Acc l k = B k l + Acc k l`, symmetric by the commutation relation `hcomm`
      have hAcc1 : Acc l k = ∑ d, (if d ∈ D.tgt l then (1 : ZMod 2) else 0) * C₂ k d := rfl
      have hAcc2 : Acc k l = ∑ d, (if d ∈ D.tgt k then (1 : ZMod 2) else 0) * C₂ l d := rfl
      have hc' : B k l + B l k = Acc k l + Acc l k := by
        rw [hAcc2, hAcc1]; exact hcomm k hkp l hlp
      have h0 : (B l k + Acc l k) + (B k l + Acc k l) = 0 := by
        rw [show (B l k + Acc l k) + (B k l + Acc k l)
            = (B k l + B l k) + (Acc k l + Acc l k) from by ring, hc', CharTwo.add_self_eq_zero]
      calc B l k + Acc l k
          = ((B l k + Acc l k) + (B k l + Acc k l)) + (B k l + Acc k l) := by
            rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        _ = B k l + Acc k l := by rw [h0, zero_add]
    · simp [hkp, hlp]
    · simp [hkp, hlp]
    · simp [hkp, hlp]
  refine ⟨phaseWires G, czPairs G, phaseWires_nodup G, fun pr hpr => czPairs_ne hpr, ?_, ?_, ?_⟩
  · intro w hw hwm
    have hw1 := mem_phaseWires.mp hw
    rw [hGmid w w (Or.inl hwm)] at hw1
    exact absurd hw1 (by decide)
  · intro pr hpr
    have hd := (mem_czPairs.mp hpr).2
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · rw [hGmid pr.1 pr.2 (Or.inl hm)] at hd; exact absurd hd (by decide)
    · rw [hGmid pr.1 pr.2 (Or.inr hm)] at hd; exact absurd hd (by decide)
  -- the standard-form pivot rows
  intro p hp
  rw [checkRow_encodingCircuit_pivot D _ _ (phaseWires_nodup G)
    (fun pr hpr => czPairs_ne hpr) hp]
  congr 1
  funext k
  rw [phaseCZZ_of_symm G hGsymm]
  -- `∑ₗ G k l · xₚ l = G k p + (contamination)`
  have hxsplit : (∑ l, G k l *
        ((if l = p then (1 : ZMod 2) else 0) + (if l ∈ D.tgt p then 1 else 0)))
      = G k p + ∑ l, G k l * (if l ∈ D.tgt p then 1 else 0) := by
    rw [Finset.sum_congr rfl (fun l _ => mul_add (G k l) _ _), Finset.sum_add_distrib]
    congr 1
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, ite_true]
  rw [hxsplit]
  -- for a fixed pivot `p`, `G k l = C₂ k l` on every fan target `l ∈ tgt p`
  by_cases hkp : k ∈ D.pivots
  · -- pivot column: `(B p k + Acc p k) + Acc p k = B p k`
    have hknd : k ∉ D.dataWires := D.pivot_not_data k hkp
    have hpnd : p ∉ D.dataWires := D.pivot_not_data p hp
    have hGkl : ∀ l, l ∉ D.pivots → G k l = if l ∈ D.dataWires then C₂ k l else 0 := by
      intro l hlnp
      simp only [hGdef, hkp, hlnp, hknd, true_and, and_false, ite_false, zero_add, add_zero]
    have hGkp : G k p = B p k + Acc p k := by
      simp only [hGdef, hkp, hp, hpnd, hknd, and_true, and_false, ite_true, ite_false, add_zero]
    have hGeqC : ∀ l, l ∈ D.tgt p → G k l = C₂ k l := by
      intro l hlt
      have hlnp : l ∉ D.pivots := fun hlp => (D.tgt_pivot_mem p hp l hlt).elim
        (D.pivot_not_middle l hlp) (D.pivot_not_data l hlp)
      rw [hGkl l hlnp]
      rcases D.tgt_pivot_mem p hp l hlt with hm | hd
      · rw [ite_eq_right (fun hh => D.data_not_middle l hh hm)]
        by_contra hc
        exact D.data_not_middle l (hC₂ k l (Ne.symm hc)) hm
      · rw [ite_eq_left hd]
    have hcontam : (∑ l, G k l * (if l ∈ D.tgt p then 1 else 0)) = Acc p k := by
      rw [hAccdef]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      by_cases hlt : l ∈ D.tgt p
      · rw [hGeqC l hlt]; simp [hlt, mul_comm]
      · simp [hlt]
    rw [hGkp, hcontam, ite_eq_left hkp, ite_eq_right hknd, add_zero, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  · by_cases hkd : k ∈ D.dataWires
    · -- data column: `C₂ p k + 0 = C₂ p k`
      have hGkp : G k p = C₂ p k := by
        simp only [hGdef, hkp, hkd, hp, false_and, and_true, ite_false, ite_true, zero_add,
            add_zero]
      have hcontam : (∑ l, G k l * (if l ∈ D.tgt p then 1 else 0)) = 0 := by
        refine Finset.sum_eq_zero (fun l _ => ?_)
        by_cases hlt : l ∈ D.tgt p
        · have hlnp : l ∉ D.pivots := fun hlp => (D.tgt_pivot_mem p hp l hlt).elim
            (D.pivot_not_middle l hlp) (D.pivot_not_data l hlp)
          have hz : G k l = 0 := by
            simp only [hGdef, hkp, hlnp, false_and, and_false, ite_false, add_zero]
          rw [hz, zero_mul]
        · rw [ite_eq_right hlt, mul_zero]
      rw [hGkp, hcontam, ite_eq_right hkp, ite_eq_left hkd, zero_add, add_zero]
    · -- middle (or other) column: everything vanishes
      have hGkp : G k p = 0 := by
        simp only [hGdef, hkp, hkd, false_and, ite_false, add_zero]
      have hcontam : (∑ l, G k l * (if l ∈ D.tgt p then 1 else 0)) = 0 := by
        refine Finset.sum_eq_zero (fun l _ => ?_)
        have hz : G k l = 0 := by simp only [hGdef, hkp, hkd, false_and, ite_false, add_zero]
        rw [hz, zero_mul]
      rw [hGkp, hcontam, ite_eq_right hkp, ite_eq_right hkd, add_zero]

end AxQM.Concrete
