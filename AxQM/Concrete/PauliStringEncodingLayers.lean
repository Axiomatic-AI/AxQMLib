/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCliffordCircuit
import AxQM.Concrete.CheckMatrix

/-!
# Concrete: the Hadamard layer of the stabilizer encoding circuit (Nielsen & Chuang, Problem 10.3)

This file begins the **synthesis** half of Nielsen & Chuang **Problem 10.3** ("encoding stabilizer
codes"): having established (in
`Concrete/PauliStringCliffordCircuit.lean`) that a `CliffordCircuit` conjugates a Pauli string to a
Pauli string and acts on the `n × 2n` **check matrix** by the composed elementary column operations,
we now build the specific circuit carrying the *trivial* check matrix `G` of Eq. (10.124) — a
listing of the single-qubit generators `Z₁, …, Zₙ` (X-part `0`, Z-part the identity) — to the
standard/encoded form of Eq. (10.125), one **layer** at a time. This file delivers the first layer.

The rows of the check matrix are individual Pauli strings (`Concrete.pauliString`,
`g : Fin n → Fin 4`); a circuit `U` acts on the whole matrix by applying its row action
`CliffordCircuit.act U` to each row. Two single-generator objects name the rows we start from and
pass through:

* `zGenPauli i` — the pure-`Z` generator `Zᵢ` (`Z` on wire `i`, `I` elsewhere): row `i` of the
  trivial matrix `G` (10.124), with check row `(0 | eᵢ)` (`checkRow_zGenPauli`).
* `xGenPauli i` — the pure-`X` generator `Xᵢ`, with check row `(eᵢ | 0)` (`checkRow_xGenPauli`).

## The Hadamard layer

`hadLayer ws` is the circuit applying a Hadamard to each wire in a list `ws : List (Fin n)`. Because
`H` swaps the `X`- and `Z`-bits of its wire (`pauliXBit_hadamardPauli` / `pauliZBit_hadamardPauli`),
this layer is exactly the **Hadamards on the first `r` qubits** that open the encoding circuit: on
the trivial matrix `G` it turns row `i` from `Zᵢ` into `Xᵢ` for every `i ∈ ws`, leaving the rest
untouched. Concretely, for a list of **distinct** wires (`ws.Nodup` — each chosen wire is
Hadamard'd once):

* `act_hadLayer` — its row action, `act (hadLayer ws) g k = hadamardPauli (g k)` for `k ∈ ws`, else
  `g k` (only the chosen wires are transformed);
* `act_hadLayer_zGenPauli` — the **first encoding-circuit layer**: `act (hadLayer ws) Zᵢ = Xᵢ` when
  `i ∈ ws`, else `Zᵢ`;
* `checkRow_act_hadLayer_zGenPauli` — the same in check-matrix terms: row `i` becomes `(eᵢ | 0)` for
  `i ∈ ws`, else `(0 | eᵢ)`. With `ws` the first `r` wires this is the transition from `G`
  (10.124, all rows `(0 | eᵢ)`) to the intermediate matrix with an `X`-identity block on top;
* `hadLayer_conj_zGenPauli` — the operator-level reading through the backbone
  `CliffordCircuit.conj_pauliString`: the layer is a unitary circuit conjugating `P_{Zᵢ}` to a
  nonzero (`±1`) multiple of `P_{Xᵢ}` / `P_{Zᵢ}` (`CliffordCircuit.sign_ne_zero`).

## Design notes

* `hadLayer ws = ws.map CliffordGate.had`, so `hadLayer` composes as list concatenation with the
  other layers and its `act`/`sign`/`toMatrix` are the existing `CliffordCircuit` folds — nothing
  new about circuits is introduced, only the specific gate list.
* `act_hadLayer` needs `ws.Nodup`: a wire appearing twice would be Hadamard'd twice, and although
  `hadamardPauli` is an involution the clean "transform exactly the wires in `ws`" statement is the
  one the encoding circuit uses (each of the first `r` qubits appears once). The `Nodup` is consumed
  only through the cons step `w ∉ ws`, which lets the final `Function.update` on wire `w` see the
  untouched value `g w`.
* The generators are `Function.update 0 i · ` on `Fin n → Fin 4` (`0 = I`, `1 = X`, `3 = Z`); their
  check rows are read off the single source of truth `pauliBit` of `Concrete/CheckMatrix.lean`.
-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### Single-generator Pauli strings (rows of the check matrix) -/

/-- The **pure-`Z` generator** `Zᵢ`: the Pauli string with `Z` on wire `i` and `I` on every other
wire (`Function.update 0 i 3`, using `0 = I`, `3 = Z`). Row `i` of the trivial check matrix `G` of
Nielsen & Chuang Eq. (10.124); its check row is `(0 | eᵢ)` (`checkRow_zGenPauli`). -/
def zGenPauli (i : Fin n) : Fin n → Fin 4 := Function.update 0 i 3

/-- The **pure-`X` generator** `Xᵢ`: the Pauli string with `X` on wire `i` and `I` on every other
wire (`Function.update 0 i 1`, using `0 = I`, `1 = X`). Its check row is `(eᵢ | 0)`
(`checkRow_xGenPauli`); it is the image of `Zᵢ` under a Hadamard on wire `i`. -/
def xGenPauli (i : Fin n) : Fin n → Fin 4 := Function.update 0 i 1

@[simp] theorem zGenPauli_apply (i k : Fin n) : zGenPauli i k = if k = i then 3 else 0 := by
  simp only [zGenPauli, Function.update_apply, Pi.zero_apply]

@[simp] theorem xGenPauli_apply (i k : Fin n) : xGenPauli i k = if k = i then 1 else 0 := by
  simp only [xGenPauli, Function.update_apply, Pi.zero_apply]

/-- The check row of the pure-`Z` generator is `(0 | eᵢ)`: no `X`-part, and a single `1` in column
`i` of the `Z`-part. This is row `i` of the trivial check matrix `G` of Eq. (10.124). -/
theorem checkRow_zGenPauli (i : Fin n) :
    checkRow (zGenPauli i) = (0, Pi.single i (1 : ZMod 2)) := by
  ext k <;> rcases eq_or_ne k i with rfl | hk <;>
    simp [checkRow, pauliBit, pauliXBit, pauliZBit, *]

/-- The check row of the pure-`X` generator is `(eᵢ | 0)`: a single `1` in column `i` of the
`X`-part, and no `Z`-part. -/
theorem checkRow_xGenPauli (i : Fin n) :
    checkRow (xGenPauli i) = (Pi.single i (1 : ZMod 2), 0) := by
  ext k <;> rcases eq_or_ne k i with rfl | hk <;>
    simp [checkRow, pauliBit, pauliXBit, pauliZBit, *]

/-! ### The Hadamard layer -/

/-- The **Hadamard layer** on the wires `ws`: the Clifford circuit applying a Hadamard gate to each
wire in the list `ws` (`ws.map CliffordGate.had`). Taking `ws` to be the first `r` qubits, this is
the opening layer of the stabilizer encoding circuit of Nielsen & Chuang Problem 10.3. -/
def hadLayer (ws : List (Fin n)) : CliffordCircuit n := ws.map CliffordGate.had

/-- The Hadamard layer is built one wire at a time: `hadLayer (w :: ws) = had w :: hadLayer ws`
(definitionally, `List.map` on a cons). -/
theorem hadLayer_cons (w : Fin n) (ws : List (Fin n)) :
    hadLayer (w :: ws) = CliffordGate.had w :: hadLayer ws := rfl

/-- **Row action of the Hadamard layer.** For a list of **distinct** wires `ws`, conjugating a Pauli
string by `hadLayer ws` applies the single-wire Hadamard tableau `hadamardPauli` to exactly the
wires in `ws`, leaving the others fixed: `act (hadLayer ws) g k = hadamardPauli (g k)` if `k ∈ ws`,
else `g k`. Proved by induction on `ws`; the cons step uses `w ∉ ws` (from `Nodup`) so the outer
`Function.update` on wire `w` reads the still-untouched value `g w`. -/
theorem act_hadLayer (ws : List (Fin n)) (g : Fin n → Fin 4) (hnd : ws.Nodup) :
    CliffordCircuit.act (hadLayer ws) g = fun k => if k ∈ ws then hadamardPauli (g k) else g k := by
  revert hnd
  induction ws with
  | nil => intro _; funext k; simp [hadLayer, CliffordCircuit.act]
  | cons w ws ih =>
      intro hnd
      obtain ⟨hw, hnd'⟩ := List.nodup_cons.mp hnd
      have hrec := ih hnd'
      funext k
      rw [hadLayer_cons]
      simp only [CliffordCircuit.act, CliffordGate.act]
      rw [hrec, Function.update_apply]
      rcases eq_or_ne k w with rfl | hk
      · simp [hw, List.mem_cons]
      · simp [hk, List.mem_cons]

/-! ### The Hadamard layer as the first layer of the encoding circuit -/

/-- The Hadamard tableau sends `I ↦ I` (`hadamardPauli 0 = 0`). -/
theorem hadamardPauli_zero : hadamardPauli (0 : Fin 4) = 0 := by decide

/-- The Hadamard tableau sends `Z ↦ X` (`hadamardPauli 3 = 1`). -/
theorem hadamardPauli_three : hadamardPauli (3 : Fin 4) = 1 := by decide

/-- **The first layer of the encoding circuit** (Nielsen & Chuang Problem 10.3): applying the
Hadamard layer on distinct wires `ws` to the pure-`Z` generator `Zᵢ` returns `Xᵢ` when `i ∈ ws`
and leaves `Zᵢ` unchanged otherwise. On the trivial check matrix `G` (10.124), whose rows are the
`Zᵢ`, Hadamarding the first `r` wires converts exactly the first `r` rows from `Z`-type to `X`-type.
The Hadamard swaps the wire's `X`/`Z` bits (`hadamardPauli 3 = 1`, i.e. `Z ↦ X`), and only wire `i`
of `Zᵢ` is non-identity, so only `i ∈ ws` matters. -/
theorem act_hadLayer_zGenPauli (ws : List (Fin n)) (hnd : ws.Nodup) (i : Fin n) :
    CliffordCircuit.act (hadLayer ws) (zGenPauli i)
      = if i ∈ ws then xGenPauli i else zGenPauli i := by
  rw [act_hadLayer ws _ hnd]
  by_cases hiws : i ∈ ws
  · rw [ite_eq_left hiws]
    funext k
    rcases eq_or_ne k i with rfl | hk <;>
      simp [hadamardPauli_three, hadamardPauli_zero, *]
  · rw [ite_eq_right hiws]
    funext k
    rcases eq_or_ne k i with rfl | hk <;>
      simp [hadamardPauli_zero, *]

/-- **The first encoding layer in check-matrix terms.** After the Hadamard layer on `ws`, row `i` of
the check matrix is `(eᵢ | 0)` (pure `X`) when `i ∈ ws` and `(0 | eᵢ)` (pure `Z`) otherwise. With
`ws` the first `r` wires this is precisely the transition from the trivial matrix `G` (10.124), all
rows `(0 | eᵢ)`, to the intermediate matrix with an `X`-part identity block on the first `r` rows —
the starting point for the CNOT and phase layers that build the standard form (10.125). -/
theorem checkRow_act_hadLayer_zGenPauli (ws : List (Fin n)) (hnd : ws.Nodup) (i : Fin n) :
    checkRow (CliffordCircuit.act (hadLayer ws) (zGenPauli i))
      = if i ∈ ws then (Pi.single i (1 : ZMod 2), 0) else (0, Pi.single i (1 : ZMod 2)) := by
  rw [act_hadLayer_zGenPauli ws hnd]
  by_cases h : i ∈ ws <;> simp [h, checkRow_xGenPauli, checkRow_zGenPauli]

/-- **Operator-level first encoding layer**, through the backbone
`CliffordCircuit.conj_pauliString`. The Hadamard layer is a unitary Clifford circuit conjugating
the Pauli operator `P_{Zᵢ}` to a
nonzero (`±1`, `CliffordCircuit.sign_ne_zero`) scalar multiple of `P_{Xᵢ}` when `i ∈ ws`, else
`P_{Zᵢ}` — the physical content of the check-matrix layer `act_hadLayer_zGenPauli`. -/
theorem hadLayer_conj_zGenPauli (ws : List (Fin n)) (hnd : ws.Nodup) (i : Fin n) :
    CliffordCircuit.toMatrix (hadLayer ws) * pauliString (zGenPauli i)
        * (CliffordCircuit.toMatrix (hadLayer ws))ᴴ
      = CliffordCircuit.sign (hadLayer ws) (zGenPauli i)
        • pauliString (if i ∈ ws then xGenPauli i else zGenPauli i) := by
  rw [CliffordCircuit.conj_pauliString, act_hadLayer_zGenPauli ws hnd]

end AxQM.Concrete
