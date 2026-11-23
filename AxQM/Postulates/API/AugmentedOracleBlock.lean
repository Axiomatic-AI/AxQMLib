/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ControlledUnitary
import AxQM.Postulates.API.Teleportation
import AxQM.Postulates.API.ControlledZ
import AxQM.Postulates.API.ToffoliHadamard
import AxQM.Postulates.API.CnotPauliPropagation
import AxQM.Postulates.API.RelativePhaseToffoli
import AxQM.Postulates.API.Evolution

/-!
# The augmented search oracle from one oracle call — response block (N&C Exercise 6.5)

Nielsen & Chuang, §6.1.4 (p. 255): to search a space in which *more than half* the items may be
solutions, one **doubles** the search space by adjoining a single extra qubit `|q⟩`, and builds an
**augmented oracle** `O'` that marks an item `(x, q)` iff `x` is a solution *and* the extra bit is
`q = 0`. Exercise 6.5 asks to show `O'` can be constructed from **one call** to the original oracle
`O` together with **elementary quantum gates**.

The original bit-flip oracle acts on an index register `|x⟩` and a response qubit `|r⟩` by
`O|x⟩|r⟩ = |x⟩|r ⊕ f(x)⟩` (`f(x) = 1` iff `x` is a solution). Because `O` does not mix different
`x`, the whole construction acts block-by-block in `x`: on the block of a fixed item `x` the oracle
call is the single-qubit bit flip `X^{f(x)}` on the response, and the circuit acts on the two
remaining qubits — the extra qubit `q` and the response `r` — as **one fixed two-qubit unitary**
depending only on the solution flag `c := f(x) : Fin 2`.

**This file formalises that two-qubit response block as an `Evolution`** — the physical
counterpart of the concrete matrix computation in
`AxQM/Concrete/AugmentedOracleConstruction.lean`. The assembly of the block over the whole
search index `x` (into the full oracle `O'` acting on the augmented register) is the subject of
`AxQM/NC/Ch6/Exercise6_5.lean`.

## The construction (phase kickback)

With the response qubit `r` supplied as a fresh work qubit in `|0⟩`, the block circuit is, in time
order, `X_r`, `CNOT_{q→r}`, `H_r`, then the single oracle call (a bit flip `X^c` on `r`), then
`H_r`, `CNOT_{q→r}`, `X_r`:

`augmentedOracleBlock c = X_r · CNOT_{q→r} · H_r · (X^c on r) · H_r · CNOT_{q→r} · X_r`.

Preparing `r` as `|−⟩` exactly when `q = 0` turns the **one** oracle call into a phase kickback: it
imprints `(-1)^c` precisely on the `q = 0` branch and nothing on the `q = 1` branch — the mark
"solution ∧ `q = 0`" defining `O'`. The heart of the proof is the gate-level Hadamard conjugation
`H X H = Z` (`hadamardGate_comp_pauliXGate_comp_hadamardGate`), which collapses the oracle sandwich
`H_r · X^c · H_r` to the diagonal `Z^c` (`hadamardConj_targetXPow`); the two flanking permutation
gates then make the whole block a phase.

## What is formalised

* The oracle response gate `X^c` is the **shared** `targetXPow c : Fin 2 → Evolution qubit`
  (`AxQM/Postulates/API/RelativePhaseToffoli.lean`); its single occurrence in
  `augmentedOracleBlock` is the
  **one** application of the original oracle, restricted to one item's block.
* `oraclePhaseGate c` — the phase-collapsed form `Z^c`, the `Z`-counterpart of `targetXPow`
  (`X^c`); genuinely new, as the library has no `targetZPow`.
* `hadamardConj_targetXPow` — the phase-kickback core `H_r · X^c · H_r = Z^c` (on the response).
* `augmentedOracleBlock c` — the seven-factor block circuit built from **one** `targetXPow c`
  and the elementary gates `X_r`, `CNOT_{q→r}`, `H_r`.
* `augmentedOracleBlock_reduce` — the block collapses to `X_r · CNOT · Z^c · CNOT · X_r`.
* `augmentedOracleBlock_hasEigenstate` — **the mark (N&C Exercise 6.5):** on the response work
  qubit supplied in `|0⟩`, the block fixes `|q⟩|0⟩` up to the augmented-oracle phase, scaling it by
  `-1` exactly when the item is a solution (`c = 1`) *and* the extra bit is `q = 0`, and by `+1`
  otherwise — precisely the mark "solution ∧ `q = 0`" defining `O'`, with the work qubit returned
  to `|0⟩`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

/-- **`H X H = Z`** at the gate level: conjugating the Pauli-`X` gate by the Hadamard gate yields
the Pauli-`Z` gate, `hadamardGate ∘ pauliXGate ∘ hadamardGate = pauliZGate`. Derived from the
companion `H Z H = X` (`hadamardGate_comp_pauliZGate_comp_hadamardGate`) together with `H² = I`
(`hadamardGate_comp_self`): `HXH = H(HZH)H = (HH)Z(HH) = Z`. This is the identity that turns the
single oracle call of the augmented-oracle construction into a diagonal phase. -/
theorem hadamardGate_comp_pauliXGate_comp_hadamardGate :
    hadamardGate.comp (pauliXGate.comp hadamardGate) = pauliZGate := by
  rw [← hadamardGate_comp_pauliZGate_comp_hadamardGate, ← Evolution.comp_assoc,
    ← Evolution.comp_assoc, hadamardGate_comp_self, Evolution.id_comp, Evolution.comp_assoc,
    hadamardGate_comp_self, Evolution.comp_id]

/-- The single-qubit **oracle phase gate** `Z^c`: the Pauli-`Z` gate when the item is a solution
(`c = 1`) and the identity otherwise. It is the diagonal collapse of the Hadamard-conjugated oracle
call `H · X^c · H` (`hadamardConj_targetXPow`).

This is the `Z`-power counterpart of the shared `X`-power gate `targetXPow`
(`Postulates/API/RelativePhaseToffoli`, `X^c`) — coherently indexed by `Fin 2` and of the same
shape (`if c = 0 then id else P`). It is genuinely new: the library has an `X^c` (`targetXPow`) but
no `Z^c`. -/
def oraclePhaseGate (c : Fin 2) : Evolution qubit := if c = 0 then Evolution.id else pauliZGate

@[simp] theorem oraclePhaseGate_zero : oraclePhaseGate 0 = Evolution.id := rfl
@[simp] theorem oraclePhaseGate_one : oraclePhaseGate 1 = pauliZGate := rfl

/-- **The phase-kickback core** `H_r · X^c · H_r = Z^c` on the response qubit `r` (the right factor
of the `(q, r)` block), for the shared oracle-call gate `X^c = targetXPow c`. Conjugating the single
oracle call `X^c` by the Hadamards collapses it to the diagonal phase `Z^c`: for `c = 1` this is
`H X H = Z` (`hadamardGate_comp_pauliXGate_comp_hadamardGate`), and for `c = 0` it is `H² = I`. This
is where the *one* oracle call becomes a phase. -/
theorem hadamardConj_targetXPow (c : Fin 2) :
    (hadamardGate.onRight qubit).comp
        (((targetXPow c).onRight qubit).comp (hadamardGate.onRight qubit))
      = (oraclePhaseGate c).onRight qubit := by
  rw [Evolution.onRight_comp, Evolution.onRight_comp]
  congr 1
  by_cases hc : c = 0
  · subst hc
    rw [targetXPow_zero, oraclePhaseGate_zero, Evolution.id_comp, hadamardGate_comp_self]
  · have hx : targetXPow c = pauliXGate := by simp only [targetXPow, ite_eq_right hc]
    have hz : oraclePhaseGate c = pauliZGate := by simp only [oraclePhaseGate, ite_eq_right hc]
    rw [hx, hz]
    exact hadamardGate_comp_pauliXGate_comp_hadamardGate

/-- **The one-call augmented-oracle response block.** In time order `X_r`, `CNOT_{q→r}`, `H_r`, the
oracle call `X^c` on `r`, `H_r`, `CNOT_{q→r}`, `X_r` — a palindrome of the elementary gates
`X_r = pauliXGate.onRight qubit`, `CNOT_{q→r} = cnotGate` (control the extra qubit `q`, target the
response `r`), and `H_r = hadamardGate.onRight qubit` around a **single** oracle call
`targetXPow c` (the shared `X^c`, placed on the response `r`). Its net action is the
augmented-oracle mark (`augmentedOracleBlock_hasEigenstate`). The middle Hadamard sandwich
`H_r · X^c · H_r` is grouped as a subterm so it collapses to `Z^c` (`hadamardConj_targetXPow`). -/
def augmentedOracleBlock (c : Fin 2) : Evolution (qubit.compose qubit) :=
  ((pauliXGate.onRight qubit).comp cnotGate).comp
    (((hadamardGate.onRight qubit).comp
        (((targetXPow c).onRight qubit).comp (hadamardGate.onRight qubit))).comp
      (cnotGate.comp (pauliXGate.onRight qubit)))

/-- The block circuit collapses to `X_r · CNOT_{q→r} · Z^c · CNOT_{q→r} · X_r`: the single oracle
call, sandwiched by the Hadamards, has become the diagonal phase `Z^c` on the response
(`hadamardConj_targetXPow`). All that remains are the two permutation gates around one `Z^c`. -/
theorem augmentedOracleBlock_reduce (c : Fin 2) :
    augmentedOracleBlock c
      = ((pauliXGate.onRight qubit).comp cnotGate).comp
          (((oraclePhaseGate c).onRight qubit).comp
            (cnotGate.comp (pauliXGate.onRight qubit))) := by
  rw [augmentedOracleBlock, hadamardConj_targetXPow]

/-- The oracle phase gate `Z^c` acts on the computational basis by `Z^c|i⟩ = (-1)^{c·i}|i⟩`
(operator/vector level): a phase `(-1)^i` on `|i⟩` when `c = 1`, and the identity when `c = 0`. -/
private theorem oraclePhaseGate_op_qubitBasis (c i : Fin 2) :
    (oraclePhaseGate c).op (qubitBasis i).vec
      = ((-1 : ℂ) ^ ((c : ℕ) * (i : ℕ))) • (qubitBasis i).vec := by
  by_cases hc : c = 0
  · subst hc
    simp only [oraclePhaseGate_zero, Evolution.id_op, one_apply_eq_self,
      Fin.val_zero, zero_mul, pow_zero, one_smul]
  · have hz : oraclePhaseGate c = pauliZGate := by simp only [oraclePhaseGate, ite_eq_right hc]
    have hc1 : (c : ℕ) = 1 := by omega
    rw [hz, pauliZGate_op_apply_qubitBasis, hc1, one_mul]

/-- **The augmented oracle from one oracle call (N&C Exercise 6.5).** On the response work qubit
supplied in `|0⟩`, the one-call response block `augmentedOracleBlock c` fixes `|q⟩|0⟩` up to the
augmented-oracle phase: it is an eigenstate whose eigenvalue is `-1` exactly when the item is a
solution (`c = 1`) *and* the extra bit is `q = 0`, and `+1` otherwise. Equivalently,
`augmentedOracleBlock c |q⟩|0⟩ = (-1)^{c ∧ (q = 0)} |q⟩|0⟩` — the mark "solution ∧ `q = 0`" that
defines the augmented oracle `O'`, with the work qubit returned to `|0⟩`.

The proof reduces the block to `X_r · CNOT · Z^c · CNOT · X_r` (`augmentedOracleBlock_reduce`) and
tracks `|q⟩|0⟩` through the five basis gates: `X_r` and the two `CNOT_{q→r}` shuttle the response to
`|1 ⊕ q⟩` and back to `|0⟩`, while `Z^c` imprints the phase `(-1)^{c·(1 ⊕ q)}`, which is `-1`
exactly when `c = 1` and `q = 0`. -/
theorem augmentedOracleBlock_hasEigenstate (c q : Fin 2) :
    (augmentedOracleBlock c).HasEigenstate (if c = 1 ∧ q = 0 then -1 else 1)
      ((qubitBasis q).tmul (qubitBasis 0)) := by
  -- `CNOT` on the computational basis (raw vector level): `CNOT(|a⟩ ⊗ |b⟩) = |a⟩ ⊗ |b ⊕ a⟩`.
  have hcnot : ∀ a b : Fin 2, cnotGate.op ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
      = (qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis (b + a)).vec := fun a b => by
    have h := congrArg PureState.vec (cnotGate_evolvePure_qubitBasis a b)
    rwa [Evolution.evolvePure_vec, PureState.tmul_vec, PureState.tmul_vec] at h
  rw [Evolution.HasEigenstate, augmentedOracleBlock_reduce]
  -- Expand the composition into a nest of operator applications, then track `|q⟩|0⟩` through the
  -- five basis gates in time order — `X_r`, `CNOT`, the phase `Z^c`, `CNOT`, `X_r` — innermost
  -- first; `map_smul` shuttles the `Z^c` phase past the two closing permutation gates.
  change (pauliXGate.onRight qubit).op (cnotGate.op
        (((oraclePhaseGate c).onRight qubit).op (cnotGate.op
          ((pauliXGate.onRight qubit).op ((qubitBasis q).vec ⊗ₜ[ℂ] (qubitBasis 0).vec)))))
      = (if c = 1 ∧ q = 0 then -1 else 1) • (qubitBasis q).vec ⊗ₜ[ℂ] (qubitBasis 0).vec
  rw [Evolution.onRight_op_tmul, pauliXGate_op_apply_qubitBasis, hcnot,
    Evolution.onRight_op_tmul, oraclePhaseGate_op_qubitBasis, TensorProduct.tmul_smul]
  erw [ContinuousLinearMap.map_smul]                                    -- pull the phase past CNOT
  rw [hcnot]                                                            -- CNOT : |1 ⊕ q⟩ ↦ |1⟩
  erw [ContinuousLinearMap.map_smul]                                    -- pull the phase past X_r
  rw [Evolution.onRight_op_tmul, pauliXGate_op_apply_qubitBasis]        -- X_r : |1⟩ ↦ |0⟩
  -- The response index has returned to `0` and the accumulated phase is the augmented-oracle mark.
  have hidx : ((0 + 1 : Fin 2) + q + q) + 1 = 0 := by fin_cases q <;> rfl
  have hphase : ((-1 : ℂ) ^ ((c : ℕ) * ((0 + 1 : Fin 2) + q : Fin 2).val))
      = if c = 1 ∧ q = 0 then -1 else 1 := by
    fin_cases c <;> fin_cases q <;> simp
  rw [hidx, hphase]; rfl

end AxQM
