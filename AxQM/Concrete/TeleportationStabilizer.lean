/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCliffordCircuit
import AxQM.Concrete.StabilizerGeneratorFlip

/-!
# Concrete: the stabilizer-formalism verification of quantum teleportation (N&C Ex 10.42)

This file verifies the teleportation circuit of Nielsen & Chuang **Figure 1.13** (p. 27)
**in the stabilizer (Heisenberg) picture** — the content of **Exercise 10.42** (§10.5.4, p. 464).
It works with Pauli strings, check matrices, matrices and vectors (`Concrete.pauliString`,
`Concrete.CliffordCircuit`, `Matrix`, `Matrix.mulVec`, `Fin n → Fin 4`). The statement of the
exercise is in `AxQM/NC/Ch10/Exercise10_42.lean`.

## The circuit

Label the three wires `0, 1, 2` = (Alice's data qubit, Alice's half of the Bell pair, Bob's qubit).
The teleportation circuit of Fig 1.13 applies, *before* the measurements, the **Clifford unitary**
`U = H₀ · CNOT₀₁` (control `0`, target `1`, then a Hadamard on `0`); Alice then measures wires
`0, 1` in the computational basis (outcomes `m₀, m₁ ∈ {0,1}`) and Bob applies the byproduct
`Z₂^{m₀} X₂^{m₁}`.  As the exercise flags, the stabilizer formalism only handles a *stabilizer*
input state, so it does not describe teleportation of a fully general `|ψ⟩` (that state-vector
verification, valid for every `|ψ⟩`, is `AxQM.teleportation_identity` in
`Postulates/API/Teleportation.lean`).  What the stabilizer formalism gives — and what this file
formalises **and proves to its conclusion** — is the operator (Heisenberg) dynamics for a stabilizer
input, ending in a machine-checked statement that the corrected circuit reproduces the input on
Bob's wire.

## The verification, in three parts

**Part 1 — the Clifford propagation table** (`teleportStabCircuit_conj_*`, all sign `+1`).  `U` is a
Clifford, so it conjugates Pauli strings to Pauli strings (`CliffordCircuit.conj_pauliString`).
Tracking the two families of operators that matter — the input qubit's **logical operators** `Z₀,
X₀` and the Bell-pair **stabilisers** `X₁X₂, Z₁Z₂` of the resource `(|00⟩+|11⟩)/√2` on wires
`1, 2` — gives `Z₀ ↦ X₀`, `X₀ ↦ Z₀X₁`, `X₁X₂ ↦ X₁X₂`, `Z₁Z₂ ↦ X₀Z₁Z₂`.

**Part 2 — the operator transfer onto Bob's wire** (`logicalZ_acts_as_bellZ`,
`logicalX_acts_as_bellX`).  On the post-Clifford stabilised subspace — the vectors `v` fixed by the
propagated Bell stabilisers `X₁X₂` and `X₀Z₁Z₂` (`v ∈ V_S`, i.e.
`Concrete.mem_stabilizedSubspace`) — the acted-on logical operators equal operators supported on the
Bell pair / Bob's wire: `X₀ v = Z₁Z₂ v` and `(Z₀X₁) v = (Z₀X₂) v`.  These are the multiplication
identities `logicalZ_transported_reduce` / `logicalX_transported_reduce` (`X₀·(X₀Z₁Z₂) = Z₁Z₂`,
`(Z₀X₁)·(X₁X₂) = Z₀X₂`) applied to a stabilised vector — the machine-checked sense in which "the
information moves onto Bob's wire".

**Part 3 — the corrected teleportation conclusion** (`teleportation_Zbasis`,
`teleportation_Xbasis`).  A stabilizer input is a `±1` eigenstate of a single-qubit Pauli.  Feeding
Part 1/2 through the §10.5.3 measurement rules, the **post-measurement** state `w` is a `±1`
eigenstate of the measured `Z₀, Z₁` (outcomes `(-1)^{m₀}, (-1)^{m₁}`) and retains one surviving
stabiliser: `Z₁Z₂` (sign `(-1)^a`, encoding the input `|a⟩`) for a `Z`-basis input, or `Z₀X₂` (sign
`(-1)^b`) for an `X`-basis input — precisely the transported input logical operator reduced by the
propagated Bell stabiliser (Part 2).  The theorems prove that after the byproduct
`teleportByproduct m₀ m₁ = Z₂^{m₀} X₂^{m₁}`, Bob's wire is stabilised by `(-1)^a Z₂` (resp.
`(-1)^b X₂`) — i.e. it holds the *input* stabilizer state.  This is the exercise's claim, machine
checked: the corrected circuit carries the input logical operators to Bob's, teleporting the qubit.

The §10.5.3 collapse enters Part 3 as the eigenvalue hypotheses on `w` — the mathematical content of
"the post-measurement state is a `±1` eigenstate of the measured observable"; that collapse is
itself formalised at
`AxQM/Postulates/API/StabilizerMeasurement.lean` (`Observable.signMeasurement`,
`postMeasPlus_hasEigenstate`, …), whose post-measurement guarantees are exactly these hypotheses.

## Pauli index convention

A Pauli string is `Concrete.pauliString g` for `g : Fin 3 → Fin 4` with `0 = I, 1 = X, 2 = Y,
3 = Z` per wire (`Concrete/Pauli.lean`); it acts on a `3`-qubit vector `v : (Fin 3 → Fin 2) → ℂ` by
`Matrix.mulVec`.  So e.g. `Z₀ = pauliString ![3,0,0]`, `X₁X₂ = pauliString ![0,1,1]`,
`X₀Z₁Z₂ = pauliString ![1,3,3]`, `Z₁Z₂ = pauliString ![0,3,3]`.
-/

open Matrix

noncomputable section

namespace AxQM.Concrete

/-! ### Part 1 — the Clifford propagation table (the dynamics) -/

/-- The **Clifford part of the teleportation circuit** of N&C Figure 1.13 on three wires
(`0` = Alice's data, `1` = Alice's Bell half, `2` = Bob): the controlled-`NOT` with control `0` and
target `1`, followed by a Hadamard on wire `0`.  As a `CliffordCircuit` the list is read
right-to-left, so `[had 0, cnot 0 1]` runs `CNOT₀₁` first and then `H₀`
(`toMatrix = H₀ · CNOT₀₁`), matching the circuit order of Fig 1.13. -/
def teleportStabCircuit : CliffordCircuit 3 :=
  [CliffordGate.had 0, CliffordGate.cnot 0 1 (by decide)]

/-- Conjugation by the teleportation Clifford `U` on a Pauli string with sign `+1`: the workhorse
for the propagation table below.  Given `U.act g = g'` (the check-matrix column operations) and
`U.sign g = 1` (no `Y` is produced along the way), `CliffordCircuit.conj_pauliString` gives
`U P_g U† = P_{g'}`. -/
private theorem teleportStabCircuit_conj_of (g g' : Fin 3 → Fin 4)
    (hact : teleportStabCircuit.act g = g') (hsign : teleportStabCircuit.sign g = 1) :
    teleportStabCircuit.toMatrix * pauliString g * teleportStabCircuit.toMatrixᴴ
      = pauliString g' := by
  rw [CliffordCircuit.conj_pauliString, hact, hsign, one_smul]

/-- **Propagation of the input logical `Z`.** `U Z₀ U† = X₀`: the Clifford part of the teleportation
circuit conjugates the data qubit's logical `Z` (`pauliString ![3,0,0]`) to its logical `X`
(`pauliString ![1,0,0]`) — `CNOT₀₁` fixes `Z₀`, then `H₀` sends `Z₀ ↦ X₀`. -/
theorem teleportStabCircuit_conj_logicalZ :
    teleportStabCircuit.toMatrix * pauliString ![3, 0, 0] * teleportStabCircuit.toMatrixᴴ
      = pauliString ![1, 0, 0] :=
  teleportStabCircuit_conj_of _ _ (by decide) <| by
    simp [teleportStabCircuit, CliffordCircuit.sign, CliffordGate.sign, CliffordCircuit.act,
      CliffordGate.act, cnotPauliString, cnotCtrlPauli, cnotPauliSign, hadamardPauliSign,
      Function.update]

/-- **Propagation of the input logical `X`.** `U X₀ U† = Z₀X₁`: `CNOT₀₁` sends `X₀ ↦ X₀X₁`, then
`H₀` sends `X₀ ↦ Z₀`, giving `Z₀X₁` (`pauliString ![3,1,0]`). -/
theorem teleportStabCircuit_conj_logicalX :
    teleportStabCircuit.toMatrix * pauliString ![1, 0, 0] * teleportStabCircuit.toMatrixᴴ
      = pauliString ![3, 1, 0] :=
  teleportStabCircuit_conj_of _ _ (by decide) <| by
    simp [teleportStabCircuit, CliffordCircuit.sign, CliffordGate.sign, CliffordCircuit.act,
      CliffordGate.act, cnotPauliString, cnotCtrlPauli, cnotPauliSign, hadamardPauliSign,
      Function.update]

/-- **Propagation of the Bell `X`-stabiliser.** `U (X₁X₂) U† = X₁X₂`: the resource stabiliser
`X₁X₂` (`pauliString ![0,1,1]`) is untouched — `CNOT₀₁` fixes `X₁` (it is the target's `X`) and `H₀`
does not act on wires `1, 2`. -/
theorem teleportStabCircuit_conj_bellStabX :
    teleportStabCircuit.toMatrix * pauliString ![0, 1, 1] * teleportStabCircuit.toMatrixᴴ
      = pauliString ![0, 1, 1] :=
  teleportStabCircuit_conj_of _ _ (by decide) <| by
    simp [teleportStabCircuit, CliffordCircuit.sign, CliffordGate.sign, CliffordCircuit.act,
      CliffordGate.act, cnotPauliString, cnotCtrlPauli, cnotPauliSign, hadamardPauliSign,
      Function.update]

/-- **Propagation of the Bell `Z`-stabiliser.** `U (Z₁Z₂) U† = X₀Z₁Z₂`: `CNOT₀₁` sends `Z₁ ↦ Z₀Z₁`
(the control picks up the target's `Z`), then `H₀` sends `Z₀ ↦ X₀`, giving `X₀Z₁Z₂`
(`pauliString ![1,3,3]`). -/
theorem teleportStabCircuit_conj_bellStabZ :
    teleportStabCircuit.toMatrix * pauliString ![0, 3, 3] * teleportStabCircuit.toMatrixᴴ
      = pauliString ![1, 3, 3] :=
  teleportStabCircuit_conj_of _ _ (by decide) <| by
    simp [teleportStabCircuit, CliffordCircuit.sign, CliffordGate.sign, CliffordCircuit.act,
      CliffordGate.act, cnotPauliString, cnotCtrlPauli, cnotPauliSign, hadamardPauliSign,
      Function.update]

/-! ### Part 2 — the operator transfer onto Bob's wire (on the stabilised subspace) -/

/-- **Stabiliser absorption of the transported logical `Z`.** The transported logical `Z`
(`= X₀`, `pauliString ![1,0,0]`) times the *propagated* Bell-`Z` stabiliser `X₀Z₁Z₂`
(`pauliString ![1,3,3]`) is `Z₁Z₂` (`pauliString ![0,3,3]`): the wire-`0` factor cancels
(`X·X = I`), leaving an operator supported entirely on the Bell pair. -/
theorem logicalZ_transported_reduce :
    pauliString ![1, 0, 0] * pauliString ![1, 3, 3] = pauliString (n := 3) ![0, 3, 3] :=
  pauliString_mul_of (by decide) (by simp [Fin.prod_univ_three, pauliMulPhase])

/-- **Stabiliser absorption of the transported logical `X`.** The transported logical `X`
(`= Z₀X₁`, `pauliString ![3,1,0]`) times the Bell-`X` stabiliser `X₁X₂` (`pauliString ![0,1,1]`)
is `Z₀X₂` (`pauliString ![3,0,1]`): the wire-`1` factor cancels (`X·X = I`), moving the `X` from
Alice's Bell half to Bob's wire. -/
theorem logicalX_transported_reduce :
    pauliString ![3, 1, 0] * pauliString ![0, 1, 1] = pauliString (n := 3) ![3, 0, 1] :=
  pauliString_mul_of (by decide) (by simp [Fin.prod_univ_three, pauliMulPhase])

/-- **The transported logical `Z` acts as `Z₁Z₂` on the stabilised subspace.** For any vector `v`
fixed by the propagated Bell-`Z` stabiliser `X₀Z₁Z₂` (`pauliString ![1,3,3]`) — one of the two
generators of the post-Clifford stabilised subspace `V_S`, cf. `Concrete.mem_stabilizedSubspace` —
the transported logical `Z` (`X₀`) and `Z₁Z₂` agree: `X₀ v = Z₁Z₂ v`.  Since `Z₁Z₂` is supported on
the Bell pair, the information carried by the input's logical `Z` has moved off Alice's data wire.
Immediate from `logicalZ_transported_reduce` (`X₀·(X₀Z₁Z₂) = Z₁Z₂`) applied to a stabilised `v`. -/
theorem logicalZ_acts_as_bellZ (v : (Fin 3 → Fin 2) → ℂ)
    (hZ : (pauliString ![1, 3, 3]).mulVec v = v) :
    (pauliString ![1, 0, 0]).mulVec v = (pauliString ![0, 3, 3]).mulVec v := by
  conv_rhs => rw [← logicalZ_transported_reduce, ← Matrix.mulVec_mulVec, hZ]

/-- **The transported logical `X` acts as `Z₀X₂` on the stabilised subspace.** For any vector `v`
fixed by the Bell-`X` stabiliser `X₁X₂` (`pauliString ![0,1,1]`) — the other generator of `V_S` —
the transported logical `X` (`Z₀X₁`) and `Z₀X₂` agree: `(Z₀X₁) v = (Z₀X₂) v`, moving the `X` onto
Bob's wire.  Immediate from `logicalX_transported_reduce` (`(Z₀X₁)·(X₁X₂) = Z₀X₂`) applied to a
stabilised `v`. -/
theorem logicalX_acts_as_bellX (v : (Fin 3 → Fin 2) → ℂ)
    (hX : (pauliString ![0, 1, 1]).mulVec v = v) :
    (pauliString ![3, 1, 0]).mulVec v = (pauliString ![3, 0, 1]).mulVec v := by
  conv_rhs => rw [← logicalX_transported_reduce, ← Matrix.mulVec_mulVec, hX]

/-! ### Part 3 — the corrected teleportation conclusion -/

/-- The **byproduct correction** `Z₂^{m₀} X₂^{m₁}` on Bob's wire `2`, as a matrix on the three-qubit
register.  This is the Pauli operation Alice's measurement outcomes `(m₀, m₁)` instruct Bob to apply
(N&C p. 27: "Bob needs to apply the transformation `Z^{M₁} X^{M₂}`"). -/
def teleportByproduct (m₀ m₁ : Fin 2) : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  pauliString ![0, 0, 3] ^ (m₀ : ℕ) * pauliString ![0, 0, 1] ^ (m₁ : ℕ)

/-- `Z₁·(Z₁Z₂) = Z₂`: the surviving `Z`-basis stabiliser `Z₁Z₂` times the measured `Z₁` is `Z₂`,
used to read off Bob's `Z` eigenvalue. -/
theorem pauliZ1_mul_pauliZ1Z2 :
    pauliString ![0, 3, 0] * pauliString ![0, 3, 3] = pauliString (n := 3) ![0, 0, 3] :=
  pauliString_mul_of (by decide) (by simp [Fin.prod_univ_three, pauliMulPhase])

/-- `Z₀·(Z₀X₂) = X₂`: the surviving `X`-basis stabiliser `Z₀X₂` times the measured `Z₀` is `X₂`,
used to read off Bob's `X` eigenvalue. -/
theorem pauliZ0_mul_pauliZ0X2 :
    pauliString ![3, 0, 0] * pauliString ![3, 0, 1] = pauliString (n := 3) ![0, 0, 1] :=
  pauliString_mul_of (by decide) (by simp [Fin.prod_univ_three, pauliMulPhase])

/-- **`Z₂` commutes past the byproduct up to the wire-`1` sign.**
`Z₂ · (Z₂^{m₀} X₂^{m₁}) = (-1)^{m₁} • ((Z₂^{m₀} X₂^{m₁}) · Z₂)`: `Z₂` commutes with the `Z₂^{m₀}`
factor and anticommutes with `X₂^{m₁}` (once per unit of `m₁`).  The engine that lets the `X`-part
of the byproduct undo the `(-1)^{m₁}` measurement sign on Bob's `Z`. -/
theorem z2_comm_byproduct (m₀ m₁ : Fin 2) :
    pauliString ![0, 0, 3] * teleportByproduct m₀ m₁
      = (-1 : ℂ) ^ (m₁ : ℕ) • (teleportByproduct m₀ m₁ * pauliString ![0, 0, 3]) := by
  have hZX : pauliString (n := 3) ![0, 0, 3] * pauliString ![0, 0, 1]
      = -(pauliString ![0, 0, 1] * pauliString ![0, 0, 3]) := by
    rw [pauliString_mul_comm_sign]
    norm_num [show pauliAnticommCount (n := 3) ![0, 0, 3] ![0, 0, 1] = 1 from by decide]
  rw [teleportByproduct]
  have hZ : Commute (pauliString ![0, 0, 3]) (pauliString (n := 3) ![0, 0, 3] ^ (m₀ : ℕ)) :=
    (Commute.refl _).pow_right _
  rw [← mul_assoc, hZ.eq, mul_assoc]
  have hZXpow : pauliString ![0, 0, 3] * pauliString ![0, 0, 1] ^ (m₁ : ℕ)
      = (-1 : ℂ) ^ (m₁ : ℕ) • (pauliString (n := 3) ![0, 0, 1] ^ (m₁ : ℕ) * pauliString ![0, 0, 3])
      := by
    fin_cases m₁
    · simp
    · simp only [pow_one]; rw [hZX]; simp
  rw [hZXpow, mul_smul_comm, ← mul_assoc]

/-- **`X₂` commutes past the byproduct up to the wire-`0` sign.**
`X₂ · (Z₂^{m₀} X₂^{m₁}) = (-1)^{m₀} • ((Z₂^{m₀} X₂^{m₁}) · X₂)`: `X₂` anticommutes with `Z₂^{m₀}`
(once per unit of `m₀`) and commutes with `X₂^{m₁}`.  The engine that lets the `Z`-part of the
byproduct undo the `(-1)^{m₀}` measurement sign on Bob's `X`. -/
theorem x2_comm_byproduct (m₀ m₁ : Fin 2) :
    pauliString ![0, 0, 1] * teleportByproduct m₀ m₁
      = (-1 : ℂ) ^ (m₀ : ℕ) • (teleportByproduct m₀ m₁ * pauliString ![0, 0, 1]) := by
  have hXZ : pauliString (n := 3) ![0, 0, 1] * pauliString ![0, 0, 3]
      = -(pauliString ![0, 0, 3] * pauliString ![0, 0, 1]) := by
    rw [pauliString_mul_comm_sign]
    norm_num [show pauliAnticommCount (n := 3) ![0, 0, 1] ![0, 0, 3] = 1 from by decide]
  rw [teleportByproduct]
  have hXZpow : pauliString ![0, 0, 1] * pauliString ![0, 0, 3] ^ (m₀ : ℕ)
      = (-1 : ℂ) ^ (m₀ : ℕ) • (pauliString (n := 3) ![0, 0, 3] ^ (m₀ : ℕ) * pauliString ![0, 0, 1])
      := by
    fin_cases m₀
    · simp
    · simp only [pow_one]; rw [hXZ]; simp
  have hXcomm : Commute (pauliString ![0, 0, 1]) (pauliString (n := 3) ![0, 0, 1] ^ (m₁ : ℕ)) :=
    (Commute.refl _).pow_right _
  rw [← mul_assoc, hXZpow, smul_mul_assoc, mul_assoc, hXcomm.eq, ← mul_assoc]

/-- **Teleportation verified — `Z`-basis input.**  For a `Z`-basis stabilizer input `|a⟩`
(`a : Fin 2`, `Z₀|a⟩ = (-1)^a|a⟩`), the post-measurement state `w` of Fig 1.13 is a `±1` eigenstate
of the measured `Z₁` with outcome `(-1)^{m₁}` (`h1`) and is stabilised by `(-1)^a Z₁Z₂` (`hstab`) —
the surviving stabiliser, which by Part 2 is the transported input logical `Z` reduced by the
propagated Bell-`Z` stabiliser.  Then after Bob's byproduct correction his wire is stabilised by
`(-1)^a Z₂`:
`Z₂ · (Z₂^{m₀}X₂^{m₁} w) = (-1)^a · (Z₂^{m₀}X₂^{m₁} w)`,
i.e. Bob holds the input state `|a⟩`.  The wire-`1` measurement sign `(-1)^{m₁}` on Bob's `Z`
(`Z₂ w = (-1)^{a+m₁} w`, via `pauliZ1_mul_pauliZ1Z2`) is undone by the `X₂^{m₁}` part of the
byproduct (`z2_comm_byproduct`); the `Z₂^{m₀}` part is inert on a `Z`-eigenstate. -/
theorem teleportation_Zbasis (m₀ m₁ a : Fin 2) (w : (Fin 3 → Fin 2) → ℂ)
    (h1 : (pauliString ![0, 3, 0]).mulVec w = (-1 : ℂ) ^ (m₁ : ℕ) • w)
    (hstab : (pauliString ![0, 3, 3]).mulVec w = (-1 : ℂ) ^ (a : ℕ) • w) :
    (pauliString ![0, 0, 3]).mulVec ((teleportByproduct m₀ m₁).mulVec w)
      = (-1 : ℂ) ^ (a : ℕ) • (teleportByproduct m₀ m₁).mulVec w := by
  have hZ2 : (pauliString ![0, 0, 3]).mulVec w = (-1 : ℂ) ^ ((a : ℕ) + (m₁ : ℕ)) • w := by
    rw [← pauliZ1_mul_pauliZ1Z2, ← Matrix.mulVec_mulVec, hstab, Matrix.mulVec_smul, h1, smul_smul,
      ← pow_add]
  rw [Matrix.mulVec_mulVec, z2_comm_byproduct, smul_mulVec, ← Matrix.mulVec_mulVec, hZ2,
    Matrix.mulVec_smul, smul_smul]
  congr 1
  rw [← pow_add, show (m₁ : ℕ) + ((a : ℕ) + (m₁ : ℕ)) = (a : ℕ) + 2 * (m₁ : ℕ) by ring, pow_add,
    pow_mul]
  simp

/-- **Teleportation verified — `X`-basis input.**  For an `X`-basis stabilizer input
(`b : Fin 2`, `X₀`-eigenvalue `(-1)^b`), the post-measurement state `w` is a `±1` eigenstate of the
measured `Z₀` with outcome `(-1)^{m₀}` (`h0`) and is stabilised by `(-1)^b Z₀X₂` (`hstab`) — the
surviving stabiliser, which by Part 2 is the transported input logical `X` reduced by the Bell-`X`
stabiliser.  Then after Bob's byproduct correction his wire is stabilised by `(-1)^b X₂`:
`X₂ · (Z₂^{m₀}X₂^{m₁} w) = (-1)^b · (Z₂^{m₀}X₂^{m₁} w)`,
i.e. Bob holds the input `X`-eigenstate.  The wire-`0` measurement sign `(-1)^{m₀}` on Bob's `X`
(`X₂ w = (-1)^{b+m₀} w`, via `pauliZ0_mul_pauliZ0X2`) is undone by the `Z₂^{m₀}` part of the
byproduct (`x2_comm_byproduct`); the `X₂^{m₁}` part is inert on an `X`-eigenstate. -/
theorem teleportation_Xbasis (m₀ m₁ b : Fin 2) (w : (Fin 3 → Fin 2) → ℂ)
    (h0 : (pauliString ![3, 0, 0]).mulVec w = (-1 : ℂ) ^ (m₀ : ℕ) • w)
    (hstab : (pauliString ![3, 0, 1]).mulVec w = (-1 : ℂ) ^ (b : ℕ) • w) :
    (pauliString ![0, 0, 1]).mulVec ((teleportByproduct m₀ m₁).mulVec w)
      = (-1 : ℂ) ^ (b : ℕ) • (teleportByproduct m₀ m₁).mulVec w := by
  have hX2 : (pauliString ![0, 0, 1]).mulVec w = (-1 : ℂ) ^ ((b : ℕ) + (m₀ : ℕ)) • w := by
    rw [← pauliZ0_mul_pauliZ0X2, ← Matrix.mulVec_mulVec, hstab, Matrix.mulVec_smul, h0, smul_smul,
      ← pow_add]
  rw [Matrix.mulVec_mulVec, x2_comm_byproduct, smul_mulVec, ← Matrix.mulVec_mulVec, hX2,
    Matrix.mulVec_smul, smul_smul]
  congr 1
  rw [← pow_add, show (m₀ : ℕ) + ((b : ℕ) + (m₀ : ℕ)) = (b : ℕ) + 2 * (m₀ : ℕ) by ring, pow_add,
    pow_mul]
  simp

end AxQM.Concrete
