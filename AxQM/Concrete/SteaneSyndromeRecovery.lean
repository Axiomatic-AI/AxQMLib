/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SteaneStandardForm
import AxQM.Concrete.PauliStringCommutation

/-!
# Concrete: explicit recovery operations for the Steane-code syndrome (Nielsen & Chuang, Ex 10.61)

This file works with phase-free Pauli-index strings (`Fin 7 → Fin 4`), the `ZMod 2` syndrome
bits, and the symplectic pairing `pauliAnticommCount`.

It answers Nielsen & Chuang, **Exercise 10.61** (§10.5.8, p. 474):

Explicit recovery operations for each error syndrome of the Steane code.

## What the circuit measures, and what the exercise asks

Figure 10.16 measures the **six standard-form generators** of the Steane code (eq. (10.112),
`Concrete.steaneStdGen`) on the encoded data, recording a `6`-bit **error syndrome**
`β ∈ (ZMod 2)⁶`. For a Pauli error `E`, the `a`-th ancilla measures `gₐ`, and since `gₐ (E|ψ⟩) =
(-1)^{βₐ} E gₐ|ψ⟩ = (-1)^{βₐ} E|ψ⟩` for a codeword `|ψ⟩`, bit `βₐ` is `1` exactly when `E`
*anticommutes* with `gₐ` — the parity of the symplectic pairing `pauliAnticommCount gₐ E`
(`Concrete.pauliString_mul_comm_sign`). This is the syndrome function `steaneSyndrome`.

The **correctable errors** are the identity together with the single-qubit Paulis `Xᵢ, Yᵢ, Zᵢ`
(`i = 0,…,6`) — Nielsen & Chuang's error set for a distance-`3` code (as in Exercise 10.49 for the
five-qubit code). There are `1 + 3·7 = 22` of them (`steaneSingleError`). The exercise's *recovery
operations* are the lookup `syndrome ↦ recovery Pauli`: measure `β`, and apply the unique
single-qubit error carrying that syndrome. Because each error `Eⱼ` is a **Hermitian involution**
(`Eⱼ† = Eⱼ`, `Eⱼ² = I`), re-applying that same Pauli is exactly `E†ⱼ` and undoes the error.

## Why the recovery is well defined, and how it is built

The recovery table is well defined precisely because the **`22` correctable errors have pairwise
distinct syndromes** (`steaneSyndrome_singleError_injective`): the syndrome pins down which
single-qubit error occurred, so a measured `β` determines a unique recovery. This distinctness
is the distance-`3` / perfect-correction property specialised to the Steane code — the analogue, at
the level of the explicit table, of the correctability delivered abstractly by Theorem 10.8. Its
CSS structure is visible in the split `β = (βₓ | β_z)`: the three `X`-type generators `g₁, g₂, g₃`
read the Hamming syndrome locating the `Z`-component of the error, and the three `Z`-type generators
`g₄, g₅, g₆` read the Hamming syndrome locating the `X`-component (so `Yᵢ = Xᵢ Zᵢ` triggers both).

## What is proved

* `steaneSyndrome` — the `6`-bit syndrome of a Pauli error, the parity vector of its symplectic
  pairing with the six Figure-10.16 generators `steaneStdGen`.
* `steaneSingleError` — the `22` correctable errors `{I} ∪ {Xᵢ, Yᵢ, Zᵢ}` as index strings.
* `steaneSyndrome_singleError_zero` — the identity (no error) has the trivial syndrome `0`.
* `steaneSyndrome_singleError_injective` — **the `22` correctable errors have distinct syndromes**,
  so the syndrome determines the recovery: the key well-definedness fact (a finite `decide`).
* `steaneRecovery` — the **explicit recovery table** `β ↦ Eⱼ`: the single-qubit error carrying the
  measured syndrome `β` (and the identity — no correction — for the `64 − 22 = 42` syndromes not
  produced by a single-qubit error, which signal a higher-weight, uncorrectable error).
* `steaneRecovery_steaneSyndrome` — **Exercise 10.61**: recovering from the measured syndrome
  returns exactly the error, `steaneRecovery (steaneSyndrome Eⱼ) = Eⱼ`; since `E†ⱼ = Eⱼ`, this
  is the recovery operation `E†ⱼ`.
* `steaneRecovery_zero` — the trivial syndrome `0` recovers with the identity (no correction).
* `steaneRecovery_pauliMulIndex_singleError` — the recovery **corrects** the error: the product
  `E†ⱼ Eⱼ` is the identity string (`pauliMulIndex (recovery) (error) = 0`), so recovery-after-error
  restores the codeword.

Everything is a finite check over `Fin 22`, `Fin 7`, `Fin 4`, `Fin 6`, `ZMod 2`, decided by
`decide`; the recovery table is genuinely computed by searching the enumerated errors for the one
matching the measured syndrome.
-/

namespace AxQM.Concrete

/-- The **`6`-bit error syndrome** measured by the Figure-10.16 circuit for a Pauli error
`E : Fin 7 → Fin 4` (Nielsen & Chuang §10.5.8). The `a`-th bit is the parity (over `ZMod 2`) of the
symplectic pairing `pauliAnticommCount (steaneStdGen a) E` of `E` with the `a`-th standard-form
generator `gₐ` (eq. (10.112)): `βₐ = 0` when `E` commutes with `gₐ` (measured eigenvalue `+1`) and
`βₐ = 1` when it anticommutes (eigenvalue `−1`), because `gₐ E |ψ⟩ = (−1)^{βₐ} E |ψ⟩` on a codeword.
The three `X`-type generators (`a = 0,1,2`) contribute the Hamming syndrome of the error's
`Z`-component, the three `Z`-type generators (`a = 3,4,5`) that of its `X`-component. -/
def steaneSyndrome (E : Fin 7 → Fin 4) : Fin 6 → ZMod 2 :=
  fun a => (pauliAnticommCount (steaneStdGen a) E : ZMod 2)

/-- The **`22` correctable errors** of the Steane code, indexed by `Fin 22` as Pauli-index strings
`Fin 7 → Fin 4` (`I = 0, X = 1, Y = 2, Z = 3`): `E₀ = I`, then the seven `Xᵢ` (`i = 0,…,6`), the
seven `Yᵢ`, and the seven `Zᵢ`. This is Nielsen & Chuang's error set of the identity together with
all single-qubit Paulis — the errors a distance-`3` code corrects (cf. `Concrete.fiveQubitError`
for the five-qubit code); their `Figure-10.16` syndromes are what the recovery table looks up. -/
def steaneSingleError : Fin 22 → Fin 7 → Fin 4 :=
  ![![0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1],
    ![2, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 2],
    ![3, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0, 0], ![0, 0, 0, 3, 0, 0, 0],
    ![0, 0, 0, 0, 3, 0, 0], ![0, 0, 0, 0, 0, 3, 0], ![0, 0, 0, 0, 0, 0, 3]]

/-- **The identity error has the trivial syndrome** `steaneSyndrome (steaneSingleError 0) = 0`: with
no error, every generator is measured with eigenvalue `+1`, so no recovery is triggered. -/
theorem steaneSyndrome_singleError_zero : steaneSyndrome (steaneSingleError 0) = 0 := by decide

/-- **The `22` correctable single-qubit errors have pairwise-distinct syndromes** — the key fact
that makes the recovery table well defined. Since the syndrome
`steaneSyndrome (steaneSingleError j)` determines `j`, a measured syndrome pins down which
single-qubit error occurred, hence the
recovery operation. This is the distance-`3` / perfect-single-error-correction property of Steane
code stated at the level of the explicit `Figure-10.16` syndrome table (a finite `decide` over the
`22 × 22` pairs and their six symplectic pairings). -/
theorem steaneSyndrome_singleError_injective :
    Function.Injective (fun j => steaneSyndrome (steaneSingleError j)) := by decide

/-- The **explicit recovery table** of Exercise 10.61: for a measured syndrome `β ∈ (ZMod 2)⁶`,
search the enumerated correctable errors `steaneSingleError` for the (unique, by
`steaneSyndrome_singleError_injective`) one whose `Figure-10.16` syndrome is `β`, and return that
Pauli string — the recovery `E†ⱼ` (each `Eⱼ` being a Hermitian involution, `E†ⱼ = Eⱼ`). For the
`64 − 22 = 42` syndromes that no single-qubit error produces — signalling a higher-weight,
uncorrectable error — it returns the identity string (no correction). -/
def steaneRecovery (β : Fin 6 → ZMod 2) : Fin 7 → Fin 4 :=
  match (List.finRange 22).find? (fun j => decide (steaneSyndrome (steaneSingleError j) = β)) with
  | some j => steaneSingleError j
  | none => fun _ => 0

/-- **Nielsen & Chuang, Exercise 10.61.** *The explicit recovery operation for each measurable
syndrome.* Recovering from the syndrome produced by a single-qubit error returns exactly that error,
`steaneRecovery (steaneSyndrome (steaneSingleError j)) = steaneSingleError j`. Because each `Eⱼ`
is a Hermitian involution (`E†ⱼ = Eⱼ`), the recovery to apply is this same Pauli — Nielsen &
Chuang's recovery operation `E†ⱼ`. Well definedness rests on the distinct syndromes
(`steaneSyndrome_singleError_injective`): the `find?` locates the error carrying the measured
syndrome, and distinctness forces it to be `steaneSingleError j` itself. -/
theorem steaneRecovery_steaneSyndrome (j : Fin 22) :
    steaneRecovery (steaneSyndrome (steaneSingleError j)) = steaneSingleError j := by
  revert j; decide

/-- **The trivial syndrome recovers with the identity** (no correction):
`steaneRecovery 0 = steaneSingleError 0 = I`. Combined with `steaneSyndrome_singleError_zero`, this
is the "no detected error ⟹ do nothing" entry of the recovery table. -/
theorem steaneRecovery_zero : steaneRecovery 0 = steaneSingleError 0 := by decide

/-- **The recovery corrects the error**: the product `E†ⱼ Eⱼ` of the recovery operation and the
error is the identity string (`pauliMulIndex (recovery) (error) = 0`), so applying the
syndrome-selected recovery after `Eⱼ` returns the codeword. This composes
`steaneRecovery_steaneSyndrome`
(the recovery equals `Eⱼ`) with the involution `Eⱼ Eⱼ = I` of a single-qubit Pauli. -/
theorem steaneRecovery_pauliMulIndex_singleError (j : Fin 22) :
    pauliMulIndex (steaneRecovery (steaneSyndrome (steaneSingleError j))) (steaneSingleError j)
      = 0 := by
  revert j; decide

end AxQM.Concrete
