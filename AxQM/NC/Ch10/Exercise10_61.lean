/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.SteaneSyndromeRecovery

/-!
# Nielsen & Chuang, Exercise 10.61 — explicit recovery operations for each Steane-code syndrome

Describe explicit recovery operations Ej-dagger for each syndrome measurable by circuit Fig 10.16.
— Nielsen & Chuang, *Quantum Computation and Quantum Information*, §10.5.8 (p. 474).

## What the exercise asks, and how it is answered

Figure 10.16 measures the **six standard-form generators** of the Steane code (eq. (10.112)) on the
encoded data, producing a `6`-bit **error syndrome** `β ∈ (ZMod 2)⁶`: bit `βₐ` is `0`/`1` as the
error commutes/anticommutes with the `a`-th generator `gₐ` (the eigenvalue `(−1)^{βₐ}` measured by
ancilla `a`). The exercise's *recovery operations* form the lookup `syndrome ↦ recovery Pauli`: the
correctable errors are the identity and the single-qubit Paulis `Xᵢ, Yᵢ, Zᵢ`, and — because these
`22` errors have **pairwise-distinct syndromes** (the distance-`3` property) — a measured `β` pins
down which one occurred. The recovery is to re-apply that Pauli: each error `Eⱼ` is a Hermitian
involution (`E†ⱼ = Eⱼ`, `Eⱼ² = I`), so re-applying it is exactly `E†ⱼ` and undoes the error.

## The declarations

Compare the other stabilizer-code items, Theorem 10.8 (`AxQM/NC/Ch10/Theorem10_8.lean`) and
Exercise 10.49 (`AxQM/NC/Ch10/Exercise10_49.lean`).

All in `AxQM/Concrete/SteaneSyndromeRecovery.lean`:

* `AxQM.Concrete.steaneSyndrome` — the `6`-bit syndrome measured by Figure 10.16 for a
  Pauli error `E`, the parity vector `a ↦ (pauliAnticommCount (steaneStdGen a) E : ZMod 2)` of its
  symplectic pairing with the six standard-form generators (eq. (10.112)).
* `AxQM.Concrete.steaneSingleError` — the `22` correctable errors `{I} ∪ {Xᵢ, Yᵢ, Zᵢ}` as
  index strings, and `steaneSyndrome_singleError_zero` — the identity has the trivial syndrome `0`.
* `AxQM.Concrete.steaneSyndrome_singleError_injective` — **the `22` correctable errors have
  pairwise-distinct syndromes**, so the measured syndrome determines the recovery: the
  well-definedness fact behind the whole table (the distance-`3` property in explicit form).
* `AxQM.Concrete.steaneRecovery` — the **explicit recovery table** `β ↦ Eⱼ`: the
  single-qubit error carrying the measured syndrome `β` (identity — no correction — for the `42`
  syndromes no single-qubit error produces, which signal a higher-weight uncorrectable error).
* `AxQM.Concrete.steaneRecovery_steaneSyndrome` — **Exercise 10.61**: recovering from the
  measured syndrome returns exactly the error, `steaneRecovery (steaneSyndrome Eⱼ) = Eⱼ` — the
  recovery operation `E†ⱼ` (since `E†ⱼ = Eⱼ`); with `steaneRecovery_zero` (trivial syndrome ⟹ no
  correction) and `steaneRecovery_pauliMulIndex_singleError` (`E†ⱼ Eⱼ = I`, so recovery-after-error
  restores the codeword).
-/
