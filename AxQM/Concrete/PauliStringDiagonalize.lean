/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringBasisChange

/-!
# Concrete: single-qubit basis change diagonalising an arbitrary Pauli string to all-`Z`

This file generalises the matrix core of Nielsen & Chuang **Exercise 4.51** (the specific `X ⊗ Y ⊗
Z` reduction of
`Concrete/PauliStringBasisChange.lean`) to an **arbitrary** `n`-qubit Pauli string, the first step
of **Problem 4.3(3)** — "implement `exp(-i h_g g Δ)` using `O(n)` one- and two-qubit gates".

## The construction (N&C §4.7.3)

N&C's simulation algorithm reduces the exponential of any tensor-product Pauli Hamiltonian
`g = ⨂ₖ σ_{gₖ}` to the exponential of an operator that is `Z` on the string's support and `I`
elsewhere — whose `e^{-iΔt}` circuit is the Figure-4.19 parity computation — by **single-qubit basis
changes**: an `X` factor is conjugated to `Z` by Hadamard (`H · Z · H = X`), a `Y` factor by `S·H`
(`(SH) · Z · (SH)† = Y`), a `Z` or `I` factor is left alone. Collecting these per-qubit gates into a
single-qubit family `B = ⨂ₖ Bₖ`, the string factorises as `g = B · d(g) · B†`, where `d(g)` is the
**diagonalised string** (`I ↦ I`, every `X`/`Y`/`Z` factor `↦ Z`); hence
`exp(s · g) = B · exp(s · d(g)) · B†` for any scalar `s` (physically `s = -i h_g Δ`).

## What is proved

* `pauliDiagGate a` — the single-qubit basis-change gate for Pauli `σ_a`
  (`![1, H, SH, 1]`: identity for `I`/`Z`, Hadamard for `X`, `S·H` for `Y`);
  `pauliToZ a` — the diagonalised Pauli index (`![0, 3, 3, 3]`: `I ↦ I`, else `↦ Z`).
* `pauliDiagGate_conj_pauli` — the per-qubit conjugation `Bₐ · σ_{d(a)} · Bₐ† = σₐ`, and
  `pauliDiagGate_mul_conjTranspose` / `pauliDiagGate_conjTranspose_mul` — each `Bₐ` unitary.
* `pauliString_conj_kronFamily_pauliDiagGate` — the string identity
  `B · d(g) · B† = g` (`B = kronFamily (Bₐ ∘ g)`, `d(g) = pauliString (pauliToZ ∘ g)`), with
  `kronFamily_pauliDiagGate_mul_conjTranspose` / `..._conjTranspose_mul` its unitarity.
* `pauliStringStd_conj_kronFamilyStd_pauliDiagGate` and its unitarity — the same on the flat
  computational-basis indexing `Fin (2ⁿ)` that `pauliStringStd` (and the register `qudit (2ⁿ)`) use.
* `pauliStringStd_exp_smul_conj_kronFamilyStd_pauliDiagGate` — the exponentiated form
  `exp(s · g) = B · exp(s · d(g)) · B†` on `Fin (2ⁿ)`, the matrix content of "apply `B`, run the
  diagonal (Figure-4.19) simulation, undo `B`" for a general Pauli string.
-/

open Matrix Complex

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The per-qubit diagonalising gate -/

/-- The **single-qubit basis-change gate** `Bₐ` diagonalising Pauli `σ_a` to `Z`: `![1, H, SH, 1]`,
i.e. the identity for `I` (`a = 0`) and `Z` (`a = 3`), Hadamard `H` for `X` (`a = 1`), and the `Y`
basis change `S·H` (`basisChangeY`) for `Y` (`a = 2`). It satisfies `Bₐ · σ_{pauliToZ a} · Bₐ† = σₐ`
(`pauliDiagGate_conj_pauli`): conjugating the diagonalised factor recovers the original Pauli. -/
noncomputable def pauliDiagGate : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![1, hadamardC, basisChangeY, 1]

/-- The **diagonalised Pauli index** `d(a)` sending every non-identity Pauli to `Z`: `![0, 3, 3, 3]`
(`I ↦ I`, `X ↦ Z`, `Y ↦ Z`, `Z ↦ Z`). For a Pauli string `g`, `pauliString (pauliToZ ∘ g)` is `Z`
on the string's support and `I` elsewhere — the operator whose exponential the Figure-4.19 parity
circuit implements. -/
def pauliToZ : Fin 4 → Fin 4 := ![0, 3, 3, 3]

/-- `pauliToZ` sends every **non-identity** Pauli index to `Z` (`3`): the diagonalisation puts a `Z`
on each support wire of a Pauli string. -/
theorem pauliToZ_eq_three_of_ne_zero (m : Fin 4) (hm : m ≠ 0) : pauliToZ m = 3 := by
  fin_cases m <;> simp_all [pauliToZ]

/-- `pauliToZ` vanishes **exactly** on the identity index `I` (`0`): `pauliToZ m = 0 ↔ m = 0`.
Together with `pauliToZ_eq_three_of_ne_zero` this pins the diagonalised string `d(g) = pauliToZ ∘ g`
— `I` off the support of `g`, `Z` on it. -/
theorem pauliToZ_eq_zero_iff {m : Fin 4} : pauliToZ m = 0 ↔ m = 0 := by
  fin_cases m <;> decide

/-- **Per-qubit diagonalisation** `Bₐ · σ_{d(a)} · Bₐ† = σₐ`. For `a = 0` (`I`) and `a = 3` (`Z`)
the gate is the identity and `d(a)` leaves the factor unchanged; for `a = 1` (`X`) this is
`H · Z · H = X` (`hadamardC_mul_pauliZ_mul_hadamardC`) and for `a = 2` (`Y`) it is
`(SH) · Z · (SH)† = Y` (`basisChangeY_conj_pauliZ`). -/
theorem pauliDiagGate_conj_pauli (a : Fin 4) :
    pauliDiagGate a * pauli (pauliToZ a) * (pauliDiagGate a)ᴴ = pauli a := by
  fin_cases a
  · simp [pauliDiagGate, pauliToZ, pauli]
  · simpa [pauliDiagGate, pauliToZ, pauli, hadamardC_isHermitian.eq] using
      hadamardC_mul_pauliZ_mul_hadamardC
  · simpa [pauliDiagGate, pauliToZ, pauli] using basisChangeY_conj_pauliZ
  · simp [pauliDiagGate, pauliToZ, pauli]

/-- Each diagonalising gate `Bₐ` is unitary: `Bₐ · Bₐ† = 1`. The identity and `Z` gates are `1`, the
`X` gate is `H` (`hadamardC_mul_self`), the `Y` gate is `S·H` (`basisChangeY_mul_conjTranspose`). -/
theorem pauliDiagGate_mul_conjTranspose (a : Fin 4) :
    pauliDiagGate a * (pauliDiagGate a)ᴴ = 1 := by
  fin_cases a
  · simp [pauliDiagGate]
  · simpa [pauliDiagGate, hadamardC_isHermitian.eq] using hadamardC_mul_self
  · simpa [pauliDiagGate] using basisChangeY_mul_conjTranspose
  · simp [pauliDiagGate]

/-- Each diagonalising gate `Bₐ` is unitary: `Bₐ† · Bₐ = 1`. As `pauliDiagGate_mul_conjTranspose`
with the factors reversed. -/
theorem pauliDiagGate_conjTranspose_mul (a : Fin 4) :
    (pauliDiagGate a)ᴴ * pauliDiagGate a = 1 := by
  fin_cases a
  · simp [pauliDiagGate]
  · simpa [pauliDiagGate, hadamardC_isHermitian.eq] using hadamardC_mul_self
  · simpa [pauliDiagGate] using basisChangeY_conjTranspose_mul
  · simp [pauliDiagGate]

/-- Each diagonalising gate `Bₐ` lies in the unitary group `U(2)`, since `Bₐ† · Bₐ = 1`
(`pauliDiagGate_conjTranspose_mul`). The membership form, letting each `Bₐ` be promoted to a gate
`Evolution` (`quditGate` / `unitaryGate`) for the basis-change layer of Problem 4.3(3). -/
theorem pauliDiagGate_mem_unitaryGroup (a : Fin 4) :
    pauliDiagGate a ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Matrix.mem_unitaryGroup_iff'.2 <| by
    rw [Matrix.star_eq_conjTranspose]; exact pauliDiagGate_conjTranspose_mul a

/-! ### The `n`-qubit basis-change reduction `g = B · d(g) · B†` -/

/-- **Problem 4.3(3), matrix form: the basis-change reduction of an arbitrary Pauli string.**
The single-qubit family `B = ⨂ₖ B_{gₖ}` conjugates the diagonalised string
`d(g) = ⨂ₖ σ_{pauliToZ (gₖ)}` (`Z` on the support, `I` elsewhere) back to the original Pauli string:
`B · d(g) · B† = g`. Reducing both strings to `kronFamily` and applying the mixed-product property
twice (`kronFamily_mul`, `kronFamily_conjTranspose`) turns the left side into
`⨂ₖ (B_{gₖ} · σ_{pauliToZ (gₖ)} · B_{gₖ}†)`, which is `⨂ₖ σ_{gₖ} = g` factor-by-factor
(`pauliDiagGate_conj_pauli`). Generalises `pauliString_conj_kronFamily` (the `X ⊗ Y ⊗ Z` case). -/
theorem pauliString_conj_kronFamily_pauliDiagGate (g : Fin n → Fin 4) :
    kronFamily (fun k => pauliDiagGate (g k)) * pauliString (fun k => pauliToZ (g k))
        * (kronFamily (fun k => pauliDiagGate (g k)))ᴴ
      = pauliString g := by
  rw [pauliString_eq_kronFamily (fun k => pauliToZ (g k)), kronFamily_conjTranspose,
    kronFamily_mul, kronFamily_mul, pauliString_eq_kronFamily g]
  congr 1
  funext k
  exact pauliDiagGate_conj_pauli (g k)

/-- The tensor basis change `B = ⨂ₖ B_{gₖ}` is unitary: `B · B† = 1`. Factor-by-factor from the
per-qubit unitarity (`pauliDiagGate_mul_conjTranspose`) via `kronFamily_mul`, `kronFamily_one`. -/
theorem kronFamily_pauliDiagGate_mul_conjTranspose (g : Fin n → Fin 4) :
    kronFamily (fun k => pauliDiagGate (g k)) * (kronFamily (fun k => pauliDiagGate (g k)))ᴴ
      = 1 := by
  rw [kronFamily_conjTranspose, kronFamily_mul]
  simp only [pauliDiagGate_mul_conjTranspose, kronFamily_one]

/-- The tensor basis change `B = ⨂ₖ B_{gₖ}` is unitary: `B† · B = 1`. -/
theorem kronFamily_pauliDiagGate_conjTranspose_mul (g : Fin n → Fin 4) :
    (kronFamily (fun k => pauliDiagGate (g k)))ᴴ * kronFamily (fun k => pauliDiagGate (g k))
      = 1 := by
  rw [kronFamily_conjTranspose, kronFamily_mul]
  simp only [pauliDiagGate_conjTranspose_mul, kronFamily_one]

/-- **Problem 4.3(3), exponentiated form on bit strings: the circuit for `exp(s · g)`.** For any
complex scalar `s` (physically `s = -i h_g Δ`), the exponential of a general Pauli string factors as
the local conjugation of the diagonalised (all-`Z`-on-support) exponential:
`exp(s · g) = B · exp(s · d(g)) · B†` on the bit-string register `Fin n → Fin 2`, where
`B = ⨂ₖ B_{gₖ}` (`kronFamily (pauliDiagGate ∘ g)`) and `d(g) = pauliToZ ∘ g` (the diagonalised
string). Since `s • g` is conjugated by `B` exactly as `g` is
(`pauliString_conj_kronFamily_pauliDiagGate`), and `B` is unitary — hence a unit with inverse `B†` —
`Matrix.exp_units_conj` pushes the conjugation through the exponential.

This is the **bit-string companion** of the flat-register
`pauliStringStd_exp_smul_conj_kronFamilyStd_pauliDiagGate`; it is the form Problem 4.3(3)'s
Figure-4.19 circuit assembly composes with the parity-cascade collapse
`pauliString_exp_smul_conj_cnotFanInto` (which is stated over bit strings), keeping the entire
exponential reduction on `Fin n → Fin 2` and reindexing to the register only once, at the end. -/
theorem pauliString_exp_smul_conj_kronFamily_pauliDiagGate (g : Fin n → Fin 4) (s : ℂ) :
    NormedSpace.exp (s • pauliString g)
      = kronFamily (fun k => pauliDiagGate (g k))
          * NormedSpace.exp (s • pauliString (fun k => pauliToZ (g k)))
          * (kronFamily (fun k => pauliDiagGate (g k)))ᴴ := by
  let u : (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)ˣ :=
    ⟨kronFamily (fun k => pauliDiagGate (g k)), (kronFamily (fun k => pauliDiagGate (g k)))ᴴ,
      kronFamily_pauliDiagGate_mul_conjTranspose g, kronFamily_pauliDiagGate_conjTranspose_mul g⟩
  have hconj : s • pauliString g
      = kronFamily (fun k => pauliDiagGate (g k))
          * (s • pauliString (fun k => pauliToZ (g k)))
          * (kronFamily (fun k => pauliDiagGate (g k)))ᴴ := by
    rw [← pauliString_conj_kronFamily_pauliDiagGate g, Matrix.mul_smul, Matrix.smul_mul]
  rw [hconj]
  exact Matrix.exp_units_conj u (s • pauliString (fun k => pauliToZ (g k)))

/-! ### The flat computational-basis (register) indexing `Fin (2ⁿ)` -/

/-- **Problem 4.3(3), the reduction on the flat register `Fin (2ⁿ)`.** The Std-indexed basis change
`B = ⨂ₖ B_{gₖ}` conjugates the diagonalised string to the original: `B · d(g) · B† = g`, on the
`Fin (2ⁿ)` computational basis that `pauliStringStd` (and the register `qudit (2ⁿ)`) use. The flat
image of `pauliString_conj_kronFamily_pauliDiagGate`, obtained by `submatrix_conj_equiv`. -/
theorem pauliStringStd_conj_kronFamilyStd_pauliDiagGate (g : Fin n → Fin 4) :
    kronFamilyStd (fun k => pauliDiagGate (g k)) * pauliStringStd (fun k => pauliToZ (g k))
        * (kronFamilyStd (fun k => pauliDiagGate (g k)))ᴴ
      = pauliStringStd g := by
  simp only [kronFamilyStd, pauliStringStd]
  rw [← submatrix_conj_equiv, pauliString_conj_kronFamily_pauliDiagGate]

/-- The Std basis change is unitary: `B · B† = 1` on `Fin (2ⁿ)`. The flat image of
`kronFamily_pauliDiagGate_mul_conjTranspose`. -/
theorem kronFamilyStd_pauliDiagGate_mul_conjTranspose (g : Fin n → Fin 4) :
    kronFamilyStd (fun k => pauliDiagGate (g k)) * (kronFamilyStd (fun k => pauliDiagGate (g k)))ᴴ
      = 1 := by
  simp only [kronFamilyStd, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, kronFamily_pauliDiagGate_mul_conjTranspose,
    Matrix.submatrix_one_equiv]

/-- The Std basis change is unitary: `B† · B = 1` on `Fin (2ⁿ)`. -/
theorem kronFamilyStd_pauliDiagGate_conjTranspose_mul (g : Fin n → Fin 4) :
    (kronFamilyStd (fun k => pauliDiagGate (g k)))ᴴ * kronFamilyStd (fun k => pauliDiagGate (g k))
      = 1 := by
  simp only [kronFamilyStd, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, kronFamily_pauliDiagGate_conjTranspose_mul,
    Matrix.submatrix_one_equiv]

/-- **Problem 4.3(3), exponentiated form: the circuit for `exp(s · g)`.** For any complex scalar `s`
(physically `s = -i h_g Δ`), the exponential of a general Pauli string factors as the local
conjugation of the diagonalised (all-`Z`-on-support) exponential:
`exp(s · g) = B · exp(s · d(g)) · B†` on the flat register `Fin (2ⁿ)`. Since `s • g` is conjugated
by `B` exactly as `g` is (`pauliStringStd_conj_kronFamilyStd_pauliDiagGate`), and `B` is unitary —
hence a unit with inverse `B†` — `Matrix.exp_units_conj` pushes the conjugation through the
exponential.
This is the algebraic content of "apply the local basis change `B`, run the Figure-4.19 diagonal
simulation, undo `B`" for an arbitrary Pauli string; it generalises
`pauliString_exp_smul_conj_kronFamily` (the `X ⊗ Y ⊗ Z` case). -/
theorem pauliStringStd_exp_smul_conj_kronFamilyStd_pauliDiagGate (g : Fin n → Fin 4) (s : ℂ) :
    NormedSpace.exp (s • pauliStringStd g)
      = kronFamilyStd (fun k => pauliDiagGate (g k))
          * NormedSpace.exp (s • pauliStringStd (fun k => pauliToZ (g k)))
          * (kronFamilyStd (fun k => pauliDiagGate (g k)))ᴴ := by
  let u : (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)ˣ :=
    ⟨kronFamilyStd (fun k => pauliDiagGate (g k)), (kronFamilyStd (fun k => pauliDiagGate (g k)))ᴴ,
      kronFamilyStd_pauliDiagGate_mul_conjTranspose g,
      kronFamilyStd_pauliDiagGate_conjTranspose_mul g⟩
  have hconj : s • pauliStringStd g
      = kronFamilyStd (fun k => pauliDiagGate (g k))
          * (s • pauliStringStd (fun k => pauliToZ (g k)))
          * (kronFamilyStd (fun k => pauliDiagGate (g k)))ᴴ := by
    rw [← pauliStringStd_conj_kronFamilyStd_pauliDiagGate g, Matrix.mul_smul, Matrix.smul_mul]
  rw [hconj]
  exact Matrix.exp_units_conj u (s • pauliStringStd (fun k => pauliToZ (g k)))

end AxQM.Concrete
