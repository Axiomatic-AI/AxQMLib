/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CheckMatrix
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Concrete: Nielsen & Chuang Proposition 10.4 — flipping a single stabilizer generator

This file formalizes Nielsen & Chuang's
**Proposition 10.4** (§10.5.1, p. 458), the "innocuous looking" but repeatedly-used fact behind
the dimension count for stabilizer code spaces (Proposition 10.5) and the manipulation of
stabilizers under Clifford gates.

Proposition 10.4: for independent generators with −I ∉ S there is a Pauli conjugating one generator
to its negative and fixing the others.

## Statement shape and faithfulness

We work throughout with the **phase-free** Pauli strings `Concrete.pauliString g` (indexed by
`g : Fin n → Fin 4`), which carry no `±1, ±i` prefactor. Two design points make this faithful to
N&C:

* **`-I ∉ S` enters only through `gⱼ² = I`.** N&C's hypothesis `-I ∉ S` forces every element of `S`
  — in particular every generator — to square to the identity and hence to be a *Hermitian
  involution* (Exercises 10.34/10.35). That per-generator involution property is all the proof of
  10.4 actually uses, and every `pauliString g` is already an involution (`pauliString_mul_self`)
  and Hermitian (`pauliString_isHermitian`) unconditionally. So the phase-free representation
  supplies exactly the consequence of `-I ∉ S` the argument needs — with no `-I ∉ S` hypothesis to
  carry. (It does *not* claim the phase-free strings generate a group avoiding `-I`; e.g.
  `(P_X P_Z)² = -I`. The proof never needs that group-level fact.)
* **"independent generators" ⇔ "check-matrix rows linearly independent".** This is exactly the
  content of Proposition 10.3 (in the `-I ∉ S` world). N&C's proof of 10.4 opens by invoking 10.3
  to pass to linear independence of the rows, and the whole argument then uses only that. We
  therefore state the hypothesis directly as `LinearIndependent (ZMod 2) (fun j ↦ checkRow (gⱼ))`
  — the equivalent (not weaker) form the proof consumes. The check row `checkRow`
  (`Concrete/CheckMatrix.lean`) is the `(x | z)` symplectic representation.

The conjugation `g gⱼ g†` is `pauliString p * pauliString (gⱼ) * star (pauliString p)`, with
`star` the Hermitian adjoint (`†`); a phase-free Pauli string is Hermitian, so `star (pauliString
p) = pauliString p`, but writing the adjoint keeps the statement literally N&C's `g gⱼ g†`.

## The proof

Conjugation by a Pauli string reads off the commutation sign (`pauliString_conj`):
`P_p P_h P_p† = (-1)^{⟨p, h⟩} P_h`, where `⟨p, h⟩ = pauliAnticommCount p h` is the symplectic form
of Exercise 10.33. So the task is to find `p` whose symplectic form with `gⱼ` has parity `δᵢⱼ`.

This is the linear-algebra heart of N&C's proof ("`GΛx = eᵢ` has a solution because the rows of
`G` are independent"). We realize it over the field `ZMod 2`:

* `checkSymplectic` is the binary symplectic form `⟨(x, z), (x', z')⟩ = ∑ₖ (xₖ z'ₖ + zₖ x'ₖ)` on
  check rows; `checkSymplectic_checkRow` identifies it with `(pauliAnticommCount g h : ZMod 2)`.
* `checkSymplectic_nondegenerate`: the form is nondegenerate.
* Since the rows `checkRow (gⱼ)` are linearly independent, `checkRow (gᵢ)` is not in the span of the
  others (`LinearIndependent.notMem_span`), so there is a *separating functional* `f`
  (`Submodule.exists_le_ker_of_notMem`) with `f (checkRow gᵢ) ≠ 0` and `f` vanishing on the others.
  Over `ZMod 2` "nonzero" means "`= 1`", so `f (checkRow gⱼ) = δᵢⱼ`.
* Nondegeneracy makes `checkSymplectic` a linear equivalence to the dual
  (`LinearMap.BilinForm.toDual`), so `f = checkSymplectic w` for some `w`; and `checkRow` is onto
  (`checkRow_surjective`), so `w = checkRow p` for a Pauli index `p`. Then
  `(pauliAnticommCount p gⱼ : ZMod 2) = f (checkRow gⱼ) = δᵢⱼ`, i.e. the count is odd exactly for
  `j = i`, giving `P_p P_{gᵢ} P_p† = -P_{gᵢ}` and `P_p P_{gⱼ} P_p† = P_{gⱼ}` for `j ≠ i`.

The reusable pieces (`pauliString_conj`, `checkSymplectic` and its nondegeneracy,
`checkRow_surjective`) are used throughout the Chapter 10 stabilizer development
(Proposition 10.5, Theorems 10.6–10.8).

These are the statements of N&C Proposition 10.4 (p. 458).
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### Conjugation of a Pauli string by another -/

/-- **Conjugation of a Pauli string reads off the commutation sign.** Conjugating `P_h` by another
Pauli string `P_p` (with its Hermitian adjoint `P_p† = star (pauliString p)`, which equals `P_p`)
multiplies it by the symplectic-form sign:
`P_p P_h P_p† = (-1)^{pauliAnticommCount p h} • P_h`. Immediate from the commutation sign law
`pauliString_mul_comm_sign` (`P_p P_h = (-1)^{…} P_h P_p`) and the involution `pauliString_mul_self`
(`P_p P_p = I`), after replacing the adjoint by `P_p` (`pauliString_isHermitian`). -/
theorem pauliString_conj (p h : Fin n → Fin 4) :
    pauliString p * pauliString h * star (pauliString p)
      = (-1 : ℂ) ^ pauliAnticommCount p h • pauliString h := by
  rw [Matrix.star_eq_conjTranspose, (pauliString_isHermitian p).eq,
    pauliString_mul_comm_sign p h, smul_mul_assoc, mul_assoc, pauliString_mul_self, mul_one]

/-- Conjugation **fixes** a Pauli string that commutes with the conjugator (even symplectic form):
`P_p P_h P_p† = P_h` when `pauliAnticommCount p h` is even. The sign `(-1)^{even}` is `+1`. -/
theorem pauliString_conj_of_even (p h : Fin n → Fin 4)
    (hc : Even (pauliAnticommCount p h)) :
    pauliString p * pauliString h * star (pauliString p) = pauliString h := by
  rw [pauliString_conj, hc.neg_one_pow, one_smul]

/-- Conjugation **flips** a Pauli string that anticommutes with the conjugator (odd symplectic
form): `P_p P_h P_p† = -P_h` when `pauliAnticommCount p h` is odd. The sign `(-1)^{odd}` is `-1`. -/
theorem pauliString_conj_of_odd (p h : Fin n → Fin 4)
    (hc : Odd (pauliAnticommCount p h)) :
    pauliString p * pauliString h * star (pauliString p) = -pauliString h := by
  rw [pauliString_conj, hc.neg_one_pow, neg_one_smul]

/-! ### The binary symplectic form on check rows -/

/-- The **binary symplectic form** on check-matrix rows, `⟨(x, z), (x', z')⟩ = ∑ₖ (xₖ z'ₖ + zₖ
x'ₖ)` over `ZMod 2`. This is `r(g) Λ r(g')ᵀ` for `Λ = [[0, I], [I, 0]]`; it is the mod-2 quantity
of Nielsen & Chuang, Exercise 10.33, packaged as an honest `ZMod 2`-bilinear form so that its
nondegeneracy is available for the linear algebra of Proposition 10.4. -/
def checkSymplectic :
    LinearMap.BilinForm (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
  LinearMap.mk₂ (ZMod 2)
    (fun u v => ∑ k, (u.1 k * v.2 k + u.2 k * v.1 k))
    (fun u₁ u₂ v => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring)
    (fun c u v => by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; ring)
    (fun u v₁ v₂ => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring)
    (fun c u v => by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; ring)

@[simp]
theorem checkSymplectic_apply (u v : (Fin n → ZMod 2) × (Fin n → ZMod 2)) :
    checkSymplectic u v = ∑ k, (u.1 k * v.2 k + u.2 k * v.1 k) := by
  simp only [checkSymplectic, LinearMap.mk₂_apply]

/-- The symplectic form on check rows **is** the mod-2 anticommutation count:
`checkSymplectic (r g) (r h) = (pauliAnticommCount g h : ZMod 2)`. Both sides are the sum over
qubits of `x_g z_h + z_g x_h`; the left computes it in `ZMod 2`, the right casts the `ℕ`-valued
`pauliAnticommCount` (a sum of `singlePauliAnticomm`s). -/
theorem checkSymplectic_checkRow (g h : Fin n → Fin 4) :
    checkSymplectic (checkRow g) (checkRow h) = (pauliAnticommCount g h : ZMod 2) := by
  rw [checkSymplectic_apply, pauliAnticommCount, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [checkRow, pauliBit, singlePauliAnticomm]
  push_cast
  ring

/-- **The binary symplectic form is nondegenerate.** If `u`'s symplectic form with every vector
vanishes, then `u = 0`: testing against `(0, eₖ)` extracts `u.1 k` and against `(eₖ, 0)` extracts
`u.2 k`. Over the field `ZMod 2` on the finite free module `(Fin n → ZMod 2)²`, left-separating
already gives full nondegeneracy (`Nondegenerate.ofSeparatingLeft`). -/
theorem checkSymplectic_nondegenerate : (checkSymplectic (n := n)).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro u hu
  have h1 : ∀ k, u.1 k = 0 := by
    intro k
    have hk := hu (0, Pi.single k 1)
    simpa [checkSymplectic_apply, Pi.single_apply, Finset.sum_ite_eq'] using hk
  have h2 : ∀ k, u.2 k = 0 := by
    intro k
    have hk := hu (Pi.single k 1, 0)
    simpa [checkSymplectic_apply, Pi.single_apply, Finset.sum_ite_eq'] using hk
  exact Prod.ext (funext h1) (funext h2)

/-! ### Surjectivity of the check-row map -/

/-- The inverse of the single-qubit check-bit map `pauliBit`: the Pauli index with prescribed
`(x, z)` bits (`(0,0) ↦ I`, `(1,0) ↦ X`, `(1,1) ↦ Y`, `(0,1) ↦ Z`). Used to invert `checkRow`
qubitwise. -/
def bitToPauli (b : ZMod 2 × ZMod 2) : Fin 4 :=
  if b.1 = 0 then (if b.2 = 0 then 0 else 3) else (if b.2 = 0 then 1 else 2)

/-- `bitToPauli` is a right inverse of `pauliBit`: `pauliBit (bitToPauli b) = b`. A finite check on
the four `(x, z)` bit patterns. -/
theorem pauliBit_bitToPauli : ∀ b : ZMod 2 × ZMod 2, pauliBit (bitToPauli b) = b := by decide

/-- **The check-row map is surjective.** Every `(x, z) : (Fin n → ZMod 2) × (Fin n → ZMod 2)` is the
check row `r(p)` of some Pauli string `p`: take `p k` to be the Pauli with bits `(xₖ, zₖ)`
(`bitToPauli`). This lets us realize any solution vector of the symplectic system as an actual
element of the Pauli group. -/
theorem checkRow_surjective : Function.Surjective (checkRow (n := n)) := by
  intro v
  exact ⟨fun k => bitToPauli (v.1 k, v.2 k), by simp only [checkRow, pauliBit_bitToPauli]⟩

/-! ### Proposition 10.4 -/

/-- **Nielsen & Chuang, Proposition 10.4.** For a family of `l` phase-free generators `g₁, …, g_l`
(`g : Fin l → (Fin n → Fin 4)`) whose check-matrix rows are `ZMod 2`-linearly independent
(equivalently, by Proposition 10.3, the generators are independent; `-I ∉ S` is automatic for
phase-free Pauli strings), and any fixed index `i`, there is a Pauli string `p ∈ Gₙ` whose
conjugation **flips** `gᵢ` (`P_p P_{gᵢ} P_p† = -P_{gᵢ}`) and **fixes** every other generator
(`P_p P_{gⱼ} P_p† = P_{gⱼ}` for `j ≠ i`).

The witness `p` is built from a separating functional for the independent rows, realized as a
symplectic pairing via nondegeneracy and pulled back through `checkRow`; conjugation then flips or
fixes each `gⱼ` according to the parity of `pauliAnticommCount p (g j)`, which is `1` for `j = i`
and `0` otherwise. -/
theorem exists_pauliString_conj_flip {l : ℕ} (g : Fin l → (Fin n → Fin 4))
    (hindep : LinearIndependent (ZMod 2) fun j => checkRow (g j)) (i : Fin l) :
    ∃ p : Fin n → Fin 4,
      pauliString p * pauliString (g i) * star (pauliString p) = -pauliString (g i) ∧
        ∀ j, j ≠ i →
          pauliString p * pauliString (g j) * star (pauliString p) = pauliString (g j) := by
  classical
  -- A separating functional `f`: nonzero on row `i`, vanishing on the others.
  obtain ⟨f, hfi, hker⟩ := Submodule.exists_le_ker_of_notMem (hindep.notMem_span i)
  have hf_i : f (checkRow (g i)) = 1 := by
    have h01 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact h01 _ hfi
  have hf_j : ∀ j, j ≠ i → f (checkRow (g j)) = 0 := by
    intro j hj
    have hmem : checkRow (g j) ∈
        Submodule.span (ZMod 2) ((fun j => checkRow (g j)) '' {i}ᶜ) :=
      Submodule.subset_span ⟨j, hj, rfl⟩
    exact LinearMap.mem_ker.mp (hker hmem)
  -- Nondegeneracy realizes `f` as a symplectic pairing; `checkRow` is onto, so the pairing partner
  -- is `checkRow p` for a Pauli string `p`.
  obtain ⟨w, hw⟩ := (checkSymplectic.toDual checkSymplectic_nondegenerate).surjective f
  obtain ⟨p, hp⟩ := checkRow_surjective w
  have key : ∀ j, f (checkRow (g j)) = (pauliAnticommCount p (g j) : ZMod 2) := by
    intro j
    rw [← hw, LinearMap.BilinForm.toDual_def, ← hp, checkSymplectic_checkRow]
  refine ⟨p, ?_, ?_⟩
  · apply pauliString_conj_of_odd
    rw [← ZMod.natCast_ne_zero_iff_odd, ← key i, hf_i]
    exact one_ne_zero
  · intro j hj
    apply pauliString_conj_of_even
    rw [← ZMod.natCast_eq_zero_iff_even, ← key j]
    exact hf_j j hj

end AxQM.Concrete
