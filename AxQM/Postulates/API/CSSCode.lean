/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Evolution
import AxQM.Postulates.API.CosetDensityState
import AxQM.Postulates.API.PureState
import ToMathlib.Analysis.InnerProductSpace.PolarNormal
import ToMathlib.Analysis.InnerProductSpace.UnitaryTwirl
import ToMathlib.Analysis.InnerProductSpace.Orthonormal
import ToMathlib.InformationTheory.Coding.DualCodeCharacterSum

/-!
# The bit-vector register and Pauli strings for CSS codes

This file sets up the ingredients used to build **CSS codes** (Nielsen & Chuang, §10.4.2) and to
compare them, over the register of `n`-qubit computational-basis states indexed by bit vectors
`ι → ZMod 2`.

* `AxQM.bitReg ι` — the register `groupSystem (ι → ZMod 2)`, whose state space is the
  group algebra `ℂ[ι → ZMod 2]` with computational basis `{|w⟩}` indexed by bit vectors.
* `AxQM.regBasis ι` / `AxQM.regBasisState w` — the computational orthonormal
  basis of the register, as an `OrthonormalBasis` and as a family of `PureState`s `|w⟩`.
* `AxQM.bitString v` — the **Pauli bit-flip string** `X^v = X^{v₁} ⊗ ⋯ ⊗ X^{vₙ}`, the
  unitary `Evolution` translating the register by `v`: `|w⟩ ↦ |w + v⟩`
  (`bitString_op_regBasisState_vec`).
* `AxQM.phaseString u` — the **Pauli phase-flip string** `Z^u = Z^{u₁} ⊗ ⋯ ⊗ Z^{uₙ}`, the
  diagonal sign unitary `|w⟩ ↦ (-1)^{u·w} |w⟩` (`phaseString_op_regBasisState_vec`).

Both strings are built as genuine unitary `Evolution`s of the register: `bitString` from the
basis permutation `Equiv.addRight v` via `Evolution.ofLinearIsometryEquiv`, and `phaseString` from
`OrthonormalBasis.diagonalOperator` with the unit-modulus sign entries `(-1)^{(u·w).val}` (the same
`(-1)^{·.val}` character used for classical binary codes in
`ToMathlib.InformationTheory.Coding.DualCodeCharacterSum`).

These are the local Pauli unitaries whose product `Z^u X^v` witnesses, in
`AxQM/NC/Ch10/Exercise10_27.lean`, that the twisted codes `CSSᵤ,ᵥ(C₁, C₂)` are equivalent to
`CSS(C₁, C₂)`.

## The CSS coset states and the twist crux (Ex 10.27)

For a classical binary code `C₂ = LinearCode (ZMod 2) ι` (a `Submodule (ZMod 2) (ι → ZMod 2)`) and a
word `x`, this file also builds the two families of code states Exercise 10.27 compares, and the
exact relationship between them:

* `AxQM.cssStdState C₂ x` — the **standard CSS coset state** `|x + C₂⟩`
  `= |C₂|^{-1/2} ∑_{y ∈ C₂} |x + y⟩` of N&C (10.64), a `PureState` of `bitReg ι`.
* `AxQM.cssTwistedState C₂ u v x` — the **twisted state** `|x + C₂⟩_{u,v}`
  `= |C₂|^{-1/2} ∑_{y ∈ C₂} (-1)^{u·y} |x + y + v⟩` of N&C (10.75), the family `CSSᵤ,ᵥ(C₁, C₂)`.
* `AxQM.cssTwistedState_vec_eq` — the **crux**: at the vector level the twisted codeword is
  the fixed local Pauli `W = Z^u X^v` applied to the standard codeword, up to a global `±1` phase,
  `|x + C₂⟩_{u,v} = (-1)^{u·(x+v)} · Z^u X^v |x + C₂⟩`.
* `AxQM.cssTwistedState_toState_eq` — the **phase-free, density-level** form: the `±1`
  phase washes out of the density operator,
  `|x+C₂⟩_{u,v}⟨x+C₂|_{u,v} = W (|x+C₂⟩⟨x+C₂|) W†` with the same
  `W = Z^u X^v` for every `x`. This feeds the code-equivalence argument
  (Problem 10.1's channel equivalence) in `AxQM/NC/Ch10/Exercise10_27.lean`: `CSSᵤ,ᵥ` is the
  image of `CSS` under one fixed unitary `W`, so their error-correcting properties coincide —
  unconditionally in `C₁, C₂, u, v` (the `C₂ ⊂ C₁` / `t`-error hypotheses make the codes *good*, not
  equivalent).
-/

namespace AxQM

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- The **bit-vector register** for CSS codes: the group quantum system on the additive group of
bit vectors `ι → ZMod 2`, i.e. the `n`-qubit register (`n = #ι`) with computational basis `{|w⟩}`
indexed by bit strings `w : ι → ZMod 2`. -/
@[reducible] noncomputable def bitReg : QSystem := groupSystem (ι → ZMod 2)

variable (ι) in
/-- The **computational orthonormal basis** `{|w⟩}` of the register `bitReg ι`, the standard
Euclidean basis indexed by bit vectors. -/
noncomputable def regBasis : OrthonormalBasis (ι → ZMod 2) ℂ (bitReg ι).space :=
  EuclideanSpace.basisFun (ι → ZMod 2) ℂ

/-- The **computational basis pure state** `|w⟩` of the register `bitReg ι`, for a bit vector
`w : ι → ZMod 2`. -/
noncomputable def regBasisState (w : ι → ZMod 2) : PureState (bitReg ι) where
  vec := regBasis ι w
  normalized := (regBasis ι).orthonormal.1 w

@[simp]
theorem regBasisState_vec (w : ι → ZMod 2) : (regBasisState w).vec = regBasis ι w := rfl

/-- The **Pauli bit-flip string** `X^v = X^{v₁} ⊗ ⋯ ⊗ X^{vₙ}` as a unitary `Evolution` of the
register `bitReg ι`: the computational-basis permutation translating by `v`, `|w⟩ ↦ |w + v⟩`. It is
`Evolution.ofLinearIsometryEquiv` of the orthonormal-basis permutation `Equiv.addRight v`. -/
noncomputable def bitString (v : ι → ZMod 2) : Evolution (bitReg ι) :=
  Evolution.ofLinearIsometryEquiv ((regBasis ι).equiv (regBasis ι) (Equiv.addRight v))

/-- The **Pauli phase-flip string** `Z^u = Z^{u₁} ⊗ ⋯ ⊗ Z^{uₙ}` as a unitary `Evolution` of the
register `bitReg ι`: the diagonal sign operator `|w⟩ ↦ (-1)^{u·w} |w⟩`, with the binary-code
character `(-1)^{(u·w).val}` on the diagonal. Unitary because each diagonal entry has unit
modulus. -/
noncomputable def phaseString (u : ι → ZMod 2) : Evolution (bitReg ι) where
  op := (regBasis ι).diagonalOperator fun w => (-1 : ℂ) ^ (u ⬝ᵥ w).val
  unitary := (regBasis ι).diagonalOperator_mem_unitary _ fun w => by
    rw [norm_pow, norm_neg, norm_one, one_pow]

/-- **The operator of a phase-flip string is the diagonal sign operator** on `regBasis`:
`(Z^u).op = diag_{regBasis} ((-1)^{u·w})`. The operator-level companion (a definitional bridge) to
`phaseString_op_regBasis`; use it to compute compositions of phase strings via
`OrthonormalBasis.diagonalOperator_comp`. -/
theorem phaseString_op (u : ι → ZMod 2) :
    (phaseString u).op = (regBasis ι).diagonalOperator (fun w => (-1 : ℂ) ^ (u ⬝ᵥ w).val) := rfl

/-- **Action of the bit-flip string on the computational basis**: `X^v |w⟩ = |w + v⟩`. -/
theorem bitString_op_regBasisState_vec (v w : ι → ZMod 2) :
    (bitString v).op (regBasisState w).vec = (regBasisState (w + v)).vec := by
  simp only [regBasisState_vec, bitString]
  rw [Evolution.ofLinearIsometryEquiv_op_apply, OrthonormalBasis.equiv_apply_basis]
  rfl

/-- **Action of the phase-flip string on the computational basis**: `Z^u |w⟩ = (-1)^{u·w} |w⟩`. -/
theorem phaseString_op_regBasisState_vec (u w : ι → ZMod 2) :
    (phaseString u).op (regBasisState w).vec
      = (-1 : ℂ) ^ (u ⬝ᵥ w).val • (regBasisState w).vec := by
  simp only [regBasisState_vec, phaseString]
  exact (regBasis ι).diagonalOperator_apply_self _ w

/-- **Action of the bit-flip string on a raw basis vector**: `X^v |w⟩ = |w + v⟩`. The `regBasis`
form of `bitString_op_regBasisState_vec`, convenient for computing on superpositions. -/
theorem bitString_op_regBasis (v w : ι → ZMod 2) :
    (bitString v).op (regBasis ι w) = regBasis ι (w + v) := by
  have h := bitString_op_regBasisState_vec (ι := ι) v w
  simpa only [regBasisState_vec] using h

/-- **Action of the phase-flip string on a raw basis vector**: `Z^u |w⟩ = (-1)^{u·w} |w⟩`. The
`regBasis` form of `phaseString_op_regBasisState_vec`. -/
theorem phaseString_op_regBasis (u w : ι → ZMod 2) :
    (phaseString u).op (regBasis ι w) = (-1 : ℂ) ^ (u ⬝ᵥ w).val • regBasis ι w := by
  have h := phaseString_op_regBasisState_vec (ι := ι) u w
  simpa only [regBasisState_vec] using h

/-- **Norm of a unit-modulus superposition of distinct computational basis states is one.** If
`idx : n → (ι → ZMod 2)` is injective — so the basis vectors `|idx i⟩` are orthonormal — and every
coefficient `coeff i` has unit modulus, then the normalized superposition
`|n|^{-1/2} ∑ᵢ coeff i |idx i⟩` is a unit vector. This is the shared normalization behind both CSS
coset states (10.64)/(10.75): `coeff ≡ 1` gives the standard state, `coeff = (-1)^{u·y}` the twisted
state. -/
private theorem norm_smul_sum_regBasis {n : Type*} [Fintype n] (hpos : 0 < Nat.card n)
    (idx : n → (ι → ZMod 2)) (hidx : Function.Injective idx)
    (coeff : n → ℂ) (hc : ∀ i, ‖coeff i‖ = 1) :
    ‖(Real.sqrt (Nat.card n) : ℂ)⁻¹ • ∑ i, coeff i • regBasis ι (idx i)‖ = 1 := by
  have horth : Orthonormal ℂ (fun i => regBasis ι (idx i)) :=
    (regBasis ι).orthonormal.comp idx hidx
  have hsq : ‖∑ i, coeff i • regBasis ι (idx i)‖ ^ 2 = (Nat.card n : ℝ) := by
    rw [horth.norm_sum_smul_sq coeff Finset.univ]
    simp only [hc, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  have hS : ‖∑ i, coeff i • regBasis ι (idx i)‖ = Real.sqrt (Nat.card n) := by
    rw [← hsq]; exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [norm_smul, hS, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hpos))]

/-- The **key `ZMod 2` sign identity** behind the twist crux: for the shift-by-`v`, twist-by-`u`
computation, `(-1)^{u·(x+v)} · (-1)^{u·(x+y+v)} = (-1)^{u·y}`. It holds because in `ZMod 2` the map
`a ↦ (-1)^{a.val}` is additive-to-multiplicative (`neg_one_pow_zmod2_val_add`) and
`(x+v) + (x+y+v) = y` (the `x` and `v` contributions cancel in characteristic two). -/
private theorem cssTwist_phase_mul {ι : Type*} [Fintype ι] (u v x y : ι → ZMod 2) :
    (-1 : ℂ) ^ (u ⬝ᵥ (x + v)).val * (-1 : ℂ) ^ (u ⬝ᵥ (x + y + v)).val
      = (-1 : ℂ) ^ (u ⬝ᵥ y).val := by
  have key : (x + v) + (x + y + v) = y := by
    funext i
    have h : ∀ a b c : ZMod 2, (a + b) + (a + c + b) = c := by decide
    simpa using h (x i) (v i) (y i)
  rw [← neg_one_pow_zmod2_val_add, ← dotProduct_add, key]

variable (C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)]

/-- The **standard CSS coset state** `|x + C₂⟩ = |C₂|^{-1/2} ∑_{y ∈ C₂} |x + y⟩` (Nielsen & Chuang,
eq. 10.64), as a `PureState` of the register `bitReg ι`. It is normalized because `y ↦ x + y` is
injective on `C₂`, so the summed computational-basis vectors `|x + y⟩` are orthonormal. The state
depends only on the coset `x + C₂`; the code `CSS(C₁, C₂)` is the span of these over `x ∈ C₁`. -/
noncomputable def cssStdState (x : ι → ZMod 2) : PureState (bitReg ι) where
  vec := (Real.sqrt (Nat.card ↥C₂) : ℂ)⁻¹ • ∑ y : ↥C₂, regBasis ι (x + (y : ι → ZMod 2))
  normalized := by
    have hpos : 0 < Nat.card ↥C₂ := by
      have : Nonempty ↥C₂ := ⟨⟨0, C₂.zero_mem⟩⟩; exact Nat.card_pos
    have hinj : Function.Injective (fun y : ↥C₂ => x + (y : ι → ZMod 2)) := fun a b hab =>
      Subtype.ext (add_left_cancel hab)
    have h := norm_smul_sum_regBasis hpos
      (fun y : ↥C₂ => x + (y : ι → ZMod 2)) hinj (fun _ => 1) (fun _ => norm_one)
    simpa only [one_smul] using h

@[simp]
theorem cssStdState_vec (x : ι → ZMod 2) :
    (cssStdState C₂ x).vec
      = (Real.sqrt (Nat.card ↥C₂) : ℂ)⁻¹ • ∑ y : ↥C₂, regBasis ι (x + (y : ι → ZMod 2)) := rfl

/-- The **twisted CSS coset state** `|x + C₂⟩_{u,v} = |C₂|^{-1/2} ∑_{y ∈ C₂} (-1)^{u·y} |x + y + v⟩`
(Nielsen & Chuang, eq. 10.75), as a `PureState` of `bitReg ι`. The family over `x ∈ C₁` spans the
twisted code `CSSᵤ,ᵥ(C₁, C₂)`. It is normalized because `y ↦ x + y + v` is injective on `C₂` and the
signs `(-1)^{u·y}` have unit modulus. -/
noncomputable def cssTwistedState (u v x : ι → ZMod 2) : PureState (bitReg ι) where
  vec := (Real.sqrt (Nat.card ↥C₂) : ℂ)⁻¹ •
    ∑ y : ↥C₂, (-1 : ℂ) ^ (u ⬝ᵥ (y : ι → ZMod 2)).val •
      regBasis ι (x + (y : ι → ZMod 2) + v)
  normalized := by
    have hpos : 0 < Nat.card ↥C₂ := by
      have : Nonempty ↥C₂ := ⟨⟨0, C₂.zero_mem⟩⟩; exact Nat.card_pos
    have hinj : Function.Injective (fun y : ↥C₂ => x + (y : ι → ZMod 2) + v) := fun a b hab =>
      Subtype.ext (add_left_cancel (add_right_cancel hab))
    exact norm_smul_sum_regBasis hpos
      (fun y : ↥C₂ => x + (y : ι → ZMod 2) + v) hinj
      (fun y => (-1 : ℂ) ^ (u ⬝ᵥ (y : ι → ZMod 2)).val)
      (fun _ => by rw [norm_pow, norm_neg, norm_one, one_pow])

@[simp]
theorem cssTwistedState_vec (u v x : ι → ZMod 2) :
    (cssTwistedState C₂ u v x).vec
      = (Real.sqrt (Nat.card ↥C₂) : ℂ)⁻¹ •
        ∑ y : ↥C₂, (-1 : ℂ) ^ (u ⬝ᵥ (y : ι → ZMod 2)).val •
          regBasis ι (x + (y : ι → ZMod 2) + v) := rfl

/-- The operator `Z^u X^v` applied to the standard coset state, computed as an explicit twisted-sign
superposition: `Z^u X^v |x + C₂⟩ = |C₂|^{-1/2} ∑_{y ∈ C₂} (-1)^{u·(x+y+v)} |x + y + v⟩`. The
linearity step feeding the twist crux. -/
private theorem phaseString_comp_bitString_op_cssStdState (u v x : ι → ZMod 2) :
    ((phaseString u).comp (bitString v)).op (cssStdState C₂ x).vec
      = (Real.sqrt (Nat.card ↥C₂) : ℂ)⁻¹ •
        ∑ y : ↥C₂, (-1 : ℂ) ^ (u ⬝ᵥ (x + (y : ι → ZMod 2) + v)).val •
          regBasis ι (x + (y : ι → ZMod 2) + v) := by
  rw [cssStdState_vec, Evolution.comp_op, ContinuousLinearMap.comp_apply, map_smul, map_sum]
  simp only [bitString_op_regBasis]
  rw [map_smul, map_sum]
  simp only [phaseString_op_regBasis]

/-- **The twist crux (Nielsen & Chuang, Exercise 10.27).** At the state-vector level, the twisted
coset state `|x + C₂⟩_{u,v}` is the fixed local Pauli string `W = Z^u X^v` applied to the standard
coset state `|x + C₂⟩`, up to the global `±1` phase `(-1)^{u·(x+v)}`:
`|x + C₂⟩_{u,v} = (-1)^{u·(x+v)} · Z^u X^v |x + C₂⟩`. Since `W` does not depend on `x`, the whole
twisted code is the `W`-image of the standard code — the geometric content of "equivalent codes". -/
theorem cssTwistedState_vec_eq (u v x : ι → ZMod 2) :
    (cssTwistedState C₂ u v x).vec
      = (-1 : ℂ) ^ (u ⬝ᵥ (x + v)).val •
        ((phaseString u).comp (bitString v)).op (cssStdState C₂ x).vec := by
  rw [cssTwistedState_vec, phaseString_comp_bitString_op_cssStdState, smul_comm]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [smul_smul, cssTwist_phase_mul]

/-- **Density-level twist crux (Ex 10.27): the `±1` phase washes out.** As density operators, the
twisted codeword equals the standard codeword conjugated by the *same* fixed local Pauli
`W = Z^u X^v`, `|x+C₂⟩_{u,v}⟨x+C₂|_{u,v} = W |x+C₂⟩⟨x+C₂| W†` — a phase-free identity
holding for every `x` with one `x`-independent `W`. This is the exact ingredient of
the code-equivalence argument: `CSSᵤ,ᵥ(C₁, C₂)` is the image of `CSS(C₁, C₂)` under the
unitary channel `W.evolve`, so the two codes have identical error-correction properties
(Prob 10.1). -/
theorem cssTwistedState_toState_eq (u v x : ι → ZMod 2) :
    (cssTwistedState C₂ u v x).toState
      = ((phaseString u).comp (bitString v)).evolve (cssStdState C₂ x).toState := by
  have hphase : (cssTwistedState C₂ u v x).vec
      = (-1 : ℂ) ^ (u ⬝ᵥ (x + v)).val •
        (((phaseString u).comp (bitString v)).evolvePure (cssStdState C₂ x)).vec := by
    rw [Evolution.evolvePure_vec]; exact cssTwistedState_vec_eq C₂ u v x
  rw [PureState.toState_eq_of_vec_eq_smul (by rw [norm_pow, norm_neg, norm_one, one_pow]) hphase]
  exact toState_evolvePure _ _

end AxQM
