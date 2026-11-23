/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.CSSCodeStabilizer
import ToMathlib.LinearAlgebra.Eigenspace.StabilizedSubmodule
import ToMathlib.InformationTheory.Coding.DualCodeCharacterSum

/-!
# The CSS code space is the stabilized subspace of the check matrix (10.106)

This file proves the **code-space identification** of Nielsen & Chuang, Exercise 10.51: for binary
linear codes `C₂ ≤ C₁`, the check matrix (10.106) "corresponds to the stabilizer of `CSS(C₁, C₂)`",
i.e. the joint `+1`-eigenspace `V_S` stabilized by its generators is *exactly* the CSS code space
`CSS(C₁, C₂) = span{ |x + C₂⟩ : x ∈ C₁ }`.

Everything is carried out directly in the `bitReg ι` register (`EuclideanSpace ℂ (ι → ZMod 2)`) in
which the CSS coset states of `AxQM.Postulates.API.CSSCode` live, so no bridge to the
`Concrete.PauliGroup n` model is needed. The two objects:

* `AxQM.cssCodeSpace C₁ C₂` — the **CSS code space**, the `ℂ`-subspace
  `span{ (cssStdState C₂ x).vec : x ∈ C₁ }` spanned by the standard coset codewords `|x + C₂⟩`.
* `AxQM.cssCheckOps C₁ C₂` / `AxQM.cssStabilizedSpace C₁ C₂` — the generators of
  the check matrix (10.106) as a set of endomorphisms — the X-type bit-flips `X^v` (`bitString v`)
  for `v ∈ C₂` and the Z-type phase-flips `Z^u` (`phaseString u`) for `u ∈ C₁⊥` — and the submodule
  `V_S = Module.End.stabilizedSubmodule (cssCheckOps C₁ C₂)` they stabilize (N&C §10.5.1). This is
  exactly the operator set of the generator family `cssCheckMatrixStabilizer` of
  `AxQM.NC.Ch10.Exercise10_51`.

The headline is `AxQM.cssStabilizedSpace_eq_cssCodeSpace : V_S = CSS(C₁, C₂)` (for
`C₂ ≤ C₁`), obtained from the two inclusions:

* **`cssCodeSpace_le_cssStabilizedSpace` (`CSS ⊆ V_S`, needs `C₂ ≤ C₁`).** Every generator fixes
  every codeword `|x + C₂⟩`: the X-type by coset invariance
  (`bitString_op_cssStdState_eq_self`, `v ∈ C₂`), the Z-type by the dual-code condition
  (`phaseString_hasEigenstate_one_cssStdState_of_mem_dual`, `u ∈ C₁⊥, x ∈ C₁, C₂ ≤ C₁`).
* **`cssStabilizedSpace_le_cssCodeSpace` (`V_S ⊆ CSS`, no `C₂ ≤ C₁` needed).** The reverse
  inclusion, by two averaging arguments avoiding any coset enumeration:
  1. **Support.** A vector `ψ` fixed by every `Z^u` (`u ∈ C₁⊥`) has `⟨w|ψ⟩ = 0` for `w ∉ C₁`: if
     `w ∉ C₁ = (C₁⊥)⊥` then some `u ∈ C₁⊥` has `u · w = 1`, and comparing the `w`-coordinate of
     `Z^u ψ = ψ` gives `⟨w|ψ⟩ = (-1)^{u·w} ⟨w|ψ⟩ = -⟨w|ψ⟩`, so `⟨w|ψ⟩ = 0`. Hence
     `ψ ∈ span{ |w⟩ : w ∈ C₁ }` (`mem_span_regBasis_of_phaseString_fixed`).
  2. **Averaging.** The X-average `cssXAverage C₂ = |C₂|⁻¹ ∑_{v ∈ C₂} X^v` fixes any `ψ` fixed by
     every `X^v` (`v ∈ C₂`), and sends each `|w⟩` (`w ∈ C₁`) to a scalar multiple of the codeword
     `|w + C₂⟩ ∈ CSS(C₁, C₂)`. So `ψ = cssXAverage C₂ ψ` lies in the image of `span{ |w⟩ : w ∈ C₁ }`
     under `cssXAverage C₂`, which the averaging step lands inside `CSS(C₁, C₂)`.

Only the *subspace equality* `V_S = CSS(C₁, C₂)` is proved here — the dimension count
`dim V_S = 2^{k₁ - k₂}` is a separate fact (it needs the orthonormality of the coset states across
`C₁ / C₂`) that N&C mentions but the exercise's identification claim does not require.

`AxQM.NC.Ch10.Exercise10_51` records the physical codeword-stabilization
(`Evolution.HasEigenstate`) and refers to the equality proved here.
-/

namespace AxQM

open scoped Matrix
open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **CSS code space** `CSS(C₁, C₂)` as a `ℂ`-subspace of the register `bitReg ι`: the span of
the standard coset codewords `|x + C₂⟩` (`cssStdState C₂ x`) over the cosets `x ∈ C₁`
(Nielsen & Chuang, §10.4.2). This is the linear-algebraic code space (a `Submodule`), the ambient
span of the code states `cssCode C₁ C₂` of `AxQM.NC.Ch10.Exercise10_27`. -/
noncomputable def cssCodeSpace (C₁ C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)] :
    Submodule ℂ (bitReg ι).space :=
  Submodule.span ℂ ((fun x => (cssStdState C₂ x).vec) '' (C₁ : Set (ι → ZMod 2)))

/-- **The generators of the CSS check matrix (10.106)** as a set of endomorphisms of the register:
the X-type bit-flip strings `X^v = bitString v` for the codewords `v ∈ C₂` (top block `[H(C₂⊥)|0]`,
rows spanning `C₂`) together with the Z-type phase-flip strings `Z^u = phaseString u` for
`u ∈ C₁⊥` (bottom block `[0|H(C₁)]`, rows spanning `C₁⊥`). This is the operator set of the generator
family `cssCheckMatrixStabilizer` of `AxQM.NC.Ch10.Exercise10_51`. -/
noncomputable def cssCheckOps (C₁ C₂ : LinearCode (ZMod 2) ι) :
    Set (Module.End ℂ (bitReg ι).space) :=
  (fun v => (bitString v).op.toLinearMap) '' (C₂ : Set (ι → ZMod 2)) ∪
    (fun u => (phaseString u).op.toLinearMap) '' (C₁.dual : Set (ι → ZMod 2))

/-- The **stabilized subspace** `V_S` of the CSS check matrix (10.106): the joint `+1`-eigenspace of
its generators, i.e. the vectors of `bitReg ι` fixed by every `X^v` (`v ∈ C₂`) and every `Z^u`
(`u ∈ C₁⊥`) (Nielsen & Chuang, §10.5.1). Exercise 10.51 identifies it with the code space
`cssCodeSpace C₁ C₂`. -/
noncomputable def cssStabilizedSpace (C₁ C₂ : LinearCode (ZMod 2) ι) :
    Submodule ℂ (bitReg ι).space :=
  Module.End.stabilizedSubmodule (cssCheckOps C₁ C₂)

/-- **Membership in `cssStabilizedSpace`.** A vector `ψ` lies in the stabilized subspace of the
check matrix (10.106) iff every X-type generator `X^v` (`v ∈ C₂`) and every Z-type generator `Z^u`
(`u ∈ C₁⊥`) fixes it. -/
theorem mem_cssStabilizedSpace_iff {C₁ C₂ : LinearCode (ZMod 2) ι} {ψ : (bitReg ι).space} :
    ψ ∈ cssStabilizedSpace C₁ C₂ ↔
      (∀ v ∈ C₂, (bitString v).op ψ = ψ) ∧ (∀ u ∈ C₁.dual, (phaseString u).op ψ = ψ) := by
  rw [cssStabilizedSpace, Module.End.mem_stabilizedSubmodule_iff, cssCheckOps]
  constructor
  · intro h
    exact ⟨fun v hv => h _ (Or.inl ⟨v, hv, rfl⟩), fun u hu => h _ (Or.inr ⟨u, hu, rfl⟩)⟩
  · rintro ⟨hX, hZ⟩ f (⟨v, hv, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact hX v hv
    · exact hZ u hu

/-- **Support of a `Z`-fixed vector.** If `ψ` is fixed by every phase-flip string `Z^u` with
`u ∈ C₁⊥`, then it lies in the span of the computational-basis vectors `|w⟩` with `w ∈ C₁`. The key
step: for `w ∉ C₁ = (C₁⊥)⊥` there is `u ∈ C₁⊥` with `u · w = 1`, and taking the `w`-coordinate of
`Z^u ψ = ψ` gives `⟨w|ψ⟩ = (-1)^{u·w} ⟨w|ψ⟩ = -⟨w|ψ⟩`, so the coordinate vanishes. -/
theorem mem_span_regBasis_of_phaseString_fixed {C₁ : LinearCode (ZMod 2) ι} {ψ : (bitReg ι).space}
    (hZ : ∀ u ∈ C₁.dual, (phaseString u).op ψ = ψ) :
    ψ ∈ Submodule.span ℂ ((fun w => regBasis ι w) '' (C₁ : Set (ι → ZMod 2))) := by
  -- Coordinates of `ψ` in the computational basis.
  obtain ⟨c, hψ⟩ : ∃ c : (ι → ZMod 2) → ℂ, ψ = ∑ i, c i • regBasis ι i :=
    ⟨fun i => ((regBasis ι).repr ψ).ofLp i, ((regBasis ι).sum_repr ψ).symm⟩
  -- The `w'`-coordinate of any explicit basis expansion is its coefficient (`Orthonormal` API).
  have hcoeff : ∀ (d : (ι → ZMod 2) → ℂ) (w' : ι → ZMod 2),
      inner ℂ (regBasis ι w') (∑ i, d i • regBasis ι i) = d w' :=
    fun d w' => (regBasis ι).orthonormal.inner_right_fintype d w'
  -- Every coordinate off `C₁` vanishes.
  have hcvanish : ∀ w ∉ C₁, c w = 0 := by
    intro w hw
    -- Some dual word is not orthogonal to `w`.
    obtain ⟨u, hu, huw⟩ : ∃ u ∈ C₁.dual, u ⬝ᵥ w ≠ 0 := by
      by_contra hcon
      refine hw ?_
      rw [← LinearCode.dual_dual C₁]
      refine LinearCode.mem_dual_iff.mpr fun x hx => ?_
      by_contra hne
      exact hcon ⟨x, hx, hne⟩
    have hval : (u ⬝ᵥ w).val = 1 := by
      have h1 : u ⬝ᵥ w = 1 := by
        rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 from by decide) (u ⬝ᵥ w) with h | h
        · exact absurd h huw
        · exact h
      rw [h1]; decide
    -- Compute `Z^u ψ` in coordinates and read off the `w`-coordinate.
    have hopψ : (phaseString u).op ψ = ∑ i, (c i * (-1 : ℂ) ^ (u ⬝ᵥ i).val) • regBasis ι i := by
      rw [hψ, map_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [map_smul, phaseString_op_regBasis, smul_smul]
    have h3 : c w * (-1 : ℂ) ^ (u ⬝ᵥ w).val = c w := by
      have e1 : inner ℂ (regBasis ι w) ((phaseString u).op ψ) = c w * (-1 : ℂ) ^ (u ⬝ᵥ w).val := by
        rw [hopψ, hcoeff]
      rw [← e1, hZ u hu, hψ, hcoeff]
    rw [hval] at h3
    linear_combination (-1 / 2 : ℂ) * h3
  -- Assemble: drop the vanishing terms, the rest is a combination of `|w⟩`, `w ∈ C₁`.
  rw [hψ]
  refine Submodule.sum_mem _ fun w _ => ?_
  by_cases hw : w ∈ C₁
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, hw, rfl⟩)
  · rw [hcvanish w hw, zero_smul]; exact Submodule.zero_mem _

/-- The **X-type averaging projector** `cssXAverage C₂ = |C₂|⁻¹ ∑_{v ∈ C₂} X^v`, the average of the
bit-flip strings over the code `C₂`, as an endomorphism of `bitReg ι`. It fixes any vector fixed by
all `X^v` (`v ∈ C₂`) and maps each computational basis vector `|w⟩` to a multiple of the coset
codeword `|w + C₂⟩`. -/
noncomputable def cssXAverage (C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)] :
    Module.End ℂ (bitReg ι).space :=
  (Nat.card ↥C₂ : ℂ)⁻¹ • ∑ v : ↥C₂, (bitString (↑v : ι → ZMod 2)).op.toLinearMap

/-- **Value of the X-average** on a vector: `cssXAverage C₂ ψ = |C₂|⁻¹ ∑_{v ∈ C₂} X^v ψ`. -/
theorem cssXAverage_apply (C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)]
    (ψ : (bitReg ι).space) :
    cssXAverage C₂ ψ = (Nat.card ↥C₂ : ℂ)⁻¹ • ∑ v : ↥C₂, (bitString (↑v : ι → ZMod 2)).op ψ := by
  rw [cssXAverage, LinearMap.smul_apply, LinearMap.sum_apply]
  simp only [ContinuousLinearMap.coe_coe]

/-- **The X-average fixes a vector fixed by all `X^v` (`v ∈ C₂`).** Since each `X^v ψ = ψ`, the
average of `|C₂|` copies of `ψ`, rescaled by `|C₂|⁻¹`, is again `ψ`. -/
theorem cssXAverage_apply_self (C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)]
    {ψ : (bitReg ι).space} (hX : ∀ v ∈ C₂, (bitString v).op ψ = ψ) :
    cssXAverage C₂ ψ = ψ := by
  have : Nonempty ↥C₂ := ⟨⟨0, C₂.zero_mem⟩⟩
  have hconst : ∀ v : ↥C₂, (bitString (↑v : ι → ZMod 2)).op ψ = ψ := fun v => hX (↑v) v.2
  rw [cssXAverage_apply, Finset.sum_congr rfl fun v _ => hconst v,
    Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := ↥C₂)), one_smul]

/-- **The X-average of a basis vector `|w⟩` with `w ∈ C₁` is a codeword multiple.** Concretely
`cssXAverage C₂ |w⟩ = |C₂|⁻¹ √|C₂| · |w + C₂⟩`, which lies in `cssCodeSpace C₁ C₂`. -/
theorem cssXAverage_regBasis_mem (C₁ C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)]
    {w : ι → ZMod 2} (hw : w ∈ C₁) :
    cssXAverage C₂ (regBasis ι w) ∈ cssCodeSpace C₁ C₂ := by
  have : Nonempty ↥C₂ := ⟨⟨0, C₂.zero_mem⟩⟩
  have hsqrt : (Real.sqrt (Nat.card ↥C₂) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Nat.card ↥C₂ := by exact_mod_cast Nat.card_pos
    exact_mod_cast Real.sqrt_ne_zero'.mpr this
  have hsum : ∑ v : ↥C₂, regBasis ι (w + (↑v : ι → ZMod 2))
      = (Real.sqrt (Nat.card ↥C₂) : ℂ) • (cssStdState C₂ w).vec := by
    rw [cssStdState_vec, smul_smul, mul_inv_cancel₀ hsqrt, one_smul]
  rw [cssXAverage_apply]
  simp only [bitString_op_regBasis]
  rw [hsum]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (Submodule.subset_span ⟨w, hw, rfl⟩))

/-- **Reverse inclusion `V_S ⊆ CSS(C₁, C₂)`** (no `C₂ ≤ C₁` needed). Any vector `ψ` stabilized by
the check matrix (10.106) is a combination of CSS codewords: by the support lemma it lies in
`span{ |w⟩ : w ∈ C₁ }`, and the X-average — which fixes `ψ` — maps that span into
`cssCodeSpace C₁ C₂`, so `ψ = cssXAverage C₂ ψ ∈ CSS(C₁, C₂)`. -/
theorem cssStabilizedSpace_le_cssCodeSpace (C₁ C₂ : LinearCode (ZMod 2) ι)
    [DecidablePred (· ∈ C₂)] : cssStabilizedSpace C₁ C₂ ≤ cssCodeSpace C₁ C₂ := by
  intro ψ hψ
  rw [mem_cssStabilizedSpace_iff] at hψ
  obtain ⟨hX, hZ⟩ := hψ
  have hsupp : ψ ∈ Submodule.span ℂ ((fun w => regBasis ι w) '' (C₁ : Set (ι → ZMod 2))) :=
    mem_span_regBasis_of_phaseString_fixed hZ
  have hmap : Submodule.map (cssXAverage C₂)
      (Submodule.span ℂ ((fun w => regBasis ι w) '' (C₁ : Set (ι → ZMod 2))))
      ≤ cssCodeSpace C₁ C₂ := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro z ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact cssXAverage_regBasis_mem C₁ C₂ hw
  have hmem : cssXAverage C₂ ψ ∈ cssCodeSpace C₁ C₂ := hmap (Submodule.mem_map_of_mem hsupp)
  rwa [cssXAverage_apply_self C₂ hX] at hmem

/-- **Forward inclusion `CSS(C₁, C₂) ⊆ V_S`** (needs `C₂ ≤ C₁`). Every generator of the check matrix
(10.106) fixes every CSS codeword `|x + C₂⟩` (`x ∈ C₁`): the X-type `X^v` (`v ∈ C₂`) by coset
invariance, the Z-type `Z^u` (`u ∈ C₁⊥`) by the dual-code condition. Hence the span of the codewords
lies in the stabilized subspace. -/
theorem cssCodeSpace_le_cssStabilizedSpace {C₁ C₂ : LinearCode (ZMod 2) ι}
    [DecidablePred (· ∈ C₂)] (hsub : C₂ ≤ C₁) :
    cssCodeSpace C₁ C₂ ≤ cssStabilizedSpace C₁ C₂ := by
  rw [cssCodeSpace, Submodule.span_le]
  rintro z ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_cssStabilizedSpace_iff]
  refine ⟨fun v hv => bitString_op_cssStdState_eq_self C₂ hv x, fun u hu => ?_⟩
  have h : (phaseString u).op (cssStdState C₂ x).vec = (1 : ℂ) • (cssStdState C₂ x).vec :=
    phaseString_hasEigenstate_one_cssStdState_of_mem_dual C₂ hsub hu hx
  rwa [one_smul] at h

/-- **Exercise 10.51 — the code-space equality.** For binary linear codes `C₂ ≤ C₁`, the check
matrix (10.106) "corresponds to the stabilizer of `CSS(C₁, C₂)`": the stabilized subspace `V_S` of
its generators is *exactly* the CSS code space `span{ |x + C₂⟩ : x ∈ C₁ }`. This is the subspace
identification N&C asserts (p. 470); the accompanying `t`-qubit correctability (Theorem 10.8) is
`AxQM.Concrete.cssStabilizer_isCorrectableErrorSet_of_correctsErrors`. -/
theorem cssStabilizedSpace_eq_cssCodeSpace {C₁ C₂ : LinearCode (ZMod 2) ι}
    [DecidablePred (· ∈ C₂)] (hsub : C₂ ≤ C₁) :
    cssStabilizedSpace C₁ C₂ = cssCodeSpace C₁ C₂ :=
  le_antisymm (cssStabilizedSpace_le_cssCodeSpace C₁ C₂) (cssCodeSpace_le_cssStabilizedSpace hsub)

/-! ### Membership from a generating set of the check codes

`mem_cssStabilizedSpace_iff` characterises the stabilized subspace by fixing under *every* `X^v`
(`v ∈ C₂`) and *every* `Z^u` (`u ∈ C₁⊥`). In practice a stabilizer code is presented by a finite set
of **generators** (the rows of the check matrix), not by all of its (exponentially many) codewords.
The lemmas here bridge the two: because `X^v = bitString v` and `Z^u = phaseString u` are group
homomorphisms of the additive group `ι → ZMod 2` (`X^{v+w} = X^v X^w`, `X^0 = 1`), the set of `v`
fixing a given `ψ` is a `ZMod 2`-submodule, so fixing under a *spanning set* of `C₂` (resp. `C₁⊥`)
already forces fixing under all of `C₂` (resp. `C₁⊥`). Hence `ψ` lies in the stabilized subspace —
equivalently, for `C₂ ≤ C₁`, in the code space `CSS(C₁, C₂)`. -/

/-- **`X^{v+w} = X^v X^w`**: the bit-flip string is an additive-to-multiplicative homomorphism, the
computational-basis translation `|x⟩ ↦ |x + (v+w)⟩` factoring as `|x⟩ ↦ |x + w⟩ ↦ |x + w + v⟩`. -/
theorem bitString_op_add (v w : ι → ZMod 2) (ψ : (bitReg ι).space) :
    (bitString (v + w)).op ψ = (bitString v).op ((bitString w).op ψ) := by
  have key : (bitString (v + w)).op.toLinearMap
      = (bitString v).op.toLinearMap ∘ₗ (bitString w).op.toLinearMap := by
    apply (regBasis ι).toBasis.ext
    intro x
    simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      bitString_op_regBasis]
    congr 1
    abel
  exact DFunLike.congr_fun key ψ

/-- **`X^0 = 1`**: the bit-flip string of the zero vector is the identity translation. -/
theorem bitString_op_zero (ψ : (bitReg ι).space) : (bitString (0 : ι → ZMod 2)).op ψ = ψ := by
  have key : (bitString (0 : ι → ZMod 2)).op.toLinearMap = LinearMap.id := by
    apply (regBasis ι).toBasis.ext
    intro x
    simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe, bitString_op_regBasis,
      add_zero, LinearMap.id_coe, id_eq]
  exact DFunLike.congr_fun key ψ

/-- **`Z^{u+u'} = Z^u Z^{u'}`**: the phase-flip string is an additive-to-multiplicative
homomorphism, the diagonal signs multiplying, `(-1)^{(u+u')·x} = (-1)^{u·x} (-1)^{u'·x}`
(`neg_one_pow_zmod2_val_add`). -/
theorem phaseString_op_add (u u' : ι → ZMod 2) (ψ : (bitReg ι).space) :
    (phaseString (u + u')).op ψ = (phaseString u).op ((phaseString u').op ψ) := by
  have key : (phaseString (u + u')).op.toLinearMap
      = (phaseString u).op.toLinearMap ∘ₗ (phaseString u').op.toLinearMap := by
    apply (regBasis ι).toBasis.ext
    intro x
    simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      phaseString_op_regBasis, map_smul, smul_smul]
    rw [add_dotProduct, neg_one_pow_zmod2_val_add, mul_comm]
  exact DFunLike.congr_fun key ψ

/-- **`Z^0 = 1`**: the phase-flip string of the zero vector is the identity (all signs `+1`). -/
theorem phaseString_op_zero (ψ : (bitReg ι).space) : (phaseString (0 : ι → ZMod 2)).op ψ = ψ := by
  have key : (phaseString (0 : ι → ZMod 2)).op.toLinearMap = LinearMap.id := by
    apply (regBasis ι).toBasis.ext
    intro x
    simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe, phaseString_op_regBasis,
      LinearMap.id_coe, id_eq, zero_dotProduct, ZMod.val_zero, pow_zero, one_smul]
  exact DFunLike.congr_fun key ψ

/-- **Fixing propagates from a spanning set to its span** (X-type). If every `X^v` (`v ∈ S`) fixes
`ψ`, then so does `X^w` for every `w` in the `ZMod 2`-span of `S`: the fixed vectors form a
submodule (`bitString_op_add` for `+`, `bitString_op_zero` for `0`, `c • v ∈ {0, v}` over 𝔽₂). -/
theorem bitString_op_eq_self_of_mem_span {ψ : (bitReg ι).space} {S : Set (ι → ZMod 2)}
    (hS : ∀ v ∈ S, (bitString v).op ψ = ψ) {w : ι → ZMod 2}
    (hw : w ∈ Submodule.span (ZMod 2) S) : (bitString w).op ψ = ψ := by
  induction hw using Submodule.span_induction with
  | mem v hv => exact hS v hv
  | zero => exact bitString_op_zero ψ
  | add a b _ _ iha ihb => rw [bitString_op_add, ihb, iha]
  | smul c a _ iha =>
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) c with rfl | rfl
      · rw [zero_smul]; exact bitString_op_zero ψ
      · rwa [one_smul]

/-- **Fixing propagates from a spanning set to its span** (Z-type). If every `Z^u` (`u ∈ S`) fixes
`ψ`, then so does `Z^w` for every `w` in the `ZMod 2`-span of `S` (the fixed vectors form a
submodule, via `phaseString_op_add` / `phaseString_op_zero`). -/
theorem phaseString_op_eq_self_of_mem_span {ψ : (bitReg ι).space} {S : Set (ι → ZMod 2)}
    (hS : ∀ u ∈ S, (phaseString u).op ψ = ψ) {w : ι → ZMod 2}
    (hw : w ∈ Submodule.span (ZMod 2) S) : (phaseString w).op ψ = ψ := by
  induction hw using Submodule.span_induction with
  | mem u hu => exact hS u hu
  | zero => exact phaseString_op_zero ψ
  | add a b _ _ iha ihb => rw [phaseString_op_add, ihb, iha]
  | smul c a _ iha =>
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) c with rfl | rfl
      · rw [zero_smul]; exact phaseString_op_zero ψ
      · rwa [one_smul]

/-- **Stabilized-subspace membership from generators.** If `ψ` is fixed by the X-type generator
`X^v` for every `v` in a spanning set `S` of `C₂` (`C₂ ≤ span S`) and by the Z-type generator `Z^u`
for every `u` in a spanning set `T` of `C₁⊥` (`C₁⊥ ≤ span T`), then `ψ` lies in the stabilized
subspace of the check matrix (10.106): fixing spreads from the generators to all of `C₂` / `C₁⊥`
(`bitString_op_eq_self_of_mem_span` / `phaseString_op_eq_self_of_mem_span`), which is
`mem_cssStabilizedSpace_iff`. This is the generator-form of the reverse inclusion, the way a
stabilizer code is actually presented (by check rows, not by all codewords). -/
theorem mem_cssStabilizedSpace_of_span_le {C₁ C₂ : LinearCode (ZMod 2) ι}
    {S T : Set (ι → ZMod 2)} {ψ : (bitReg ι).space}
    (hC₂ : C₂ ≤ Submodule.span (ZMod 2) S) (hC₁d : C₁.dual ≤ Submodule.span (ZMod 2) T)
    (hX : ∀ v ∈ S, (bitString v).op ψ = ψ) (hZ : ∀ u ∈ T, (phaseString u).op ψ = ψ) :
    ψ ∈ cssStabilizedSpace C₁ C₂ := by
  rw [mem_cssStabilizedSpace_iff]
  exact ⟨fun v hv => bitString_op_eq_self_of_mem_span hX (hC₂ hv),
    fun u hu => phaseString_op_eq_self_of_mem_span hZ (hC₁d hu)⟩

/-- **Code-space membership from generators** (needs `C₂ ≤ C₁`). The composition of
`mem_cssStabilizedSpace_of_span_le` with the code-space equality `V_S = CSS(C₁, C₂)`
(`cssStabilizedSpace_eq_cssCodeSpace`): a state fixed by a spanning set of the X- and Z-type check
generators lies in the CSS code space `span{ |x + C₂⟩ : x ∈ C₁ }`. -/
theorem mem_cssCodeSpace_of_span_le {C₁ C₂ : LinearCode (ZMod 2) ι} [DecidablePred (· ∈ C₂)]
    {S T : Set (ι → ZMod 2)} {ψ : (bitReg ι).space} (hsub : C₂ ≤ C₁)
    (hC₂ : C₂ ≤ Submodule.span (ZMod 2) S) (hC₁d : C₁.dual ≤ Submodule.span (ZMod 2) T)
    (hX : ∀ v ∈ S, (bitString v).op ψ = ψ) (hZ : ∀ u ∈ T, (phaseString u).op ψ = ψ) :
    ψ ∈ cssCodeSpace C₁ C₂ := by
  rw [← cssStabilizedSpace_eq_cssCodeSpace hsub]
  exact mem_cssStabilizedSpace_of_span_le hC₂ hC₁d hX hZ

end AxQM
