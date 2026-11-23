/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CSSStabilizerElements
import AxQM.Concrete.PauliSubgroupNormalizer
import AxQM.Concrete.StabilizerCodeDistance

/-!
# Concrete: the normalizer (logical operators) of the CSS stabilizer

This file continues the formalisation of
**Nielsen & Chuang, Exercise 10.51** — *the check matrix (10.106) is the stabilizer of the CSS code
`CSS(C₁, C₂)`, and Theorem 10.8 gives `t`-qubit correction* (p. 470). Where the earlier files build
the stabilizer group `cssStabilizer C₁ C₂`, its element normal form `X^v Z^u`, and its genuineness
`-I ∉ S`, this file characterises the **normalizer** `N(S)` — the logical operators — which is what
the code's distance (and hence the `t`-qubit correction) is measured over.

## The normalizer inclusion (`checkRow_mem_of_mem_normalizer`)

Because the CSS stabilizer is a genuine stabilizer (`-I ∉ S`), its normalizer equals its centralizer
(Exercise 10.44, `normalizer_eq_centralizer_of_negOne_notMem`): an element `p ∈ N(S)` **commutes**
with every stabilizer element, in particular with every generator `X^v` (`v ∈ C₂`) and `Z^u`
(`u ∈ C₁⊥`). Commutation of Pauli-group elements is the vanishing of the binary symplectic
pairing of their check rows (Exercise 10.33), so:

* commuting with `Z^u` (`u ∈ C₁⊥`) forces `(checkRow p.idx).₁ ⬝ᵥ u = 0` for all `u ∈ C₁⊥`, i.e. the
  `X`-part of `p` lies in `(C₁⊥)⊥ = C₁` (`LinearCode.dual_dual`);
* commuting with `X^v` (`v ∈ C₂`) forces `(checkRow p.idx).₂ ⬝ᵥ v = 0` for all `v ∈ C₂`, i.e. the
  `Z`-part of `p` lies in `C₂⊥`.

Hence `N(S) ⊆ { X^a Z^b : a ∈ C₁, b ∈ C₂⊥ }` (read modulo the global phase, which the check row
discards) — exactly the CSS description of the logical operators: an `X`-type logical operator has
its support in `C₁`, a `Z`-type one in `C₂⊥`.

## The weight bridge (`hammingNorm_checkRow_..._le_weight`)

The Pauli weight of `p` (the number of non-identity tensor factors) bounds the Hamming weight of
each of its check-row blocks: a qubit where the `X`-bit or `Z`-bit of `p` is nonzero is one where
`p` acts non-trivially, so the support of `(checkRow p.idx).₁` (and of `.₂`) is contained in
`pauliStringSupport p.idx`. This is the last geometric ingredient the CSS distance bound needs: a
logical operator whose `X`-part is a nonzero codeword of `C₁` has weight at least the minimum
distance of `C₁`, and likewise for the `Z`-part and `C₂⊥`.

The distance
bound `stabilizerCodeDistance S ≥ 2t + 1` and the `t`-qubit correction it powers are in
`AxQM/Concrete/CSSStabilizerDistance.lean`.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The index of the CSS generators -/

/-- The Pauli string of the `X`-type generator is `X^v`: `(xPauli v).idx = xString v`. -/
@[simp]
theorem xPauli_idx (v : Fin n → ZMod 2) : (xPauli v).idx = xString v := rfl

/-- The Pauli string of the `Z`-type generator is `Z^u`: `(zPauli u).idx = zString u`. -/
@[simp]
theorem zPauli_idx (u : Fin n → ZMod 2) : (zPauli u).idx = zString u := rfl

/-! ### Group commutation as the vanishing of the symplectic pairing -/

/-- **Cancelling nonzero scalars from a commutation.** If `a • A` and `b • B` commute, with
`a, b ≠ 0` (as operators over a field), then `A` and `B` commute. Both `(a•A)(b•B)` and `(b•B)(a•A)`
equal `(ab) • (A·)` of the respective products, and `ab ≠ 0` is cancellable. Used to strip the phase
`iˢ` off `PauliGroup.toMat = iˢ • pauliString` when reducing a group commutation to a Pauli-string
commutation. -/
theorem commute_of_smul_commute {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    {A B : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ} (h : Commute (a • A) (b • B)) :
    Commute A B := by
  refine smul_right_injective _ (mul_ne_zero ha hb) ?_
  have he : (a • A) * (b • B) = (b • B) * (a • A) := h
  rwa [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm b a] at he

/-- **Commuting Pauli-group elements have vanishing symplectic pairing** (Exercise 10.33 at the
group level). If `p` and `q` commute in the Pauli group, then the binary symplectic pairing of their
check rows vanishes: `symplecticForm (checkVec p.idx) (checkVec q.idx) = 0`. The faithful
representation `pauliRep` (a monoid hom) carries the group commutation to
`Commute (iˢ • P_{p.idx}) (iᵗ • P_{q.idx})`; stripping the nonzero phases
(`commute_of_smul_commute`) gives `Commute P_{p.idx} P_{q.idx}`, which is the symplectic condition
by `pauliString_commute_iff_symplecticForm`. -/
theorem symplecticForm_checkVec_eq_zero_of_commute {p q : PauliGroup n} (h : Commute p q) :
    symplecticForm (checkVec p.idx) (checkVec q.idx) = 0 := by
  rw [← pauliString_commute_iff_symplecticForm]
  refine commute_of_smul_commute (zmod4Pow_ne_zero p.phase) (zmod4Pow_ne_zero q.phase) ?_
  simpa only [PauliGroup.pauliRep_apply] using h.map PauliGroup.pauliRep

/-! ### The symplectic pairing of a Pauli string against a CSS generator -/

/-- **Pairing against a `Z`-type generator picks out the `X`-part.** For any Pauli string `g` and
support `u`, `symplecticForm (checkVec g) (checkVec (zString u)) = (checkRow g).₁ ⬝ᵥ u`: the twisted
product of `r(g) = (x_g | z_g)` with `r(Z^u) = (0 | u)` is `x_g ⬝ᵥ u`. -/
theorem symplecticForm_checkVec_zString (g : Fin n → Fin 4) (u : Fin n → ZMod 2) :
    symplecticForm (checkVec g) (checkVec (zString u)) = (checkRow g).1 ⬝ᵥ u := by
  rw [symplecticForm_checkVec_eq_checkSymplectic, checkRow_zString, checkSymplectic_apply]
  simp only [Pi.zero_apply, mul_zero, add_zero, dotProduct]

/-- **Pairing against an `X`-type generator picks out the `Z`-part.** For any Pauli string `g` and
support `v`, `symplecticForm (checkVec g) (checkVec (xString v)) = (checkRow g).₂ ⬝ᵥ v`: the twisted
product of `r(g) = (x_g | z_g)` with `r(X^v) = (v | 0)` is `z_g ⬝ᵥ v`. -/
theorem symplecticForm_checkVec_xString (g : Fin n → Fin 4) (v : Fin n → ZMod 2) :
    symplecticForm (checkVec g) (checkVec (xString v)) = (checkRow g).2 ⬝ᵥ v := by
  rw [symplecticForm_checkVec_eq_checkSymplectic, checkRow_xString, checkSymplectic_apply]
  simp only [Pi.zero_apply, mul_zero, zero_add, dotProduct]

/-! ### A normalizer element commutes with every stabilizer element -/

/-- **A normalizer element commutes with every stabilizer element** (for a genuine stabilizer).
Since `-I ∉ S`, the normalizer equals the centralizer (Exercise 10.44), so `p ∈ N(S)` commutes with
`g ∈ S`. This is the contrapositive of `notMem_normalizer_of_mem_of_ne_comm`. -/
theorem commute_of_mem_normalizer {S : Subgroup (PauliGroup n)} (hS : PauliGroup.negOne n ∉ S)
    {g p : PauliGroup n} (hg : g ∈ S) (hp : p ∈ Subgroup.normalizer S) : Commute g p := by
  by_contra hne
  exact notMem_normalizer_of_mem_of_ne_comm hS hg hne hp

/-! ### The normalizer inclusion `N(S) ⊆ { X^a Z^b : a ∈ C₁, b ∈ C₂⊥ }` -/

/-- **The `X`-part of a logical operator lies in `C₁`** (Nielsen & Chuang, Exercise 10.51). For
classical binary codes `C₂ ≤ C₁`, if `p` lies in the normalizer of the CSS stabilizer, then the
`X`-part of its check row is a codeword of `C₁`. Proof: `p` commutes with every `Z`-type generator
`Z^u` (`u ∈ C₁⊥`), and that commutation is `(checkRow p.idx).₁ ⬝ᵥ u = 0`; holding for all `u ∈ C₁⊥`
places the `X`-part in `(C₁⊥)⊥ = C₁` (`LinearCode.dual_dual`). -/
theorem checkRow_fst_mem_of_mem_normalizer {C₁ C₂ : LinearCode (ZMod 2) (Fin n)} (hsub : C₂ ≤ C₁)
    {p : PauliGroup n} (hp : p ∈ Subgroup.normalizer (cssStabilizer C₁ C₂)) :
    (checkRow p.idx).1 ∈ C₁ := by
  rw [← C₁.dual_dual, LinearCode.mem_dual_iff]
  intro u hu
  have hcomm : Commute (zPauli u) p :=
    commute_of_mem_normalizer (negOne_notMem_cssStabilizer hsub) (zPauli_mem_cssStabilizer hu) hp
  have hsym := symplecticForm_checkVec_eq_zero_of_commute hcomm.symm
  rw [zPauli_idx, symplecticForm_checkVec_zString] at hsym
  rw [dotProduct_comm]; exact hsym

/-- **The `Z`-part of a logical operator lies in `C₂⊥`** (Nielsen & Chuang, Exercise 10.51). For
classical binary codes `C₂ ≤ C₁`, if `p` lies in the normalizer of the CSS stabilizer, then the
`Z`-part of its check row is a dual codeword of `C₂`. Proof: `p` commutes with every `X`-type
generator `X^v` (`v ∈ C₂`), and that commutation is `(checkRow p.idx).₂ ⬝ᵥ v = 0`; holding for all
`v ∈ C₂` places the `Z`-part in `C₂⊥` (`LinearCode.mem_dual_iff`). -/
theorem checkRow_snd_mem_of_mem_normalizer {C₁ C₂ : LinearCode (ZMod 2) (Fin n)} (hsub : C₂ ≤ C₁)
    {p : PauliGroup n} (hp : p ∈ Subgroup.normalizer (cssStabilizer C₁ C₂)) :
    (checkRow p.idx).2 ∈ C₂.dual := by
  rw [LinearCode.mem_dual_iff]
  intro v hv
  have hcomm : Commute (xPauli v) p :=
    commute_of_mem_normalizer (negOne_notMem_cssStabilizer hsub) (xPauli_mem_cssStabilizer hv) hp
  have hsym := symplecticForm_checkVec_eq_zero_of_commute hcomm.symm
  rw [xPauli_idx, symplecticForm_checkVec_xString] at hsym
  rw [dotProduct_comm]; exact hsym

/-- **The normalizer inclusion `N(S) ⊆ { X^a Z^b : a ∈ C₁, b ∈ C₂⊥ }`** (Nielsen & Chuang,
Exercise 10.51). For classical binary codes `C₂ ≤ C₁`, every logical operator `p ∈ N(S)` of the CSS
stabilizer has `X`-part in `C₁` and `Z`-part in `C₂⊥` — the check-row form of N&C's statement that
the logical operators of `CSS(C₁, C₂)` are (up to phase) the `X^a Z^b` with `a ∈ C₁` and `b ∈ C₂⊥`.
Together with the normal form of `S` itself (`mem_cssStabilizer_iff`: `a ∈ C₂`, `b ∈ C₁⊥`), this is
what makes the code distance a classical minimum-distance computation. -/
theorem checkRow_mem_of_mem_normalizer {C₁ C₂ : LinearCode (ZMod 2) (Fin n)} (hsub : C₂ ≤ C₁)
    {p : PauliGroup n} (hp : p ∈ Subgroup.normalizer (cssStabilizer C₁ C₂)) :
    (checkRow p.idx).1 ∈ C₁ ∧ (checkRow p.idx).2 ∈ C₂.dual :=
  ⟨checkRow_fst_mem_of_mem_normalizer hsub hp, checkRow_snd_mem_of_mem_normalizer hsub hp⟩

/-! ### The Pauli weight bounds the Hamming weight of each check-row block -/

/-- **The Pauli weight bounds the Hamming weight of the `X`-part.**
`hammingNorm (checkRow p.idx).₁ ≤ weight p`: a qubit where the `X`-bit of `p` is nonzero is one
where `p` acts non-trivially, so the support of the `X`-part is contained in the Pauli-string
support `pauliStringSupport p.idx`. -/
theorem hammingNorm_checkRow_fst_le_weight (p : PauliGroup n) :
    hammingNorm (checkRow p.idx).1 ≤ p.weight := by
  rw [hammingNorm, PauliGroup.weight]
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [mem_pauliStringSupport]
  intro h0
  exact hi (by rw [checkRow]; simp only [h0]; decide)

/-- **The Pauli weight bounds the Hamming weight of the `Z`-part.**
`hammingNorm (checkRow p.idx).₂ ≤ weight p`: a qubit where the `Z`-bit of `p` is nonzero is one
where `p` acts non-trivially, so the support of the `Z`-part is contained in the Pauli-string
support `pauliStringSupport p.idx`. -/
theorem hammingNorm_checkRow_snd_le_weight (p : PauliGroup n) :
    hammingNorm (checkRow p.idx).2 ≤ p.weight := by
  rw [hammingNorm, PauliGroup.weight]
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [mem_pauliStringSupport]
  intro h0
  exact hi (by rw [checkRow]; simp only [h0]; decide)

end AxQM.Concrete
