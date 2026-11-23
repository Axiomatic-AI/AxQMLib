/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CSSStabilizerGenerators
import AxQM.Concrete.PauliGroup
import ToMathlib.GroupTheory.Subgroup.Centralizer

/-!
# Concrete: the CSS stabilizer subgroup `cssStabilizer C₁ C₂`

This file continues the formalisation of
**Nielsen & Chuang, Exercise 10.51** — *the check matrix (10.106) is the stabilizer of the CSS code
`CSS(C₁, C₂)`* (p. 470). Where `AxQM/Concrete/CSSStabilizerGenerators.lean` builds the
`X`-type / `Z`-type generator strings and proves the check-matrix commutativity condition
`H(C₂⊥) H(C₁)ᵀ = 0` at the level of matrices, this file assembles those generators into an honest
**subgroup of the `n`-qubit Pauli group** and shows it is **abelian** — the group-theoretic
realisation of N&C's remark that the commutativity condition is exactly what is needed "to see that
this defines a stabilizer code".

## The stabilizer group

The stabilizer generators of the CSS check matrix (10.106) are the phase-`0` Pauli strings
`X^v = xPauli v` (`v` a codeword of `C₂`, the row space of the top block `H(C₂⊥)`) and
`Z^u = zPauli u` (`u` a dual codeword of `C₁`, the row space of the bottom block `H(C₁)`). The **CSS
stabilizer group** is the subgroup they generate:

`cssStabilizer C₁ C₂ = ⟨ X^v : v ∈ C₂ ⟩ ∪ ⟨ Z^u : u ∈ C₁⊥ ⟩`.

We take the *basis-free* generating set — every codeword, not a chosen basis — so the definition is
canonical (independent of a parity-check matrix); the two generator families `X^v` and `Z^u` are
each closed under multiplication (`X^v X^{v'} = X^{v+v'}`), so the closure is unchanged and the
codeword-indexed presentation is the most faithful to N&C's "rows of `H(C₂⊥)` / `H(C₁)`".

## What this file proves

* `cssStabilizer` — the subgroup (of the finite Pauli group `PauliGroup n`).
* `xPauli_mem_cssStabilizer`, `zPauli_mem_cssStabilizer` — the generators lie in it.
* `cssStabilizer_isMulCommutative` — **`S` is abelian** when `C₂ ≤ C₁`. All four kinds of generator
  pair commute: two `X`-type (`xPauli_commute_xPauli`) or two `Z`-type (`zPauli_commute_zPauli`)
  strings commute unconditionally, and an `X`-type against a `Z`-type commutes because
  `v ⬝ᵥ u = 0` for `v ∈ C₂ ⊆ C₁`, `u ∈ C₁⊥` (`xPauli_commute_zPauli`, from the check-matrix
  condition `pauliString_xString_commute_zString_of_mem_dual`). The lift from the matrix-level
  `Commute` of `AxQM/Concrete/CSSStabilizerGenerators.lean` to `Commute` in `PauliGroup n` is
  `commute_of_toMat_commute`, using the faithfulness of `toMat` (`toMat_injective`, `toMat_mul`).

The genuineness of the stabilizer (`-I ∉ S`) and its code space — the dimension `2^{k₁-k₂}` and the
identification with `CSS(C₁, C₂)` — are in
`AxQM/Concrete/CSSStabilizerElements.lean` and later files.
-/

open Matrix

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The `X`- and `Z`-type Pauli-group generators -/

/-- The **`X`-type Pauli-group generator** `X^v` of a binary support vector `v : Fin n → ZMod 2`:
the phase-`0` element `(0, xString v)` of the Pauli group whose matrix is the `X`-type Pauli string
`pauliString (xString v)`. These are the generators from the top block `H(C₂⊥)` of the CSS check
matrix (10.106). -/
def xPauli (v : Fin n → ZMod 2) : PauliGroup n := ⟨0, xString v⟩

/-- The **`Z`-type Pauli-group generator** `Z^u` of a binary support vector `u : Fin n → ZMod 2`:
the phase-`0` element `(0, zString u)` of the Pauli group whose matrix is the `Z`-type Pauli string
`pauliString (zString u)`. These are the generators from the bottom block `H(C₁)` of the CSS check
matrix (10.106). -/
def zPauli (u : Fin n → ZMod 2) : PauliGroup n := ⟨0, zString u⟩

/-- The matrix of `X^v` is the `X`-type Pauli string: `(xPauli v).toMat = pauliString (xString v)`.
The phase power is `i⁰ = 1`, so the scalar drops. -/
@[simp]
theorem xPauli_toMat (v : Fin n → ZMod 2) : (xPauli v).toMat = pauliString (xString v) := by
  simp only [xPauli, PauliGroup.toMat, zmod4Pow_zero, one_smul]

/-- The matrix of `Z^u` is the `Z`-type Pauli string: `(zPauli u).toMat = pauliString (zString u)`.
The phase power is `i⁰ = 1`, so the scalar drops. -/
@[simp]
theorem zPauli_toMat (u : Fin n → ZMod 2) : (zPauli u).toMat = pauliString (zString u) := by
  simp only [zPauli, PauliGroup.toMat, zmod4Pow_zero, one_smul]

/-! ### Commutation lifted from the matrix representation to the group -/

/-- **The faithful representation reflects commutation.** If the operators `p.toMat` and `q.toMat`
commute, then `p` and `q` commute in the Pauli group. This is `Commute.of_map` applied to the
injective monoid hom `pauliRep` (whose underlying function is `toMat`, `pauliRep_injective`), which
lifts the matrix-level `Commute` results of `AxQM/Concrete/CSSStabilizerGenerators.lean` to
`PauliGroup n`. -/
theorem commute_of_toMat_commute {p q : PauliGroup n} (h : Commute p.toMat q.toMat) :
    Commute p q :=
  Commute.of_map PauliGroup.pauliRep_injective h

/-- **Two `X`-type generators commute** in the Pauli group. -/
theorem xPauli_commute_xPauli (v v' : Fin n → ZMod 2) : Commute (xPauli v) (xPauli v') :=
  commute_of_toMat_commute <| by
    rw [xPauli_toMat, xPauli_toMat]; exact pauliString_xString_commute_xString v v'

/-- **Two `Z`-type generators commute** in the Pauli group. -/
theorem zPauli_commute_zPauli (u u' : Fin n → ZMod 2) : Commute (zPauli u) (zPauli u') :=
  commute_of_toMat_commute <| by
    rw [zPauli_toMat, zPauli_toMat]; exact pauliString_zString_commute_zString u u'

/-- **An `X`-type generator commutes with a `Z`-type generator** whenever their supports come from
the CSS check matrix — `v ∈ C₂`, `u ∈ C₁⊥`, `C₂ ≤ C₁` — because then `v ⬝ᵥ u = 0`. This is the
check-matrix condition `H(C₂⊥) H(C₁)ᵀ = 0` of Exercise 10.51, lifted to `PauliGroup n`. -/
theorem xPauli_commute_zPauli {C₁ C₂ : LinearCode (ZMod 2) (Fin n)} (hsub : C₂ ≤ C₁)
    {v u : Fin n → ZMod 2} (hv : v ∈ C₂) (hu : u ∈ C₁.dual) : Commute (xPauli v) (zPauli u) :=
  commute_of_toMat_commute <| by
    rw [xPauli_toMat, zPauli_toMat]
    exact pauliString_xString_commute_zString_of_mem_dual hsub hv hu

/-! ### The CSS stabilizer subgroup -/

/-- **The CSS stabilizer group of the check matrix (10.106)** (Nielsen & Chuang, Exercise 10.51):
the subgroup of the `n`-qubit Pauli group `PauliGroup n` generated by the `X`-type strings `X^v`
(`v ∈ C₂`, the row space of `H(C₂⊥)`) and the `Z`-type strings `Z^u` (`u ∈ C₁⊥`, the row space of
`H(C₁)`). The generating set is basis-free — indexed by *all* codewords of `C₂` and `C₁⊥`, not a
chosen basis — so the group depends only on the codes `C₁, C₂`, not on a choice of parity-check
matrix. -/
noncomputable def cssStabilizer (C₁ C₂ : LinearCode (ZMod 2) (Fin n)) : Subgroup (PauliGroup n) :=
  Subgroup.closure ((xPauli '' (C₂ : Set (Fin n → ZMod 2))) ∪
    (zPauli '' (C₁.dual : Set (Fin n → ZMod 2))))

/-- **Every `X`-type generator `X^v` (`v ∈ C₂`) lies in the CSS stabilizer.** -/
theorem xPauli_mem_cssStabilizer {C₁ C₂ : LinearCode (ZMod 2) (Fin n)} {v : Fin n → ZMod 2}
    (hv : v ∈ C₂) : xPauli v ∈ cssStabilizer C₁ C₂ :=
  Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_image_of_mem xPauli hv))

/-- **Every `Z`-type generator `Z^u` (`u ∈ C₁⊥`) lies in the CSS stabilizer.** -/
theorem zPauli_mem_cssStabilizer {C₁ C₂ : LinearCode (ZMod 2) (Fin n)} {u : Fin n → ZMod 2}
    (hu : u ∈ C₁.dual) : zPauli u ∈ cssStabilizer C₁ C₂ :=
  Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_image_of_mem zPauli hu))

/-- **The CSS stabilizer group is abelian** (Nielsen & Chuang, Exercise 10.51). For classical binary
codes `C₂ ≤ C₁`, the group `cssStabilizer C₁ C₂` is commutative: every pair of its generators
commutes — two `X`-type or two `Z`-type strings unconditionally, and an `X`-type against a `Z`-type
by the check-matrix condition (`xPauli_commute_zPauli`, valid because `v ⬝ᵥ u = 0` for
`v ∈ C₂ ⊆ C₁`, `u ∈ C₁⊥`) — so `Subgroup.isMulCommutative_closure` makes the whole generated
subgroup abelian. This
is exactly N&C's observation that the commutativity `H(C₂⊥) H(C₁)ᵀ = 0` is what makes the check
matrix (10.106) define a genuine (abelian) stabilizer code. -/
theorem cssStabilizer_isMulCommutative {C₁ C₂ : LinearCode (ZMod 2) (Fin n)} (hsub : C₂ ≤ C₁) :
    IsMulCommutative ↥(cssStabilizer C₁ C₂) := by
  apply Subgroup.isMulCommutative_closure
  rintro x (⟨v, hv, rfl⟩ | ⟨u, hu, rfl⟩) y (⟨v', hv', rfl⟩ | ⟨u', hu', rfl⟩) -
  · exact xPauli_commute_xPauli v v'
  · exact xPauli_commute_zPauli hsub hv hu'
  · exact (xPauli_commute_zPauli hsub hv' hu).symm
  · exact zPauli_commute_zPauli u u'

end AxQM.Concrete
