/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliGroup
import Mathlib.Algebra.Group.Subgroup.Basic
import ToMathlib.Algebra.Group.Subgroup.InvolutionClosure
import ToMathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Concrete: the structure of a Pauli subgroup `S` with `-I ∉ S`

This file develops the
elementary group theory Nielsen & Chuang use in the proof of **Proposition 10.3**
for a subgroup `S` of the `n`-qubit Pauli group `Gₙ` (`Concrete.PauliGroup`)
satisfying `-I ∉ S` (`negOne n ∉ S`). Everything here names only the abstract group
`PauliGroup n`, its subgroups, and the check row (`ZMod`, `Fin n → Fin 4`).

## Squares in the Pauli group

Every Pauli-group element is an involution up to phase: since each single-qubit
Pauli squares to `I` (`pauliMul a a = 0`) with trivial phase
(`singlePhasePow a a = 0`), a group element `p = (s, a)` squares to `p * p = (2s, 0)`
(`mul_self`), a *phase-only* element. Hence `p * p` is always `I` or `-I`
(`mul_self_eq_one_or_negOne`).

## The `-I ∉ S` structure (N&C Exercises 10.30, 10.35)

For a subgroup `S` with `negOne n ∉ S`, `p * p ∈ S` for `p ∈ S`, and `p * p ≠ -I`,
so:

* `imOne_notMem_of_negOne_notMem`, `negImOne_notMem_of_negOne_notMem` — **N&C Exercise 10.30**
  (`-I ∉ S ⟹ ±iI ∉ S`): the phase-only elements `iI` (`imOne := (1, 0)`) and `-iI`
  (`negImOne := (3, 0)`) both square to `-I` (`imOne_mul_self`, `negImOne_mul_self`), so a subgroup
  `S` that is closed under products and has `-I ∉ S` can contain neither. (`pauliRep_imOne`,
  `pauliRep_negImOne` confirm these two elements really represent the operators `iI` and `-iI`.)
* `sq_eq_one_of_negOne_notMem` — **`g² = I` for all `g ∈ S`** (N&C Exercise 10.35):
  `S` is an *elementary abelian* `2`-group. Equivalently every `g ∈ S` is its own
  inverse (`inv_eq_self_of_negOne_notMem`, N&C's `g† = g`).
* `mul_comm_of_negOne_notMem` — **`S` is abelian**: any group in which every element
  squares to `1` is commutative (`gh = (gh)⁻¹ = h⁻¹g⁻¹ = hg`). This is N&C's
  necessary condition (a) (commuting elements), here derived from `-I ∉ S` alone.
* `eq_one_of_checkRowHom_eq_zero_of_negOne_notMem` — **the check row is injective on
  `S`**: from `r(g) = 0` and `g ∈ S` we get `g = I`. The bare kernel of `r` is the
  phase-only elements `iˢ · I` (`checkRowHom_eq_zero_iff`); of those, `iI` and `-iI`
  square to `-I ∉ S`, while `-I` itself is excluded directly as `-I ∉ S`, so only
  `g = I` remains (the phase argument of Exercise 10.30, here inlined at the level of
  the phase `s ∈ {0, 2}` rather than routed through `imOne_notMem_of_negOne_notMem`).

Together these are the ingredients Proposition 10.3's proof invokes ("note first
that `gᵢ² = I` for all `i`") and turn the *bare* kernel of `Concrete/PauliGroup.lean`
into a *trivial* kernel on `S` — exactly what identifies `S` with its check-matrix
rows as an `𝔽₂`-vector space (the Proposition 10.3 equivalence).

## N&C Exercise 10.34 (`-I ∉ S ⟺ gⱼ² = I ∧ gⱼ ≠ -I`) — false as literally stated

Exercise 10.34 asks to show, for `S = ⟨g₁,…,g_l⟩`, that `-I ∉ S` iff `gⱼ² = I` and
`gⱼ ≠ -I` for every generator `gⱼ`.

* The **forward** implication is true and is
  `sq_eq_one_and_ne_negOne_of_negOne_notMem_closure`: every generator lies in `S`, so
  this is `sq_eq_one_of_negOne_notMem` (Exercise 10.35) together with the fact that a
  member of `S` cannot equal the non-member `-I`.
* The **reverse** implication is **false** as the exercise states it: the two
  per-generator conditions `gⱼ² = I` and `gⱼ ≠ -I` do not imply `-I ∉ S`. Two
  hypotheses are omitted from the wording, and **neither alone suffices**:
  - *Commutativity alone is insufficient.* `⟨X, -X⟩` in `PauliGroup 1`: `X` and `-X`
    **commute**, both square to `I`, neither is `-I`, yet `X·(-X) = -I ∈ ⟨X, -X⟩`
    (`pauliXOne_mul_negPauliXOne`,
    `exists_commuting_gens_sq_one_ne_negOne_with_negOne_mem`). Here `X` and `-X` have
    equal check rows, i.e. are `𝔽₂`-**dependent**.
  - *Independence alone is insufficient.* `⟨X, Z⟩` in `PauliGroup 1`: `X` and `Z` are
    `𝔽₂`-independent (check rows `(1,0)`, `(0,1)`) but **anticommute**, so
    `(XZ)² = -I ∈ ⟨X, Z⟩` (`pauliXZ_sq_eq_negOne`, `negOne_mem_closure_pauliXZ`,
    `exists_gens_sq_one_ne_negOne_with_negOne_mem`).

The genuinely missing ingredient is `𝔽₂`-**independence** of the generators (N&C
Proposition 10.3), *together with* commutativity. Commutativity is **not** an
independent discriminator once `-I ∉ S` is known (any such subgroup is automatically
abelian, `mul_comm_of_negOne_notMem`); but for the *reverse* implication `-I ∉ S` is the
conclusion, not a hypothesis, so commutativity must be assumed alongside independence,
and neither alone suffices (the two counterexamples above).

**The intended correct statement** — the result the book evidently means — restores
exactly these two hypotheses. Under them the biconditional holds with the exercise's own
right-hand side: `negOne_notMem_closure_iff_forall_sq_eq_one_and_ne_negOne` proves, for a
family `g` that pairwise commutes and whose check rows are `𝔽₂`-linearly independent,
`-I ∉ ⟨g₁,…,g_l⟩ ⟺ (∀ j, gⱼ² = I ∧ gⱼ ≠ -I)`. Its reverse half
(`negOne_notMem_closure_of_commute_of_checkRowHom_linearIndependent`) is Proposition
10.3's check-matrix argument run in reverse: the commuting involutions generate an
elementary abelian `2`-group whose elements are the subset products
`∏ⱼ gⱼ ^ (cⱼ).val` (the general `ToMathlib` lemma
`Subgroup.exists_zmod2_prod_of_mem_closure`), and applying the check-row homomorphism
to a putative `-I = ∏ⱼ gⱼ ^ (cⱼ).val` gives `∑ⱼ cⱼ · r(gⱼ) = r(-I) = 0`, which
independence forces to the empty product `I ≠ -I`.

So this item is formalised in full: the true forward implication, the **refutation** of
the false reverse implication by two explicit counterexamples (one commuting, one
independent — each isolating a necessary hypothesis the wording omits), **and** the
intended correct biconditional, proved. We never patch the false `⟺` silently; we exhibit
its failure and separately state and prove the corrected form.
-/

open scoped BigOperators
open scoped IsMulCommutative

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### Diagonal identities of the Pauli-index product tables -/

/-- Each single-qubit Pauli squares to the identity: `a ⊙ a = 0` (i.e. `σ_a σ_a = I`).
The diagonal of the `pauliMul` table is `0`. -/
theorem pauliMul_self (a : Fin 4) : pauliMul a a = 0 := by fin_cases a <;> decide

/-- Squaring a single-qubit Pauli has trivial phase: `singlePhasePow a a = 0`
(`σ_a σ_a = I`, no `i`-factor). The diagonal of the `singlePhasePow` table is `0`. -/
theorem singlePhasePow_self (a : Fin 4) : singlePhasePow a a = 0 := by fin_cases a <;> decide

/-- The `n`-qubit product index of a string with itself is the identity index:
`a ⊙ a = 0` (componentwise `pauliMul_self`). -/
theorem pauliMulIndex_self (a : Fin n → Fin 4) : pauliMulIndex a a = 0 := by
  funext k; exact pauliMul_self (a k)

/-- The `n`-qubit product-phase exponent of a string with itself vanishes:
`phasePow a a = 0` (the sum of the per-qubit zeros `singlePhasePow_self`). -/
theorem phasePow_self (a : Fin n → Fin 4) : phasePow a a = 0 := by
  simp only [phasePow, singlePhasePow_self, Finset.sum_const_zero]

namespace PauliGroup

/-! ### Squares of Pauli-group elements -/

/-- The phase of a square doubles: `(p * p).phase = 2 · p.phase` (the twist
`phasePow p.idx p.idx` vanishes by `phasePow_self`). -/
theorem mul_self_phase (p : PauliGroup n) : (p * p).phase = 2 * p.phase := by
  rw [mul_phase, phasePow_self, add_zero, two_mul]

/-- The index of a square is the identity index: `(p * p).idx = 0`
(`pauliMulIndex_self`). -/
theorem mul_self_idx (p : PauliGroup n) : (p * p).idx = 0 := by
  rw [mul_idx, pauliMulIndex_self]

/-- **A Pauli-group element squares to a phase-only element**: `p * p = (2 · p.phase, 0)`,
i.e. `(iˢ P_a)² = i²ˢ · I`. The index cancels (`mul_self_idx`), the phase doubles
(`mul_self_phase`). -/
theorem mul_self (p : PauliGroup n) : p * p = ⟨2 * p.phase, 0⟩ :=
  PauliGroup.ext (mul_self_phase p) (mul_self_idx p)

/-- **Every Pauli-group element squares to `±I`**: `p * p = I` or `p * p = -I`. Since
`p * p = (2 · p.phase, 0)` is phase-only and `2s ∈ {0, 2}` in `ZMod 4`, the square is
`(0,0) = I` or `(2,0) = -I` (`negOne`). -/
theorem mul_self_eq_one_or_negOne (p : PauliGroup n) : p * p = 1 ∨ p * p = negOne n := by
  rw [mul_self p]
  rcases (by decide : ∀ s : ZMod 4, 2 * s = 0 ∨ 2 * s = 2) p.phase with h | h
  · rw [h]; left; rfl
  · rw [h]; right; rfl

/-! ### The structure of a subgroup with `-I ∉ S` -/

/-- **N&C Exercise 10.35**: for a subgroup `S` of the Pauli group with `-I ∉ S`, every
`g ∈ S` satisfies `g² = I`. Indeed `g² = I` or `g² = -I` (`mul_self_eq_one_or_negOne`),
and `g² ∈ S` (closure under multiplication) while `-I ∉ S`, so `g² = I`. This makes `S`
an elementary abelian `2`-group. -/
theorem sq_eq_one_of_negOne_notMem {S : Subgroup (PauliGroup n)} (hS : negOne n ∉ S)
    {p : PauliGroup n} (hp : p ∈ S) : p ^ 2 = 1 := by
  rw [pow_two]
  rcases mul_self_eq_one_or_negOne p with h | h
  · exact h
  · exact absurd (h ▸ S.mul_mem hp hp) hS

/-- **N&C Exercise 10.35** (the group form of `g† = g`): for a subgroup `S` with `-I ∉ S`,
every `g ∈ S` is its own inverse, `g⁻¹ = g`. Immediate from `g² = I`
(`sq_eq_one_of_negOne_notMem`). Because the Pauli-group representation `toMat` is unitary,
this is the operator statement `g† = g`, recorded at the matrix level as
`toMat_isHermitian_of_negOne_notMem`. -/
theorem inv_eq_self_of_negOne_notMem {S : Subgroup (PauliGroup n)} (hS : negOne n ∉ S)
    {p : PauliGroup n} (hp : p ∈ S) : p⁻¹ = p := by
  exact inv_eq_of_mul_eq_one_right (pow_two p ▸ sq_eq_one_of_negOne_notMem hS hp)

/-- **N&C Exercise 10.35** (`g† = g`, the operator form): for a subgroup `S` of the
`n`-qubit Pauli group with `-I ∉ S`, the operator `toMat g` of every `g ∈ S` is **Hermitian**,
`(toMat g)ᴴ = toMat g`. This is N&C's `g† = g` at the level of the actual matrix (`†` = the
conjugate transpose): the adjoint of a Pauli-group element is its inverse
(`toMat_inv : (toMat p)ᴴ = toMat p⁻¹`, i.e. the representation is unitary), and `g⁻¹ = g` on `S`
(`inv_eq_self_of_negOne_notMem`), so the adjoint equals `g` itself. Physically the stabilizer
generators are therefore genuine observables (Hermitian, with `±1` eigenvalues by `g² = I`). -/
theorem toMat_isHermitian_of_negOne_notMem {S : Subgroup (PauliGroup n)} (hS : negOne n ∉ S)
    {p : PauliGroup n} (hp : p ∈ S) : (p.toMat).IsHermitian := by
  rw [Matrix.IsHermitian, ← toMat_inv, inv_eq_self_of_negOne_notMem hS hp]

/-- **The subgroup `S` is abelian** (N&C's necessary condition (a), derived from
`-I ∉ S`): for `g, h ∈ S`, `g h = h g`. A group in which every element squares to `1`
is commutative — `g`, `h` and `gh` are all their own inverses
(`inv_eq_self_of_negOne_notMem`), so `gh = (gh)⁻¹ = h⁻¹ g⁻¹ = h g`. -/
theorem mul_comm_of_negOne_notMem {S : Subgroup (PauliGroup n)} (hS : negOne n ∉ S)
    {p q : PauliGroup n} (hp : p ∈ S) (hq : q ∈ S) : p * q = q * p := by
  have hpq : (p * q)⁻¹ = p * q := inv_eq_self_of_negOne_notMem hS (S.mul_mem hp hq)
  rw [mul_inv_rev, inv_eq_self_of_negOne_notMem hS hq,
    inv_eq_self_of_negOne_notMem hS hp] at hpq
  exact hpq.symm

/-- **The check row is injective on a subgroup with `-I ∉ S`** (the *trivial* kernel,
packaging N&C Exercise 10.30): if `g ∈ S`, `-I ∉ S`, and `r(g) = 0`, then `g = I`. The
bare kernel of `r` is the phase-only elements `p = (s, 0)` (`checkRowHom_eq_zero_iff`);
such a `p` has `p² = (2s, 0)`, forced to `I` by `-I ∉ S`
(`sq_eq_one_of_negOne_notMem`), so `2s = 0`, i.e. `s ∈ {0, 2}`. `s = 2` gives
`p = -I ∈ S`, impossible; hence `s = 0` and `p = I`. -/
theorem eq_one_of_checkRowHom_eq_zero_of_negOne_notMem {S : Subgroup (PauliGroup n)}
    (hS : negOne n ∉ S) {p : PauliGroup n} (hp : p ∈ S) (h : checkRowHom p = 0) :
    p = 1 := by
  have hidx : p.idx = 0 := (checkRowHom_eq_zero_iff p).mp h
  have hsq : p * p = 1 := by rw [← pow_two]; exact sq_eq_one_of_negOne_notMem hS hp
  have hphase : 2 * p.phase = 0 := by rw [← mul_self_phase p, hsq]; rfl
  rcases (by decide : ∀ s : ZMod 4, 2 * s = 0 → s = 0 ∨ s = 2) p.phase hphase with hph | hph
  · exact PauliGroup.ext hph hidx
  · refine absurd ?_ hS
    have hp' : p = negOne n := PauliGroup.ext hph hidx
    rwa [hp'] at hp

/-! ### The phase-only elements `iI`, `-iI`, and N&C Exercise 10.30 -/

/-- The Pauli-group element **`iI`**, i.e. `(1, 0)` (`i¹ · I = iI`). With `-iI` (`negImOne`) these
are the two phase-only elements N&C Exercise 10.30 excludes from a subgroup `S` with `-I ∉ S`:
both square to `-I`. -/
def imOne (n : ℕ) : PauliGroup n := ⟨1, 0⟩

/-- The Pauli-group element **`-iI`**, i.e. `(3, 0)` (`i³ · I = -iI`). -/
def negImOne (n : ℕ) : PauliGroup n := ⟨3, 0⟩

/-- The representation of `imOne` is the operator `iI` (`Complex.I` times the identity matrix):
`i¹ • P₀ = i • I`. Mirrors `pauliRep_negOne`; confirms `imOne` really is `iI`. -/
theorem pauliRep_imOne : pauliRep (imOne n) = Complex.I • 1 := by
  simp only [pauliRep_apply, imOne]
  rw [zmod4Pow_one, (pauliString_eq_one_iff (0 : Fin n → Fin 4)).mpr rfl]

/-- The representation of `negImOne` is the operator `-iI`: `i³ • P₀ = -i • I`. Mirrors
`pauliRep_negOne`; confirms `negImOne` really is `-iI`. -/
theorem pauliRep_negImOne : pauliRep (negImOne n) = -Complex.I • 1 := by
  simp only [pauliRep_apply, negImOne]
  rw [zmod4Pow_three, (pauliString_eq_one_iff (0 : Fin n → Fin 4)).mpr rfl]

/-- **`(iI)² = -I`**: `imOne² = negOne`. The index cancels and the phase doubles to `2 · 1 = 2`
in `ZMod 4` (`mul_self`), giving the phase-only element `(2, 0) = -I`. -/
theorem imOne_mul_self : imOne n * imOne n = negOne n :=
  PauliGroup.ext (by simp only [mul_self_phase, imOne, negOne]; decide) (mul_self_idx _)

/-- **`(-iI)² = -I`**: `negImOne² = negOne`. The phase doubles to `2 · 3 = 6 = 2` in `ZMod 4`. -/
theorem negImOne_mul_self : negImOne n * negImOne n = negOne n :=
  PauliGroup.ext (by simp only [mul_self_phase, negImOne, negOne]; decide) (mul_self_idx _)

/-- **N&C Exercise 10.30** (the `iI` half): for a subgroup `S` of the `n`-qubit Pauli group with
`-I ∉ S`, the element `iI` is not in `S`. If `iI ∈ S` then `(iI)² = -I ∈ S` by closure
(`imOne_mul_self`), contradicting `-I ∉ S`. -/
theorem imOne_notMem_of_negOne_notMem {S : Subgroup (PauliGroup n)} (hS : negOne n ∉ S) :
    imOne n ∉ S := fun h => hS (imOne_mul_self ▸ S.mul_mem h h)

/-- **N&C Exercise 10.30** (the `-iI` half): for a subgroup `S` of the `n`-qubit Pauli group with
`-I ∉ S`, the element `-iI` is not in `S`. If `-iI ∈ S` then `(-iI)² = -I ∈ S` by closure
(`negImOne_mul_self`), contradicting `-I ∉ S`. -/
theorem negImOne_notMem_of_negOne_notMem {S : Subgroup (PauliGroup n)} (hS : negOne n ∉ S) :
    negImOne n ∉ S := fun h => hS (negImOne_mul_self ▸ S.mul_mem h h)

/-! ### N&C Exercise 10.34: `-I ∉ S ⟺ gⱼ² = I ∧ gⱼ ≠ -I` (forward true, reverse false) -/

/-- **N&C Exercise 10.34, forward implication** (the true half). Let `S = ⟨g₁,…,g_l⟩ = closure T` be
the subgroup generated by a set `T` of Pauli-group elements. If `-I ∉ S` then every generator
`g ∈ T` satisfies `g² = I` and `g ≠ -I`. Both follow from `g ∈ S` (`Subgroup.subset_closure`): the
square is `I` by `sq_eq_one_of_negOne_notMem` (Exercise 10.35), and `g ≠ -I` because `g ∈ S` while
`-I ∉ S`. (The converse is **false**: the two per-generator conditions do not imply `-I ∉ S`
without `𝔽₂`-independence of the generators — see `exists_gens_sq_one_ne_negOne_with_negOne_mem`
and `exists_commuting_gens_sq_one_ne_negOne_with_negOne_mem`.) -/
theorem sq_eq_one_and_ne_negOne_of_negOne_notMem_closure {T : Set (PauliGroup n)}
    (hS : negOne n ∉ Subgroup.closure T) {g : PauliGroup n} (hg : g ∈ T) :
    g ^ 2 = 1 ∧ g ≠ negOne n := by
  have hmem : g ∈ Subgroup.closure T := Subgroup.subset_closure hg
  exact ⟨sq_eq_one_of_negOne_notMem hS hmem, fun h => hS (h ▸ hmem)⟩

/-- The single-qubit Pauli `X` as an element of the Pauli group `PauliGroup 1`: phase `0`, index
`X = 1` (so `pauliRep` sends it to the operator `X`). One of the two generators of the Exercise
10.34 counterexample `⟨X, Z⟩ ∋ -I`. -/
def pauliXOne : PauliGroup 1 := ⟨0, ![1]⟩

/-- The single-qubit Pauli `Z` as an element of the Pauli group `PauliGroup 1`: phase `0`, index
`Z = 3`. The second generator of the Exercise 10.34 counterexample. -/
def pauliZOne : PauliGroup 1 := ⟨0, ![3]⟩

/-- `X² = I` in `PauliGroup 1`: the index cancels and the phase doubles to `2·0 = 0`
(`mul_self`). -/
theorem pauliXOne_sq : pauliXOne ^ 2 = 1 := by decide

/-- `Z² = I` in `PauliGroup 1`, exactly as for `X` (`mul_self`, phase `2·0 = 0`). -/
theorem pauliZOne_sq : pauliZOne ^ 2 = 1 := by decide

/-- `X ≠ -I` in `PauliGroup 1` (they differ in their Pauli index: `X` has index `1`, `-I` index
`0`). -/
theorem pauliXOne_ne_negOne : pauliXOne ≠ negOne 1 := by decide

/-- `Z ≠ -I` in `PauliGroup 1` (index `3` versus `0`). -/
theorem pauliZOne_ne_negOne : pauliZOne ≠ negOne 1 := by decide

/-- The phase of the product `X·Z` in `PauliGroup 1` is `3`: `0 + 0 + phasePow ![1] ![3] =
singlePhasePow 1 3 = 3`. (Equivalently `XZ = -iY = i³·Y`.) -/
theorem pauliXOne_mul_pauliZOne_phase : (pauliXOne * pauliZOne).phase = 3 := by decide

/-- **`(XZ)² = -I`** in `PauliGroup 1`: `X` and `Z` anticommute, so their product `XZ = -iY` squares
to `-I`. Concretely `(XZ)²` is phase-only with phase `2·(XZ).phase = 2·3 = 2` (`mul_self`,
`pauliXOne_mul_pauliZOne_phase`), i.e. `⟨2, 0⟩ = -I`. This is the crux of the Exercise 10.34
counterexample. -/
theorem pauliXZ_sq_eq_negOne :
    pauliXOne * pauliZOne * (pauliXOne * pauliZOne) = negOne 1 := by decide

/-- **`-I ∈ ⟨X, Z⟩`** in `PauliGroup 1`: since `X, Z ∈ ⟨X, Z⟩` and the subgroup is closed under
products, `(XZ)² ∈ ⟨X, Z⟩`, and `(XZ)² = -I` (`pauliXZ_sq_eq_negOne`). So `-I` lies in the group
generated by `X` and `Z` even though `X² = Z² = I` and `X, Z ≠ -I` — the failure of the reverse
implication of Exercise 10.34. -/
theorem negOne_mem_closure_pauliXZ :
    negOne 1 ∈ Subgroup.closure ({pauliXOne, pauliZOne} : Set (PauliGroup 1)) := by
  have hX : pauliXOne ∈ Subgroup.closure ({pauliXOne, pauliZOne} : Set (PauliGroup 1)) :=
    Subgroup.subset_closure (by simp)
  have hZ : pauliZOne ∈ Subgroup.closure ({pauliXOne, pauliZOne} : Set (PauliGroup 1)) :=
    Subgroup.subset_closure (by simp)
  have hmem := Subgroup.mul_mem _ (Subgroup.mul_mem _ hX hZ) (Subgroup.mul_mem _ hX hZ)
  rwa [pauliXZ_sq_eq_negOne] at hmem

/-- **N&C Exercise 10.34, reverse implication is false.** There is a set `T` of Pauli-group elements
each satisfying `g² = I` and `g ≠ -I`, whose generated subgroup `⟨T⟩` nevertheless contains `-I`.
The witness is `T = {X, Z}` in `PauliGroup 1`: `X² = Z² = I` and `X, Z ≠ -I`
(`pauliXOne_sq`, `pauliZOne_sq`, `pauliXOne_ne_negOne`, `pauliZOne_ne_negOne`), yet `-I ∈ ⟨X, Z⟩`
(`negOne_mem_closure_pauliXZ`), because `X` and `Z` anticommute. This refutes the `⟸` direction of
the exercise's `⟺`. (Here `X, Z` are `𝔽₂`-independent but non-commuting; for a *commuting*
counterexample, isolating independence as the missing hypothesis, see
`exists_commuting_gens_sq_one_ne_negOne_with_negOne_mem`.) -/
theorem exists_gens_sq_one_ne_negOne_with_negOne_mem :
    ∃ T : Set (PauliGroup 1),
      (∀ g ∈ T, g ^ 2 = 1 ∧ g ≠ negOne 1) ∧ negOne 1 ∈ Subgroup.closure T := by
  refine ⟨{pauliXOne, pauliZOne}, ?_, negOne_mem_closure_pauliXZ⟩
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact ⟨pauliXOne_sq, pauliXOne_ne_negOne⟩
  · exact ⟨pauliZOne_sq, pauliZOne_ne_negOne⟩

/-- The single-qubit Pauli `-X` as an element of `PauliGroup 1`: phase `2` (`i² = -1`), index
`X = 1`. With `X` it forms a *commuting* Exercise 10.34 counterexample witnessing that commutativity
of the generators is **not** enough to rescue the reverse implication. -/
def negPauliXOne : PauliGroup 1 := ⟨2, ![1]⟩

/-- `(-X)² = I` in `PauliGroup 1`: the index cancels and the phase doubles to `2·2 = 0` in `ZMod 4`
(`mul_self`). -/
theorem negPauliXOne_sq : negPauliXOne ^ 2 = 1 := by decide

/-- `-X ≠ -I` in `PauliGroup 1` (they differ in their Pauli index: `-X` has index `1`, `-I` index
`0`). -/
theorem negPauliXOne_ne_negOne : negPauliXOne ≠ negOne 1 := by decide

/-- **`X·(-X) = -I`** in `PauliGroup 1`: the phases add to `0 + 2 = 2` and the indices cancel
(`X·X = I`, `pauliMulIndex_self`), giving `⟨2, 0⟩ = -I`. This puts `-I` in `⟨X, -X⟩` in a single
product — no anticommutation needed. -/
theorem pauliXOne_mul_negPauliXOne : pauliXOne * negPauliXOne = negOne 1 := by decide

/-- **`(-X)·X = -I`** in `PauliGroup 1`, symmetric to `pauliXOne_mul_negPauliXOne`. -/
theorem negPauliXOne_mul_pauliXOne : negPauliXOne * pauliXOne = negOne 1 := by decide

/-- **`X` and `-X` commute** in `PauliGroup 1`: both products equal `-I`
(`pauliXOne_mul_negPauliXOne`, `negPauliXOne_mul_pauliXOne`). They differ only by the central phase
`i²`, so of course they commute — the point of the commuting counterexample. -/
theorem pauliXOne_mul_negPauliXOne_comm :
    pauliXOne * negPauliXOne = negPauliXOne * pauliXOne :=
  pauliXOne_mul_negPauliXOne.trans negPauliXOne_mul_pauliXOne.symm

/-- **N&C Exercise 10.34, reverse implication is false even for COMMUTING generators.** The
generating set `T = {X, -X}` in `PauliGroup 1` consists of two *commuting* elements (obligation on
the pairwise product below), each squaring to `I` and different from `-I`, yet `X·(-X) = -I ∈
⟨X, -X⟩` (`pauliXOne_mul_negPauliXOne`). Hence the `⟸` direction of the exercise's `⟺` fails **even
under §10.5's standing abelian convention**: commutativity of the generators is not the missing
hypothesis (indeed any subgroup with `-I ∉ S` is automatically abelian,
`mul_comm_of_negOne_notMem`). The genuinely omitted hypothesis is `𝔽₂`-**independence** of the
generators (N&C Proposition 10.3, `IndependentGenerators`): `X` and `-X` have equal check rows
(`r(X) = r(-X)`), so they are dependent. -/
theorem exists_commuting_gens_sq_one_ne_negOne_with_negOne_mem :
    ∃ T : Set (PauliGroup 1),
      (∀ g ∈ T, g ^ 2 = 1 ∧ g ≠ negOne 1) ∧
        (∀ g ∈ T, ∀ h ∈ T, g * h = h * g) ∧
          negOne 1 ∈ Subgroup.closure T := by
  refine ⟨{pauliXOne, negPauliXOne}, ?_, ?_, ?_⟩
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨pauliXOne_sq, pauliXOne_ne_negOne⟩
    · exact ⟨negPauliXOne_sq, negPauliXOne_ne_negOne⟩
  · intro g hg h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg hh
    rcases hg with rfl | rfl <;> rcases hh with rfl | rfl
    · rfl
    · exact pauliXOne_mul_negPauliXOne_comm
    · exact pauliXOne_mul_negPauliXOne_comm.symm
    · rfl
  · have hX : pauliXOne ∈ Subgroup.closure ({pauliXOne, negPauliXOne} : Set (PauliGroup 1)) :=
      Subgroup.subset_closure (by simp)
    have hnX : negPauliXOne ∈ Subgroup.closure ({pauliXOne, negPauliXOne} : Set (PauliGroup 1)) :=
      Subgroup.subset_closure (by simp)
    have hmem := Subgroup.mul_mem _ hX hnX
    rwa [pauliXOne_mul_negPauliXOne] at hmem

/-! ### N&C Exercise 10.34, the intended correct statement: the `⟺` for independent commuting
generators -/

/-- The check row of a power: `checkRowHom (p ^ k) = k • checkRowHom p`. `checkRowHom` is a
homomorphism to the additive group `𝔽₂^{2n}` (`checkRowHom_mul`), so it carries a power to the
`ℕ`-scalar multiple of the row. -/
theorem checkRowHom_pow (p : PauliGroup n) (k : ℕ) :
    checkRowHom (p ^ k) = k • checkRowHom p := by
  induction k with
  | zero => rw [pow_zero, checkRowHom_one, zero_smul]
  | succ k ih => rw [pow_succ, checkRowHom_mul, ih, succ_nsmul]

/-- `-I ≠ I` in the Pauli group: they differ in their phase (`2 ≠ 0` in `ZMod 4`). -/
theorem negOne_ne_one : negOne n ≠ 1 := by
  intro h
  have hp : (negOne n).phase = (1 : PauliGroup n).phase := congrArg PauliGroup.phase h
  simp only [negOne, one_phase] at hp
  exact absurd hp (by decide)

/-- **N&C Exercise 10.34, the intended correct statement (reverse implication).** The exercise's
`⟸` (`gⱼ² = I ∧ gⱼ ≠ -I ⟹ -I ∉ S`) is false as literally stated
(`exists_gens_sq_one_ne_negOne_with_negOne_mem`): it omits `𝔽₂`-**independence** of the generators
(N&C Proposition 10.3) *and* their commutativity, and neither alone suffices. Restoring both
hypotheses makes it true — this is the result the book evidently means. If `g₁, …, g_l` pairwise
commute, each squares to `I`, and their check rows `r(gⱼ)` are `𝔽₂`-linearly independent, then
`-I ∉ ⟨g₁, …, g_l⟩`.

The proof is Proposition 10.3's check-matrix argument, run in reverse. As the generators commute and
are involutions, `⟨g₁, …, g_l⟩` is an elementary abelian `2`-group in which every element is a
subset product `∏ⱼ gⱼ ^ (cⱼ).val`, `c : Fin l → 𝔽₂` (`exists_zmod2_prod_of_mem_closure`). If `-I`
were such a product then, pushing the check-row homomorphism through it (`checkRowHom_pow`,
`checkRowHom_mul`),
`0 = r(-I) = ∑ⱼ cⱼ · r(gⱼ)`; `𝔽₂`-independence forces `c = 0`, so the product is the empty product
`I ≠ -I`. -/
theorem negOne_notMem_closure_of_commute_of_checkRowHom_linearIndependent {l : ℕ}
    {g : Fin l → PauliGroup n} (hcomm : ∀ i j, g i * g j = g j * g i)
    (hsq : ∀ i, g i ^ 2 = 1)
    (hindep : LinearIndependent (ZMod 2) fun i => (g i).checkRowHom) :
    negOne n ∉ Subgroup.closure (Set.range g) := by
  intro hmem
  set S := Subgroup.closure (Set.range g) with hSdef
  -- the closure of pairwise-commuting generators is a commutative group
  have hcs : ∀ x ∈ Set.range g, ∀ y ∈ Set.range g, x * y = y * x := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hcomm i j
  have hic : IsMulCommutative ↥S :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hcs x hx y hy
  -- the generators, lifted into the subgroup, are commuting involutions generating all of `↥S`
  have hmemg : ∀ i, g i ∈ S := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  let g' : Fin l → ↥S := fun i => ⟨g i, hmemg i⟩
  have hg'sq : ∀ i, g' i ^ 2 = 1 := fun i =>
    Subtype.ext (by simpa [SubmonoidClass.coe_pow] using hsq i)
  have hgen : Subgroup.closure (Set.range g') = ⊤ := by
    apply Subgroup.map_injective S.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      show S.subtype '' Set.range g' = Set.range g from by rw [← Set.range_comp]; rfl, ← hSdef]
  -- normal form: `-I` is a subset product of the generators (`↥S` is a `CommGroup` via the
  -- scoped `IsMulCommutative → CommGroup` instance)
  obtain ⟨c, hc⟩ := Subgroup.exists_zmod2_prod_of_mem_closure g' hg'sq
    (hgen ▸ Subgroup.mem_top (⟨negOne n, hmem⟩ : ↥S))
  -- push the check-row homomorphism through the product: `r(-I) = ∑ⱼ (cⱼ).val • r(gⱼ)`
  have hcheck : ∀ s : Finset (Fin l),
      checkRowHom ((∏ i ∈ s, g' i ^ (c i).val : ↥S) : PauliGroup n)
        = ∑ i ∈ s, (c i).val • checkRowHom (g i) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simp only [Finset.prod_empty, Finset.sum_empty, OneMemClass.coe_one, checkRowHom_one]
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, Subgroup.coe_mul, checkRowHom_mul, ih,
          SubmonoidClass.coe_pow, checkRowHom_pow]
  have hval : ((∏ i, g' i ^ (c i).val : ↥S) : PauliGroup n) = negOne n := by rw [← hc]
  have hsum : ∑ i, (c i).val • checkRowHom (g i) = 0 := by
    rw [← hcheck Finset.univ, hval]
    exact checkRowHom_negOne
  -- rewrite the `ℕ`-scalars as `𝔽₂`-scalars and apply linear independence
  have hsum' : ∑ i, c i • checkRowHom (g i) = 0 := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) (c i).val (checkRowHom (g i)),
      ZMod.natCast_rightInverse (c i)]
  have hc0 : ∀ i, c i = 0 := Fintype.linearIndependent_iff.mp hindep c hsum'
  -- with `c = 0` the product is the identity, contradicting `-I = ∏ⱼ gⱼ ^ (cⱼ).val`
  have hone : (⟨negOne n, hmem⟩ : ↥S) = 1 :=
    hc.trans (Finset.prod_eq_one fun i _ => by rw [hc0 i]; simp)
  exact negOne_ne_one (by simpa using Subtype.ext_iff.mp hone)

/-- **N&C Exercise 10.34, the intended correct statement (the `⟺`).** The book's biconditional
`-I ∉ ⟨g₁, …, g_l⟩ ⟺ (gⱼ² = I ∧ gⱼ ≠ -I ∀j)` is false as literally stated; it becomes true once the
two hypotheses N&C's context supplies are restored — the generators **commute** and their check rows
are `𝔽₂`-**independent** (equivalently, by Proposition 10.3, the generators are independent). Under
these standing hypotheses the biconditional holds with exactly the exercise's right-hand side. Its
forward direction is `sq_eq_one_and_ne_negOne_of_negOne_notMem_closure` (needing neither
hypothesis); the reverse is `negOne_notMem_closure_of_commute_of_checkRowHom_linearIndependent`. -/
theorem negOne_notMem_closure_iff_forall_sq_eq_one_and_ne_negOne {l : ℕ}
    {g : Fin l → PauliGroup n} (hcomm : ∀ i j, g i * g j = g j * g i)
    (hindep : LinearIndependent (ZMod 2) fun i => (g i).checkRowHom) :
    negOne n ∉ Subgroup.closure (Set.range g) ↔ ∀ i, g i ^ 2 = 1 ∧ g i ≠ negOne n :=
  ⟨fun hS i => sq_eq_one_and_ne_negOne_of_negOne_notMem_closure hS ⟨i, rfl⟩,
    fun h => negOne_notMem_closure_of_commute_of_checkRowHom_linearIndependent hcomm
      (fun i => (h i).1) hindep⟩

end PauliGroup

end AxQM.Concrete
