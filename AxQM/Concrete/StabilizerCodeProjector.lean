/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliGroupNegOne
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Concrete: the group-average stabilizer code projector (Nielsen & Chuang, Theorem 10.8 setup)

This file builds the **projector onto the
code space `C(S)`** of a stabilizer code, directly from the abstract stabilizer group `S`, and
proves the algebra Nielsen & Chuang's **Theorem 10.8** consumes. Everything here is stated for the
abstract `n`-qubit Pauli group `PauliGroup n`, its subgroups, and raw matrices
(`Matrix`, `Concrete.pauliString`).

## The stabilizer and its code projector

A **stabilizer** is a subgroup `S ≤ Gₙ` of the `n`-qubit Pauli group with `-I ∉ S` (`negOne n ∉ S`).
This is *exactly* Nielsen & Chuang's notion of a stabilizer group: `-I ∉ S` already forces `S` to be
abelian and every element to square to `I` (`mul_comm_of_negOne_notMem`,
`sq_eq_one_of_negOne_notMem`), so such an `S` is an elementary abelian `2`-group and admits `n - k`
independent commuting generators — the presentation N&C give is a *consequence*, not an extra
hypothesis. Working with the abstract subgroup is therefore faithful, not a weakening.

The projector onto the code space `C(S)` (the joint `+1`-eigenspace `V_S`) is the **group average**

`P_S = |S|⁻¹ · ∑_{s ∈ S} toMat(s)`      (`codeProjector`),

where `toMat` is the faithful matrix representation `iˢ • P_a` (`PauliGroup.toMat`). This is the
standard basis-free form of the code projector (equal to the generator product `∏_l (I + gₗ)/2`
of Proposition 10.5, but not requiring a chosen generating set). Its defining algebra falls out of
one fact — **left/right translation is a bijection of `S`** — with no commutativity or induction:

* `toMat_mul_codeProjector` / `codeProjector_mul_toMat` — **absorption**: `s ∈ S ⟹ toMat(s) · P = P`
  and `P · toMat(s) = P`. (N&C: "`P` is invariant under multiplication by elements of `S`".)
* `codeProjector_isHermitian` — `P† = P` (`S` is closed under inverse and `toMat(s⁻¹) = toMat(s)†`).
* `codeProjector_mul_self` — `P² = P`: `P` is a genuine (self-adjoint idempotent) projector.
* `codeProjector_mulVec_self_iff` — **`P` is the projector onto `C(S)`**: `P ·ᵥ v = v` iff every
  `s ∈ S` fixes `v` (`toMat(s) ·ᵥ v = v`), i.e. the range of `P` is exactly the joint
  `+1`-eigenspace `V_S`.

These are the standing facts of Theorem 10.8's proof; the theorem itself
(`AxQM/Concrete/StabilizerErrorCorrection.lean`) supplies the error operators and the
Knill–Laflamme conclusion.
-/

open Matrix

open scoped BigOperators

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The group-average code projector -/

/-- The **unnormalized stabilizer sum** `Q = ∑_{s ∈ S} toMat(s)` over a stabilizer subgroup `S`. -/
noncomputable def stabilizerSum (S : Subgroup (PauliGroup n)) [Fintype S] :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ∑ s : S, (↑s : PauliGroup n).toMat

/-- `stabilizerSum` unfolded to its defining sum (a `rfl` lemma, for targeted rewriting). -/
theorem stabilizerSum_eq (S : Subgroup (PauliGroup n)) [Fintype S] :
    stabilizerSum S = ∑ s : S, (↑s : PauliGroup n).toMat := rfl

/-- The **group-average code projector** `P_S = |S|⁻¹ · ∑_{s ∈ S} toMat(s)`, the projector onto the
code space `C(S) = V_S` of the stabilizer code with stabilizer `S`. -/
noncomputable def codeProjector (S : Subgroup (PauliGroup n)) [Fintype S] :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  (Fintype.card S : ℂ)⁻¹ • stabilizerSum S

/-- The order `|S|` of a stabilizer subgroup is nonzero as a complex scalar (it contains `I`). -/
theorem card_stabilizer_ne_zero (S : Subgroup (PauliGroup n)) [Fintype S] :
    (Fintype.card S : ℂ) ≠ 0 := by
  have : Nonempty S := ⟨⟨1, S.one_mem⟩⟩
  exact_mod_cast Fintype.card_ne_zero

/-! ### Absorption: `S` fixes the stabilizer sum on both sides -/

/-- **Left absorption**: `s ∈ S ⟹ toMat(s) · Q = Q`. Multiplication by `toMat p` sends the summand
`toMat s` to `toMat (p·s)`, and `s ↦ ⟨p, hp⟩ · s` is a bijection of `S` (`Equiv.mulLeft`), so the
sum is unchanged. -/
theorem toMat_mul_stabilizerSum {S : Subgroup (PauliGroup n)} [Fintype S] {p : PauliGroup n}
    (hp : p ∈ S) : p.toMat * stabilizerSum S = stabilizerSum S := by
  rw [stabilizerSum_eq, Matrix.mul_sum,
    ← Equiv.sum_comp (Equiv.mulLeft (⟨p, hp⟩ : S)) (fun t : S => (↑t : PauliGroup n).toMat)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Equiv.coe_mulLeft, Subgroup.coe_mul, PauliGroup.toMat_mul]

/-- **Right absorption**: `s ∈ S ⟹ Q · toMat(s) = Q`. Symmetric to `toMat_mul_stabilizerSum`, via
the right-translation bijection `s ↦ s · ⟨p, hp⟩` (`Equiv.mulRight`). -/
theorem stabilizerSum_mul_toMat {S : Subgroup (PauliGroup n)} [Fintype S] {p : PauliGroup n}
    (hp : p ∈ S) : stabilizerSum S * p.toMat = stabilizerSum S := by
  rw [stabilizerSum_eq, Matrix.sum_mul,
    ← Equiv.sum_comp (Equiv.mulRight (⟨p, hp⟩ : S)) (fun t : S => (↑t : PauliGroup n).toMat)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Equiv.coe_mulRight, Subgroup.coe_mul, PauliGroup.toMat_mul]

/-! ### `Q` is Hermitian and idempotent up to scale -/

/-- **`Q` is Hermitian**: `Q† = Q`. Conjugate-transposing each summand gives `(toMat s)† =
toMat (s⁻¹)` (`PauliGroup.toMat_inv`), and `s ↦ s⁻¹` is a bijection of `S`. -/
theorem stabilizerSum_conjTranspose {S : Subgroup (PauliGroup n)} [Fintype S] :
    (stabilizerSum S)ᴴ = stabilizerSum S := by
  rw [stabilizerSum_eq, conjTranspose_sum,
    ← Equiv.sum_comp (Equiv.inv S) (fun t : S => (↑t : PauliGroup n).toMat)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Equiv.inv_apply, Subgroup.coe_inv, PauliGroup.toMat_inv]

/-- **`Q · Q = |S| · Q`**: distributing the left factor, each `toMat s · Q = Q`
(`toMat_mul_stabilizerSum`), so the product is `∑_{s ∈ S} Q = |S| · Q`. -/
theorem stabilizerSum_mul_self {S : Subgroup (PauliGroup n)} [Fintype S] :
    stabilizerSum S * stabilizerSum S = (Fintype.card S : ℂ) • stabilizerSum S := by
  nth_rewrite 1 [stabilizerSum_eq]
  rw [Matrix.sum_mul, Finset.sum_congr rfl (fun (s : S) _ => toMat_mul_stabilizerSum s.2),
    Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

/-! ### The code projector is a self-adjoint idempotent onto `C(S)` -/

/-- **The code projector is self-adjoint**: `P† = P`. Immediate from `stabilizerSum_conjTranspose`
(the scalar `|S|⁻¹` is real). -/
theorem codeProjector_isHermitian {S : Subgroup (PauliGroup n)} [Fintype S] :
    (codeProjector S).IsHermitian := by
  change (codeProjector S)ᴴ = codeProjector S
  rw [codeProjector, conjTranspose_smul, stabilizerSum_conjTranspose, star_inv₀, star_natCast]

/-- **The code projector is idempotent**: `P · P = P`. From `Q · Q = |S| · Q`
(`stabilizerSum_mul_self`) and `|S|⁻¹ · |S|⁻¹ · |S| = |S|⁻¹`. -/
theorem codeProjector_mul_self {S : Subgroup (PauliGroup n)} [Fintype S] :
    codeProjector S * codeProjector S = codeProjector S := by
  rw [codeProjector, smul_mul_smul_comm, stabilizerSum_mul_self, smul_smul, mul_assoc,
    inv_mul_cancel₀ (card_stabilizer_ne_zero S), mul_one]

/-- **Left absorption for the projector**: `s ∈ S ⟹ toMat(s) · P = P`. -/
theorem toMat_mul_codeProjector {S : Subgroup (PauliGroup n)} [Fintype S] {p : PauliGroup n}
    (hp : p ∈ S) : p.toMat * codeProjector S = codeProjector S := by
  rw [codeProjector, mul_smul_comm, toMat_mul_stabilizerSum hp]

/-- **Right absorption for the projector**: `s ∈ S ⟹ P · toMat(s) = P`. -/
theorem codeProjector_mul_toMat {S : Subgroup (PauliGroup n)} [Fintype S] {p : PauliGroup n}
    (hp : p ∈ S) : codeProjector S * p.toMat = codeProjector S := by
  rw [codeProjector, smul_mul_assoc, stabilizerSum_mul_toMat hp]

/-- **The code projector is the projector onto the code space `C(S)`.** A vector `v` is fixed by
`P` iff it is a joint `+1`-eigenvector of every element of `S`: `P ·ᵥ v = v ↔ ∀ s ∈ S,
toMat(s) ·ᵥ v = v`. Thus `range P = V_S`, the code space. The forward direction reads
`toMat(s) ·ᵥ v = toMat(s) ·ᵥ (P ·ᵥ v) = (toMat(s) · P) ·ᵥ v = P ·ᵥ v = v` (left absorption); the
backward direction computes `Q ·ᵥ v = ∑_{s ∈ S} v = |S| • v`, so
`P ·ᵥ v = |S|⁻¹ • (|S| • v) = v`. -/
theorem codeProjector_mulVec_self_iff {S : Subgroup (PauliGroup n)} [Fintype S]
    (v : (Fin n → Fin 2) → ℂ) :
    (codeProjector S).mulVec v = v ↔ ∀ p ∈ S, p.toMat.mulVec v = v := by
  constructor
  · intro hv p hp
    have h1 : (p.toMat * codeProjector S).mulVec v = v := by
      rw [toMat_mul_codeProjector hp, hv]
    rwa [← Matrix.mulVec_mulVec, hv] at h1
  · intro hv
    have hQ : (stabilizerSum S).mulVec v = (Fintype.card S : ℂ) • v := by
      rw [stabilizerSum_eq, Matrix.sum_mulVec,
        Finset.sum_congr rfl (fun (s : S) _ => hv (↑s) s.2),
        Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [codeProjector, Matrix.smul_mulVec, hQ, smul_smul,
      inv_mul_cancel₀ (card_stabilizer_ne_zero S), one_smul]

end AxQM.Concrete
