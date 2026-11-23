/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ModularMultiplication
import Mathlib.Logic.Equiv.Prod

/-!
# Concrete: the order-finding state via the adder `V` vs. the powers `Uʲ`

Nielsen & Chuang, Exercise 5.14 (§5.3.1, p. 227). The quantum state produced in the order-finding
algorithm *before* the inverse Fourier transform is (Eq. 5.46)

`|ψ⟩ = ∑ⱼ |j⟩ Uʲ|1⟩ = ∑ⱼ |j⟩ |xʲ mod N⟩`,

where `U|y⟩ = |xy mod N⟩` (Eq. 5.36, Exercise 5.12) and the second register starts in `|1⟩`. The
exercise asks one to show that the **same state** is obtained by replacing the powers `Uʲ` with a
single *different* unitary transform `V` acting on the joint register,

`V|j⟩|k⟩ = |j⟩|k + xʲ mod N⟩`  (Eq. 5.47),

started with the second register in `|0⟩` (so `V|j⟩|0⟩ = |j⟩|xʲ mod N⟩ = |j⟩Uʲ|1⟩`). It also asks
one to construct `V` with `O(L³)` gates.

## Mathematical content and grounding

The heart of the exercise is a pair of basis-ket identities on the register `{0, …, d - 1}`
(`d = 2ᴸ`, so `N ≤ d`), both of which reduce, term by term, to

`Uʲ|1⟩ = |xʲ mod N⟩  and  V|j⟩|0⟩ = |j⟩|xʲ mod N⟩`.

Here `U` is the permutation `modMulPerm` of `ModularMultiplication.lean` (Exercise 5.12), so `Uʲ|1⟩`
is the forward image `|modMulPerm ʲ 1⟩`, whose value is `xʲ mod N` (`modMulPerm_pow_apply_one`); and
`V` is the "controlled modular adder" permutation `modExpAddPerm` of the joint register, which for
each control value `j` translates the target by `xʲ mod N` modulo `N`. Both operators are
permutation matrices, hence unitary — this is *why* `V` is "a different unitary transform" — and the
two superpositions coincide because their `j`-th basis kets agree.

This is a concrete number-theoretic construction — the states are amplitude vectors and the
operators are permutation matrices — like Exercise 5.12
(`AxQM/Concrete/ModularMultiplication.lean`). The statement of Exercise 5.14 is in
`AxQM/NC/Ch5/Exercise5_14.lean`.

The `O(L³)`-gate construction of `V` (Box 5.2, *modular exponentiation*) is a gate-*complexity*
claim about a reversible arithmetic circuit; N&C give no explicit circuit for `V`, and the library
has no cost model in which "`O(L³)` gates" is a proposition, so — like the other asymptotic
gate-count sub-claims of the book — that half is not formalised. What is formalised is the
state-equivalence (`orderFindingStateV_eq_orderFindingStateU`) together with the unitarity of `V`
(`modExpAddMatrix_mem_unitaryGroup`).

## Contents

* `modMulPerm_pow_apply_of_lt` / `modMulPerm_pow_apply_one` — `Uʲ` on residues acts as
  `y ↦ xʲ y mod N`; in particular `Uʲ|1⟩ = |xʲ mod N⟩`.
* `modShiftIndex` / `modShiftPerm` — the target-register adder `k ↦ (k + c) mod N` (identity for
  `k ≥ N`) and, as a permutation of `Fin d`, the "add the constant `c` modulo `N`" gate.
* `modExpAddPerm` — the joint operator `V` (`V(j, k) = (j, k + xʲ mod N)`), with
  `modExpAddPerm_apply_zero_eq_pow`: `V|j⟩|0⟩ = |j⟩Uʲ|1⟩`.
* `modExpAddMatrix` / `modExpAddMatrix_mem_unitaryGroup` — `V` as a (unitary) permutation matrix.
* `orderFindingStateU` / `orderFindingStateV` and `orderFindingStateV_eq_orderFindingStateU` —
  **Exercise 5.14:** the `V`-from-`|0⟩` state equals the `Uʲ`-from-`|1⟩` state.
-/

open scoped Matrix

namespace AxQM.Concrete

/-- The permutation-matrix representation `Matrix.permMatrixHom σ` (`= permMatrix σ⁻¹`) acts on the
computational basis by the **forward** permutation: `V|q⟩ = |σ q⟩`. (The bare `permMatrix σ` uses
the opposite convention `permMatrix σ · eₖ = e_{σ⁻¹ k}`, so `permMatrixHom` is the faithful
"operator of `σ`" whose `mulVec` matches `σ` itself.) Stated over an arbitrary `CommRing`, matching
the generality of `permMatrix_mem_unitaryGroup`. -/
theorem permMatrixHom_mulVec_single_one {n : Type*} [Fintype n] [DecidableEq n] {R : Type*}
    [CommRing R] (σ : Equiv.Perm n) (q : n) :
    (Matrix.permMatrixHom σ : Matrix n n R).mulVec (Pi.single q 1) = Pi.single (σ q) 1 := by
  rw [Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]
  funext p
  rw [Function.comp_apply, Pi.single_apply, Pi.single_apply]
  simp only [Equiv.Perm.inv_def, Equiv.symm_apply_eq]

/-- `Uʲ` on a residue `y < N` acts as `y ↦ xʲ y mod N`: the `j`-fold iterate of the order-finding
permutation `modMulPerm x` (Exercise 5.12). Proved by induction on `j`, each step feeding the
residue `xʲ y mod N < N` back through `modMulPerm_apply_of_lt` and folding
`x · (xʲ y mod N) ≡ x^{j+1} y  (mod N)`. -/
theorem modMulPerm_pow_apply_of_lt (x : ℕ) {N d : ℕ} (hx : x.Coprime N) (hNd : N ≤ d) {y : Fin d}
    (hy : (y : ℕ) < N) (j : ℕ) :
    (((modMulPerm x hx hNd) ^ j) y : ℕ) = x ^ j * (y : ℕ) % N := by
  have hN : 0 < N := (Nat.zero_le _).trans_lt hy
  induction j with
  | zero =>
    simp only [pow_zero, Equiv.Perm.one_apply, one_mul]
    exact (Nat.mod_eq_of_lt hy).symm
  | succ j ih =>
    have hz : (((modMulPerm x hx hNd) ^ j) y : ℕ) < N := ih ▸ Nat.mod_lt _ hN
    rw [pow_succ', Equiv.Perm.mul_apply, modMulPerm_apply_of_lt x hx hNd hz, ih]
    conv_rhs => rw [pow_succ', mul_assoc]
    exact Nat.ModEq.mul_left x (Nat.mod_modEq _ _)

/-- **Exercise 5.14, key identity for the `Uʲ` register.** `Uʲ|1⟩ = |xʲ mod N⟩`: the forward image
of `|1⟩` under `j` powers of the order-finding operator has register value `xʲ mod N`. Needs
`1 < N` so that `1` is a genuine residue. -/
theorem modMulPerm_pow_apply_one (x : ℕ) {N d : ℕ} [NeZero d] (hx : x.Coprime N) (hNd : N ≤ d)
    (hN : 1 < N) (j : ℕ) : (((modMulPerm x hx hNd) ^ j) (1 : Fin d) : ℕ) = x ^ j % N := by
  have hd : 1 < d := hN.trans_le hNd
  have h1 : ((1 : Fin d) : ℕ) = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt hd
  rw [modMulPerm_pow_apply_of_lt x hx hNd (by rw [h1]; exact hN) j, h1, mul_one]

/-- The register-index map of the target-register adder `k ↦ (k + c) mod N` (Eq. 5.47's second
register): on residues `k < N` it is `k ↦ (k + c) mod N`, and it fixes `k ≥ N` (N&C's register
convention, matching `U`). -/
def modShiftIndex (c : ℕ) {N d : ℕ} (hNd : N ≤ d) (k : Fin d) : Fin d :=
  if h : (k : ℕ) < N then
    ⟨((k : ℕ) + c) % N, (Nat.mod_lt _ ((Nat.zero_le _).trans_lt h)).trans_le hNd⟩
  else k

/-- On a residue `k < N`, the adder index map is `k ↦ (k + c) mod N`. -/
theorem modShiftIndex_apply_of_lt (c : ℕ) {N d : ℕ} (hNd : N ≤ d) {k : Fin d} (h : (k : ℕ) < N) :
    (modShiftIndex c hNd k : ℕ) = ((k : ℕ) + c) % N := by simp only [modShiftIndex, dite_eq_left h]

/-- On `k ≥ N` the adder index map is the identity. -/
theorem modShiftIndex_apply_of_le (c : ℕ) {N d : ℕ} (hNd : N ≤ d) {k : Fin d} (h : N ≤ (k : ℕ)) :
    modShiftIndex c hNd k = k := by simp only [modShiftIndex, dite_eq_right (not_lt.mpr h)]

/-- The adder index map is injective. Via the shared `injective_of_residue` skeleton
(`ModularMultiplication.lean`), the only case-specific step is residue injectivity: adding the
constant `c` modulo `N` is cancellable (`Nat.ModEq.add_right_cancel'`). (No coprimality needed — a
translation is a bijection.) -/
theorem modShiftIndex_injective (c : ℕ) {N d : ℕ} (hNd : N ≤ d) :
    Function.Injective (modShiftIndex c hNd) := by
  refine injective_of_residue N (fun k hk => ?_) (fun k hk => modShiftIndex_apply_of_le c hNd hk)
    (fun a b ha hb hab => ?_)
  · rw [modShiftIndex_apply_of_lt c hNd hk]
    exact Nat.mod_lt _ ((Nat.zero_le _).trans_lt hk)
  · have e : ((a : ℕ) + c) % N = ((b : ℕ) + c) % N := by
      rw [← modShiftIndex_apply_of_lt c hNd ha, ← modShiftIndex_apply_of_lt c hNd hb, hab]
    refine Fin.ext ?_
    have : (a : ℕ) ≡ (b : ℕ) [MOD N] := Nat.ModEq.add_right_cancel' c e
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- The target-register adder "add the constant `c` modulo `N`" as a permutation of the register
`Fin d`, fixing `k ≥ N`. It is a permutation because translation by `c` in `ℤ/N` is a bijection. -/
noncomputable def modShiftPerm (c : ℕ) {N d : ℕ} (hNd : N ≤ d) : Equiv.Perm (Fin d) :=
  Equiv.ofBijective (modShiftIndex c hNd)
    (Finite.injective_iff_bijective.mp (modShiftIndex_injective c hNd))

@[simp] theorem modShiftPerm_apply (c : ℕ) {N d : ℕ} (hNd : N ≤ d) (k : Fin d) :
    modShiftPerm c hNd k = modShiftIndex c hNd k :=
  Equiv.ofBijective_apply _ _ k

/-- At `k = 0` the adder outputs `c mod N`: `V`'s second register maps `|0⟩ ↦ |c mod N⟩`. -/
theorem modShiftPerm_apply_zero (c : ℕ) {N d : ℕ} [NeZero d] (hNd : N ≤ d) (hN : 0 < N) :
    ((modShiftPerm c hNd) (0 : Fin d) : ℕ) = c % N := by
  have h0 : ((0 : Fin d) : ℕ) = 0 := rfl
  rw [modShiftPerm_apply, modShiftIndex_apply_of_lt c hNd (by rw [h0]; exact hN), h0, Nat.zero_add]

/-- **Exercise 5.14's transform `V`** (Eq. 5.47) as a permutation of the joint register
`Fin m × Fin d`: it fixes the control register `j` and applies to the target register the adder
`modShiftPerm (xʲ mod N)`, i.e. `V(j, k) = (j, k + xʲ mod N)`. Being a permutation is exactly what
makes `V` "a different unitary transform". -/
noncomputable def modExpAddPerm (x : ℕ) {N d : ℕ} (hNd : N ≤ d) (m : ℕ) :
    Equiv.Perm (Fin m × Fin d) :=
  Equiv.prodCongrRight (fun j : Fin m => modShiftPerm (x ^ (j : ℕ) % N) hNd)

/-- `V(j, k) = (j, k + xʲ mod N)` (Eq. 5.47): the joint operator fixes the control and adds
`xʲ mod N` to the target. -/
theorem modExpAddPerm_apply (x : ℕ) {N d : ℕ} (hNd : N ≤ d) (m : ℕ) (j : Fin m) (k : Fin d) :
    modExpAddPerm x hNd m (j, k) = (j, modShiftPerm (x ^ (j : ℕ) % N) hNd k) :=
  Equiv.prodCongrRight_apply _ j k

/-- **Exercise 5.14, the state-equivalence crux.** `V|j⟩|0⟩ = |j⟩Uʲ|1⟩`: started with the target in
`|0⟩`, `V` produces exactly the `j`-th basis ket of the `Uʲ`-superposition, because both target
registers hold `xʲ mod N` (`modShiftPerm_apply_zero` and `modMulPerm_pow_apply_one`). -/
theorem modExpAddPerm_apply_zero_eq_pow (x : ℕ) {N d : ℕ} [NeZero d] (hx : x.Coprime N)
    (hNd : N ≤ d) (hN : 1 < N) (m : ℕ) (j : Fin m) :
    modExpAddPerm x hNd m (j, (0 : Fin d))
      = (j, (modMulPerm x hx hNd ^ (j : ℕ)) (1 : Fin d)) := by
  rw [modExpAddPerm_apply]
  refine Prod.ext rfl (Fin.ext ?_)
  rw [modShiftPerm_apply_zero _ hNd (by omega), modMulPerm_pow_apply_one x hx hNd hN, Nat.mod_mod]

/-- **Exercise 5.14's transform `V` as a (unitary) permutation matrix.** `Matrix.permMatrixHom`
represents `V` with the forward action `V|q⟩ = |modExpAddPerm q⟩` (see
`permMatrixHom_mulVec_single_one`). -/
noncomputable def modExpAddMatrix (x : ℕ) {N d : ℕ} (hNd : N ≤ d) (m : ℕ) :
    Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ :=
  Matrix.permMatrixHom (modExpAddPerm x hNd m)

/-- **Exercise 5.14: `V` is unitary.** As a permutation matrix, `V ∈ unitaryGroup`
(`Matrix.permMatrix_mem_unitaryGroup`, via `permMatrixHom σ = permMatrix σ⁻¹`). -/
theorem modExpAddMatrix_mem_unitaryGroup (x : ℕ) {N d : ℕ} (hNd : N ≤ d) (m : ℕ) :
    modExpAddMatrix x hNd m ∈ Matrix.unitaryGroup (Fin m × Fin d) ℂ := by
  rw [modExpAddMatrix, Matrix.permMatrixHom_apply]
  exact Matrix.permMatrix_mem_unitaryGroup _

/-- The order-finding state **from the powers `Uʲ`** (Eq. 5.46), `∑ⱼ |j⟩ Uʲ|1⟩`, with the target
register started in `|1⟩`. Its `j`-th joint basis ket is `|j⟩|Uʲ·1⟩`; by `modMulPerm_pow_apply_one`
the target holds `xʲ mod N`, so this is N&C's `∑ⱼ |j⟩|xʲ mod N⟩`. -/
noncomputable def orderFindingStateU (x : ℕ) {N d : ℕ} [NeZero d] (hx : x.Coprime N) (hNd : N ≤ d)
    (m : ℕ) : (Fin m × Fin d) → ℂ :=
  ∑ j : Fin m, Pi.single (j, (modMulPerm x hx hNd ^ (j : ℕ)) (1 : Fin d)) 1

/-- The order-finding state **from the single transform `V`**: apply `V` to the input
`∑ⱼ |j⟩|0⟩` (target register started in `|0⟩`), i.e. `V ·(∑ⱼ |j⟩|0⟩)`. -/
noncomputable def orderFindingStateV (x : ℕ) {N d : ℕ} [NeZero d] (hNd : N ≤ d) (m : ℕ) :
    (Fin m × Fin d) → ℂ :=
  (modExpAddMatrix x hNd m).mulVec (∑ j : Fin m, Pi.single (j, (0 : Fin d)) 1)

/-- **Nielsen & Chuang, Exercise 5.14.** The order-finding state obtained by applying the single
transform `V` to `∑ⱼ |j⟩|0⟩` equals the state obtained from the powers `Uʲ` on `∑ⱼ |j⟩|1⟩`:

`V ·(∑ⱼ |j⟩|0⟩) = ∑ⱼ |j⟩ Uʲ|1⟩`.

Termwise, `V` distributes over the sum (`Matrix.mulVec_sum`), sends each `|j⟩|0⟩` to `|V(j,0)⟩`
(`permMatrixHom_mulVec_single_one`), and `V(j,0) = (j, Uʲ·1)`
(`modExpAddPerm_apply_zero_eq_pow`). -/
theorem orderFindingStateV_eq_orderFindingStateU (x : ℕ) {N d : ℕ} [NeZero d] (hx : x.Coprime N)
    (hNd : N ≤ d) (hN : 1 < N) (m : ℕ) :
    orderFindingStateV x hNd m = orderFindingStateU x hx hNd m := by
  simp only [orderFindingStateV, orderFindingStateU, modExpAddMatrix]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [permMatrixHom_mulVec_single_one, modExpAddPerm_apply_zero_eq_pow x hx hNd hN m j]

end AxQM.Concrete
