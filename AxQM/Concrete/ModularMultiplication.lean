/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.LinearAlgebra.Matrix.PermutationUnitary
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card

/-!
# Concrete: the modular-multiplication operator `U|y⟩ = |xy mod N⟩` is unitary

Nielsen & Chuang, Exercise 5.12 (§5.3.1, p. 227): the quantum order-finding algorithm applies phase
estimation to the operator

`U|y⟩ = |xy (mod N)⟩`  (Eq. 5.36),

acting on the `L`-qubit computational basis `y ∈ {0,1}^L`, i.e. on the register indices
`{0, 1, …, 2ᴸ - 1}`. N&C use the convention that when `N ≤ y ≤ 2ᴸ - 1` the value `xy (mod N)` is
just `y` again, so `U` acts non-trivially only on `0 ≤ y ≤ N - 1`. *Exercise 5.12* asks one to show
that `U` is unitary; the hint is that `x` is co-prime to `N` and therefore has an inverse modulo
`N`, so `y ↦ xy (mod N)` is invertible.

The mathematical content is exactly this: because `x` is a unit modulo `N`, the map `y ↦ xy (mod N)`
is a **bijection** of the residues `{0, …, N - 1}`, and — extended by the identity on
`{N, …, d - 1}` — a **permutation** of the register `{0, …, d - 1}` (any `d ≥ N`; the N&C case is
`d = 2ᴸ` with `L = ⌈log N⌉`, so `N ≤ 2ᴸ`). The operator `U` is the permutation matrix of that
permutation, and a permutation matrix is always unitary.

This is a concrete instantiation of the number-theoretic order-finding construction. The only
genuinely general fact used, that a permutation matrix over any commutative star ring is unitary
(`Matrix.permMatrix_mem_unitaryGroup`), is in
`ToMathlib/LinearAlgebra/Matrix/PermutationUnitary.lean` and is imported here.

## Contents

* `modMulIndex` / `modMulPerm` — the register-index map `y ↦ xy (mod N)` (identity for `y ≥ N`) and,
  once `x` is co-prime to `N`, the permutation of `Fin d` it defines (`modMulPerm_apply_of_lt` /
  `modMulPerm_apply_of_le` pin down its action).
* `modMulMatrix` — the operator `U` as the permutation matrix of `modMulPerm` over `ℂ`.
* `modMulMatrix_mem_unitaryGroup` — **Exercise 5.12**: `U` is unitary; and
  `modMulMatrix_two_pow_mem_unitaryGroup` specialises this to N&C's `d = 2ᴸ` register.
-/

open scoped Matrix

namespace AxQM.Concrete

/-- The register-index map underlying N&C's order-finding operator `U|y⟩ = |xy (mod N)⟩`
(Eq. 5.36): on residues `y < N` it is `y ↦ xy (mod N)`, and it fixes `y ≥ N`, matching N&C's
convention on the register `{0, …, d - 1}` (`d = 2ᴸ`). Well-defined for any `N ≤ d`, since
`xy (mod N) < N ≤ d`. -/
def modMulIndex (x : ℕ) {N d : ℕ} (hNd : N ≤ d) (y : Fin d) : Fin d :=
  if h : (y : ℕ) < N then
    ⟨x * (y : ℕ) % N, (Nat.mod_lt _ ((Nat.zero_le _).trans_lt h)).trans_le hNd⟩
  else y

/-- On a residue `y < N`, the index map is `y ↦ xy (mod N)`. -/
theorem modMulIndex_apply_of_lt (x : ℕ) {N d : ℕ} (hNd : N ≤ d) {y : Fin d} (h : (y : ℕ) < N) :
    (modMulIndex x hNd y : ℕ) = x * (y : ℕ) % N := by
  simp only [modMulIndex, dite_eq_left h]

/-- On `y ≥ N` the index map is the identity (N&C's convention). -/
theorem modMulIndex_apply_of_le (x : ℕ) {N d : ℕ} (hNd : N ≤ d) {y : Fin d} (h : N ≤ (y : ℕ)) :
    modMulIndex x hNd y = y := by
  simp only [modMulIndex, dite_eq_right (not_lt.mpr h)]

/-- **The identity-extended residue-bijection pattern.** A self-map `f` of the register `Fin d`
that (i) sends every residue `k < N` into `< N`, (ii) fixes every `k ≥ N`, and (iii) is injective on
the residues is injective on all of `Fin d`: the residue range `< N` and the fixed range `≥ N` are
disjoint, so no residue can collide with a fixed point. This is the shared skeleton behind the
order-finding index maps `modMulIndex` (Exercise 5.12) and `modShiftIndex` (Exercise 5.14): each
supplies only its own residue-injectivity (iii), the cross-range argument being factored here. -/
theorem injective_of_residue (N : ℕ) {d : ℕ} {f : Fin d → Fin d}
    (hlt : ∀ k : Fin d, (k : ℕ) < N → (f k : ℕ) < N)
    (hfix : ∀ k : Fin d, N ≤ (k : ℕ) → f k = k)
    (hres : ∀ a b : Fin d, (a : ℕ) < N → (b : ℕ) < N → f a = f b → a = b) :
    Function.Injective f := by
  -- a residue `< N` and a fixed point `≥ N` land in disjoint ranges, so cannot be identified
  have mixed : ∀ u v : Fin d, (u : ℕ) < N → ¬ (v : ℕ) < N → f u ≠ f v := by
    intro u v hu hv h
    have h1 : (f u : ℕ) < N := hlt u hu
    rw [hfix v (not_lt.mp hv)] at h
    rw [h] at h1
    exact absurd h1 hv
  intro a b hab
  by_cases ha : (a : ℕ) < N <;> by_cases hb : (b : ℕ) < N
  · exact hres a b ha hb hab
  · exact absurd hab (mixed a b ha hb)
  · exact absurd hab.symm (mixed b a hb ha)
  · rw [hfix a (not_lt.mp ha), hfix b (not_lt.mp hb)] at hab; exact hab

/-- The heart of Exercise 5.12: when `x` is co-prime to `N`, the index map is injective. Via the
shared `injective_of_residue` skeleton, the only case-specific step is residue injectivity —
cancellation of the coprime factor `x` modulo `N` (`Nat.ModEq.cancel_left_of_coprime`). -/
theorem modMulIndex_injective (x : ℕ) {N d : ℕ} (hx : x.Coprime N) (hNd : N ≤ d) :
    Function.Injective (modMulIndex x hNd) := by
  refine injective_of_residue N (fun k hk => ?_) (fun k hk => modMulIndex_apply_of_le x hNd hk)
    (fun a b ha hb hab => ?_)
  · rw [modMulIndex_apply_of_lt x hNd hk]
    exact Nat.mod_lt _ ((Nat.zero_le _).trans_lt hk)
  · -- both residues: cancel the coprime factor `x` mod `N`
    have e : x * (a : ℕ) % N = x * (b : ℕ) % N := by
      rw [← modMulIndex_apply_of_lt x hNd ha, ← modMulIndex_apply_of_lt x hNd hb, hab]
    refine Fin.ext ?_
    rw [← Nat.mod_eq_of_lt ha, ← Nat.mod_eq_of_lt hb]
    exact Nat.ModEq.cancel_left_of_coprime hx.symm e

/-- N&C's order-finding operator `U|y⟩ = |xy (mod N)⟩` as a permutation of the register basis
`{0, …, d - 1}` (`d = 2ᴸ`). It is a permutation precisely because `x` is co-prime to `N`, so
multiplication by `x` is invertible modulo `N` (Exercise 5.12's hint); injectivity of a self-map of
the finite register then upgrades to bijectivity. -/
noncomputable def modMulPerm (x : ℕ) {N d : ℕ} (hx : x.Coprime N) (hNd : N ≤ d) :
    Equiv.Perm (Fin d) :=
  Equiv.ofBijective (modMulIndex x hNd)
    (Finite.injective_iff_bijective.mp (modMulIndex_injective x hx hNd))

@[simp]
theorem modMulPerm_apply (x : ℕ) {N d : ℕ} (hx : x.Coprime N) (hNd : N ≤ d) (y : Fin d) :
    modMulPerm x hx hNd y = modMulIndex x hNd y :=
  Equiv.ofBijective_apply _ _ y

/-- The permutation acts as `y ↦ xy (mod N)` on residues `y < N`. -/
theorem modMulPerm_apply_of_lt (x : ℕ) {N d : ℕ} (hx : x.Coprime N) (hNd : N ≤ d) {y : Fin d}
    (h : (y : ℕ) < N) : ((modMulPerm x hx hNd) y : ℕ) = x * (y : ℕ) % N := by
  rw [modMulPerm_apply]; exact modMulIndex_apply_of_lt x hNd h

/-- The permutation fixes `y ≥ N` (N&C's convention). -/
theorem modMulPerm_apply_of_le (x : ℕ) {N d : ℕ} (hx : x.Coprime N) (hNd : N ≤ d) {y : Fin d}
    (h : N ≤ (y : ℕ)) : (modMulPerm x hx hNd) y = y := by
  rw [modMulPerm_apply]; exact modMulIndex_apply_of_le x hNd h

/-- N&C's order-finding operator `U` (Eq. 5.36) as the permutation matrix of `modMulPerm` over `ℂ`,
on the register `{0, …, d - 1}`. -/
noncomputable def modMulMatrix (x : ℕ) {N d : ℕ} (hx : x.Coprime N) (hNd : N ≤ d) :
    Matrix (Fin d) (Fin d) ℂ := (modMulPerm x hx hNd).permMatrix ℂ

/-- `modMulMatrix` unfolds to the permutation matrix of `modMulPerm` (the `def` equation, exposed
as a named lemma so that users, e.g. Exercises 5.13/5.14, can rewrite `U` to a `permMatrix`
and reuse its API). Completes the `modMulMatrix` API, alongside `modMulPerm_apply_of_lt` and
`modMulPerm_apply_of_le`. -/
theorem modMulMatrix_eq_permMatrix (x : ℕ) {N d : ℕ} (hx : x.Coprime N) (hNd : N ≤ d) :
    modMulMatrix x hx hNd = (modMulPerm x hx hNd).permMatrix ℂ := rfl

/-- **Nielsen & Chuang, Exercise 5.12.** The order-finding operator `U|y⟩ = |xy (mod N)⟩` is
unitary. This holds for any register dimension `d ≥ N`, because `x` co-prime to `N` makes
`y ↦ xy (mod N)` a permutation of the register (`modMulPerm`) and every permutation matrix is
unitary (`Matrix.permMatrix_mem_unitaryGroup`). -/
theorem modMulMatrix_mem_unitaryGroup (x : ℕ) {N d : ℕ} (hx : x.Coprime N) (hNd : N ≤ d) :
    modMulMatrix x hx hNd ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [modMulMatrix_eq_permMatrix]
  exact Matrix.permMatrix_mem_unitaryGroup _

/-- Exercise 5.12 on N&C's own register: with `L = ⌈log N⌉` qubits the basis is
`{0, …, 2ᴸ - 1}` (so `N ≤ 2ᴸ`), and there the order-finding operator `U` is unitary. -/
theorem modMulMatrix_two_pow_mem_unitaryGroup (x N L : ℕ) (hx : x.Coprime N) (hN : N ≤ 2 ^ L) :
    modMulMatrix x hx hN ∈ Matrix.unitaryGroup (Fin (2 ^ L)) ℂ :=
  modMulMatrix_mem_unitaryGroup x hx hN

end AxQM.Concrete
