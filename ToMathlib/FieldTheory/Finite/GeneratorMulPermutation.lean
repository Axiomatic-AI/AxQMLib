/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init
public import ToMathlib.LinearAlgebra.Matrix.TransvectionCount
public import ToMathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# The cyclic multiplication permutation of a finite field (N&C Problem 7.1)

Nielsen & Chuang, *Quantum Computation and Quantum Information*, Problem 7.1 (p. 346, "Efficient
temporal labeling") asks whether one can build **efficient** circuits — using only `O(poly(n))`
gates — that **cyclically permute all diagonal elements of a `2ⁿ × 2ⁿ` diagonal density matrix
except the `|0ⁿ⟩⟨0ⁿ|` term**. Reading the diagonal populations as the computational-basis labels
`0, 1, …, 2ⁿ − 1`, this asks for a reversible circuit whose induced basis permutation fixes `0` and
cyclically permutes the `2ⁿ − 1` non-zero labels as a single long cycle, with a gate count
polynomial in `n`.

The affirmative answer has a clean algebraic core, formalised here. Identify the `n`-bit register
with the finite field `GF(2ⁿ) = GaloisField 2 n` (a `2ⁿ`-element `𝔽₂`-vector space). Its
multiplicative group `GF(2ⁿ)ˣ` is **cyclic** of order `2ⁿ − 1`; let `g` be a generator. Then **left
multiplication by `g`**, the permutation `x ↦ g · x` (`Units.mulLeft g`), has exactly the three
properties the problem needs:

* it **fixes `0`** (`g · 0 = 0`) — the `|0ⁿ⟩⟨0ⁿ|` term is untouched;
* it is **`𝔽₂`-linear** (`Units.mulLeftLinearEquiv`). This is the certificate of `O(poly(n))`
  efficiency: `GF(2ⁿ)` is an `n`-dimensional `𝔽₂`-vector space (`GaloisField.finrank`, so the
  register is `n` bits/wires), an `𝔽₂`-linear permutation of it is described by an `n × n` `𝔽₂`
  matrix — i.e. a linear feedback shift register on `n` wires — and any invertible `𝔽₂`-linear map
  is realised by `O(n²)` `CNOT` gates (the standard linear-reversible-circuit synthesis, decomposing
  the matrix into transvections). So an `𝔽₂`-linear permutation is automatically an efficient
  circuit, whereas a *generic* permutation of the `2ⁿ` states needs exponentially many gates;
* it **cyclically permutes the `2ⁿ − 1` non-zero elements** — because `g` generates the unit group,
  the orbit of any non-zero `x` is the whole of `GF(2ⁿ)ˣ` (`exists_pow_mulLeft_apply_eq`), so on the
  non-zero elements it is a single `(2ⁿ − 1)`-cycle (`isCycle_mulLeft`).

This is the general-`n` counterpart of the concrete three-qubit partial cyclic permutation of N&C
Exercise 4.27 (`AxQM/Concrete/PartialCyclicPermutation.lean`), which fixes `|000⟩` and
cycles `1 → 2 → ⋯ → 7 → 1`.

## Contents

* `Units.mulLeft_pow_apply` — iterating `Units.mulLeft u` is left multiplication by a power of `u`
  (a general monoid fact).
* `Units.exists_pow_mulLeft_apply_eq` — for a generator `g` of `Kˣ` (`K` a `GroupWithZero`, e.g. a
  field), the permutation `Units.mulLeft g` acts transitively on the non-zero elements: any non-zero
  `x` reaches any non-zero `y` in finitely many steps. This is the "single orbit / cyclic" content.
* `Units.isCycle_mulLeft` — for a non-identity generator, `Units.mulLeft g` is a genuine cycle
  (`Equiv.Perm.IsCycle`).
* `GaloisField.card_units` — `GF(2ⁿ)` has `2ⁿ − 1` non-zero elements, the length of the cycle.
* `GaloisField.exists_linear_isCycle_perm` — the cyclic-permutation half: an `𝔽₂`-linear `L` fixing
  `0` with `L.toEquiv` a single cycle, transitive on the non-zeros.
* `GaloisField.exists_linear_isCycle_perm_transvecCount` — the **full affirmative answer**: the same
  `L` is realised by a circuit of at most `2n²` transvections (`CNOT` gates), i.e.
  `LinearMap.toMatrix b b L = (T.map toMatrix).prod` with `T.length ≤ 2 * n²`; together with
  `transvecCount_isBigO_sq` (`2n² = O(n²)`) this is the efficient (`O(poly(n))`-gate) cyclic
  permutation the problem asks for.

The gate-count bound rests on the generic length-bounded linear-reversible synthesis of
`ToMathlib.LinearAlgebra.Matrix.TransvectionCount` (`Matrix.exists_transvecStruct_prod_length_le` /
`Matrix.exists_transvecStruct_prod_toMatrix_length_le`).

## Scope

The problem is a "can you construct efficient circuits" question. Its formalisable *mathematical*
content is the existence of a permutation with the right cycle structure that is `𝔽₂`-linear **and**
realised by polynomially many `CNOT` gates. Both are delivered as proved propositions here: the
cyclic permutation (fixed point `0`, single-cycle action on the `2ⁿ − 1` non-zero states) and the
`O(n²)` gate-count bound. The bridge from `𝔽₂`-linearity to a concrete gate count is the general
length-bounded linear-reversible synthesis of an invertible `𝔽₂` matrix — an `n × n` matrix is a
product of `O(n²)` transvections, and an `𝔽₂`-transvection with coefficient `1` is a `CNOT`. That
generic step lives in `ToMathlib.LinearAlgebra.Matrix.TransvectionCount`; here it is specialised to
the multiplication permutation. A *generic* permutation of the `2ⁿ` states would need
exponentially many gates, so `𝔽₂`-linearity is precisely the property that makes the circuit
efficient.

These are the statements of N&C Problem 7.1 (`AxQM/NC/Ch7/Problem7_1.lean`).
-/

@[expose] public section

open Equiv

namespace Units

/-- **Iterated left multiplication by a unit is left multiplication by its power.** For a unit `u`
of a monoid `M`, the `k`-fold composite of the permutation `Units.mulLeft u` (`x ↦ u * x`) sends `x`
to `↑(u ^ k) * x`. -/
theorem mulLeft_pow_apply {M : Type*} [Monoid M] (u : Mˣ) (k : ℕ) (x : M) :
    (u.mulLeft ^ k) x = ↑(u ^ k) * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, Units.mulLeft_apply, pow_succ', Units.val_mul,
      mul_assoc]

variable {K : Type*} [GroupWithZero K]

/-- **Left multiplication by a generator acts transitively on the non-zero elements.** If `g`
generates the unit group `Kˣ` of a `GroupWithZero` `K` (e.g. a field; every unit is a power of `g`),
then for any two non-zero `x, y` there is a step count `k` with `(Units.mulLeft g) ^ k`
sending `x` to `y`. Equivalently, the non-zero elements form a single orbit — the
"cyclic permutation of all the non-zero diagonal elements" of N&C Problem 7.1. -/
theorem exists_pow_mulLeft_apply_eq {g : Kˣ} (hg : ∀ y : Kˣ, y ∈ Submonoid.powers g) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) : ∃ k : ℕ, (g.mulLeft ^ k) x = y := by
  obtain ⟨k, hk⟩ :=
    (Submonoid.mem_powers_iff _ _).mp (hg (Units.mk0 (y * x⁻¹) (mul_ne_zero hy (inv_ne_zero hx))))
  refine ⟨k, ?_⟩
  rw [Units.mulLeft_pow_apply, hk, Units.val_mk0, mul_assoc, inv_mul_cancel₀ hx, mul_one]

/-- **Left multiplication by a non-identity generator is a cycle.** If `g` generates `Kˣ` and
`g ≠ 1`, the permutation `Units.mulLeft g` of the `GroupWithZero` `K` is a single cycle
(`Equiv.Perm.IsCycle`): its support is exactly the non-zero elements (it fixes `0`), which it
permutes in one orbit. For `K = GF(2ⁿ)` this is the `(2ⁿ − 1)`-cycle on the non-zero computational
basis states of N&C Problem 7.1 (the requirement `g ≠ 1` excludes only the degenerate
`GF(2) = 𝔽₂` case, where there is a single non-zero element and nothing to permute). -/
theorem isCycle_mulLeft {g : Kˣ} (hg : ∀ y : Kˣ, y ∈ Submonoid.powers g) (hg1 : g ≠ 1) :
    (g.mulLeft : Equiv.Perm K).IsCycle := by
  refine ⟨1, ?_, ?_⟩
  · -- `g.mulLeft 1 = g ≠ 1`.
    simp only [Units.mulLeft_apply, mul_one]
    exact fun h => hg1 (Units.val_eq_one.mp h)
  · intro y hy
    -- `hy : g.mulLeft y ≠ y`; in particular `y ≠ 0`, so transitivity from `1` reaches `y`.
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hy (by simp only [Units.mulLeft_apply, mul_zero])
    obtain ⟨k, hk⟩ := exists_pow_mulLeft_apply_eq hg one_ne_zero hy0
    exact ⟨(k : ℤ), by rw [zpow_natCast]; exact hk⟩

end Units

namespace GaloisField

/-- **`GF(2ⁿ)` has `2ⁿ − 1` non-zero elements.** The number of non-zero diagonal populations that
the cyclic permutation of N&C Problem 7.1 shuffles, i.e. the length of the cycle `isCycle_mulLeft`
produces on `GaloisField 2 n`. -/
theorem card_units (n : ℕ) [NeZero n] :
    Nat.card (GaloisField 2 n)ˣ = 2 ^ n - 1 := by
  have h := Nat.card_eq_card_units_add_one (GaloisField 2 n)
  rw [GaloisField.card 2 n (NeZero.ne n)] at h
  omega

/-- A non-identity generator of the (cyclic) unit group of `GF(2ⁿ)`, for `n ≥ 2`: it generates
`GF(2ⁿ)ˣ` and is not `1` (otherwise every unit equals `1`, forcing `2ⁿ − 1 = 1`, impossible for
`n ≥ 2`). Its left-multiplication is the temporal-labeling permutation of N&C Problem 7.1. -/
theorem exists_generator_ne_one (n : ℕ) (hn : 2 ≤ n) :
    ∃ g : (GaloisField 2 n)ˣ, (∀ y : (GaloisField 2 n)ˣ, y ∈ Submonoid.powers g) ∧ g ≠ 1 := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := (GaloisField 2 n)ˣ)
  refine ⟨g, hg, ?_⟩
  rintro rfl
  have hsub : Subsingleton (GaloisField 2 n)ˣ := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp (hg a)
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (hg b)
    rw [one_pow] at hj hk
    rw [← hj, ← hk]
  have hcard1 : Nat.card (GaloisField 2 n)ˣ = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  have hcard : Nat.card (GaloisField 2 n)ˣ = 2 ^ n - 1 := card_units n
  have h4 : 4 ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

open Matrix Matrix.TransvectionStruct in
/-- **N&C Problem 7.1 (Efficient temporal labeling), affirmative answer with the efficiency bound.**
For `n ≥ 2` there is an `𝔽₂`-linear permutation `L` of `GF(2ⁿ)`, a basis `b` of `GF(2ⁿ)` over `𝔽₂`
(indexed by `Fin n`, since `GF(2ⁿ)` is `n`-dimensional), and a list `T` of transvections with

* `L` **fixes `0`** and **cyclically permutes the `2ⁿ − 1` non-zero elements** (`IsCycle`,
  transitive on the non-zeros) — the temporal-labeling permutation, and
* `L` **is realised by a circuit of at most `2n²` `CNOT` gates**: `LinearMap.toMatrix b b L` equals
  the product of `T`, with `T.length ≤ 2 * n²`. An `𝔽₂`-transvection with coefficient `1` is exactly
  a `CNOT` (add one wire into another), so `T` is an explicit `O(n²)`-gate reversible circuit.

This is the full affirmative answer — the cyclic permutation exists **and** is efficient — with the
efficiency now a proved gate-count bound rather than only the linearity certificate. The
cycle-structure-only corollary is `exists_linear_isCycle_perm`; the asymptotics `2n² = O(n²)` are
`transvecCount_isBigO_sq`. -/
theorem exists_linear_isCycle_perm_transvecCount (n : ℕ) (hn : 2 ≤ n) :
    ∃ (L : GaloisField 2 n ≃ₗ[ZMod 2] GaloisField 2 n)
      (b : Module.Basis (Fin n) (ZMod 2) (GaloisField 2 n))
      (T : List (TransvectionStruct (Fin n) (ZMod 2))),
      L 0 = 0 ∧ Equiv.Perm.IsCycle L.toEquiv ∧
        (∀ x y : GaloisField 2 n, x ≠ 0 → y ≠ 0 → ∃ k : ℕ, (L.toEquiv ^ k) x = y) ∧
        LinearMap.toMatrix b b L.toLinearMap = (T.map toMatrix).prod ∧ T.length ≤ 2 * n ^ 2 := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨g, hg, hg1⟩ := exists_generator_ne_one n hn
  have hfr : Module.finrank (ZMod 2) (GaloisField 2 n) = n := GaloisField.finrank 2 (by omega)
  let b : Module.Basis (Fin n) (ZMod 2) (GaloisField 2 n) :=
    (Module.finBasis (ZMod 2) (GaloisField 2 n)).reindex (finCongr hfr)
  obtain ⟨T, hT, hTlen⟩ :=
    exists_transvecStruct_prod_toMatrix_length_le b
      (Units.mulLeftLinearEquiv (ZMod 2) (GaloisField 2 n) g)
  refine ⟨Units.mulLeftLinearEquiv (ZMod 2) (GaloisField 2 n) g, b, T, map_zero _, ?_, ?_, hT,
    by simpa using hTlen⟩
  · rw [Units.toEquiv_mulLeftLinearEquiv]
    exact Units.isCycle_mulLeft hg hg1
  · intro x y hx hy
    rw [Units.toEquiv_mulLeftLinearEquiv]
    exact Units.exists_pow_mulLeft_apply_eq hg hx hy

/-- **N&C Problem 7.1 (Efficient temporal labeling), the cyclic-permutation half.** For `n ≥ 2`
there is an `𝔽₂`-linear permutation `L` of `GF(2ⁿ)` that **fixes `0`** (the `|0ⁿ⟩⟨0ⁿ|` term is
untouched) and **cyclically permutes the `2ⁿ − 1` non-zero elements** (`L.toEquiv` a single
`IsCycle`, transitive on the non-zeros). This is the projection of the full answer
`exists_linear_isCycle_perm_transvecCount` onto its cycle-structure conjuncts (same witness
`L = Units.mulLeftLinearEquiv … g`), dropping the `O(n²)`-`CNOT` efficiency bound. -/
theorem exists_linear_isCycle_perm (n : ℕ) (hn : 2 ≤ n) :
    ∃ L : GaloisField 2 n ≃ₗ[ZMod 2] GaloisField 2 n,
      L 0 = 0 ∧ Equiv.Perm.IsCycle L.toEquiv ∧
        ∀ x y : GaloisField 2 n, x ≠ 0 → y ≠ 0 → ∃ k : ℕ, (L.toEquiv ^ k) x = y := by
  obtain ⟨L, _, _, h0, hcyc, htrans, _, _⟩ := exists_linear_isCycle_perm_transvecCount n hn
  exact ⟨L, h0, hcyc, htrans⟩

open Asymptotics Filter in
/-- The temporal-labeling gate-count bound `2n²` is `O(n²)`: the cyclic permutation of N&C
Problem 7.1 is realised (`exists_linear_isCycle_perm_transvecCount`) by `O(n²)` `CNOT` gates,
polynomially many in `n` — exactly the `O(poly(n))` efficiency the problem asks for. -/
theorem transvecCount_isBigO_sq :
    (fun n : ℕ => ((2 * n ^ 2 : ℕ) : ℝ)) =O[atTop] fun n => (n : ℝ) ^ 2 := by
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact (isBigO_refl (fun n : ℕ => (n : ℝ) ^ 2) atTop).const_mul_left 2

end GaloisField
