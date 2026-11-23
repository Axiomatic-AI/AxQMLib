/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.ControlledSingleQubit
import AxQM.Concrete.SingleQubitRotationUniversality

/-!
# Concrete: the (uncontrolled) single-qubit gate on a wire (N&C §4.3/§4.5)

(Nielsen & Chuang §4.3, §4.5.2, p. 182–193 — the `n`-qubit lift.)

The §4.5 decomposition (`Concrete/UnitaryControlledProduct.lean`) writes any register unitary as a
product of *controlled* single-qubit gates (`ctrlSingleQubit`). The next stage of Nielsen & Chuang's
argument (§4.3) reduces each such controlled gate to a circuit of **uncontrolled single-qubit gates
placed on individual wires** and `CNOT`s; then the single-qubit gates are approximated by the
reachable set (`SingleQubitRotationUniversality.lean`) and, through the error-chaining inequality
(§4.5.3), the whole register unitary is approximated. This file provides the matrix object that
reduction produces and the approximation consumes — the **single-qubit gate on wire `j`** — together
with the property that makes the approximation phase-clean.

## The construction

Fix an encoding `enc : (Fin m → Fin 2) ≃ Fin d` of the `m`-bit strings as the `d = 2 ^ m` basis
indices, a wire `j : Fin m`, and a `2 × 2` matrix `g`.

* `AxQM.Concrete.singleQubitOnWire enc j g` — on `|enc x⟩` it applies `g` to bit `j` of `x`
  (regardless of the other bits), fixing the other bits. It is the `ctrlSingleQubit` gate with its
  control condition dropped: `g` acts on *every* fibre of the `j`-th bit, so the matrix is block
  diagonal over those two-dimensional fibres.

## Why it matters — the phase-clean property

A general `2 × 2` unitary is reachable only *up to a global phase* (`exists_zy_decomposition`); the
reachable single-qubit set sits in `SU(2)`. On a **controlled** gate that residual phase is a
*relative* phase and cannot be absorbed. On an **uncontrolled** wire gate it is a genuine *global*
phase: `singleQubitOnWire enc j (c • g) = c • singleQubitOnWire enc j g` — the scalar `c` multiplies
the *whole* `d × d` matrix (`singleQubitOnWire_smul`), not just a sub-block. This is exactly why
N&C's §4.3 reduces controlled gates to uncontrolled single-qubit gates *before* approximating: the
per-gate phase ambiguities then combine into one physically irrelevant global phase.

The algebra confirms `singleQubitOnWire enc j` is a `*`-homomorphism on the block
(`singleQubitOnWire_one`, `singleQubitOnWire_mul`, `singleQubitOnWire_conjTranspose`), so it sends
unitaries to unitaries (`singleQubitOnWire_mem_unitaryGroup`); and it is continuous
(`continuous_singleQubitOnWire`). Assembling these:

* `AxQM.Concrete.exists_phase_smul_singleQubitOnWire_mem_closure` — **the headline**: for
  `cos θ = 3/5` and every `U ∈ U(2)`, some global phase `e^{iα}` makes
  `e^{iα} • singleQubitOnWire enc j U` a limit of `singleQubitOnWire enc j` applied to the reachable
  single-qubit gates. It is the single-qubit universality of Exercise 4.43 (Step 2), lifted to a
  chosen wire of the `m`-qubit register and kept phase-clean.

## Use

This is reused by the `n`-qubit lift of Exercise 4.43 (`AxQM/NC/Ch4/Exercise4_43.lean`).
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- **The single-qubit gate on wire `j`.** Relative to an encoding `enc : (Fin m → Fin 2) ≃ Fin d`,
a wire `j`, and a `2 × 2` matrix `g`, it applies `g` to bit `j` of `x` on the basis state `|enc x⟩`
(regardless of the other bits), fixing the other bits. It is `ctrlSingleQubit` with the control
condition removed — `g` acts on every fibre of the `j`-th bit. -/
def singleQubitOnWire (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (g : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i i' =>
    if ∀ k, k ≠ j → enc.symm i k = enc.symm i' k then g (enc.symm i j) (enc.symm i' j) else 0

/-- Unfolding lemma for `singleQubitOnWire` entries. -/
theorem singleQubitOnWire_apply (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (i i' : Fin d) :
    singleQubitOnWire enc j g i i' =
      if ∀ k, k ≠ j → enc.symm i k = enc.symm i' k then g (enc.symm i j) (enc.symm i' j)
      else 0 := rfl

/-- **`singleQubitOnWire` is the fibrewise gate (`wireGate`, `ControlledSingleQubit.lean`) with a
constant block.** The gate's action / multiplicativity / identity lemmas below are one-line
consequences of the general `wireGate_*` lemmas through this bridge. -/
theorem singleQubitOnWire_eq_wireGate (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    singleQubitOnWire enc j g = wireGate enc j (fun _ => g) := by
  ext i i'
  simp only [singleQubitOnWire, wireGate, Matrix.of_apply]

/-- **A diagonal single-qubit block on a wire is a diagonal matrix.** `singleQubitOnWire enc j
(diagonal v) = diagonal (fun i => v (enc.symm i j))`: with a diagonal block, the gate multiplies the
basis state `|enc x⟩` by `v (bit j of x)` and mixes nothing (two distinct basis states agreeing off
wire `j` disagree at `j`, so the off-diagonal entry vanishes by `Matrix.diagonal_apply_ne`). -/
theorem singleQubitOnWire_diagonal (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m) (v : Fin 2 → ℂ) :
    singleQubitOnWire enc j (Matrix.diagonal v) = Matrix.diagonal fun i => v (enc.symm i j) := by
  ext i i'
  rw [singleQubitOnWire_apply]
  by_cases hii : i = i'
  · subst hii
    rw [ite_eq_left fun _ _ => rfl, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hii]
    by_cases hbits : ∀ k, k ≠ j → enc.symm i k = enc.symm i' k
    · rw [ite_eq_left hbits]
      exact Matrix.diagonal_apply_ne v fun hj => hii (enc.symm.injective (funext fun k => by
        rcases eq_or_ne k j with rfl | hk
        · exact hj
        · exact hbits k hk))
    · rw [ite_eq_right hbits]

/-- **A scalar pulls out of the whole matrix** — the phase-clean property. Because the gate is
uncontrolled, multiplying its `2 × 2` block by `c` multiplies the *entire* `d × d` matrix by `c`. -/
theorem singleQubitOnWire_smul (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m) (c : ℂ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    singleQubitOnWire enc j (c • g) = c • singleQubitOnWire enc j g := by
  ext i i'
  simp only [singleQubitOnWire, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **The action of a single-qubit wire gate on a vector.** It mixes only the two components whose
bit-strings agree off wire `j`, through `g`. -/
theorem singleQubitOnWire_mulVec (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin d → ℂ) (i : Fin d) :
    (singleQubitOnWire enc j g *ᵥ v) i =
      g (enc.symm i j) 0 * v (enc (Function.update (enc.symm i) j 0))
        + g (enc.symm i j) 1 * v (enc (Function.update (enc.symm i) j 1)) := by
  rw [singleQubitOnWire_eq_wireGate, wireGate_mulVec]

/-- The single-qubit wire gate of the `2 × 2` identity is the `d × d` identity. -/
theorem singleQubitOnWire_one (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m) :
    singleQubitOnWire enc j (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [singleQubitOnWire_eq_wireGate, wireGate_one]

/-- **`singleQubitOnWire enc j` is multiplicative on the block**: it respects matrix products.
It is the constant-block case of the general fibrewise multiplicativity `wireGate_mul`
(`ControlledSingleQubit.lean`), through the bridge `singleQubitOnWire_eq_wireGate`. -/
theorem singleQubitOnWire_mul (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (a b : Matrix (Fin 2) (Fin 2) ℂ) :
    singleQubitOnWire enc j a * singleQubitOnWire enc j b
      = singleQubitOnWire enc j (a * b) := by
  simp only [singleQubitOnWire_eq_wireGate, wireGate_mul]

/-- **`singleQubitOnWire enc j` commutes with the conjugate transpose**:
`(singleQubitOnWire enc j g)ᴴ = singleQubitOnWire enc j gᴴ`. -/
theorem singleQubitOnWire_conjTranspose (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (singleQubitOnWire enc j g)ᴴ = singleQubitOnWire enc j gᴴ := by
  ext i i'
  rw [Matrix.conjTranspose_apply, singleQubitOnWire_apply, singleQubitOnWire_apply,
    Matrix.conjTranspose_apply]
  by_cases hoff : ∀ k, k ≠ j → enc.symm i k = enc.symm i' k
  · rw [ite_eq_left hoff, ite_eq_left (fun k hk => (hoff k hk).symm)]
  · rw [ite_eq_right hoff, ite_eq_right (fun h => hoff (fun k hk => (h k hk).symm)), star_zero]

/-- **A single-qubit wire gate with unitary block is unitary.** Follows from the `*`-homomorphism
laws: `(SQ g)ᴴ · SQ g = SQ (gᴴ · g) = SQ 1 = 1`. -/
theorem singleQubitOnWire_mem_unitaryGroup (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    singleQubitOnWire enc j g ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hg ⊢
  rw [Matrix.star_eq_conjTranspose] at hg ⊢
  rw [singleQubitOnWire_conjTranspose, singleQubitOnWire_mul, hg, singleQubitOnWire_one]

/-- **`singleQubitOnWire enc j` is continuous** in its `2 × 2` block: each matrix entry is either
the constant `0` or the continuous projection `g ↦ g a b`. -/
theorem continuous_singleQubitOnWire (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m) :
    Continuous (fun g : Matrix (Fin 2) (Fin 2) ℂ => singleQubitOnWire enc j g) := by
  apply continuous_matrix
  intro i i'
  simp only [singleQubitOnWire, Matrix.of_apply]
  split_ifs with h
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const

/-- **The per-wire phase-clean transport** (N&C §4.3/§4.5, the generic single-qubit-density lift).
If some global phase `e^{iα}` makes `e^{iα} • U` a closure limit of a set `S` of `2 × 2` gates, then
the *same* phase makes `e^{iα} • singleQubitOnWire enc j U` a closure limit of
`singleQubitOnWire enc j '' S`. Because `singleQubitOnWire enc j` is *continuous*
(`continuous_singleQubitOnWire`) it carries the closure membership through
(`image_closure_subset_closure_image`), and because the phase pulls out *globally* on the
uncontrolled wire (`singleQubitOnWire_smul`) the residual phase survives as a genuine global phase
on the whole register — the property the §4.3 reduction to uncontrolled gates buys and the
error-chaining assembly needs.

This is the transport shared by every single-qubit density on a wire: it is fed the reachable
rotations for Exercise 4.43 (`exists_phase_smul_singleQubitOnWire_mem_closure`) and the Deutsch
single-qubit submonoid for Exercise 4.44
(`exists_phase_smul_singleQubitOnWire_mem_closure_deutschWireGateSubmonoid`,
`Concrete/DeutschWireUniversality.lean`). -/
theorem exists_phase_smul_singleQubitOnWire_mem_closure_of_exists_phase_smul_mem_closure
    (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m) {S : Set (Matrix (Fin 2) (Fin 2) ℂ)}
    {U : Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∃ α : ℝ, Complex.exp ((α : ℂ) * Complex.I) • U ∈ closure S) :
    ∃ α : ℝ, Complex.exp ((α : ℂ) * Complex.I) • singleQubitOnWire enc j U
      ∈ closure (singleQubitOnWire enc j '' S) := by
  obtain ⟨α, hα⟩ := h
  refine ⟨α, ?_⟩
  have hmem := image_closure_subset_closure_image (continuous_singleQubitOnWire enc j)
    (Set.mem_image_of_mem (singleQubitOnWire enc j) hα)
  rwa [singleQubitOnWire_smul] at hmem

/-- **Single-qubit universality on a wire, kept phase-clean** (Exercise 4.43, Step 2 lifted to the
`m`-qubit register). For `cos θ = 3/5` and every single-qubit unitary `U`, some global phase
`e^{iα}` makes `e^{iα} • singleQubitOnWire enc j U` a limit of `singleQubitOnWire enc j` applied to
the reachable gates `R_z(±θ), R_x(±θ)`.

A one-line application of the generic per-wire transport
`exists_phase_smul_singleQubitOnWire_mem_closure_of_exists_phase_smul_mem_closure` to the reachable
set's density up to a phase (`exists_phase_smul_mem_closure_reachableRotations`): the transport
keeps the residual phase global on the uncontrolled wire — the property the §4.3 reduction buys and
the error-chaining assembly needs. -/
theorem exists_phase_smul_singleQubitOnWire_mem_closure {θ : ℝ} (hθ : Real.cos θ = 3 / 5)
    (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m) {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ α : ℝ, Complex.exp ((α : ℂ) * Complex.I) • singleQubitOnWire enc j U
      ∈ closure (singleQubitOnWire enc j ''
        (reachableRotations θ : Set (Matrix (Fin 2) (Fin 2) ℂ))) :=
  exists_phase_smul_singleQubitOnWire_mem_closure_of_exists_phase_smul_mem_closure enc j
    (exists_phase_smul_mem_closure_reachableRotations hθ U hU)

end AxQM.Concrete
