/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.RotationComposition

/-!
# Concrete: the search-simulation step `U(Δt)` in Bloch/Pauli form (Nielsen & Chuang, Eq. 6.25)

Nielsen & Chuang, §6.2, study quantum search as the simulation of the Hamiltonian
`H = |x⟩⟨x| + |ψ⟩⟨ψ|` (eq. 6.18). The lowest-order simulation step is the product of the two
projector-Hamiltonian propagators; N&C focus (Exercise 6.9) on

`U(Δt) ≡ exp(−i|ψ⟩⟨ψ|Δt) exp(−i|x⟩⟨x|Δt)`,

which acts non-trivially only on the two-dimensional subspace `span{|x⟩,|ψ⟩}`, an effective qubit.
Writing `|x⟩⟨x| = (I + ẑ·σ)/2` (with `ẑ = (0,0,1)`) and `|ψ⟩⟨ψ| = (I + ⃗ψ·σ)/2` (with
`⃗ψ = (2αβ, 0, α²−β²)` for `|ψ⟩ = α|x⟩ + β|y⟩`), a "simple calculation shows that up to an
unimportant global phase factor" (eq. 6.25, with `c = cos(Δt/2)`, `s = sin(Δt/2)`)

`U(Δt) = (c² − s² ⃗ψ·ẑ) I − 2is (c (⃗ψ+ẑ)/2 + s (⃗ψ×ẑ)/2)·σ`.

This file develops the pure `2 × 2` complex-matrix core of that fact, for arbitrary unit Bloch
vectors `a` (playing `⃗ψ`) and `b` (playing `ẑ`). The physical fact — that the two factors are the
projector-Hamiltonian propagators `exp(−i|·⟩⟨·|Δt)` of Exercise 6.7 — is in
`AxQM/Postulates/API/SearchSimulationStep.lean` and `AxQM/NC/Ch6/Exercise6_9.lean`.

## The derivation

The projector `(I + n·σ)/2` (`Concrete.blochMatrix n`, for unit `n`) is the Hamiltonian; its
propagator `exp(−i (I + n·σ)/2 · Δt)`, in the general closed form
`1 + (e^{−iΔt} − 1)|·⟩⟨·|` of Exercise 6.7, splits off a global phase and becomes a **Bloch
rotation**:

* `blochPropagatorMatrix` — the propagator matrix `1 + (e^{−iΔt} − 1) blochMatrix n` itself.
* `blochPropagatorMatrix_eq_smul_rotAxis` — `blochPropagatorMatrix Δt n = e^{−iΔt/2} R_n̂(Δt)`,
  the bridge from the general propagator form to the rotation operator `R_n̂(Δt) = rotAxis n Δt`
  (`= cos(Δt/2) I − i sin(Δt/2)(n·σ)`, `rotAxis_eq_of_unit`). The whole content is the Euler
  identity `e^{−iΔt/2} = cos(Δt/2) − i sin(Δt/2)` matched coefficient-wise over `{I, n·σ}` using
  `cos²(Δt/2) + sin²(Δt/2) = 1`.

The product of the two rotations is then the composition law of Exercise 4.15
(`rotAxis_mul_rotAxis`), and the phase factors multiply to `e^{−iΔt}`:

* `searchStepReduced` / `searchStepAxis` — the right-hand side of eq. 6.25 as an explicit matrix
  (the scalar `c² − s² a·b` times `I`, minus `2is` times `(c (a+b)/2 + s (a×b)/2)·σ`).
* `rotAxis_mul_rotAxis_eq_searchStepReduced` — `R_â(Δt) R_b̂(Δt) = searchStepReduced Δt a b`: the
  Exercise 4.15 composition law (`rotAxis_mul_rotAxis`) rewritten into N&C's eq. 6.25 shape, using
  its `β₁ = β₂` specialisation (eqs. 4.21/4.22, the same as N&C eqs. 6.26/6.27).
* `searchStep_eq` — **Eq. 6.25**:
  `blochPropagatorMatrix Δt a * blochPropagatorMatrix Δt b = e^{−iΔt} searchStepReduced Δt a b`.
  The two propagator factors become `e^{−iΔt/2}R_â`, `e^{−iΔt/2}R_b̂`; the phases multiply to
  `e^{−iΔt}` and the rotations to `searchStepReduced`. The global phase `e^{−iΔt}` is made explicit
  rather than discarded.

-/

namespace AxQM.Concrete

open Matrix Complex

/-- **The projector-Hamiltonian propagator matrix** `exp(−i (I + n·σ)/2 · Δt)`, in the general
closed form `1 + (e^{−iΔt} − 1)|·⟩⟨·|` of Exercise 6.7 with the projector written as the Bloch
matrix `blochMatrix n = (I + n·σ)/2`:
`blochPropagatorMatrix Δt n = 1 + (e^{−iΔt} − 1) blochMatrix n`.
For a unit Bloch vector `n` it factors as a global phase times a rotation
(`blochPropagatorMatrix_eq_smul_rotAxis`); the search-simulation step `U(Δt)` is the product of two
of these (`searchStep_eq`). -/
noncomputable def blochPropagatorMatrix (Δt : ℝ) (n : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) + (Complex.exp (-(Complex.I * (Δt : ℂ))) - 1) • blochMatrix n

/-- **The projector-Hamiltonian propagator, in Bloch/rotation form.** For a unit Bloch vector `n`,
the propagator matrix `blochPropagatorMatrix Δt n = 1 + (e^{−iΔt} − 1) blochMatrix n` (Exercise 6.7,
with `|·⟩⟨·| = blochMatrix n = (I + n·σ)/2`) factors into a global phase times the Bloch rotation
`R_n̂(Δt)`:
`blochPropagatorMatrix Δt n = e^{−iΔt/2} · rotAxis n Δt`.
Both sides are scalar combinations of `{I, n·σ}`; matching coefficients is the Euler identity
`e^{−iΔt/2} = cos(Δt/2) − i sin(Δt/2)` together with `cos²(Δt/2) + sin²(Δt/2) = 1`. -/
theorem blochPropagatorMatrix_eq_smul_rotAxis {n : Fin 3 → ℝ}
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) (Δt : ℝ) :
    blochPropagatorMatrix Δt n = Complex.exp (-(Complex.I * ((Δt : ℂ) / 2))) • rotAxis n Δt := by
  rw [blochPropagatorMatrix]
  have hsq : Complex.exp (-(Complex.I * (Δt : ℂ)))
      = Complex.exp (-(Complex.I * ((Δt : ℂ) / 2)))
          * Complex.exp (-(Complex.I * ((Δt : ℂ) / 2))) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [hsq, blochMatrix, rotAxis_eq_of_unit hn]
  -- Fold the phase and the real cosine/sine into opaque `ℂ`-atoms `e`, `c`, `s`, so the coefficient
  -- matching below stays in `{e, c, s, I}` (no `↑(Real.cos …)` ↔ `Complex.cos …` cast drift).
  set e := Complex.exp (-(Complex.I * ((Δt : ℂ) / 2))) with he_def
  set c := (Real.cos (Δt / 2) : ℂ) with hc_def
  set s := (Real.sin (Δt / 2) : ℂ) with hs_def
  have he : e = c - s * Complex.I := by
    rw [he_def, hc_def, hs_def,
      show -(Complex.I * ((Δt : ℂ) / 2)) = ((-(Δt / 2) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have hpyth : c ^ 2 + s ^ 2 = 1 := by
    rw [hc_def, hs_def, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq]
    norm_num
  rw [he]
  match_scalars
  · linear_combination (-2⁻¹ : ℂ) * hpyth + (s ^ 2 / 2) * Complex.I_sq
  · linear_combination (2⁻¹ : ℂ) * hpyth + (-(s ^ 2) / 2) * Complex.I_sq

/-- The **axis vector of eq. 6.25**: `c (a+b)/2 + s (a×b)/2` (with `c = cos(Δt/2)`,
`s = sin(Δt/2)`), the vector whose Pauli combination appears in `searchStepReduced` (N&C eq. 6.25);
with `a = ⃗ψ`, `b = ẑ` it is N&C's `c (⃗ψ+ẑ)/2 + s (⃗ψ×ẑ)/2` (the un-normalised axis `s₁₂ n̂₁₂` of
eqs. 6.26/4.22). -/
noncomputable def searchStepAxis (Δt : ℝ) (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  Real.cos (Δt / 2) • ((2⁻¹ : ℝ) • (a + b))
    + Real.sin (Δt / 2) • ((2⁻¹ : ℝ) • crossProduct a b)

/-- **The right-hand side of Nielsen & Chuang, Eq. 6.25**, as an explicit `2 × 2` complex matrix:
`(c² − s² a·b) I − 2is (c (a+b)/2 + s (a×b)/2)·σ`
with `c = cos(Δt/2)`, `s = sin(Δt/2)`. With `a = ⃗ψ` (Bloch vector of `|ψ⟩`) and `b = ẑ` (Bloch
vector of `|x⟩`) this is exactly the reduced form of `U(Δt)` (up to the global phase `e^{−iΔt}`,
made explicit in `searchStep_eq`). -/
noncomputable def searchStepReduced (Δt : ℝ) (a b : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (↑(Real.cos (Δt / 2) ^ 2 - Real.sin (Δt / 2) ^ 2 * (a ⬝ᵥ b)) : ℂ)
      • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    - (2 * (Real.sin (Δt / 2) : ℂ) * Complex.I) • pauliDot (searchStepAxis Δt a b)

/-- **The composed axis-vector of the two search rotations is `2 sin(Δt/2)` times the eq.-6.25 axis
`searchStepAxis`**: `rotComposeVec Δt b Δt a = 2 sin(Δt/2) • searchStepAxis Δt a b`. The composed
axis-vector `s c (a+b) + s² (a×b)` (`rotComposeVec`, Exercise 4.15 at `β₁ = β₂ = Δt`, `n₁ = b`,
`n₂ = a`) is `2s` times N&C's `c (a+b)/2 + s (a×b)/2`. Shared by
`rotAxis_mul_rotAxis_eq_searchStepReduced` and `searchStepReduced_eq_rotAxis`. -/
theorem rotComposeVec_eq_smul_searchStepAxis (Δt : ℝ) (a b : Fin 3 → ℝ) :
    rotComposeVec Δt b Δt a = (2 * Real.sin (Δt / 2)) • searchStepAxis Δt a b := by
  rw [rotComposeVec, searchStepAxis]; module

/-- **The composed search axis-vector has strictly positive squared norm** when the step half-angle
and the eq.-6.25 axis are both nonzero: `0 < ‖rotComposeVec Δt b Δt a‖²` (with `‖·‖²` the scalar
`·₀² + ·₁² + ·₂²`) given `sin(Δt/2) ≠ 0` and `searchStepAxis Δt a b ≠ 0`. Since
`rotComposeVec Δt b Δt a = 2 sin(Δt/2) • searchStepAxis Δt a b`
(`rotComposeVec_eq_smul_searchStepAxis`), the squared norm is `(2 sin(Δt/2))² ‖searchStepAxis‖²`, a
product of two positive factors. This is the composite-non-degeneracy fact (`rotComposeVec ≠ ±0`, so
`U(Δt)` is not `±I`) that the Exercise 6.10 landing consumes — both as `0 <` to normalise the
composed axis and, via `.ne'`, as the `≠ 0` hypothesis of `rotComposeUnitAxis_normSq`. -/
theorem rotComposeVec_normSq_pos {a b : Fin 3 → ℝ} (Δt : ℝ)
    (hs : Real.sin (Δt / 2) ≠ 0)
    (hax : (searchStepAxis Δt a b) 0 ^ 2 + (searchStepAxis Δt a b) 1 ^ 2
        + (searchStepAxis Δt a b) 2 ^ 2 ≠ 0) :
    0 < (rotComposeVec Δt b Δt a) 0 ^ 2 + (rotComposeVec Δt b Δt a) 1 ^ 2
        + (rotComposeVec Δt b Δt a) 2 ^ 2 := by
  have hw : 0 < (searchStepAxis Δt a b) 0 ^ 2 + (searchStepAxis Δt a b) 1 ^ 2
      + (searchStepAxis Δt a b) 2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hax)
  rw [rotComposeVec_eq_smul_searchStepAxis]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  have h2s : (0 : ℝ) < (2 * Real.sin (Δt / 2)) ^ 2 := by positivity
  nlinarith [mul_pos h2s hw]

/-- **The composed rotation is N&C's eq. 6.25 reduced form.** For unit Bloch vectors `a`, `b`, the
product `R_â(Δt) R_b̂(Δt)` of the two Bloch rotations equals `searchStepReduced Δt a b`. This is the
Exercise 4.15 composition law (`rotAxis_mul_rotAxis`) — at the shared angle `β₁ = β₂ = Δt` — written
into the eq. 6.25 shape: the composed half-angle cosine gives the scalar `c² − s² a·b` and the
composed axis-vector `s c (a+b) + s² (a×b)` is `2s` times the eq.-6.25 axis
`c (a+b)/2 + s (a×b)/2` (`searchStepAxis`). -/
theorem rotAxis_mul_rotAxis_eq_searchStepReduced {a b : Fin 3 → ℝ}
    (ha : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1) (hb : b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 = 1) (Δt : ℝ) :
    rotAxis a Δt * rotAxis b Δt = searchStepReduced Δt a b := by
  have hscal : rotComposeCos Δt b Δt a
      = Real.cos (Δt / 2) ^ 2 - Real.sin (Δt / 2) ^ 2 * (a ⬝ᵥ b) := by
    rw [rotComposeCos, dotProduct_comm b a]; ring
  rw [rotAxis_mul_rotAxis hb ha Δt Δt, hscal, rotComposeVec_eq_smul_searchStepAxis Δt a b,
    pauliDot_smul, searchStepReduced]
  push_cast
  module

/-- **Nielsen & Chuang, Exercise 6.9 — verification of Eq. 6.25 (matrix core).** For unit Bloch
vectors `a` (`= ⃗ψ`) and `b` (`= ẑ`), the product of the two projector-Hamiltonian propagators (in
the general closed form `1 + (e^{−iΔt} − 1)|·⟩⟨·|` of Exercise 6.7, with the projectors written as
Bloch matrices) equals the global phase `e^{−iΔt}` times N&C's reduced form:

`(1 + (e^{−iΔt}−1) blochMatrix a)(1 + (e^{−iΔt}−1) blochMatrix b)`
`= e^{−iΔt} · searchStepReduced Δt a b`.

Each factor becomes `e^{−iΔt/2} R_·̂(Δt)` (`blochPropagatorMatrix_eq_smul_rotAxis`); the
phases multiply to `e^{−iΔt}` (`Complex.exp_add`) and the rotations to `searchStepReduced`
(`rotAxis_mul_rotAxis_eq_searchStepReduced`). The unimportant global phase of N&C's "up to a global
phase factor" is here made explicit. -/
theorem searchStep_eq {a b : Fin 3 → ℝ}
    (ha : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1) (hb : b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 = 1) (Δt : ℝ) :
    blochPropagatorMatrix Δt a * blochPropagatorMatrix Δt b
      = Complex.exp (-(Complex.I * (Δt : ℂ))) • searchStepReduced Δt a b := by
  rw [blochPropagatorMatrix_eq_smul_rotAxis ha, blochPropagatorMatrix_eq_smul_rotAxis hb,
    smul_mul_assoc, mul_smul_comm, smul_smul, ← Complex.exp_add,
    rotAxis_mul_rotAxis_eq_searchStepReduced ha hb,
    show -(Complex.I * ((Δt : ℂ) / 2)) + -(Complex.I * ((Δt : ℂ) / 2)) = -(Complex.I * (Δt : ℂ)) by
      ring]

/-- **The reduced search-simulation step is a single Bloch rotation.** For unit Bloch vectors `a`
(`= ⃗ψ`), `b` (`= ẑ`), a nonzero step half-angle (`sin(Δt/2) ≠ 0`) and a nonzero composed axis
(`searchStepAxis ≠ 0`), the N&C eq.-6.25 reduced form `searchStepReduced Δt a b` — i.e. `U(Δt)` up
to the global phase `e^{−iΔt}` — is the single Bloch rotation `R_n̂₁₂(β₁₂)` about the unit axis
`rotComposeUnitAxis` through the angle `rotComposeAngle`. Because `searchStepReduced` is the product
of the two projector-propagator rotations `R_â(Δt) R_b̂(Δt)`
(`rotAxis_mul_rotAxis_eq_searchStepReduced`), this is `rotAxis_mul_rotAxis_eq_rotAxis` specialised
to `β₁ = β₂ = Δt`, `n₁ = b`, `n₂ = a`; the composed axis-vector `rotComposeVec Δt b Δt a =
2 sin(Δt/2) · searchStepAxis` is nonzero exactly under the two hypotheses. Presenting `U(Δt)` as one
`rotAxis` is what lets `rotAxis_pow` compute its `j`-th power `U(Δt)^j` for N&C Exercise 6.10. -/
theorem searchStepReduced_eq_rotAxis {a b : Fin 3 → ℝ}
    (ha : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1) (hb : b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 = 1) (Δt : ℝ)
    (hs : Real.sin (Δt / 2) ≠ 0)
    (hax : (searchStepAxis Δt a b) 0 ^ 2 + (searchStepAxis Δt a b) 1 ^ 2
        + (searchStepAxis Δt a b) 2 ^ 2 ≠ 0) :
    searchStepReduced Δt a b
      = rotAxis (rotComposeUnitAxis Δt b Δt a) (rotComposeAngle Δt b Δt a) := by
  refine (rotAxis_mul_rotAxis_eq_searchStepReduced ha hb Δt).symm.trans
    (rotAxis_mul_rotAxis_eq_rotAxis hb ha Δt Δt ?_)
  rw [rotComposeVec_eq_smul_searchStepAxis Δt a b]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← mul_add]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)) hax

end AxQM.Concrete
