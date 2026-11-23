/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.StabilizerEntanglementDistillation

/-!
# Nielsen & Chuang, Exercise 12.34 (Entanglement distillation by error-correction)

*(N&C §12.6.3 "Quantum cryptography", p. 597.)*

Entanglement distillation by error-correction: stabilizer measurements yield |beta>^m.

## The formalisation

The two `n`-qubit halves of the `n` EPR pairs `|β₀₀⟩^⊗n = ∑_{x∈{0,1}ⁿ} |x⟩_A|x⟩_B` are the two
tensor legs of the *(unnormalised)* **maximally entangled vector** `maxEntVec (Fin n → Fin 2) ℂ`
(`ToMathlib/`, N&C Ex 9.16). Measuring the `n − m` stabilizer generators of an `[n, m]` code on a
half and Pauli-correcting the outcome to the simultaneous `+1` eigenstate is, as a *net* operation,
exactly projection onto the code space `V_S = range (codeProjector S)` (`codeProjector S = P_S` the
Hermitian idempotent group-average projector of Chapter 10). So the measure-and-correct procedure of
the exercise is modelled by projecting the maximally entangled vector onto the code space, and its
distilled output is `stabilizerDistilledVec S`.

* **Part (a) — encoded `|β₀₀⟩^⊗m`.** Doing this to *both* halves gives `(P_S ⊗ P̄_S)|m⟩`, where on
  the second (Bob) leg identical generator measurements act as the entrywise conjugate `P̄_S` (the
  transpose trick for `|m⟩`); "correcting for differences in the measurement results" is the
  statement that the two halves land in the *same* code space, which collapses the two-sided
  projection to the single-sided `(P_S ⊗ I)|m⟩` (`stabilizerDistilledVec_bothHalves`, matched
  syndromes). That vector is the *(unnormalised)* maximally entangled state on `V_S`, and for an
  `[n, m]` code (`|S| = 2ⁿ⁻ᵐ`, so `dim V_S = 2ᵐ`) it has squared norm `2ᵐ`
  (`stabilizerDistilledVec_normSq_eq_two_pow`) — precisely `m` encoded Bell pairs, the encoded
  `|β₀₀⟩^⊗m`.
* **Part (b) — error robustness.** A Pauli error `E` on one half plus a syndrome-consistent Pauli
  correction `C` (same syndrome as `E`, `C * E ∈ N(S)`) of below-distance residual weight
  (`weight (C · E) < d`; automatic for weight-`≤ δn` error and correction of a code with
  `d ≥ 2δn + 1`) still returns the distilled state up to a **unit-modulus global phase**
  (`stabilizerDistilledVec_error_corrected`, `stabilizerDistilledVec_error_corrected_of_weight_le`).
  As a unit-modulus multiple of the part-(a) vector it is physically the *same* maximally entangled
  state on `V_S`, so "even if `δn` errors are suffered by an `n` qubit half, we still obtain
  `|β₀₀⟩^⊗m`".

### Design decisions (fidelity to N&C)

* *Encoded `|β₀₀⟩^⊗m` = the maximally entangled state on `V_S`.* Rather than construct an explicit
  encoding isometry `U : (ℂ²)^⊗m → V_S` for a general stabilizer code (not in the library) and write
  the output literally as `(U ⊗ Ū)|β₀₀⟩^⊗m`, we characterise it isometry-invariantly as the
  maximally entangled state on the `2ᵐ`-dimensional code space. This is the physically correct
  meaning of "`m` encoded Bell pairs" and is faithful to N&C's general `[n, m]`-stabilizer
  statement: the construction only needs `P_S` Hermitian idempotent, which `codeProjector S` is — no
  specialisation to CSS or real Paulis (which would be a weakening).
* *Part (b) as exact recovery up to a phase.* N&C's "we still obtain `|β₀₀⟩^⊗m`" is read as: the
  recovery moves the errored state back to the distilled state up to a global phase. The unit
  modulus `‖c‖ = 1` (a fourth root of unity `iˢ`) is essential — it is exactly what certifies it is
  *recovered*, not annihilated (a below-distance element outside `N(S)` can conjugate `P` to `0`).

## The declarations

The maximally entangled vector and its transpose-trick / projector identities — the linear-algebra
kernel of the exercise — in `ToMathlib/LinearAlgebra/Matrix/MaxEntVec.lean` (N&C Ex 9.16 and
the Ex 12.34 kernel):

* `Matrix.maxEntVec` — the *(unnormalised)* maximally entangled vector `|m⟩ = ∑ᵢ eᵢ ⊗ eᵢ`, with its
  Hilbert–Schmidt pairing (N&C Ex 9.16) `Matrix.star_maxEntVec_dotProduct_kronecker` and
  `Matrix.star_maxEntVec_dotProduct_map_star_kronecker`, and
  `Matrix.not_forall_trace_conjTranspose_mul_eq_star_maxEntVec_dotProduct_kronecker` (the sharpness
  refutation of N&C's literal `tr(A† B)` form of Ex 9.16).
* `Matrix.kronecker_mulVec_maxEntVec` / `Matrix.kronecker_one_mulVec_maxEntVec` — the **transpose
  trick** in Choi and ricochet form (`(A ⊗ B)|m⟩ = vec(B Aᵀ)`, `(A ⊗ I)|m⟩ = (I ⊗ Aᵀ)|m⟩`).
* `Matrix.map_star_eq_transpose_of_isHermitian`,
  `Matrix.kronecker_map_star_mulVec_maxEntVec_of_isHermitian_of_isIdempotent` (projecting **both**
  halves = projecting **one** half, for a Hermitian idempotent projector) and
  `Matrix.star_kronecker_one_mulVec_maxEntVec_dotProduct_self_of_isHermitian_of_isIdempotent` (the
  projected vector has squared norm `tr P`).

The distillation itself, in `AxQM/Concrete/StabilizerEntanglementDistillation.lean`
(namespace `AxQM.Concrete`):

* `stabilizerDistilledVec` — the distilled state `(P_S ⊗ I)|m⟩`, the maximally entangled state on
  the code space, i.e. the encoded `|β₀₀⟩^⊗m`; with closed form
  `stabilizerDistilledVec_eq_vec_transpose` (`= (P_S)ᵀ.vec`).
* `stabilizerDistilledVec_bothHalves` — **part (a), matched syndromes:** the two-sided code-space
  projection `(P_S ⊗ P̄_S)|m⟩` collapses to the one-sided `stabilizerDistilledVec S`.
* `stabilizerDistilledVec_normSq` (squared norm `= tr(P_S)`) and
  `stabilizerDistilledVec_normSq_eq_two_pow` — **part (a) headline:** for an `[n, m]` code the
  squared norm is `2ᵐ`, identifying the distilled state as `m` encoded Bell pairs.
* `stabilizerDistilledVec_error_corrected` — **part (b) headline:** a below-distance error plus a
  syndrome-consistent Pauli correction returns the distilled state up to a unit-modulus phase; and
  `stabilizerDistilledVec_error_corrected_of_weight_le` — the same in the textbook parameters
  (weight-`≤ δn` error and correction, distance `≥ 2δn + 1`).

The part-(a) trace value and the part-(b) unit-phase conjugation core, in
`AxQM/Concrete/StabilizerCodeDistance.lean`:

* `AxQM.Concrete.codeProjector_trace_eq` — `tr(codeProjector S) = |S|⁻¹ · 2ⁿ` (with
  `|S| = 2ⁿ⁻ᵐ` this is `2ᵐ = dim V_S`).
* `AxQM.Concrete.exists_norm_one_codeProjector_conj_toMat_of_mem_normalizer_of_weight_lt` —
  a below-distance normalizer element conjugates `P_S` to a *unit* phase multiple `c • P_S`,
  `‖c‖ = 1` (sharpening `exists_codeProjector_conj_smul_of_weight_lt`, whose scalar can vanish).

These use the Chapter 10 stabilizer infrastructure — `AxQM.Concrete.codeProjector`
(`StabilizerCodeProjector.lean`; Hermitian, idempotent) and the weight/distance correction machinery
(`StabilizerCodeDistance.lean`) — rather than reproving it.
Compare Theorem 10.8 (`AxQM/NC/Ch10/Theorem10_8.lean`).
-/
