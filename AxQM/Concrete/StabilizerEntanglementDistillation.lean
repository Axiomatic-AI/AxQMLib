/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import ToMathlib.LinearAlgebra.Matrix.MaxEntVec
import AxQM.Concrete.StabilizerCodeDistance

/-!
# Concrete: entanglement distillation of EPR pairs by a stabilizer code (N&C Ex 12.34)

This file formalises the linear-algebra core of **Nielsen & Chuang, Exercise 12.34** (*Entanglement
distillation by error-correction*, p. 597), parts (a) and (b). Everything here is stated for the
abstract Pauli group `PauliGroup n`, its subgroups, the group-average code projector `codeProjector`
(`AxQM/Concrete/StabilizerCodeProjector.lean`) and raw matrices/vectors.

## The exercise (part a)

N&C: start with `n` EPR pairs in the state `|β₀₀⟩^⊗n`, perform **identical** stabilizer-generator
measurements on the two `n`-qubit halves of the pairs, and apply Pauli operations to correct for
differences in the measurement results between the halves; then one obtains an **encoded**
`|β₀₀⟩^⊗m` state (`m` the number of logical qubits of the `[n, m]` code).

## The formalisation

We work with the *(unnormalised)* maximally entangled vector `maxEntVec (Fin n → Fin 2) ℂ`
(`ToMathlib/LinearAlgebra/Matrix/MaxEntVec.lean`, N&C Ex 9.16) as the `n` EPR pairs
`|β₀₀⟩^⊗n = ∑_{x ∈ {0,1}ⁿ} |x⟩_A|x⟩_B`, its two tensor legs being Alice's and Bob's `n` qubits.
The stabilizer code space `V_S` of a stabilizer `S ≤ PauliGroup n` (`-I ∉ S`) is the range of the
group-average projector `P_S = codeProjector S` (Hermitian and idempotent).

* `stabilizerDistilledVec S` — the distilled state: `(P_S ⊗ I)|m⟩`, obtained by projecting **one**
  half of the maximally entangled state onto the code space. This is the (unnormalised) maximally
  entangled state on `V_S`, i.e. the encoded `|β₀₀⟩^⊗m`.
* `stabilizerDistilledVec_eq_vec_transpose` — its explicit closed form `(P_S)ᵀ.vec`.
* `stabilizerDistilledVec_bothHalves` — **matched syndromes:** the *physical* operation of
  projecting **both** halves (`P_S ⊗ P̄_S`, the conjugate `P̄_S` on Bob's half being how identical
  measurements act on the second leg of `|m⟩` — the transpose trick) collapses to the single-sided
  projection `stabilizerDistilledVec S`. Identical generator measurements plus Pauli correction on
  the two halves land both in the *same* code space, so a single projection already captures the
  joint outcome.
* `stabilizerDistilledVec_normSq` — its squared norm is `tr(P_S)`.
* `stabilizerDistilledVec_normSq_eq_two_pow` — for an `[n, m]` code (`|S| = 2ⁿ⁻ᵐ`) the squared norm
  is `2ᵐ`. Since the (unnormalised) maximally entangled state on a `d`-dimensional space has squared
  norm `d`, this identifies `stabilizerDistilledVec S` as the maximally entangled state on the
  `2ᵐ`-dimensional code space — precisely `m` encoded Bell pairs, the encoded `|β₀₀⟩^⊗m`.

The proof reuses the transpose-trick/projector vector identities for `maxEntVec` (N&C Ex 12.34
kernel, `MaxEntVec.lean`) together with the existing Chapter 10 stabilizer infrastructure
(`codeProjector` Hermitian/idempotent, and the trace value `codeProjector_trace_eq` in
`AxQM/Concrete/StabilizerCodeDistance.lean`), rather than constructing an explicit encoding isometry
for a general stabilizer code.

## The exercise (part b) — error robustness

N&C: *"Also show that if the stabilizer code corrects up to `δn` errors, then even if `δn` errors
are suffered by an `n`-qubit half, we still obtain `|β₀₀⟩^⊗m`."* We formalise this as an **exact
recovery up to a global phase**. Suppose one half suffers a Pauli error `E` (weight `≤ δn`), and the
syndrome-based recovery applies a Pauli correction `C` with the *same syndrome* as `E`
(`C * E ∈ N(S)`, so the residual `C · E` commutes with `S`, i.e. has trivial syndrome) whose weight
is below the code distance (`weight (C · E) < d`, automatic when the code corrects `δn = t` errors,
`d ≥ 2t + 1`, and `weight C, weight E ≤ t`). Then, after the error and correction, the same
two-sided stabiliser measurement of part (a) returns the distilled state up to a **unit phase**:

* `exists_norm_one_codeProjector_conj_toMat_of_mem_normalizer_of_weight_lt` — the algebraic core (in
  `StabilizerCodeDistance.lean`, beside its `exists_codeProjector_conj_smul_of_weight_lt` sibling):
  a below-distance normalizer element `q` conjugates `P` to a *unit* phase multiple,
  `P (toMat q) P = c • P` with `‖c‖ = 1` (a fourth root of unity `iˢ`). This sharpens
  `exists_codeProjector_conj_smul_of_weight_lt`, whose scalar can be `0` for `q ∉ N(S)`; the unit
  modulus is exactly what rules out the state being annihilated, certifying genuine recovery.
* `stabilizerDistilledVec_error_corrected` — the recovery: `(P · C · E ⊗ P̄)|m⟩ = c • distilled`,
  `‖c‖ = 1`. Since the recovered vector is a unit-modulus multiple of the distilled state, it is the
  *same* (unnormalised) maximally entangled state on `V_S` — the encoded `|β₀₀⟩^⊗m`. The transpose
  trick turns the clean half's conjugate projector `P̄` into a second `P` on the errored half,
  yielding the sandwich `P (C·E) P` that the core lemma collapses to `c • P`.
* `stabilizerDistilledVec_error_corrected_of_weight_le` — the textbook parameters: for an `[n, m]`
  code correcting `t = δn` errors (`d ≥ 2t + 1`) and error/correction of weight `≤ t` with matched
  syndromes, the residual has weight `≤ 2t < d`, so recovery is exact up to phase.
-/

open Matrix
open scoped Kronecker Matrix

namespace AxQM.Concrete

variable {n : ℕ} {S : Subgroup (PauliGroup n)} [Fintype ↥S]

/-- The **distilled entangled state** of `n` EPR pairs by the stabilizer code with stabilizer `S`:
the maximally entangled vector `|m⟩ = maxEntVec (Fin n → Fin 2) ℂ` with **one** half projected onto
the code space `V_S = range (codeProjector S)`, i.e. `(P_S ⊗ I)|m⟩`. This is the (unnormalised)
maximally entangled state on `V_S`; for an `[n, m]` stabilizer code `V_S` is `2ᵐ`-dimensional, so
this is the encoded `|β₀₀⟩^⊗m` of Nielsen & Chuang, Exercise 12.34(a). -/
noncomputable def stabilizerDistilledVec (S : Subgroup (PauliGroup n)) [Fintype ↥S] :
    (Fin n → Fin 2) × (Fin n → Fin 2) → ℂ :=
  (codeProjector S ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)).mulVec
    (maxEntVec (Fin n → Fin 2) ℂ)

/-- **Closed form of the distilled state.** Projecting one half of the maximally entangled vector
onto the code space gives the vectorisation of the transposed code projector:
`stabilizerDistilledVec S = (codeProjector S)ᵀ.vec`. As `codeProjector S` is the projector onto
`V_S`, this is the (unnormalised) maximally entangled state on `V_S`. -/
theorem stabilizerDistilledVec_eq_vec_transpose :
    stabilizerDistilledVec S = (codeProjector S)ᵀ.vec := by
  unfold stabilizerDistilledVec
  rw [kronecker_mulVec_maxEntVec, one_mul]

/-- **Matched syndromes (identical measurements on both halves = one code-space projection).**
The physical operation of Exercise 12.34(a) — identical stabilizer-generator measurements on the
two `n`-qubit halves plus Pauli correction — projects **both** halves of the maximally entangled
state onto the code space. On the second (Bob) leg identical measurements act as the entrywise
conjugate `(codeProjector S).map star = (codeProjector S)̄` (the transpose trick for `|m⟩`). By the
ricochet identity for a Hermitian idempotent projector this two-sided projection collapses to the
single-sided `stabilizerDistilledVec S`: both halves land in the *same* code space. -/
theorem stabilizerDistilledVec_bothHalves :
    (codeProjector S ⊗ₖ (codeProjector S).map star).mulVec (maxEntVec (Fin n → Fin 2) ℂ)
      = stabilizerDistilledVec S :=
  kronecker_map_star_mulVec_maxEntVec_of_isHermitian_of_isIdempotent
    codeProjector_isHermitian codeProjector_mul_self

/-- **Squared norm of the distilled state.** The distilled maximally entangled state on the code
space has squared norm `⟨distilled|distilled⟩ = tr(codeProjector S)`, the sesquilinear pairing
`star _ ⬝ᵥ _` being the standard bra–ket inner product. (Direct specialisation of the projected
maximally entangled vector's norm identity to `P = codeProjector S`.) -/
theorem stabilizerDistilledVec_normSq :
    star (stabilizerDistilledVec S) ⬝ᵥ stabilizerDistilledVec S = (codeProjector S).trace :=
  star_kronecker_one_mulVec_maxEntVec_dotProduct_self_of_isHermitian_of_isIdempotent
    codeProjector_isHermitian codeProjector_mul_self

/-- **The distilled state is the encoded `|β₀₀⟩^⊗m`.** For an `[n, m]` stabilizer code — `m ≤ n`
logical qubits, so the stabilizer has `n - m` generators and order `|S| = 2ⁿ⁻ᵐ` — the distilled
state has squared norm `2ᵐ`. Since the (unnormalised) maximally entangled state on a
`d`-dimensional space has squared norm `d`, this exhibits `stabilizerDistilledVec S` as the
maximally entangled state on the `2ᵐ`-dimensional code space `V_S`: `m` encoded Bell pairs, i.e. the
encoded `|β₀₀⟩^⊗m` of Nielsen & Chuang, Exercise 12.34(a). -/
theorem stabilizerDistilledVec_normSq_eq_two_pow {m : ℕ} (hneg : PauliGroup.negOne n ∉ S)
    (hmn : m ≤ n) (hcard : Fintype.card ↥S = 2 ^ (n - m)) :
    star (stabilizerDistilledVec S) ⬝ᵥ stabilizerDistilledVec S = 2 ^ m := by
  have h2 : (2 : ℂ) ^ n = 2 ^ (n - m) * 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
  rw [stabilizerDistilledVec_normSq, codeProjector_trace_eq hneg, hcard]
  push_cast
  rw [h2, inv_mul_cancel_left₀ (pow_ne_zero _ two_ne_zero)]

/-! ### Part (b): error robustness — a below-distance error on one half is corrected -/

/-- **Part (b): a below-distance Pauli error on one half is corrected — the distilled state is
recovered up to a global phase.** Suppose one `n`-qubit half of the `n` EPR pairs suffers a Pauli
error `E`, and the syndrome-based recovery applies a Pauli correction `C` with the *same syndrome*
(`C * E ∈ N(S)`: `C` and `E` commute identically with `S`, so the residual `C · E` has trivial
syndrome) whose weight is below the code distance (`weight (C · E) < d`). Then the identical
two-sided stabiliser measurement of part (a) — `P` on the corrected half, its entrywise conjugate
`P̄ = P.map star` on the clean half (as in `stabilizerDistilledVec_bothHalves`) — performed after
the error `E` and correction `C` returns the distilled state up to a **unit-modulus phase** `c`
(`‖c‖ = 1`):

`(P · C · E ⊗ P̄) |m⟩ = c • stabilizerDistilledVec S`.

Because `‖c‖ = 1`, the recovered vector is the *same* (unnormalised) maximally entangled state on
the code space `V_S` as the error-free distilled state — the encoded `|β₀₀⟩^⊗m` of
Exercise 12.34(a) — so
"even if `δn` errors are suffered by an `n`-qubit half, we still obtain `|β₀₀⟩^⊗m`". The transpose
trick (`kronecker_mulVec_maxEntVec` with `map_star_eq_transpose_of_isHermitian`) sends the clean
half's conjugate projector `P̄` to a second `P` on the errored half, producing the sandwich
`P (C·E) P`, which the below-distance conjugation lemma collapses to `c • P`. By the symmetry of
`|m⟩` the same holds with the two halves exchanged. -/
theorem stabilizerDistilledVec_error_corrected {E C : PauliGroup n}
    (hsynd : C * E ∈ Subgroup.normalizer S)
    (hw : ((C * E).weight : ℕ∞) < stabilizerCodeDistance S) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ((codeProjector S * C.toMat * E.toMat) ⊗ₖ (codeProjector S).map star).mulVec
          (maxEntVec (Fin n → Fin 2) ℂ)
        = c • stabilizerDistilledVec S := by
  obtain ⟨c, hcnorm, hc⟩ :=
    exists_norm_one_codeProjector_conj_toMat_of_mem_normalizer_of_weight_lt hsynd hw
  refine ⟨c, hcnorm, ?_⟩
  have hmat : (codeProjector S).map star * (codeProjector S * C.toMat * E.toMat)ᵀ
      = c • (codeProjector S)ᵀ := by
    rw [map_star_eq_transpose_of_isHermitian codeProjector_isHermitian, ← Matrix.transpose_mul,
      ← Matrix.transpose_smul]
    refine congrArg Matrix.transpose ?_
    rw [mul_assoc (codeProjector S) C.toMat E.toMat, ← PauliGroup.toMat_mul]
    exact hc
  rw [kronecker_mulVec_maxEntVec, hmat, Matrix.vec_smul,
    ← stabilizerDistilledVec_eq_vec_transpose]

/-- **Part (b) in the textbook's parameters.** For an `[n, m]` stabilizer code correcting up to
`t = δn` errors — distance at least `2t + 1` (`hdist`) — if a Pauli error `E` of weight `≤ t` is
suffered by one `n`-qubit half and the syndrome-based correction `C` also has weight `≤ t` and the
same syndrome (`C * E ∈ N(S)`), then the distilled state is recovered up to a unit-modulus phase:
"even if `δn` errors are suffered by an `n`-qubit half, we still obtain `|β₀₀⟩^⊗m`". The residual
`C · E` has weight `≤ weight C + weight E ≤ 2t < 2t + 1 ≤ d`, so
`stabilizerDistilledVec_error_corrected` applies. -/
theorem stabilizerDistilledVec_error_corrected_of_weight_le {E C : PauliGroup n} {t : ℕ}
    (hE : E.weight ≤ t) (hC : C.weight ≤ t)
    (hdist : (2 * t + 1 : ℕ∞) ≤ stabilizerCodeDistance S)
    (hsynd : C * E ∈ Subgroup.normalizer S) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ((codeProjector S * C.toMat * E.toMat) ⊗ₖ (codeProjector S).map star).mulVec
          (maxEntVec (Fin n → Fin 2) ℂ)
        = c • stabilizerDistilledVec S := by
  refine stabilizerDistilledVec_error_corrected hsynd (lt_of_lt_of_le ?_ hdist)
  exact_mod_cast (weight_mul_le C E).trans_lt (by omega)

end AxQM.Concrete
