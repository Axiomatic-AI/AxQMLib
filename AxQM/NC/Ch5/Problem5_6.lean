/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuantumFourierTransform
import AxQM.Postulates.API.InverseQuantumFourierTransform
import AxQM.Postulates.API.Qudit
import AxQM.Postulates.API.Evolution

/-!
# Nielsen & Chuang, Problem 5.6 (Addition by Fourier transforms)

*(N&C p. 244.)*

Addition by Fourier transforms: circuit for |x> -> |x+y mod 2^n> via QFT, phase shifts, inverse QFT.

## The construction

Constant addition is *diagonalized by the Fourier transform*. Adding `y` to the computational
index is a **translation** of the cyclic group `ℤ/dℤ`; conjugating a translation by the Fourier
transform turns it into a **multiplication operator** (a diagonal phase), which is exactly the
single-qubit phase-shift layer. Concretely, with `d = 2ⁿ` the circuit is
`QFT → phase shifts → inverse QFT`:

1. `F` : the quantum Fourier transform (`qftEvolution d`), sending
   `|x⟩ ↦ (1/√d) ∑ₖ e^{2πi xk/d} |k⟩`.
2. `D_y` : the diagonal **phase-shift** layer `fourierAddPhase d y`, imprinting the phase
   `e^{2πi yk/d}` on the `k`-th Fourier mode, i.e. `D_y|k⟩ = e^{2πi yk/d}|k⟩`. On the QFT of `|x⟩`
   it multiplies mode `k` by `e^{2πi yk/d}`, producing `(1/√d) ∑ₖ e^{2πi (x+y)k/d} |k⟩`, which is
   the QFT of `|x+y mod d⟩`.
3. `F⁻¹` : the inverse Fourier transform (`qftInverseEvolution d`), taking that back to the
   computational-basis state `|x+y mod d⟩`.

Composed, `A_y = F⁻¹ ∘ D_y ∘ F` (`additionByFourier d y`) sends `|x⟩ ↦ |x+y mod d⟩` — the exact
content of `additionByFourier_evolvePure_quditBasis` below. The `mod d` is automatic: the phase
`e^{2πi(x+y)k/d}` depends only on `(x+y) mod d` (integer multiples of `2πi` in the exponent are
invisible), so the wrap-around costs nothing.

The formalization is carried out for a **general dimension `d ≥ 1`**, not just `d = 2ⁿ`: the
identity `A_y = F⁻¹ D_y F` and its action `|x⟩ ↦ |x+y⟩` hold verbatim (with `+` the modular
addition of `Fin d`). The restriction to `d = 2ⁿ` is only what makes `D_y` a product of *single*
qubit phase gates, and hence the whole thing efficient — see the cost-model note.

## Answers to the questions (a cost-model annotation, not a theorem)

*What values of `y` can be added easily, and how many operations are required?* For `d = 2ⁿ`, the
diagonal phase `D_y` factorizes over the `n` qubits: writing `k = ∑ₗ kₗ 2^{n-ℓ}`, the phase
`e^{2πi yk/d} = ∏ₗ e^{2πi y kₗ / 2ˡ}` is a product of `n` **single-qubit** phase gates, one per
qubit `ℓ`, each rotating `|1⟩` by `e^{2πi y/2ˡ}` — this is the "single qubit phase shifts" step.
So **every fixed `y`** can be added this way with `n` single-qubit phase gates; `y = 1` (and small
`y`) are singled out because their angles `2π/2ˡ` are the standard rotation set. The total cost is
`Θ(n²)` operations, dominated by the `Θ(n²)` gates of the QFT and inverse QFT (the phase layer adds
only `n`). Gate counts and "efficiency" are claims in a circuit/complexity model the postulate
framework has no vocabulary to express (cf. Problem 5.1, Problem 4.1); they are recorded here, while
the verifiable content — that the circuit *correctly* realizes `|x⟩ ↦ |x+y mod d⟩` — is the theorem.

## What is formalized

* `fourierAddPhase d y` — the phase-shift layer `D_y`, `|k⟩ ↦ e^{2πi yk/d}|k⟩`, a `diagPhase`.
* `fourierAddPhase_hasEigenstate_quditBasis` — its eigenvalue action `D_y|k⟩ = e^{2πi yk/d}|k⟩`.
* `additionByFourier d y` — the circuit `A_y = F⁻¹ ∘ D_y ∘ F`.
* `fourierAddPhase_evolvePure_qft` — the key step: `D_y (F|x⟩) = F|x+y⟩` (the phase layer turns the
  Fourier transform of `|x⟩` into the Fourier transform of `|x+y⟩`).
* `additionByFourier_evolvePure_quditBasis` — **correctness**: `A_y |x⟩ = |x+y mod d⟩`.

-/

noncomputable section

namespace AxQM

/-- The **Fourier-basis phase-shift layer** `D_y` of Nielsen & Chuang Problem 5.6, on the register
`qudit d`: the diagonal gate imprinting the phase `e^{2πi yk/d}` on the `k`-th Fourier mode,
`D_y|k⟩ = e^{2πi yk/d}|k⟩`. Modelled as `diagPhase` with the angle `θ_k = 2π y k / d` (so
`e^{iθ_k} = e^{2πi yk/d}`). For `d = 2ⁿ` this diagonal unitary factorizes into `n` single-qubit
phase gates (the "single qubit phase shifts" step); the correctness proof needs only the diagonal
eigenvalue action, so it is stated for a general dimension `d`. -/
def fourierAddPhase (d : ℕ) (y : Fin d) : Evolution (qudit d) :=
  diagPhase (fun k => 2 * Real.pi * (y : ℕ) * (k : ℕ) / d)

/-- **Eigenvalue action of the phase-shift layer** (Nielsen & Chuang Problem 5.6): each
computational-basis state `|k⟩` is an eigenstate of `D_y = fourierAddPhase d y` with eigenvalue
`e^{2πi yk/d}`, `D_y|k⟩ = e^{2πi yk/d}|k⟩`. This is the diagonal eigenvalue action of `diagPhase`
(`diagPhase_op_apply_quditBasis`), with the angle `θ_k = 2π y k / d` rewritten into the phase
`e^{2πi yk/d}`. It is the "phase shift" content of the circuit: mode `k` is rotated by the phase
`e^{2πi yk/d}`. -/
theorem fourierAddPhase_hasEigenstate_quditBasis (d : ℕ) [NeZero d] (y k : Fin d) :
    (fourierAddPhase d y).HasEigenstate
      (Complex.exp (2 * Real.pi * Complex.I * ((y : ℕ) * (k : ℕ)) / d)) (quditBasis k) := by
  change (fourierAddPhase d y).op (quditBasis k).vec
      = Complex.exp (2 * Real.pi * Complex.I * ((y : ℕ) * (k : ℕ)) / d) • (quditBasis k).vec
  unfold fourierAddPhase
  rw [diagPhase_op_apply_quditBasis]
  congr 2
  push_cast
  ring

/-- The **Fourier-addition circuit** `A_y = F⁻¹ ∘ D_y ∘ F` of Nielsen & Chuang Problem 5.6, on the
register `qudit d`: the quantum Fourier transform `F` (`qftEvolution d`), then the single-qubit
phase-shift layer `D_y` (`fourierAddPhase d y`), then the inverse Fourier transform `F⁻¹`
(`qftInverseEvolution d`). It computes the constant addition `|x⟩ ↦ |x+y mod d⟩`
(`additionByFourier_evolvePure_quditBasis`). -/
def additionByFourier (d : ℕ) [NeZero d] (y : Fin d) : Evolution (qudit d) :=
  (qftInverseEvolution d).comp ((fourierAddPhase d y).comp (qftEvolution d))

/-- The Fourier-addition circuit is, by construction, the three-step composite
`A_y = F⁻¹ ∘ D_y ∘ F`. -/
theorem additionByFourier_eq_comp (d : ℕ) [NeZero d] (y : Fin d) :
    additionByFourier d y
      = (qftInverseEvolution d).comp ((fourierAddPhase d y).comp (qftEvolution d)) := rfl

/-- **The phase layer turns `F|x⟩` into `F|x+y⟩`** (the heart of Nielsen & Chuang Problem 5.6).
Applying the phase-shift layer `D_y` to the Fourier transform `F|x⟩` yields the Fourier transform
of `|x+y mod d⟩`: `D_y (F|x⟩) = F|x+y⟩`. Indeed `F|x⟩ = (1/√d) ∑ₖ e^{2πi xk/d}|k⟩`, and `D_y`
multiplies mode `k` by `e^{2πi yk/d}`, giving `(1/√d) ∑ₖ e^{2πi (x+y)k/d}|k⟩`; since the exponential
depends only on `(x+y) mod d` (integer multiples of `2πi` drop out,
`Complex.exp_nat_mul_two_pi_mul_I`), this is
exactly `F|(x+y) mod d⟩`, and `Fin` addition already reduces mod `d`. -/
theorem fourierAddPhase_evolvePure_qft (d : ℕ) [NeZero d] (x y : Fin d) :
    (fourierAddPhase d y).evolvePure ((qftEvolution d).evolvePure (quditBasis x))
      = (qftEvolution d).evolvePure (quditBasis (x + y)) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  -- Periodicity of the Fourier phase in the index: `e^{2πi m k/d}` depends only on `m mod d`,
  -- because `m = (m % d) + d·(m / d)` and the `d·(m/d)` part contributes `e^{2πi·(integer)} = 1`.
  have hper : ∀ (m : ℕ) (k : Fin d),
      Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) * (k : ℕ)) / d)
        = Complex.exp (2 * Real.pi * Complex.I * (((m % d : ℕ) : ℂ) * (k : ℕ)) / d) := by
    intro m k
    rw [show (2 * Real.pi * Complex.I * ((m : ℂ) * (k : ℕ)) / d)
          = (2 * Real.pi * Complex.I * (((m % d : ℕ) : ℂ) * (k : ℕ)) / d)
            + (((m / d) * (k : ℕ) : ℕ) : ℂ) * (2 * Real.pi * Complex.I) by
        have hmod : (m : ℂ) = ((m % d : ℕ) : ℂ) + (d : ℂ) * ((m / d : ℕ) : ℂ) := by
          exact_mod_cast (Nat.mod_add_div m d).symm
        rw [hmod]; push_cast; field_simp]
    rw [Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  -- The diagonal eigenvalue action of `D_y` as an equation of vectors (from the eigenstate lemma).
  have hD : ∀ k : Fin d, (fourierAddPhase d y).op (quditBasis k).vec
      = Complex.exp (2 * Real.pi * Complex.I * ((y : ℕ) * (k : ℕ)) / d) • (quditBasis k).vec :=
    fun k => fourierAddPhase_hasEigenstate_quditBasis d y k
  apply PureState.ext
  rw [Evolution.evolvePure_vec, Evolution.evolvePure_vec, Evolution.evolvePure_vec,
    qftEvolution_op_apply_quditBasis, qftEvolution_op_apply_quditBasis, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, hD k, smul_smul]
  refine congrArg (· • _) ?_
  rw [mul_assoc, ← Complex.exp_add, Fin.val_add, ← hper ((x : ℕ) + (y : ℕ)) k]
  congr 2
  push_cast
  ring

/-- **Nielsen & Chuang, Problem 5.6 (correctness):** the Fourier-addition circuit
`A_y = F⁻¹ ∘ D_y ∘ F` computes constant addition `|x⟩ ↦ |x+y mod d⟩`:
`(additionByFourier d y).evolvePure |x⟩ = |x+y⟩` (with `+` the modular addition of `Fin d`).

The proof unfolds the composite into `F`, `D_y`, `F⁻¹` (`Evolution.evolvePure_comp`): `F` produces
the Fourier transform of `|x⟩`, the phase layer turns it into the Fourier transform of `|x+y⟩`
(`fourierAddPhase_evolvePure_qft`), and `F⁻¹` inverts `F` (since `qftInverseEvolution d` is
`(qftEvolution d).adjoint` by definition, via `Evolution.evolvePure_adjoint_evolvePure`), returning
`|x+y⟩`. This is the postulate-level content of "QFT, then phase shifts, then inverse QFT adds `y`";
the efficiency of the gate decomposition (`Θ(n²)` for `d = 2ⁿ`) is the cost-model annotation in the
module docstring. -/
theorem additionByFourier_evolvePure_quditBasis (d : ℕ) [NeZero d] (x y : Fin d) :
    (additionByFourier d y).evolvePure (quditBasis x) = quditBasis (x + y) := by
  rw [additionByFourier_eq_comp, Evolution.evolvePure_comp, Evolution.evolvePure_comp,
    fourierAddPhase_evolvePure_qft]
  exact Evolution.evolvePure_adjoint_evolvePure (qftEvolution d) (quditBasis (x + y))

end AxQM
