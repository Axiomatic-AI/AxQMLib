/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Qudit
import AxQM.Concrete.QuantumFourierTransform
import ToMathlib.Analysis.CStarAlgebra.Matrix
import ToMathlib.Analysis.CStarAlgebra.ToEuclideanCLMSingle

/-!
# AxQM.Postulates.API — the quantum Fourier transform as a unitary evolution

The concrete `d`-dimensional quantum Fourier transform matrix
`Concrete.qftMatrix d` (Nielsen & Chuang eq. 5.2, `Fₖⱼ = (1/√d)·e^{2πijk/d}`, proved unitary in
`AxQM/Concrete/QuantumFourierTransform.lean`) is promoted here to a genuine unitary `Evolution`
of the qudit register `qudit d`, together with its action on computational-basis states, as used
in Nielsen & Chuang **Problem 5.1** (`AxQM/NC/Ch5/Problem5_1.lean`).

## What is formalised

* `qftEvolution d` — the **QFT as a unitary `Evolution (qudit d)`**, whose operator is the concrete
  matrix promoted through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`. Unitarity is
  transported from `Concrete.qftMatrix_mem_unitaryGroup` by `Unitary.map_mem`. That this typechecks
  as an `Evolution` is the content of N&C's remark that the QFT "is a unitary transformation, and
  thus can be implemented as the dynamics for a quantum computer."
* `qftEvolution_op_apply_quditBasis` — the **action (5.2)/(5.79)**
  `F|j⟩ = ∑ₖ (1/√d)·e^{2πijk/d} |k⟩`: the QFT sends the computational-basis state `|j⟩` to the
  explicit Fourier superposition. (`qftEvolution_op_apply_quditBasis_matrix` is the same in the
  compact `∑ₖ Fₖⱼ |k⟩` form using the raw matrix entry.)
* `qftFourierImage d j` — the **QFT image state** `∑ₖ (1/√d)·e^{2πijk/d} |k⟩` as a `PureState`
  in its own right (normalized, because it is the image of a unit vector under the unitary `F`).
* `qftEvolution_evolvePure_quditBasis` — the **pure-state form** of the action,
  `evolvePure F |j⟩ = qftFourierImage d j`: evolving `|j⟩` under the QFT yields the named image
  state. Stated for `evolvePure` and `quditBasis`, this
  is the result that Problem 5.1 specializes to `p` prime.

## Design notes

* **Unitarity transport.** `Matrix.toEuclideanCLM` is a `StarAlgEquiv`, hence a star-monoid
  homomorphism, so `Unitary.map_mem` carries `qftMatrix d ∈ unitary (Matrix …)` to
  `toEuclideanCLM (qftMatrix d) ∈ unitary (EuclideanSpace … →L …)`, which is precisely the
  `Evolution.unitary` obligation. No entrywise recomputation of `F†F = 1` is needed at the operator
  level — it is inherited from the matrix.
* **Action proof.** The compact action `qftEvolution_op_apply_quditBasis_matrix` is a direct
  instance of the general fact `Matrix.toEuclideanCLM_apply_single` — the `ToMathlib`
  lemma `toEuclideanCLM M |j⟩ = ∑ₖ Mₖⱼ |k⟩`, i.e. the operator sends a computational-basis vector to
  the matrix column, proved entrywise via `Matrix.ofLp_toEuclideanCLM`. The statements are
  phrased over `(quditBasis _).vec` so that the `(qudit d).space` instances stay consistent.
* **General `d`.** The evolution, its unitarity, and the action all hold for every dimension
  `d ≥ 1`; Problem 5.1's restriction to `p` prime concerns only the *efficient gate-level circuit*,
  documented (not formalised) in `AxQM/NC/Ch5/Problem5_1.lean`. The statements here are in full
  generality.
-/

noncomputable section

namespace AxQM

open AxQM.Concrete

/-- The **quantum Fourier transform on `qudit d`** as a unitary `Evolution` (Nielsen & Chuang
eq. 5.2). Its operator is the concrete matrix `qftMatrix d` (entry `Fₖⱼ = (1/√d)·e^{2πijk/d}`)
promoted through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`; it is unitary because
`qftMatrix d` is (`Concrete.qftMatrix_mem_unitaryGroup`), transported by `Unitary.map_mem`. This is
the "dynamics for a quantum computer" realizing the transform. -/
def qftEvolution (d : ℕ) [NeZero d] : Evolution (qudit d) where
  op := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) (qftMatrix d)
  unitary :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)) (qftMatrix_mem_unitaryGroup d)

/-- The underlying operator of `qftEvolution d` is `Matrix.toEuclideanCLM (qftMatrix d)`. -/
@[simp]
theorem qftEvolution_op (d : ℕ) [NeZero d] :
    (qftEvolution d).op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) (qftMatrix d) := rfl

/-- **Action of the QFT on a computational-basis state, compact form:**
`F|j⟩ = ∑ₖ Fₖⱼ |k⟩` with `Fₖⱼ = qftMatrix d k j`. The `(quditBasis _).vec`-phrased instance of the
general fact `Matrix.toEuclideanCLM_apply_single` (`toEuclideanCLM M` acting on `|j⟩` is the
`j`-th column of `M`; here `M = qftMatrix d` and `|i⟩ = quditBasis i`). -/
theorem qftEvolution_op_apply_quditBasis_matrix (d : ℕ) [NeZero d] (j : Fin d) :
    (qftEvolution d).op (quditBasis j).vec
      = ∑ k : Fin d, (qftMatrix d k j) • (quditBasis k).vec :=
  Matrix.toEuclideanCLM_apply_single (qftMatrix d) j

/-- **Action of the QFT on a computational-basis state** (Nielsen & Chuang eq. 5.2, and eq. 5.79 of
Problem 5.1): `F|j⟩ = ∑ₖ (1/√d)·e^{2πijk/d} |k⟩`. Unfolds the matrix entry of
`qftEvolution_op_apply_quditBasis_matrix` to its literal exponential form (`qftMatrix_apply`). -/
theorem qftEvolution_op_apply_quditBasis (d : ℕ) [NeZero d] (j : Fin d) :
    (qftEvolution d).op (quditBasis j).vec
      = ∑ k : Fin d, ((Real.sqrt d : ℂ)⁻¹
          * Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / d))
          • (quditBasis k).vec := by
  rw [qftEvolution_op_apply_quditBasis_matrix]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [qftMatrix_apply]

/-- The **quantum Fourier image state** `F|j⟩ = ∑ₖ (1/√d)·e^{2πijk/d} |k⟩` of the
computational-basis state `|j⟩`, as a `PureState` of `qudit d` (N&C eq. 5.2 / 5.79).
It is normalized because it is the image `(qftEvolution d).op |j⟩` of a unit vector under the
unitary `F` (`Evolution.norm_op_apply`, `quditBasis` normalized). -/
def qftFourierImage (d : ℕ) [NeZero d] (j : Fin d) : PureState (qudit d) where
  vec := ∑ k : Fin d, ((Real.sqrt d : ℂ)⁻¹
      * Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / d)) • (quditBasis k).vec
  normalized := by
    rw [← qftEvolution_op_apply_quditBasis d j, (qftEvolution d).norm_op_apply]
    exact (quditBasis j).normalized

/-- The underlying vector of `qftFourierImage d j` is the explicit Fourier superposition
`∑ₖ (1/√d)·e^{2πijk/d} |k⟩` (Nielsen & Chuang eq. 5.79). -/
@[simp]
theorem qftFourierImage_vec (d : ℕ) [NeZero d] (j : Fin d) :
    (qftFourierImage d j).vec
      = ∑ k : Fin d, ((Real.sqrt d : ℂ)⁻¹
          * Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / d)) • (quditBasis k).vec :=
  rfl

/-- **The QFT evolution sends `|j⟩` to the Fourier image state** (pure-state form of
Nielsen & Chuang eq. 5.2 / 5.79): `evolvePure F |j⟩ = qftFourierImage d j`. Stated for
`Evolution.evolvePure` and `quditBasis`, this is the statement that Problem 5.1 specializes to
`p` prime. -/
theorem qftEvolution_evolvePure_quditBasis (d : ℕ) [NeZero d] (j : Fin d) :
    (qftEvolution d).evolvePure (quditBasis j) = qftFourierImage d j := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, qftFourierImage_vec, qftEvolution_op_apply_quditBasis]

end AxQM
