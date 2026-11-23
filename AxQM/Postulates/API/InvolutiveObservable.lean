/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.PauliTrotter
import AxQM.Postulates.API.Eigenstate
import AxQM.Concrete.PauliStringStdInvolution
import AxQM.Postulates.API.InvolutionPropagatorConjugation

/-!
# AxQM.Postulates.API — an involutive observable is a controllable unitary

The bridge that turns an **involutive
observable** — a self-adjoint operator `A` with `A² = I`, i.e. a Hermitian operator with eigenvalues
`±1` — into an `Evolution` (a unitary), so it can be *controlled*. This is exactly the promotion
Nielsen & Chuang invoke for Figure 10.13: the measurement circuit `(H ⊗ 1) · C(U) · (H ⊗ 1)` needs
its measured operator as a controllable unitary `U`, and "`M` is an arbitrary Hermitian operator
with eigenvalues `±1`" — products of Pauli operators included. The stabilizer syndrome circuits of
§10.5.8 (Exercise 10.60) feed each stabilizer generator through this bridge.

## What is provided

* `Observable.toEvolution` — the bridge: from `A : Observable S` and a proof `A.op * A.op = 1`,
  the `Evolution S` with operator `A.op`. Unitarity is immediate: `A` self-adjoint means
  `star A.op = A.op`, so `star A.op * A.op = A.op * A.op = 1` and likewise on the other side.
* `Observable.toEvolution_op` — its operator is `A.op` (definitional; a `simp` lemma).
* `Observable.toEvolution_hasEigenstate` — an eigenstate of the observable `A` (real eigenvalue
  `μ`) is an eigenstate of `A.toEvolution` (as the complex eigenvalue `μ`): the eigenvalue equation
  is the same, `A.op ψ = μ ψ`.
* `pauliStringHamiltonian_op_mul_self` — the honest (phase `+1`) Pauli-string observable
  `pauliStringHamiltonian g 1` is an involution: `(P_g)² = I`, from the matrix fact
  `Concrete.pauliStringStd_mul_self` through the `⋆`-algebra isomorphism `Matrix.toEuclideanCLM`.
-/

open scoped Matrix

namespace AxQM

variable {S : QSystem}

/-- **An involutive observable is a unitary evolution.** Given `A : Observable S` with `A² = I`
(`hA : A.op * A.op = 1`), the operator `A.op` is unitary — it is self-adjoint (Postulate 2), so
`star A.op = A.op` and `star A.op * A.op = A.op * A.op = 1`, and symmetrically `A.op * star A.op =
1`. Hence `A` promotes to an `Evolution` with the same operator. This is the "`M` is Hermitian with
eigenvalues `±1`, so `C(M)` makes sense" step of the Figure-10.13 operator-measurement circuit. -/
def Observable.toEvolution (A : Observable S) (hA : A.op * A.op = 1) : Evolution S where
  op := A.op
  unitary := by
    rw [Unitary.mem_iff]
    have hsa : star A.op = A.op := A.selfAdjoint
    rw [hsa]
    exact ⟨hA, hA⟩

@[simp]
theorem Observable.toEvolution_op (A : Observable S) (hA : A.op * A.op = 1) :
    (A.toEvolution hA).op = A.op := rfl

/-- **Eigenstates transport across `toEvolution`.** If `ψ` is an eigenstate of the observable `A`
with (real) eigenvalue `μ`, it is an eigenstate of the unitary `A.toEvolution hA` with (complex)
eigenvalue `μ`: both are the single equation `A.op ψ = μ ψ`. Since `A² = I`, the possible values of
`μ` are `±1`, matching a unitary's unit-circle spectrum. -/
theorem Observable.toEvolution_hasEigenstate {A : Observable S} (hA : A.op * A.op = 1) {μ : ℝ}
    {ψ : PureState S} (h : A.HasEigenstate μ ψ) : (A.toEvolution hA).HasEigenstate (μ : ℂ) ψ := h

/-- **An honest Pauli-string observable is an involution**: `(P_g)² = I` for
`P_g = pauliStringHamiltonian g 1`. Its operator is `Matrix.toEuclideanCLM (pauliStringStd g)`, and
that `⋆`-algebra isomorphism is multiplicative, so the square is
`Matrix.toEuclideanCLM (pauliStringStd g · pauliStringStd g) = Matrix.toEuclideanCLM I = I` by
`Concrete.pauliStringStd_mul_self`. -/
theorem pauliStringHamiltonian_op_mul_self {n : ℕ} (g : Fin n → Fin 4) :
    (pauliStringHamiltonian g 1).op * (pauliStringHamiltonian g 1).op = 1 := by
  unfold pauliStringHamiltonian
  simp only [Complex.ofReal_one, one_smul]
  -- `erw` bridges the definitional coercion between `(qudit (2^n)).space` and `EuclideanSpace ℂ _`.
  erw [← map_mul Matrix.toEuclideanCLM, Concrete.pauliStringStd_mul_self]
  exact map_one Matrix.toEuclideanCLM

/-- **The closed form of a Pauli-string Trotter summand (Nielsen & Chuang, Problem 4.3(3)).** For a
Pauli string `g : Fin n → Fin 4`, a real coefficient `c` and a real time `t`, the unit-`ℏ`
propagator of the Pauli-string Hamiltonian `c · g` is the explicit rotation
`exp(-i c t g) = cos(c t) · I - i sin(c t) · g`,
where `g = (pauliStringHamiltonian g 1).op` is the (involutive) unit-coefficient Pauli-string
operator. This is the concrete operator that Problem 4.3(3) asks to implement with `O(n)` one- and
two-qubit gates for `c = h_g`, `t = Δ = 1/k` — a genuine rotation whose axis is the Pauli string `g`
(`g² = I`, so the exponent's involution formula collapses the exponential to `cos - i sin`).

It is the direct specialisation of `Observable.propagator_op_of_op_eq_smul_involution` (the general
`H.op = c • G`, `G² = I` ⟹ propagator `= cos(ct)·1 − (sin(ct)·i)·G` law) at
`H = pauliStringHamiltonian g c`, `G = (pauliStringHamiltonian g 1).op`: the scalar factorisation
`H.op = c • G` is `pauliStringHamiltonian_op` (with `↑(1:ℝ) • G = G`), and the involution `G² = I`
is `pauliStringHamiltonian_op_mul_self`. -/
theorem pauliStringHamiltonian_propagator_op {n : ℕ} (g : Fin n → Fin 4) (c t : ℝ) :
    ((pauliStringHamiltonian g c).propagator 1 0 t).op
      = (Real.cos (c * t) : ℂ) • 1
        - ((Real.sin (c * t) : ℂ) * Complex.I) • (pauliStringHamiltonian g 1).op := by
  refine (pauliStringHamiltonian g c).propagator_op_of_op_eq_smul_involution ?_
    (pauliStringHamiltonian_op_mul_self g) t
  rw [pauliStringHamiltonian_op g 1, Complex.ofReal_one, one_smul]
  exact pauliStringHamiltonian_op g c

end AxQM
