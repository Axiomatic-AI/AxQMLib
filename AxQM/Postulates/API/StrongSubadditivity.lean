/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.Associator
import AxQM.Postulates.API.Entropy
import AxQM.Postulates.Composite
import ToMathlib.Analysis.InnerProductSpace.QuantumStrongSubadditivity

/-!
# AxQM — strong subadditivity of the von Neumann entropy (N&C Theorem 11.14)

For a tripartite quantum system `A ⊗ (B ⊗ C)` and a faithful state `ρ`, the von Neumann entropy
satisfies **strong subadditivity**

`S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)`

(Nielsen & Chuang, *Quantum Computation and Quantum Information*, Theorem 11.14, eq. (11.73)),
where the marginals are the reduced states

* `S(A,B,C) = S(ρ)` — the whole tripartite state;
* `S(B,C)   = S(ρ.reducedRight)` — trace out `A`;
* `S(B)     = S(ρ.reducedRight.reducedLeft)` — further trace out `C`;
* `S(A,B)   = S((ρ.congr (QSystem.assoc A B C)).reducedLeft)` — re-associate to `(A ⊗ B) ⊗ C`
  and trace out `C`.

Equivalently, the quantum mutual information is monotone under discarding `C`,
`I(A:B) ≤ I(A:BC)`.

## Relation to the operator-level theorem

The theorem is stated with the entropy `State.vonNeumannEntropy` and the reduced states
`State.reducedLeft`, `State.reducedRight`, `State.congr`. The faithfulness hypothesis is
`IsStrictlyPositive ρ.op`, as in the relative-entropy theorems it descends from
(`State.quantumRelativeEntropy_reduced_le`, etc.). It is the state-level form of the operator
theorem `ContinuousLinearMap.vonNeumannEntropy_add_partialTrace_le`.

## Faithfulness

As with Klein's inequality, joint convexity, and monotonicity under partial trace, the finite,
real-valued relative-entropy engine underlying the proof requires the states to be **faithful**
(strictly positive spectrum). The fully general (entropy-only) statement follows by a
continuity/limiting argument over faithful approximants, which needs von Neumann entropy continuity;
it is not formalised here.

## The other form of the theorem (N&C eq. (11.72))

N&C Theorem 11.14 also states the equivalent form `S(A) + S(B) ≤ S(A,C) + S(B,C)` (eq. (11.72)).
The two forms are equivalent, and deriving (11.72) from strong subadditivity is the content of the
separate **Exercise 11.24** (via purification and the equality of the entropies of
complementary subsystems of a pure state); it builds on this theorem rather than being re-proved.

## Main results

* `AxQM.State.vonNeumannEntropy_add_le_add` — strong subadditivity
  `S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)` for a faithful tripartite state.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A B C : QSystem}

/-- **Strong subadditivity of the von Neumann entropy** (Nielsen & Chuang, Theorem 11.14,
eq. (11.73)): for a faithful (strictly positive) state `ρ` on the tripartite system
`A ⊗ (B ⊗ C)`,

`S(A,B,C) + S(B) ≤ S(A,B) + S(B,C)`,

with the marginals read off as reduced states — `S(B,C) = S(ρ.reducedRight)` (trace out `A`),
`S(B) = S(ρ.reducedRight.reducedLeft)` (further trace out `C`), and
`S(A,B) = S((ρ.congr (QSystem.assoc A B C)).reducedLeft)` (re-associate to `(A ⊗ B) ⊗ C`, then
trace out `C`). Equivalently, the mutual information is monotone under discarding `C`,
`I(A:B) ≤ I(A:BC)`.

This is the state-level form of the operator theorem
`ContinuousLinearMap.vonNeumannEntropy_add_partialTrace_le`. Faithfulness
(`IsStrictlyPositive ρ.op`) is the finite-branch hypothesis of the relative-entropy engine (module
docstring). The equivalent form `S(A) + S(B) ≤ S(A,C) + S(B,C)` (eq. (11.72)) is Exercise 11.24. -/
theorem State.vonNeumannEntropy_add_le_add (ρ : State (A ⊗ (B ⊗ C)))
    (hρ : IsStrictlyPositive ρ.op) :
    ρ.vonNeumannEntropy + ρ.reducedRight.reducedLeft.vonNeumannEntropy ≤
      (ρ.congr (QSystem.assoc A B C)).reducedLeft.vonNeumannEntropy +
        ρ.reducedRight.vonNeumannEntropy := by
  -- Nontriviality of each factor (so the traced-out bases are nonempty), read off reduced states.
  have : Nontrivial A.space := ρ.reducedLeft.nontrivial_space
  have : Nontrivial B.space := ρ.reducedRight.reducedLeft.nontrivial_space
  have : Nontrivial C.space := ρ.reducedRight.reducedRight.nontrivial_space
  have : Nonempty (Fin (Module.finrank ℂ A.space)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  have : Nonempty (Fin (Module.finrank ℂ B.space)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  have : Nonempty (Fin (Module.finrank ℂ C.space)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  -- The three marginal identities the operator-level theorem consumes, discharged from the
  -- definitions. Each identity is definitional: the reduced states and transport unfold to exactly
  -- the operator-level partial-trace expressions (the `stdOrthonormalBasis` canonicalization
  -- matches).
  have hBC : LinearMap.partialTraceLeft (stdOrthonormalBasis ℂ A.space) ρ.op.toLinearMap =
      ρ.reducedRight.op.toLinearMap := rfl
  have hB : LinearMap.partialTraceRight (stdOrthonormalBasis ℂ C.space)
      ρ.reducedRight.op.toLinearMap = ρ.reducedRight.reducedLeft.op.toLinearMap := rfl
  have hAB : LinearMap.partialTraceRight (stdOrthonormalBasis ℂ C.space)
      ((TensorProduct.assocIsometry ℂ A.space B.space C.space).symm.conjStarAlgEquiv
        ρ.op).toLinearMap =
      (ρ.congr (QSystem.assoc A B C)).reducedLeft.op.toLinearMap := rfl
  have key := ContinuousLinearMap.vonNeumannEntropy_add_partialTrace_le
    (stdOrthonormalBasis ℂ A.space) (stdOrthonormalBasis ℂ B.space) (stdOrthonormalBasis ℂ C.space)
    ρ.isDensity hρ hAB hBC hB
  simp only [State.vonNeumannEntropy_def]
  exact key

end AxQM
