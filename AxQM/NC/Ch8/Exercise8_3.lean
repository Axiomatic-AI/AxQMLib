/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.EnvironmentModelOperatorSum

/-!
# Nielsen & Chuang, Exercise 8.3 (operator-sum with different input/output spaces)

*(N&C p. 361.)*

Show discarding subsystems after unitary interaction gives operator-sum form with ΣE_k†E_k=I.

Exercise 8.3 is the *different-input/output-space* generalization of the operator-sum
representation of §8.2.3. The operation elements `Eₖ` are linear maps
`(A ⊗ B).space →ₗ (B ⊗ C).space`, and the claim `↑E(ρ) = ∑ₖ Eₖ ρ Eₖ†`, `∑ₖ Eₖ† Eₖ = I` involves the
density operator `State.op` and `LinearMap` conjugation. Compare Exercise 8.2
(`AxQM/Postulates/API/MeasurementOperation.lean`).

## The formalisation

The formalisation is in `AxQM/Postulates/API/EnvironmentModelOperatorSum.lean`:

* `AxQM.envModelChannel` — the **channel** `E(ρ) = ρ'`, built
  as `((U.evolve (ρ ⊗ |ω⟩⟨ω|)).congr Φ).reducedLeft`. The system isomorphism
  `Φ = QSystem.interchangeBCAD` first regroups `(A ⊗ B) ⊗ (C ⊗ D)` into `(B ⊗ C) ⊗ (A ⊗ D)` so that
  `State.reducedLeft` (which traces out the *right* factor) discards exactly the `A ⊗ D` subsystem,
  leaving the output on `B ⊗ C`.
* `AxQM.envModelChannel_hasOperatorSum` — **the exercise:** the channel `E` has an
  operator-sum representation, i.e. there is a family of operation elements
  `Eₖ : (A ⊗ B).space →ₗ (B ⊗ C).space` with `E(ρ) = ∑ₖ Eₖ ρ Eₖ†` (eq. 8.15) **and**
  `∑ₖ Eₖ† Eₖ = I` (eq. 8.14, completeness / trace preservation), both witnessed by the *same*
  family, exactly as N&C requires. The operation elements are
  `Eₖ = ⟨eₖ| (W (· ⊗ ω)) = krausOp (stdOB (A ⊗ D).space) (W ∘ tmulRightVec ω.vec)`, with `eₖ` a
  basis of the discarded space `A ⊗ D` and `W = Φ ∘ U` the interaction-then-regrouping map; `W` is
  an isometry (`Φ` a system isomorphism, `U` unitary), which is what makes the family complete.

The proof instantiates the operator-sum infrastructure in
`ToMathlib/Analysis/InnerProductSpace/OperatorSum.lean`
(`LinearMap.partialTraceRight_conj_map_rankOne_eq_sum_krausOp` for eq. 8.15, N&C eqs. 8.9–8.10;
`LinearMap.sum_adjoint_krausOp_tmulRightVec_comp_krausOp` for eq. 8.14) after
bridging the constructions (`Evolution.evolve`, `State.tmul`, `PureState.toState`,
`State.congr`, `State.reducedLeft`) down to the joint dilation `W`. See the module docstring
there for the full argument.
-/
