/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.MeasurementTransport
import AxQM.Postulates.API.SquareRootMeasurement
import AxQM.Postulates.API.SchmidtReducedSpectrum
import AxQM.Postulates.API.ReducedStateOneFactor
import ToMathlib.Analysis.InnerProductSpace.PartialIsometryOrthonormal

/-!
# Born probabilities of the simulating measurement (Proposition 12.14, `hprob`)

The measurement-simulation step of **Nielsen & Chuang, Proposition 12.14** transports a measurement
`mB` that Bob performs on his factor `T` to a measurement Alice performs on her factor `S` — the
square-root measurement `mA = Measurement.ofPOVM (mB.transportPOVM W hW)` of the transported POVM
`{W Mⱼ† Mⱼ W†} ∪ {1 − W W†}` (`Postulates.API.MeasurementTransport`), where `W = crossSynthesis a b`
identifies Bob's Schmidt basis `b` with Alice's `a`. This file proves that Alice's simulation
**reproduces Bob's outcome probabilities** — the `hprob` hypothesis consumed by the general
`bobMeasure` closure case:

* Bob measuring `mB` on the right factor and Alice measuring `mA`'s outcome `some j` on the left
  factor give **equal Born probabilities** (`Measurement.bornProb_onLeft_ofPOVM_transportPOVM_eq`);
* the completeness **caveat outcome** `none` has **zero probability**
  (`Measurement.bornProb_onLeft_ofPOVM_transportPOVM_none_eq_zero`) — Alice's marginal lives on her
  Schmidt support `span a = range (W W†)`, so `1 − W W†` never fires.

The engine is a reusable, state-general bridge (`Measurement.bornProb_onLeft_reducedLeft` and its
right mirror): **the Born probability of a measurement on one factor equals the Born probability of
the same measurement on the reduced state of that factor**, `(m.onLeft T).bornProb ρ i = m.bornProb
ρ_A i`. Physically, measuring Alice's subsystem is measuring her reduced state; formally it is the
trace/partial-trace duality `tr[(Eᵢ ⊗ 1) ρ] = tr[Eᵢ ρ_A]`
(`LinearMap.trace_tensorMap_id_comp_eq_trace_comp_partialTraceRight`).

The two `hprob` facts then follow from the state identity `W† ρ_A W = ρ_B` (conjugation of the
reduced operators by the Schmidt-basis identification,
`InnerProductSpace.crossSynthesis_conj_diagonal` specialised to `c = λ²`): the `some j` Born
probability is `re tr[W Mⱼ† Mⱼ W† ρ_A] = re tr[Mⱼ† Mⱼ ρ_B]` by trace cyclicity, exactly Bob's; and
the `none` probability is `re tr[(1 − W W†) ρ_A] = tr[ρ_A] − tr[W W† ρ_A] = 1 − tr[ρ_B] = 0`.

-/

open scoped InnerProductSpace TensorProduct
open ContinuousLinearMap (adjoint)
open InnerProductSpace (crossSynthesis)

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] {S T : QSystem}

/-- **Born probability of a left-factor measurement equals the reduced-state Born probability.** For
a measurement `m` on `S` and a joint state `ρ` on `S ⊗ T`, measuring `m` on Alice's factor
(`m.onLeft T`) gives outcome `i` with the same probability as measuring `m` on Alice's reduced state
`ρ_A = tr_T ρ`: `(m.onLeft T).bornProb ρ i = m.bornProb ρ.reducedLeft i`. Physically, measuring a
subsystem is measuring its reduced state; formally it is the trace/partial-trace duality
`tr[(Mᵢ† Mᵢ ⊗ 1) ρ] = tr[Mᵢ† Mᵢ · ρ_A]`
(`LinearMap.trace_tensorMap_id_comp_eq_trace_comp_partialTraceRight`), after
`(Mᵢ ⊗ 1)† (Mᵢ ⊗ 1) = (Mᵢ† Mᵢ) ⊗ 1` (`TensorProduct.adjoint_mapL`, `mapL_mul`). -/
theorem Measurement.bornProb_onLeft_reducedLeft (m : Measurement ι S) (ρ : State (S ⊗ T)) (i : ι) :
    (m.onLeft T).bornProb ρ i = m.bornProb ρ.reducedLeft i := by
  rw [Measurement.bornProb_eq_re_trace_postOp, Measurement.bornProb_eq_re_trace_postOp,
    ContinuousLinearMap.trace_postOp, ContinuousLinearMap.trace_postOp]
  congr 1
  -- `(Mᵢ ⊗ 1)† (Mᵢ ⊗ 1) = (Mᵢ† Mᵢ) ⊗ 1` (the effect of the lifted measurement), exactly as in
  -- `Measurement.onLeft`'s completeness relation.  Proved for the *raw* `mapL` (whose adjoint uses
  -- the tensor inner-product instance) and bridged to the `QSystem.compose` space by `exact`
  -- (the two inner-product instances are defeq, but not syntactically equal — cf. `mapL` on the
  -- composite in `EnsemblePurification`).
  have hM : (adjoint ((m.onLeft T).op i)).comp ((m.onLeft T).op i)
      = TensorProduct.mapL ((adjoint (m.op i)).comp (m.op i)) (1 : T.space →L[ℂ] T.space) := by
    have h : (adjoint (TensorProduct.mapL (m.op i) (1 : T.space →L[ℂ] T.space))).comp
          (TensorProduct.mapL (m.op i) (1 : T.space →L[ℂ] T.space))
        = TensorProduct.mapL ((adjoint (m.op i)).comp (m.op i)) (1 : T.space →L[ℂ] T.space) := by
      rw [TensorProduct.mapL_adjoint_comp_self]
      congr 1
      rw [ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_comp]
    exact h
  rw [← ContinuousLinearMap.comp_assoc, hM, ← ContinuousLinearMap.comp_assoc]
  -- Trace/partial-trace duality on both sides; `ρ.reducedLeft.op = partialTraceRight ρ.op`.
  rw [State.reducedLeft_op]
  -- Restate over the generic tensor-product instances, where `toLinearMap_mapL` applies.
  let ρg : S.space ⊗[ℂ] T.space →L[ℂ] S.space ⊗[ℂ] T.space := ρ.op
  change LinearMap.trace ℂ (S.space ⊗[ℂ] T.space)
      (((TensorProduct.mapL ((adjoint (m.op i)).comp (m.op i)) (1 : T.space →L[ℂ] T.space)).comp
          ρg :
        S.space ⊗[ℂ] T.space →ₗ[ℂ] S.space ⊗[ℂ] T.space)) = _
  rw [ContinuousLinearMap.toLinearMap_comp, TensorProduct.toLinearMap_mapL,
    ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id]
  simp only [ContinuousLinearMap.toLinearMap_comp, LinearMap.coe_toContinuousLinearMap]
  exact LinearMap.trace_tensorMap_id_comp_eq_trace_comp_partialTraceRight
    (stdOrthonormalBasis ℂ T.space) _ _

/-- **Born probability of a right-factor measurement equals the reduced-state Born probability.**
The right-factor mirror of `Measurement.bornProb_onLeft_reducedLeft`: for a measurement `m` on `T`
and a joint state `ρ` on `S ⊗ T`, measuring `m` on Bob's factor (`m.onRight S`) gives outcome `i`
with the same probability as measuring `m` on Bob's reduced state `ρ_B = tr_S ρ`:
`(m.onRight S).bornProb ρ i = m.bornProb ρ.reducedRight i`. Same trace/partial-trace duality
(`LinearMap.trace_tensorMap_id_comp_eq_trace_comp_partialTraceLeft`) on the *left* factor. -/
theorem Measurement.bornProb_onRight_reducedRight (m : Measurement ι T) (ρ : State (S ⊗ T))
    (i : ι) :
    (m.onRight S).bornProb ρ i = m.bornProb ρ.reducedRight i := by
  rw [Measurement.bornProb_eq_re_trace_postOp, Measurement.bornProb_eq_re_trace_postOp,
    ContinuousLinearMap.trace_postOp, ContinuousLinearMap.trace_postOp]
  congr 1
  -- `(1 ⊗ Mᵢ)† (1 ⊗ Mᵢ) = 1 ⊗ (Mᵢ† Mᵢ)`.
  have hM : (adjoint ((m.onRight S).op i)).comp ((m.onRight S).op i)
      = TensorProduct.mapL (1 : S.space →L[ℂ] S.space) ((adjoint (m.op i)).comp (m.op i)) := by
    have h : (adjoint (TensorProduct.mapL (1 : S.space →L[ℂ] S.space) (m.op i))).comp
          (TensorProduct.mapL (1 : S.space →L[ℂ] S.space) (m.op i))
        = TensorProduct.mapL (1 : S.space →L[ℂ] S.space) ((adjoint (m.op i)).comp (m.op i)) := by
      rw [TensorProduct.mapL_adjoint_comp_self]
      congr 1
      rw [ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_comp]
    exact h
  rw [← ContinuousLinearMap.comp_assoc, hM, ← ContinuousLinearMap.comp_assoc]
  -- Trace/partial-trace duality on both sides; `ρ.reducedRight.op = partialTraceLeft ρ.op`.
  rw [State.reducedRight_op]
  -- Restate over the generic tensor-product instances, where `toLinearMap_mapL` applies.
  let ρg : S.space ⊗[ℂ] T.space →L[ℂ] S.space ⊗[ℂ] T.space := ρ.op
  change LinearMap.trace ℂ (S.space ⊗[ℂ] T.space)
      (((TensorProduct.mapL (1 : S.space →L[ℂ] S.space) ((adjoint (m.op i)).comp (m.op i))).comp
          ρg :
        S.space ⊗[ℂ] T.space →ₗ[ℂ] S.space ⊗[ℂ] T.space)) = _
  rw [ContinuousLinearMap.toLinearMap_comp, TensorProduct.toLinearMap_mapL,
    ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id]
  simp only [ContinuousLinearMap.toLinearMap_comp, LinearMap.coe_toContinuousLinearMap]
  exact LinearMap.trace_tensorMap_id_comp_eq_trace_comp_partialTraceLeft
    (stdOrthonormalBasis ℂ S.space) _ _

/-- **The Schmidt-basis identification conjugates Alice's marginal to Bob's.** For a bipartite pure
state `ψ` in Schmidt form `|ψ⟩ = ∑ᵢ lᵢ |aᵢ⟩|bᵢ⟩`, the cross-synthesis partial isometry
`W = crossSynthesis a b` (identifying `bᵢ ↦ aᵢ`) satisfies `W† ρ_A W = ρ_B`, where
`ρ_A = tr_T|ψ⟩⟨ψ|` and `ρ_B = tr_S|ψ⟩⟨ψ|`.  Both marginals are diagonal in their Schmidt bases
with the *same* eigenvalues `λᵢ²` (`reducedLeft_op_eq_sum_rankOne`,
`reducedRight_op_eq_sum_rankOne`), so this is the diagonal-conjugation identity
`InnerProductSpace.crossSynthesis_conj_diagonal` (with `c = λ²`) read on the reduced operators —
the state identity behind Proposition 12.14's Born-probability matching. -/
theorem PureState.adjoint_crossSynthesis_reducedLeft_conj {n : ℕ} (ψ : PureState (S ⊗ T))
    {l : Fin n → ℝ} {a : Fin n → S.space} {b : Fin n → T.space} (ha : Orthonormal ℂ a)
    (hb : Orthonormal ℂ b) (hψ : ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i) :
    (adjoint (crossSynthesis ℂ a b)).comp
        (ψ.toState.reducedLeft.op.comp (crossSynthesis ℂ a b))
      = ψ.toState.reducedRight.op := by
  rw [ψ.reducedLeft_op_eq_sum_rankOne hb hψ, ψ.reducedRight_op_eq_sum_rankOne ha hψ,
    InnerProductSpace.adjoint_crossSynthesis a b, ← InnerProductSpace.adjoint_crossSynthesis b a]
  exact InnerProductSpace.crossSynthesis_conj_diagonal b ha _

/-- **Born-probability matching (Proposition 12.14, `hprob`).** For a bipartite pure state `ψ` on
`S ⊗ T` in Schmidt form `|ψ⟩ = ∑ᵢ lᵢ |aᵢ⟩|bᵢ⟩`, Alice's square-root simulation measurement
`ofPOVM (mB.transportPOVM W hW)` (with `W = crossSynthesis a b`) reproduces Bob's outcome
probabilities: measuring its outcome `some j` on Alice's factor `S` has the same Born probability as
Bob measuring `mB` and obtaining `j` on his factor `T`.

By the reduced-state Born bridges, both probabilities are traces against the marginals:
`re tr[(W Mⱼ† Mⱼ W†) ρ_A]` (Alice) and `re tr[Mⱼ† Mⱼ ρ_B]` (Bob).  The state identity
`W† ρ_A W = ρ_B` (`PureState.adjoint_crossSynthesis_reducedLeft_conj`) and one trace cyclicity
(`LinearMap.trace_comp_comm'`, moving `W` around the cycle) identify the two. -/
theorem Measurement.bornProb_onLeft_ofPOVM_transportPOVM_eq {n : ℕ} (mB : Measurement ι T)
    {ψ : PureState (S ⊗ T)} {l : Fin n → ℝ} {a : Fin n → S.space} {b : Fin n → T.space}
    (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b) (hψ : ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i)
    (hW : IsStarProjection ((crossSynthesis ℂ a b).comp (adjoint (crossSynthesis ℂ a b)))) (j : ι) :
    ((Measurement.ofPOVM (mB.transportPOVM (crossSynthesis ℂ a b) hW)).onLeft T).bornProb
        ψ.toState (some j)
      = (mB.onRight S).bornProb ψ.toState j := by
  have hconj := ψ.adjoint_crossSynthesis_reducedLeft_conj ha hb hψ
  set W := crossSynthesis ℂ a b with hWdef
  rw [(Measurement.ofPOVM (mB.transportPOVM W hW)).bornProb_onLeft_reducedLeft,
    mB.bornProb_onRight_reducedRight, Measurement.ofPOVM_bornProb_eq_re_trace,
    Measurement.transportPOVM_elements_some, Measurement.bornProb_eq_re_trace_postOp,
    ContinuousLinearMap.trace_postOp]
  congr 1
  -- Alice's side (`conv_lhs`, to avoid touching Bob's trace): trace cyclicity moves the leading `W`
  -- around the cycle, then the state identity `W† ρ_A W = ρ_B` collapses it to `(Mⱼ† Mⱼ) ρ_B`.
  conv_lhs => rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.trace_comp_comm', ← ContinuousLinearMap.toLinearMap_comp,
        ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_assoc, hconj]
  -- Bob's side: reassociate `Mⱼ† (Mⱼ ρ_B)` to `(Mⱼ† Mⱼ) ρ_B`.
  rw [← ContinuousLinearMap.comp_assoc]

/-- **The caveat outcome never fires (Proposition 12.14, `hprob`).** The completeness caveat outcome
`none` of Alice's simulation `ofPOVM (mB.transportPOVM W hW)` has Born probability zero on `ψ`: its
effect `1 − W W†` is the projector onto the orthogonal complement of Alice's Schmidt support, and
`ρ_A` lives on that support.  Concretely `re tr[(1 − W W†) ρ_A] = tr[ρ_A] − tr[W W† ρ_A]
= 1 − tr[ρ_B] = 0`, using `tr[W W† ρ_A] = tr[W† ρ_A W] = tr[ρ_B]` (cyclicity and the state
identity `W† ρ_A W = ρ_B`) and that both marginals are density operators
(`State.trace_op_eq_one`). -/
theorem Measurement.bornProb_onLeft_ofPOVM_transportPOVM_none_eq_zero {n : ℕ} (mB : Measurement ι T)
    {ψ : PureState (S ⊗ T)} {l : Fin n → ℝ} {a : Fin n → S.space} {b : Fin n → T.space}
    (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b) (hψ : ψ.vec = ∑ i, (l i : ℂ) • a i ⊗ₜ[ℂ] b i)
    (hW : IsStarProjection ((crossSynthesis ℂ a b).comp (adjoint (crossSynthesis ℂ a b)))) :
    ((Measurement.ofPOVM (mB.transportPOVM (crossSynthesis ℂ a b) hW)).onLeft T).bornProb
        ψ.toState none = 0 := by
  have hconj := ψ.adjoint_crossSynthesis_reducedLeft_conj ha hb hψ
  set W := crossSynthesis ℂ a b with hWdef
  rw [(Measurement.ofPOVM (mB.transportPOVM W hW)).bornProb_onLeft_reducedLeft,
    Measurement.ofPOVM_bornProb_eq_re_trace, Measurement.transportPOVM_elements_none]
  -- `tr[W W† ρ_A] = tr[ρ_B]` by cyclicity + the state identity.
  have hWW : LinearMap.trace ℂ S.space
        ↑((W.comp (adjoint W)).comp ψ.toState.reducedLeft.op)
      = LinearMap.trace ℂ T.space ↑ψ.toState.reducedRight.op := by
    conv_lhs => rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.trace_comp_comm', ← ContinuousLinearMap.toLinearMap_comp,
          ContinuousLinearMap.comp_assoc,
      hconj]
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.toLinearMap_sub, map_sub, hWW, ψ.toState.reducedLeft.trace_op_eq_one,
    ψ.toState.reducedRight.trace_op_eq_one, sub_self, map_zero]

end AxQM
