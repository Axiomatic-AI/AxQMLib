/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.AvgOutputTypicalSubspace
import AxQM.Postulates.API.SquareRootMeasurement
import ToMathlib.Analysis.InnerProductSpace.PrettyGoodMeasurement

/-!
# The pretty-good decoding measurement of a product-state codebook (N&C Thm 12.8, Box 12.5)

In Nielsen & Chuang's random-coding proof of the Holevo–Schumacher–Westmoreland theorem
(Theorem 12.8, Box 12.5, eq. (12.78)), Bob decodes the `n`-use channel output of a length-`n`
product-state codebook `w : Fin K → Fin n → α` with the **pretty-good (square-root) measurement** of
the conjugated projector family

`A_{M'} = P · P_{M'} · P`,

where `P = avgOutputTypicalProj …` is the average-output ε-typical subspace projector and
`P_{M'} = condTypicalSubspaceProj …` is the conditional typical projector of codeword `M'`.

## Main definition

* `AxQM.prettyGoodDecoder` — the measurement
  `Measurement.ofPOVM (POVM.prettyGood A)` on the `n`-fold output system `S ^⊗ₛ n`, with outcome
  `some M` decoding message `M` and `none` the inconclusive element.  The family positivity
  `0 ≤ A_{M'}` needed by `POVM.prettyGood` is `State.avgOutputTypicalProj_condTypical_conj_nonneg`.

It is used in the product-state code `ProductStateCode.prettyGood`.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  Theorem 12.8, Box 12.5, eq. (12.78).
-/

open scoped BigOperators

noncomputable section

namespace AxQM

variable {S : QSystem} {α : Type*} [Fintype α]

/-- **The pretty-good decoding measurement of a product-state codebook** (Nielsen & Chuang,
Theorem 12.8, Box 12.5, eq. (12.78)).  For an input ensemble `{pₐ, ρₐ}`, channel `E`, block length
`n`, entropy parameter `s`, threshold `ε`, and a codebook `w : Fin K → Fin n → α`, this is Bob's
decoding measurement `Measurement.ofPOVM (POVM.prettyGood A)` of the conjugated projector family
`A_{M'} = P · P_{M'} · P` — `P = avgOutputTypicalProj …` the average-output ε-typical projector,
`P_{M'} = condTypicalSubspaceProj …` the conditional typical projector of codeword `M'` — on the
`n`-fold output system, with `some M` decoding message `M` and `none` the inconclusive outcome.

The family positivity `0 ≤ A_{M'}` required by `POVM.prettyGood` is
`State.avgOutputTypicalProj_condTypical_conj_nonneg`. -/
def prettyGoodDecoder (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (E : State S → State S) (ρ : α → State S) (n : ℕ) (s ε : ℝ) {K : ℕ}
    (w : Fin K → Fin n → α) : Measurement (Option (Fin K)) (S.tensorPow n) :=
  Measurement.ofPOVM (POVM.prettyGood
    (fun M' => (State.avgOutputTypicalProj p hp hsum E ρ n ε).comp
      ((State.condTypicalSubspaceProj (fun i => E (ρ (w M' i))) s ε).comp
        (State.avgOutputTypicalProj p hp hsum E ρ n ε)))
    (fun M' => State.avgOutputTypicalProj_condTypical_conj_nonneg p hp hsum E ρ n ε
      (fun i => E (ρ (w M' i))) s ε))

end AxQM
