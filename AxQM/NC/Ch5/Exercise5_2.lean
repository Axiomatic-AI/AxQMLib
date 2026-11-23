/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuantumFourierTransform
import AxQM.Postulates.API.UniformSuperposition

/-!
# Nielsen & Chuang, Exercise 5.2 (Fourier transform of `|0…0⟩`)

Explicitly compute the Fourier transform of the n-qubit state |00...0>.

This computes a quantum evolution acting on a quantum state: the
quantum Fourier transform `F` (Nielsen & Chuang, eq. (5.2)) applied to the computational-basis
ground state `|0…0⟩`. Here `F` is the unitary `Evolution` `AxQM.qftEvolution` (defined in
Problem 5.1) and `|0…0⟩` is the `PureState` `AxQM.quditBasis 0`.

## The computation

For the `n`-qubit register `N = 2ⁿ` and `F|j⟩ = N⁻¹ᐟ² ∑ₖ e^{2πijk/N}|k⟩` (the general action
`qftEvolution_evolvePure_quditBasis`, giving `qftFourierImage`). At `j = 0` **every phase is
trivial**, `e^{2πi·0·k/N} = e⁰ = 1`, so the Fourier superposition collapses to the equal-weight sum

```
        F|0…0⟩ = N⁻¹ᐟ² ∑ₖ |k⟩ = |+⟩^{⊗n},
```

the **equal (uniform) superposition** over all `N` computational-basis states
(`uniformSuperposition`). This is the explicit value asked for; the collapse of the phases is the
whole content of the computation. Equivalently, since `N = 2ⁿ`, this is the `n`-fold tensor
product of `|+⟩ = (|0⟩+|1⟩)/√2` — that tensor factorisation (N&C's
product representation) is not needed here.

## What is formalised

* `qftEvolution_evolvePure_quditBasis_zero` — Exercise 5.2, for a general `d`-level register
  (`qudit (2ⁿ)` is the `n`-qubit case): `F|0⟩ = |s⟩`, i.e.
  `(qftEvolution d).evolvePure (quditBasis 0) = uniformSuperposition d`.
* `qftEvolution_evolvePure_quditBasis_zero_two_pow` — the `n`-qubit specialisation `d = 2ⁿ`,
  making the "`n`-qubit state `|00…0⟩`" of the exercise text explicit.

The QFT definitions (`qftEvolution`, `qftFourierImage`, the action (5.2)) are in
`AxQM/Postulates/API/QuantumFourierTransform.lean` (Problem 5.1); this file adds only the
`j = 0` specialisation, whose point is that the exponential phases vanish.
-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 5.2.** The quantum Fourier transform sends the computational-basis
ground state `|0⟩` of the register `qudit d` to the equal (uniform) superposition `N⁻¹ᐟ² ∑ₖ |k⟩`
(`N = d`):

```
        F|0…0⟩ = uniformSuperposition d.
```

Stated for a general `d`-level register; the `n`-qubit case `|00…0⟩` is `d = 2ⁿ`
(`qftEvolution_evolvePure_quditBasis_zero_two_pow`). The proof takes the general QFT action
`qftEvolution_evolvePure_quditBasis` (`F|0⟩ = qftFourierImage d 0`) and simplifies each amplitude:
at `j = 0` the phase `e^{2πi·0·k/d} = 1`, so every coefficient is `N⁻¹ᐟ²` and the Fourier image is
the equal superposition. -/
theorem qftEvolution_evolvePure_quditBasis_zero (d : ℕ) [NeZero d] :
    (qftEvolution d).evolvePure (quditBasis (0 : Fin d)) = uniformSuperposition d := by
  rw [qftEvolution_evolvePure_quditBasis]
  apply PureState.ext
  rw [qftFourierImage_vec, uniformSuperposition_vec, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp

/-- **Exercise 5.2 for an `n`-qubit register** (`d = 2ⁿ`): the quantum Fourier transform of the
`n`-qubit ground state `|00…0⟩` is the equal superposition over all `2ⁿ` computational-basis states.
The direct specialisation of `qftEvolution_evolvePure_quditBasis_zero` to the dimension `2ⁿ` named
in the exercise text. -/
theorem qftEvolution_evolvePure_quditBasis_zero_two_pow (n : ℕ) :
    (qftEvolution (2 ^ n)).evolvePure (quditBasis (0 : Fin (2 ^ n)))
      = uniformSuperposition (2 ^ n) :=
  qftEvolution_evolvePure_quditBasis_zero (2 ^ n)

end AxQM
