/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BellReducedState

/-!
# Nielsen & Chuang, Exercise 2.75 (reduced density operators of the Bell states)

For each Bell state, find the reduced density operator for each qubit.

The four **Bell states** `|β_xy⟩` (`bellState x y`, Nielsen & Chuang §1.3.6 / §2.3) are the
maximally entangled two-qubit states `(|00⟩+|11⟩)/√2`, `(|01⟩+|10⟩)/√2`, `(|00⟩−|11⟩)/√2`,
`(|01⟩−|10⟩)/√2`.  For **every** one of them, tracing out either qubit yields the same answer: the
**maximally mixed** single-qubit state `I/2` (`maximallyMixedState qubit`).  N&C computes this
explicitly for `|β₀₀⟩` at eqs. (2.185)–(2.191); this file proves it uniformly for all four states
and both qubits.  The result is the hallmark of entanglement: the joint state `|β_xy⟩` is pure
(known exactly), yet each subsystem is in a completely mixed state (maximal ignorance).

The statements concern the `PureState` of a composite
system `qubit ⊗ qubit`, its density operator `PureState.toState` (`|ψ⟩⟨ψ|`), the reduced states
`State.reducedLeft` / `State.reducedRight` (partial trace, Postulate 4), and
`maximallyMixedState`:

* `bellState_reducedLeft` — `Tr_B|β_xy⟩⟨β_xy| = I/2` (reduced density operator of the **first**
  qubit is maximally mixed), for all `x, y`.
* `bellState_reducedRight` — `Tr_A|β_xy⟩⟨β_xy| = I/2` (reduced density operator of the **second**
  qubit is maximally mixed), for all `x, y`.

The Schmidt-decomposition computation — that both marginals equal `(1/2) I` at the operator level —
is `bellState_reducedLeft_op` / `bellState_reducedRight_op` in
`AxQM/Postulates/API/BellReducedState.lean` (with `maximallyMixedState` in
`AxQM/Postulates/API/MaximallyMixed.lean`).  Each theorem below follows by `State.ext` from its
`_op` counterpart via `maximallyMixedState_qubit_op`
(`(maximallyMixedState qubit).op = (1/2) I`, since `dim qubit = 2`).
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.75 (first qubit).** The reduced density operator of the first
qubit of any Bell state `|β_xy⟩` is the maximally mixed state `I/2`: `Tr_B|β_xy⟩⟨β_xy| =
maximallyMixedState qubit`, for all `x, y`.  Each Bell state is maximally entangled, so tracing out
the second qubit leaves the first in a state of maximal ignorance. -/
theorem bellState_reducedLeft (x y : Fin 2) :
    (bellState x y).toState.reducedLeft = maximallyMixedState qubit := by
  ext1
  rw [maximallyMixedState_qubit_op]
  exact bellState_reducedLeft_op x y

/-- **Nielsen & Chuang, Exercise 2.75 (second qubit).** The reduced density operator of the second
qubit of any Bell state `|β_xy⟩` is the maximally mixed state `I/2`: `Tr_A|β_xy⟩⟨β_xy| =
maximallyMixedState qubit`, for all `x, y`.  By the symmetry of the Bell states, tracing out the
first qubit likewise leaves the second maximally mixed. -/
theorem bellState_reducedRight (x y : Fin 2) :
    (bellState x y).toState.reducedRight = maximallyMixedState qubit := by
  ext1
  rw [maximallyMixedState_qubit_op]
  exact bellState_reducedRight_op x y

end AxQM
