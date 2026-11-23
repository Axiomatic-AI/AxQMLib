/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PlusStateTensorPower

/-!
# Nielsen & Chuang, Exercise 2.26

Write out |psi>^{tensor2} and ^{tensor3} for |psi>=(|0>+|1>)/sqrt2.

The formalisation is in `AxQM/Concrete/PlusStateTensorPower.lean`. The state
`|ψ⟩` is the `X`-eigenvector `|+⟩` (`AxQM.Concrete.xPlus`), identified with
N&C's form by `AxQM.Concrete.xPlus_eq_smul_add : |+⟩ = (1/√2) · (|0⟩ + |1⟩)`.
The Kronecker product of column vectors is `AxQM.Concrete.vecKron`
(`(u ⊗ v) (i, j) = uᵢ · vⱼ`), whose basis kets `vecKron (ket i) (ket j)` are the
tensor-product basis states `|i⟩|j⟩`. The two requested representations are recorded as
separate theorems for each power:

* `AxQM.Concrete.vecKron_xPlus_xPlus` — `|ψ⟩^⊗2` **via the Kronecker product**:
  the explicit uniform column vector `½(1, 1, 1, 1)ᵀ` (every entry `1/2`).
* `AxQM.Concrete.vecKron_xPlus_xPlus_eq_sum` — `|ψ⟩^⊗2` **in terms of tensor
  products**: `½(|00⟩ + |01⟩ + |10⟩ + |11⟩)`.
* `AxQM.Concrete.vecKron_xPlus_vecKron_xPlus_xPlus` — `|ψ⟩^⊗3` **via the
  Kronecker product**: the explicit uniform 8-component column vector with every entry
  `1/(2√2)`.
* `AxQM.Concrete.vecKron_xPlus_vecKron_xPlus_xPlus_eq_sum` — `|ψ⟩^⊗3` **in
  terms of tensor products**: `1/(2√2) · (|000⟩ + |001⟩ + ⋯ + |111⟩)`, the equal
  superposition of all eight computational-basis kets.
-/
