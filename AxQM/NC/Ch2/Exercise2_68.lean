/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.BellState
import AxQM.Concrete.BellVector

/-!
# Nielsen & Chuang, Exercise 2.68 (the Bell state is not a product state)

Prove (|00>+|11>)/sqrt2 is not a product state |a>|b>.

Here `|ψ⟩ = (|00⟩ + |11⟩)/√2` is the two-qubit state of equation (2.132) — the maximally entangled
Bell state `bellPhiPlus` of `AxQM/Postulates/API/BellState.lean`. A composite state with
this property — that it cannot be written as a product `|a⟩|b⟩` of states of its component systems —
is called *entangled*; `|ψ⟩` is the archetypal example, and this fact underlies superdense coding
(§2.3) and the violation of Bell's inequality (§2.6).

* `bellPhiPlus_ne_tmul` — the statement: `bellPhiPlus ≠ a ⊗ b` for
  *all* single-qubit pure states `a, b`.

The mathematical core — that the underlying vector `(|00⟩ + |11⟩)/√2` is not a simple tensor
`a ⊗ₜ b` for any `a, b : ℂ²` — is the pure linear-algebra fact `Concrete.bellVector_ne_tmul`
(`AxQM/Concrete/BellVector.lean`), proved by the standard coefficient argument. The statement
follows from it: `bellPhiPlus = a ⊗ b` would make their state vectors equal,
`bellPhiPlus.vec = a.vec ⊗ₜ b.vec`. And `bellPhiPlus.vec` reduces to `Concrete.bellVector`
(both `(√2)⁻¹ • (|00⟩ + |11⟩)`), which contradicts the fact above.
-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 2.68.** The Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` is not a product
state: `bellPhiPlus ≠ a ⊗ b` for every pair of single-qubit pure states `a, b`. Equivalently, `|Φ⁺⟩`
is *entangled* — it cannot be factored across the two qubits. Reduces to the concrete fact that the
Bell vector is not a simple tensor (`Concrete.bellVector_ne_tmul`), since `bellPhiPlus.vec` is
definitionally `Concrete.bellVector`. -/
theorem bellPhiPlus_ne_tmul (a b : PureState qubit) : bellPhiPlus ≠ a ⊗ b := by
  intro h
  have hvec : bellPhiPlus.vec = a.vec ⊗ₜ[ℂ] b.vec := by
    rw [← PureState.tmul_vec]; exact congrArg PureState.vec h
  exact Concrete.bellVector_ne_tmul a.vec b.vec hvec

end AxQM
