/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.InversionAboutMean

/-!
# Nielsen & Chuang, Exercise 6.2 (Inversion about the mean)

Show (2|psi><psi| - I) applied to sum a_k|k> gives sum (-a_k + 2<a>)|k>.

The operator `2|ψ⟩⟨ψ| − I` is the second stage of the Grover iteration
(`H⊗ⁿ (2|0⟩⟨0| − I) H⊗ⁿ = 2|ψ⟩⟨ψ| − I`, Eq. 6.6). Eq. (6.7) says it reflects every
amplitude `αₖ` about the common mean `⟨α⟩`, whence the name *inversion about the mean*.

This is pure finite-dimensional linear algebra over `ℂ^N`: the state `∑ₖ αₖ|k⟩` is a column
vector `v : Fin n → ℂ`, the operator `2|ψ⟩⟨ψ| − I` an `n × n` matrix, and its action the
matrix–vector product `M *ᵥ v`.

The formalisation is in `AxQM/Concrete/InversionAboutMean.lean`:

* **The exercise (Eq. 6.7).** `AxQM.Concrete.inversionAboutMean_mulVec_apply` —
  `(inversionAboutMean n *ᵥ v) k = − v k + 2 * amplitudeMean v`, the `k`-th component of
  `(2|ψ⟩⟨ψ| − I) v`.
* **The objects.** `AxQM.Concrete.inversionAboutMean` (`= 2|ψ⟩⟨ψ| − I`),
  `uniformSuperposition` (`= |ψ⟩`, Eq. 6.4), and `amplitudeMean` (`= ⟨α⟩`). The operator
  is defined as the reflection `reflectionMatrix (uniformSuperposition n)`, where the
  reusable `reflectionMatrix u = 2|u⟩⟨u| − I` (with action `reflectionMatrix_mulVec`) also
  serves the neighbouring Grover items (Ex. 6.1's `2|0⟩⟨0| − I`, 6.3, 6.6).
* **Supporting facts.** `uniformSuperposition_apply` (`ψₖ = (√N)⁻¹`),
  `star_uniformSuperposition` (`ψ` is real), and `uniformSuperposition_dotProduct_self`
  (`⟨ψ|ψ⟩ = 1`, certifying `|ψ⟩` is the genuine normalized state 6.4).
-/
