/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch10.Problem10_1
import AxQM.Postulates.API.CSSCode

/-!
# Nielsen & Chuang, Exercise 10.27 — the twisted CSS codes `CSSᵤ,ᵥ(C₁, C₂)`

Codes CSS_{u,v}(C1,C2) defined by (10.75) are equivalent to CSS(C1,C2) in error-correcting
properties.

## The formalisation

`CSS(C₁, C₂)` is the quantum code whose codewords are the standard coset states `|x + C₂⟩` of
N&C (10.64), one per coset `x ∈ C₁`; `CSSᵤ,ᵥ(C₁, C₂)` replaces each by the twisted coset state
`|x + C₂⟩ᵤ,ᵥ` of (10.75). Both are formalised as **sets of code states** of the bit-vector register
`bitReg ι` (`AxQM/Postulates/API/CSSCode.lean`):

* `AxQM.cssCode C₁ C₂` — the standard code `{ |x + C₂⟩⟨x + C₂| : x ∈ C₁ }`
  (`cssStdState C₂ x`, eq. 10.64, taken to density level via `PureState.toState`).
* `AxQM.cssTwistedCode u v C₁ C₂` — the twisted code
  `{ |x + C₂⟩ᵤ,ᵥ⟨x + C₂|ᵤ,ᵥ : x ∈ C₁ }` (`cssTwistedState C₂ u v x`, eq. 10.75).

The equivalence rests on the **twist crux** proved in `AxQM/Postulates/API/CSSCode.lean`
(`cssTwistedState_toState_eq`): at density level the twisted codeword is the standard codeword
conjugated by the single **fixed local Pauli string** `W = Z^u X^v`
(`AxQM.cssTwistUnitary u v`), the *same* `W` for every coset `x`. Two consequences:

* `AxQM.cssTwistedCode_eq_image` — the **structural equivalence**: the twisted code is the
  image of the standard code under the one fixed unitary channel `W`,
  `CSSᵤ,ᵥ(C₁, C₂) = W '' CSS(C₁, C₂)`. This is the geometric content of "equivalent codes": one
  fixed local unitary, independent of the codeword, carries one code exactly onto the other.
* `AxQM.cssTwistedCode_same_correction` and `AxQM.cssCode_same_correction` — the
  **same error-correcting properties**, both directions. Feeding the fixed unitary `W` (and its
  inverse `W†`) into the channel-equivalence transfer of Problem 10.1
  (`corrects_of_channelEquiv`): any recovery `R` correcting a noise channel `E` on one code yields a
  recovery `W R W†` (resp. `W† R W`) correcting the conjugated channel `W E W†` (resp. `W† E W`) on
  the other. So each code corrects exactly the errors the other does, transported by `W`.

Because `W = Z^u X^v` is a *local* Pauli (a tensor product of single-qubit Paulis, independent of
`x`), this conjugation preserves the weight of every Pauli error — it maps the standard "errors on
`≤ t` qubits" model to itself — so the transported error sets are the same physical error sets:
`CSSᵤ,ᵥ(C₁, C₂)` and `CSS(C₁, C₂)` genuinely have the *same* error-correcting properties, which is
the content of the exercise.

## Design notes

* **Unconditional in `C₁, C₂, u, v`.** The equivalence needs neither `C₂ ⊂ C₁` nor the `t`-error
  hypotheses on `C₁, C₂⊥`: those make the CSS code *good* (an `[n, k₁ - k₂]` code correcting `t`
  errors), not *equivalent to its twist*. The twist crux `cssTwistedState_toState_eq` holds for
  every `x` and every code, so the code-level image equality and the correction transfer hold with
  no side conditions — a faithful reading (the statement is more general, not weaker).
* **Ingredients.** The fixed-unitary crux is `cssTwistedState_toState_eq` in
  `AxQM/Postulates/API/CSSCode.lean`, and the code-transfer along a channel equivalence is
  `corrects_of_channelEquiv` in `AxQM/NC/Ch10/Problem10_1.lean`. This file assembles them at the
  level of code sets.

N&C Exercise 10.27, p. 452.
-/

noncomputable section

namespace AxQM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **fixed local Pauli string** `W = Z^u X^v` relating a twisted CSS code to the standard one:
the composite of the phase-flip string `Z^u` (`phaseString u`) and the bit-flip string `X^v`
(`bitString v`), a single unitary `Evolution` of the register `bitReg ι` that does **not** depend on
the codeword. Conjugation by this one `W` carries `CSS(C₁, C₂)` onto `CSSᵤ,ᵥ(C₁, C₂)`
(`cssTwistedCode_eq_image`). -/
def cssTwistUnitary (u v : ι → ZMod 2) : Evolution (bitReg ι) :=
  (phaseString u).comp (bitString v)

/-- The **standard CSS code** `CSS(C₁, C₂)` (Nielsen & Chuang, §10.4.2) as a set of code states: the
density operators `|x + C₂⟩⟨x + C₂|` of the standard coset states (eq. 10.64) over the cosets
`x ∈ C₁`. -/
def cssCode (C₁ C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)] :
    Set (State (bitReg ι)) :=
  (fun x => (cssStdState C₂ x).toState) '' (C₁ : Set (ι → ZMod 2))

/-- The **twisted CSS code** `CSSᵤ,ᵥ(C₁, C₂)` (Nielsen & Chuang, Exercise 10.27) as a set of code
states: the density operators `|x + C₂⟩ᵤ,ᵥ⟨x + C₂|ᵤ,ᵥ` of the twisted coset states (eq. 10.75) over
the cosets `x ∈ C₁`. -/
def cssTwistedCode (u v : ι → ZMod 2) (C₁ C₂ : LinearCode (ZMod 2) ι) [DecidablePred (· ∈ C₂)] :
    Set (State (bitReg ι)) :=
  (fun x => (cssTwistedState C₂ u v x).toState) '' (C₁ : Set (ι → ZMod 2))

/-- **The twisted code is the fixed-unitary image of the standard code** (Nielsen & Chuang, Exercise
10.27, the geometric content of "equivalent codes"):
`CSSᵤ,ᵥ(C₁, C₂) = W '' CSS(C₁, C₂)` with the *single* fixed local Pauli `W = Z^u X^v`
(`cssTwistUnitary u v`) applied as a unitary channel. Immediate from the density-level twist crux
`cssTwistedState_toState_eq` (each twisted codeword is `W` applied to the corresponding standard
codeword) pushed through `Set.image_image`. The one `x`-independent unitary carrying one code onto
the other is precisely why the two codes are equivalent. -/
theorem cssTwistedCode_eq_image (u v : ι → ZMod 2) (C₁ C₂ : LinearCode (ZMod 2) ι)
    [DecidablePred (· ∈ C₂)] :
    cssTwistedCode u v C₁ C₂ = (cssTwistUnitary u v).evolve '' cssCode C₁ C₂ := by
  rw [cssTwistedCode, cssCode, Set.image_image]
  exact Set.image_congr' fun x => cssTwistedState_toState_eq C₂ u v x

/-- **Same error-correcting properties, forward: a recovery for `CSS(C₁, C₂)` transfers to
`CSSᵤ,ᵥ(C₁, C₂)`** (Nielsen & Chuang, Exercise 10.27). If a recovery `R` corrects a noise channel
`E` on the standard
code `CSS(C₁, C₂)`, then the conjugated recovery `W R W†` corrects the conjugated channel `W E W†`
on the twisted code `CSSᵤ,ᵥ(C₁, C₂)`, with the *same* fixed local Pauli `W = Z^u X^v`
(`cssTwistUnitary u v`) for every codeword.

This is Problem 10.1's channel-equivalence transfer (`corrects_of_channelEquiv`) fed with `U = W`,
`V = W†`: the twisted code is the transported code `W '' CSS(C₁, C₂)` (`cssTwistedCode_eq_image`),
and the equivalent channel `W E W†` is corrected by `W R W†` on it. Since `W` is a fixed local
Pauli, `W E W†` is the same physical error model as `E` (Pauli conjugation preserves error weight),
so the twisted code corrects exactly the errors the standard code does. -/
theorem cssTwistedCode_same_correction (u v : ι → ZMod 2) (C₁ C₂ : LinearCode (ZMod 2) ι)
    [DecidablePred (· ∈ C₂)] {E R : State (bitReg ι) → State (bitReg ι)}
    (hR : Corrects R E (cssCode C₁ C₂)) :
    Corrects
      (fun σ => (cssTwistUnitary u v).evolve (R ((cssTwistUnitary u v).adjoint.evolve σ)))
      (fun ρ => (cssTwistUnitary u v).evolve (E ((cssTwistUnitary u v).adjoint.evolve ρ)))
      (cssTwistedCode u v C₁ C₂) := by
  rw [cssTwistedCode_eq_image]
  have h := corrects_of_channelEquiv
    (E₂ := fun ρ => (cssTwistUnitary u v).evolve (E ((cssTwistUnitary u v).adjoint.evolve ρ)))
    (cssTwistUnitary u v) (cssTwistUnitary u v).adjoint (fun _ => rfl) hR
  simpa only [Evolution.adjoint_adjoint] using h

/-- **Same error-correcting properties, reverse: a recovery for `CSSᵤ,ᵥ(C₁, C₂)` transfers to
`CSS(C₁, C₂)`** (Nielsen & Chuang, Exercise 10.27). The symmetric statement: if a recovery `R`
corrects a noise
channel `E` on the twisted code `CSSᵤ,ᵥ(C₁, C₂)`, then the conjugated recovery `W† R W` corrects the
conjugated channel `W† E W` on the standard code `CSS(C₁, C₂)`, using the inverse `W† = (Z^u X^v)†`
of the same fixed local Pauli.

Together with `cssTwistedCode_same_correction` this makes the equivalence symmetric — each code's
error-correcting capability transfers to the other under the fixed local unitary `W` — completing
"they have the same error-correcting properties". Again `corrects_of_channelEquiv`, now with
`U = W†`, `V = W`, on the transported code `W† '' CSSᵤ,ᵥ(C₁, C₂) = CSS(C₁, C₂)` (the image equality
run backwards, using the two-sided cancellation `W† (W ρ W†) W = ρ`). -/
theorem cssCode_same_correction (u v : ι → ZMod 2) (C₁ C₂ : LinearCode (ZMod 2) ι)
    [DecidablePred (· ∈ C₂)] {E R : State (bitReg ι) → State (bitReg ι)}
    (hR : Corrects R E (cssTwistedCode u v C₁ C₂)) :
    Corrects
      (fun σ => (cssTwistUnitary u v).adjoint.evolve (R ((cssTwistUnitary u v).evolve σ)))
      (fun ρ => (cssTwistUnitary u v).adjoint.evolve (E ((cssTwistUnitary u v).evolve ρ)))
      (cssCode C₁ C₂) := by
  have hcode : (cssTwistUnitary u v).adjoint.evolve '' cssTwistedCode u v C₁ C₂
      = cssCode C₁ C₂ := by
    rw [cssTwistedCode_eq_image, Set.image_image]
    simp only [Evolution.evolve_adjoint_evolve, Set.image_id']
  have h := corrects_of_channelEquiv
    (E₂ := fun ρ => (cssTwistUnitary u v).adjoint.evolve (E ((cssTwistUnitary u v).evolve ρ)))
    (cssTwistUnitary u v).adjoint (cssTwistUnitary u v) (fun _ => rfl) hR
  rw [hcode] at h
  simpa only [Evolution.adjoint_adjoint] using h

end AxQM
