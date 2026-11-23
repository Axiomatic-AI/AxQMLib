/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch10.Exercise10_52
import AxQM.Postulates.API.PhaseStringCommute

/-!
# Nielsen & Chuang, Exercise 10.56 — a stabilizer factor doesn't change an encoded operator's action

*(N&C §10.5.7, p. 471–472.)*

Replacing encoded X or Z operator by g times it (g in stabilizer) doesn't change its action on the
code.

## The content, and why it holds

An **encoded** (logical) operator `L` for a stabilizer code lies in the normalizer `N(S) = Z(S)`
of the stabilizer `S` (Exercise 10.44), hence **commutes** with every stabilizer element `g ∈ S`.
A **code state** `|ψ⟩` is one stabilized by `S`: every `g ∈ S` fixes it, `g|ψ⟩ = |ψ⟩` (a `+1`
eigenstate). Replacing `L` by `g·L` therefore leaves its action on the code untouched:

`(g·L)|ψ⟩ = g(L|ψ⟩) = L(g|ψ⟩) = L|ψ⟩`,

the middle step using `g·L = L·g` (commutation) and the last using `g|ψ⟩ = |ψ⟩` (code state). The
only two facts consumed are that `L` **commutes with `g`** (which is what "encoded operator" buys)
and that `g` **fixes the code state** (which is what "`g` in the stabilizer, `|ψ⟩` in the code"
buys); the argument is otherwise agnostic to whether `L` is an encoded `X` or an encoded `Z`. This
is captured by the single general theorem `evolvePure_comp_eq_of_commute_hasEigenstate_one`.

## N&C's own worked example (the Steane `Z̄`)

Nielsen & Chuang motivate this exercise with the Steane code (p. 471): the standard form gives the
encoded `Z̄ = Z₂Z₄Z₆`, while equation (10.107) gives `Z̄ = Z₁Z₂Z₃Z₄Z₅Z₆Z₇`; the two "differ only by
a factor `Z₁Z₃Z₅Z₇`, which is an element of the stabilizer of the Steane code, and thus both have
the same effect on Steane code states." Here `Z₁Z₃Z₅Z₇ = Z^{h₂}` is exactly the Steane `Z`-type
stabilizer generator `steaneGenZ 2` (the third Hamming parity-check row `h₂ = 1010101`), and
`(steaneGenZ 2)·(Z₁…Z₇)` is, as a product of `Z`'s, precisely `Z₂Z₄Z₆`. So the instantiation below,
for `i = 2`, is literally N&C's statement that `Z₁…Z₇` and `Z₂Z₄Z₆` act identically on `|0_L⟩` and
`|1_L⟩`; for the other generators `i = 0, 1` it is the same fact for the remaining stabilizer
factors. (The encoded-`X` case `X̄ = X₁…X₇` is identical in mechanism — `X̄` likewise commutes with
the stabilizer — and is covered verbatim by the general theorem.)

## Fidelity

The operators are `Evolution`s of the register `bitReg (Fin 7)`, the code states are `PureState`s,
and the action is `Evolution.evolvePure`; the code-state hypothesis is `Evolution.HasEigenstate 1`.
The technical input — that any two phase-flip strings commute — is `phaseString_commute`
(`AxQM/Postulates/API/PhaseStringCommute.lean`), whose proof goes through the diagonal-operator
realization.

## Declarations

* `evolvePure_comp_eq_of_commute_hasEigenstate_one` — **Exercise 10.56, general form**: for any
  evolutions `g, L` on a system `S` with `Commute g L` and `g.HasEigenstate 1 ψ` (a code state),
  `(g.comp L).evolvePure ψ = L.evolvePure ψ`. The whole content of the exercise, for `X` or `Z`.
* `steaneGenZ_comp_logicalZBar_evolvePure_logicalZero` /
  `steaneGenZ_comp_logicalZBar_evolvePure_logicalOne` — the Steane demonstration: for each
  `Z`-generator `steaneGenZ i`, the modified encoded operator `(steaneGenZ i)·Z̄` has the same
  action as `Z̄ = Z₁…Z₇` on `|0_L⟩` (resp. `|1_L⟩`). For `i = 2` this is N&C's `Z₁…Z₇` vs `Z₂Z₄Z₆`.
* `phaseString_commute` (`AxQM/Postulates/API/PhaseStringCommute.lean`) — the input: `Z^u` and
  `Z^v` commute.
-/

namespace AxQM

/-- **Nielsen & Chuang, Exercise 10.56 (general form).** Replacing an operator `L` by `g·L`, where
`g` **commutes** with `L` and **fixes** the state `ψ` (i.e. `ψ` is a `+1` eigenstate of `g`), does
not change its action on `ψ`: `(g·L)|ψ⟩ = L|ψ⟩`.

This is exactly the situation of the exercise: an *encoded* `X` or `Z` operator `L` lies in the
centralizer of the stabilizer, so it commutes with any stabilizer element `g` (`Commute g L`); a
*code state* `ψ` is fixed by `g` (`g.HasEigenstate 1 ψ`). The proof is
`(g·L)ψ = L(gψ) = Lψ`, commuting `g` past `L` and then using `gψ = ψ`. -/
theorem evolvePure_comp_eq_of_commute_hasEigenstate_one {S : QSystem} {g L : Evolution S}
    {ψ : PureState S} (hcomm : Commute g L) (hfix : g.HasEigenstate 1 ψ) :
    (g.comp L).evolvePure ψ = L.evolvePure ψ := by
  have hc : g.comp L = L.comp g := by simpa only [Evolution.mul_def] using hcomm.eq
  rw [hc, Evolution.evolvePure_comp, hfix.evolvePure_eq]

/-- **Exercise 10.56 for the Steane code, on `|0_L⟩`.** For every `Z`-type stabilizer generator
`steaneGenZ i = Z^{hᵢ}`, the modified encoded operator `(steaneGenZ i)·Z̄` acts on the Steane
logical zero exactly as the encoded `Z̄ = Z₁…Z₇` does. For `i = 2` (`steaneGenZ 2 = Z₁Z₃Z₅Z₇` and
`(steaneGenZ 2)·Z̄ = Z₂Z₄Z₆`) this is Nielsen & Chuang's remark that the standard-form `Z̄ = Z₂Z₄Z₆`
and the `(10.107)` `Z̄ = Z₁…Z₇` have the same effect on the code. Uses that `Z`-strings commute
(`phaseString_commute`) and that the generators fix the codeword
(`steaneGenZ_hasEigenstate_one_logicalZero`). -/
theorem steaneGenZ_comp_logicalZBar_evolvePure_logicalZero (i : Fin 3) :
    ((steaneGenZ i).comp steaneLogicalZBar).evolvePure steaneLogicalZero
      = steaneLogicalZBar.evolvePure steaneLogicalZero :=
  evolvePure_comp_eq_of_commute_hasEigenstate_one
    (phaseString_commute (Concrete.hammingParityCheck i) 1)
    (steaneGenZ_hasEigenstate_one_logicalZero i)

/-- **Exercise 10.56 for the Steane code, on `|1_L⟩`.** For every `Z`-type stabilizer generator
`steaneGenZ i = Z^{hᵢ}`, the modified encoded operator `(steaneGenZ i)·Z̄` acts on the Steane
logical one exactly as the encoded `Z̄ = Z₁…Z₇` does — the companion of
`steaneGenZ_comp_logicalZBar_evolvePure_logicalZero` on the other codeword. -/
theorem steaneGenZ_comp_logicalZBar_evolvePure_logicalOne (i : Fin 3) :
    ((steaneGenZ i).comp steaneLogicalZBar).evolvePure steaneLogicalOne
      = steaneLogicalZBar.evolvePure steaneLogicalOne :=
  evolvePure_comp_eq_of_commute_hasEigenstate_one
    (phaseString_commute (Concrete.hammingParityCheck i) 1)
    (steaneGenZ_hasEigenstate_one_logicalOne i)

end AxQM
