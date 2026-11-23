/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.CheckMatrixSymplectic

/-!
# Nielsen & Chuang, Exercise 10.33 — commutation via the symplectic check-matrix form

*(N&C §10.5.1, p. 457.)*

g and g' commute iff r(g) Lambda r(g')^T = 0 (mod 2).

## What the exercise asks, and what is proved

In the stabilizer formalism (N&C §10.5.1), an `n`-qubit Pauli-group element `g` is assigned a
**`2n`-bit check-matrix row** `r(g) = (x_g | z_g)` over `ZMod 2`: a `1` in the `k`-th `X`-slot
when `g` has an `X` (or `Y`) on qubit `k`, a `1` in the `k`-th `Z`-slot when `g` has a `Z` (or `Y`).
N&C then defines the `2n × 2n` **symplectic matrix** (eq. (10.84))
```
Λ = ⎡ 0 I ⎤
    ⎣ I 0 ⎦
```
with `n × n` identity blocks on the off-diagonal, and states that `g` and `g′` commute iff the
"twisted inner product" `r(g) Λ r(g′)ᵀ` vanishes (mod 2). This exercise proves that equivalence.

This is proved as `pauliString_commute_iff_symplecticForm`: for phase-free Pauli strings `P_g, P_h`
(the phase `±1, ±i` is irrelevant to commutation, so `pauliString` is the appropriate model),
```
Commute P_g P_h  ↔  symplecticForm (checkVec g) (checkVec h) = 0,
```
where `checkVec g` is `r(g)` and `symplecticForm x y = x ⬝ᵥ Λ.mulVec y` is `x Λ yᵀ`, with `Λ` the
explicit block matrix `Matrix.fromBlocks 0 1 1 0`. The bridge to the underlying engine is
`symplecticForm_checkVec`: `r(g) Λ r(h)ᵀ = (pauliAnticommCount g h : ZMod 2)`, so the criterion
is exactly the mod-2 reduction of the commutation/anticommutation parity already established for the
Pauli strings.

## Declarations

All in `AxQM/Concrete/CheckMatrixSymplectic.lean`, namespace `AxQM.Concrete`, for
the `n`-qubit phase-free Pauli strings `pauliString g` (`g : Fin n → Fin 4`):

* `checkVec` — the `2n`-vector `r(g) = (x_g | z_g)` over `Fin n ⊕ Fin n → ZMod 2` (the flat form of
  `checkRow g`).
* `symplecticMatrix` — the symplectic form `Λ = [[0, I], [I, 0]]` (eq. (10.84)), literally
  `Matrix.fromBlocks 0 1 1 0`.
* `symplecticForm` — the twisted inner product `x Λ yᵀ = x ⬝ᵥ Λ.mulVec y`.
* `symplecticForm_checkVec_eq_checkSymplectic` — the `Matrix`-level product **is** the pre-existing
  bilinear form: `r(g) Λ r(h)ᵀ = checkSymplectic (checkRow g) (checkRow h)`.
* `symplecticForm_checkVec` — `r(g) Λ r(h)ᵀ = (pauliAnticommCount g h : ZMod 2)`, the bridge to the
  parity engine (derived from the identification above and `checkSymplectic_checkRow`).
* `pauliString_commute_iff_symplecticForm` — **the exercise itself**: `Commute P_g P_h ↔ r(g) Λ
  r(h)ᵀ = 0`.

The commutation/anticommutation engine it rests on — `pauliString_commute_iff` (`Commute ↔ Even
(pauliAnticommCount g h)`), the sign law `pauliString_mul_comm_sign`, the check row `checkRow` / its
bits `pauliBit`, and the bilinear form `checkSymplectic` (with `checkSymplectic_checkRow`) — live in
`AxQM/Concrete/PauliStringCommutation.lean`, `.../CheckMatrix.lean`, and
`.../StabilizerGeneratorFlip.lean`.

## Faithfulness

* **The exact statement.** `checkVec g` is N&C's `r(g)` (the `2n`-bit `(x | z)` row);
  `symplecticMatrix` is the exact block matrix `Λ` of eq. (10.84), and `symplecticForm (checkVec g)
  (checkVec h)` is literally `r(g) Λ r(h)ᵀ` — a `ZMod 2` scalar (mod-2 arithmetic, as the exercise
  stipulates). The theorem is the full "iff", for all `n` and arbitrary Pauli strings, with no extra
  hypothesis.
* **Not a weakening.** Commutation is stated as `Commute P_g P_h` for the operators `P_g, P_h`
  (`2ⁿ × 2ⁿ` complex matrices), not a proxy; the `2n` coordinates are indexed by `Fin n ⊕ Fin n`
  (canonically `≃ Fin (2n)`) to make `Λ`'s block structure literal. Because the multiplicative
  phase `±1, ±i` never affects commutation, the phase-free `pauliString` faithfully represents the
  Pauli-group element `g` for the purposes of this criterion.
-/
