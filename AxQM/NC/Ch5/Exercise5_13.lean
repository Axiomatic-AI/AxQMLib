/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.OrderFindingEigenstate

/-!
# Nielsen & Chuang, Exercise 5.13 — the order-finding eigenstate reconstruction (5.44)/(5.45)

*(N&C p. 227, §5.3.1.)*

Prove (5.44) that the sum of eigenstates |u_s> equals |1>, and more generally (5.45).

In the order-finding subroutine one fixes the modulus `N`, a residue `x` coprime to `N` (a unit of
`ZMod N`) of multiplicative order `r`, and the unitary `U|y⟩ = |xy mod N⟩`. Its eigenstates (eq.
5.37) are the discrete-Fourier superpositions over the orbit `{x^k mod N : k < r}`:

  `|u_s⟩ = (1/√r) ∑_{k=0}^{r−1} e^{−2πisk/r} |x^k mod N⟩`,  `0 ≤ s ≤ r − 1`.

Exercise 5.13 asks to prove that the eigenstates **reconstruct** the orbit basis states by the
inverse discrete Fourier transform — the "clever observation" that circumvents having to prepare an
individual `|u_s⟩` (which would require knowing `r`):

  `(1/√r) ∑_{s=0}^{r−1} |u_s⟩ = |1⟩`     (5.44)

and, more generally, for every integer `k`,

  `(1/√r) ∑_{s=0}^{r−1} e^{2πisk/r} |u_s⟩ = |x^k mod N⟩`.   (5.45)

Equation (5.44) is the `k = 0` case of (5.45), since `x^0 mod N = 1`.

## What is formalised

The two theorems (eqs. 5.44 / 5.45) and the eigenstate `orderEigenstate` are in
`AxQM/Postulates/API/OrderFindingEigenstate.lean`, together with the supporting results below (for
a unit `x : (ZMod N)ˣ` of order `r = orderOf x`):

* `AxQM.orderEigenstate` — the eigenstate `|u_s⟩` (eq. 5.37) as a genuine
  `PureState (qudit N)`; its `normalized` field is the Pythagorean identity
  `‖(1/√r) ∑_k e^{−2πisk/r}|x^k⟩‖² = r·(1/r) = 1` over the orthonormal orbit family.
* `AxQM.orderEigenstate_reconstruct` — **eq. (5.45)**, the inverse-DFT reconstruction, for
  every `k : ℕ`.
* `AxQM.orderEigenstate_sum_eq_one` — **eq. (5.44)**, the `k = 0` specialisation
  (`|x^0 mod N⟩ = |1⟩`, needing `1 < N`).
* `AxQM.Concrete.orbitIndex` (`Concrete/OrderFindingOrbit.lean`) — the index `x^k mod N :
  Fin N`, with `orbitIndex_fin_injective` (the `r` orbit points are distinct) and `orbitIndex_mod`
  (`r`-periodicity); these are `ZMod`/`Fin` combinatorics.
* `AxQM.quditBasis_orthonormal` (`Postulates/API/Qudit.lean`) — the computational basis of
  `qudit N` is orthonormal.
* `geom_sum_eq_ite_of_pow_eq_one` (`ToMathlib/Algebra/Field/GeomSumRootOfUnity.lean`) — the
  root-of-unity orthogonality `∑_{s<r} ζ^s = r·[ζ=1]` (when `ζ^r = 1`, the Hint), the
  finite-dimension analogue of the identity making the QFT matrix unitary (used, for example, by
  `Concrete.qftMatrix_star_mul_self`).

## Design notes

* **Fidelity.** Eq. (5.45) is proved for *every* `k : ℕ`, not merely `k < r` — both
  sides depend on `k` only through `k mod r`, which is precisely the "in fact, prove that …" clause.
  `x` is an arbitrary unit of `ZMod N` (N&C's "coprime to `N`"), and `r = orderOf x` its genuine
  multiplicative order. Eq. (5.44) is stated with `|1⟩` on the right (not the opaque `|x^0 mod N⟩`),
  the `1 < N` hypothesis being satisfied by every order-finding modulus.
* **The `U`-eigenstate context.** The exercise only asks for the reconstruction identities, so the
  unitary `U` and the eigenvalue equation `U|u_s⟩ = e^{2πis/r}|u_s⟩` (5.37–5.39) are not needed to
  state or prove (5.44)/(5.45); `|u_s⟩` is characterised directly by its defining superposition.
* **Related exercises.** Compare the inverse-QFT development of Exercise 5.5
  (`qftInverseFourierImage`) and the phase estimation on a superposition of Exercise 5.8.
-/
