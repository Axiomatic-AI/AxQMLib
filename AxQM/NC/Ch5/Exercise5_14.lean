/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.OrderFindingState

/-!
# Nielsen & Chuang, Exercise 5.14

Show V|j>|k>=|j>|k+x^j mod N> from |0> gives same state as U^j from |1>; construct V in O(L^3)
gates.

Here `U|y⟩ = |xy mod N⟩` is the order-finding operator (Eq. 5.36, Exercise 5.12) on the register
`{0, …, 2ᴸ - 1}`, `x` co-prime to `N`.

The state-equivalence is a pair of basis-ket identities on the register — `Uʲ|1⟩ = |xʲ mod N⟩`
and `V|j⟩|0⟩ = |j⟩|xʲ mod N⟩` — that reduce, term by term, to an equality of amplitude vectors
under permutation matrices. Like Exercise 5.12 (`Concrete/ModularMultiplication.lean`), the
statements concern `Fin`, `Matrix` and `Equiv.Perm`.

## What is formalised

The formalisation is in `AxQM/Concrete/OrderFindingState.lean`
(namespace `AxQM.Concrete`):

* `modMulPerm_pow_apply_one` — **`Uʲ|1⟩ = |xʲ mod N⟩`**: the forward image of `|1⟩` under `j` powers
  of the order-finding permutation `modMulPerm` has register value `xʲ mod N`
  (with `modMulPerm_pow_apply_of_lt` giving the general residue action `y ↦ xʲ y mod N`).
* `modShiftPerm` / `modExpAddPerm` — the target-register adder `k ↦ (k + c) mod N` and, from it,
  **the transform `V`** (Eq. 5.47) as a permutation of the joint register:
  `V(j, k) = (j, k + xʲ mod N)` (`modExpAddPerm_apply`). `modExpAddPerm_apply_zero_eq_pow` is the
  crux `V|j⟩|0⟩ = |j⟩Uʲ|1⟩`.
* `modExpAddMatrix` / `modExpAddMatrix_mem_unitaryGroup` — **`V` is a unitary** (permutation)
  matrix, the exercise's "different unitary transform `V`".
* `orderFindingStateU` / `orderFindingStateV` and
  `AxQM.Concrete.orderFindingStateV_eq_orderFindingStateU` — **Exercise 5.14, the "same
  state":** applying `V` to `∑ⱼ |j⟩|0⟩` yields exactly `∑ⱼ |j⟩Uʲ|1⟩`.

## The `O(L³)`-gate construction

The exercise's second request — build `V` with `O(L³)` gates via modular exponentiation (Box 5.2) —
is a gate-*complexity* claim about a reversible arithmetic circuit. N&C give no explicit circuit for
`V`, and the library has no cost model in which "`O(L³)` gates" is a proposition, so — as with the
other asymptotic gate-count sub-claims of the book — it is not formalised. The formalised content
is the state-equivalence and the unitarity of `V`.
-/
