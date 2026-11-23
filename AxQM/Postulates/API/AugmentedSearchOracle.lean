/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.AugmentedOracleBlock
import AxQM.Postulates.API.Qudit
import AxQM.Postulates.API.DeutschAlgorithm
import AxQM.Postulates.API.CnotXBasis

/-!
# The augmented search oracle `O'` over the whole search index (N&C Exercise 6.5)

Nielsen & Chuang, §6.1.4 (p. 255): to search a space in which *more than half* the items may be
solutions, one **doubles** the search space by adjoining a single extra qubit `|q⟩`, and builds an
**augmented oracle** `O'` that marks an item `(x, q)` iff `x` is a solution *and* the extra bit is
`q = 0`. Exercise 6.5 asks to show `O'` can be constructed from **one call** to the original oracle
`O` together with **elementary quantum gates**, using the extra qubit `|q⟩`.

This file is the **full-register assembly** over the entire search index. Its companion
`AxQM/Postulates/API/AugmentedOracleBlock.lean` formalised the two-qubit response
block for a *single item* with a fixed solution flag `c`, using a concrete oracle-call gate `X^c`;
here the oracle is a genuine **one-call black box** `O` acting on the whole index register
`qudit N`, and the mark is proved for *every* item `x` of the search space at once — the content
that makes the resource claim "**one** application of `O`" honest (the surrounding elementary gates
are independent of `x` and `f`).

## The register and the oracle

The augmented register is `qudit N ⊗ (qubit ⊗ qubit)`: the search index `|x⟩` (`x : Fin N`), the
extra search qubit `|q⟩`, and the oracle **response** qubit `|r⟩`. The original bit-flip oracle
acts on the index and the response by `O|x⟩|r⟩ = |x⟩|r ⊕ f(x)⟩` (`f(x) = 1` iff `x` is a solution),
leaving the extra qubit `q` untouched; this is the predicate `IsSearchBitFlipOracle f O`, stated on
the computational basis via `evolvePure` (the `qudit N`-index generalisation of `IsDeutschOracle`).

## The construction (phase kickback), `|0⟩` work-qubit form

With the response `r` supplied as a fresh work qubit in `|0⟩`, the circuit is, in time order,
`X_r`, `CNOT_{q→r}`, `H_r`, then the single oracle call `O`, then `H_r`, `CNOT_{q→r}`, `X_r` —
`augmentedSearchOracle O` — a palindrome of the `x`-independent elementary gates `X_r`, `CNOT_{q→r}`
(control the extra qubit `q`, target the response `r`), `H_r`, around **one** call to `O`. Preparing
`r` as `|−⟩` exactly on the `q = 0` branch turns the single oracle call into a phase kickback: it
imprints `(−1)^{f(x)}` precisely when `q = 0` and nothing when `q = 1` — the mark
"solution ∧ `q = 0`" defining `O'`, with the work qubit returned to `|0⟩`.

The heart of the proof is the abstract-oracle collapse `hadamardConj_oracle_op`:
`H_r · O · H_r` acts on the computational response `|b⟩` as the diagonal phase `(−1)^{f(x)·b}`, i.e.
as `Z^{f(x)}` on the response — the one-call analogue of the block's gate identity
`hadamardConj_targetXPow` (`H X^c H = Z^c`). It rests on the two phase-kickback facts
`op_tmul_qubitMinus` / `op_tmul_qubitPlus` for the abstract oracle `O`.

## What is formalised

* `IsSearchBitFlipOracle f O` — the abstract one-call oracle: `O|x⟩|a⟩|b⟩ = |x⟩|a⟩|b ⊕ f(x)⟩`.
* `augmentedSearchOracle O` — the seven-factor circuit built from **one** `O` and the elementary
  gates `X_r`, `CNOT_{q→r}`, `H_r`.
* `augmentedSearchOracle_hasEigenstate` — **the mark (N&C Exercise 6.5):** on the response work
  qubit supplied in `|0⟩`, the circuit fixes `|x⟩|q⟩|0⟩` up to the augmented-oracle phase, scaling
  it by `−1` exactly when the item is a solution (`f(x) = 1`) *and* the extra bit is `q = 0`, and by
  `+1` otherwise — precisely the mark "solution ∧ `q = 0`" defining `O'`, with the work qubit
  returned to `|0⟩`, for **every** item `x` of the search space.

The mark statement `augmentedSearchOracle_hasEigenstate` is restated in
`AxQM/NC/Ch6/Exercise6_5.lean`.
-/

open scoped TensorProduct

noncomputable section

namespace AxQM

variable {N : ℕ} {f : Fin N → Fin 2}
  {O : Evolution ((qudit N).compose (qubit.compose qubit))}

/-- **The abstract one-call bit-flip oracle** for `f : Fin N → Fin 2` on the augmented register
`qudit N ⊗ (qubit ⊗ qubit)` (index `|x⟩`, extra qubit `|a⟩`, response `|b⟩`): the reversible XOR
oracle `O|x⟩|a⟩|b⟩ = |x⟩|a⟩|b ⊕ f(x)⟩`, adding `f(x)` into the response and leaving both the index
`x` and the extra qubit `a` alone. Stated on the computational basis via `evolvePure`. The
`qudit N`-index generalisation of `IsDeutschOracle`; `O` is used as a *single black box* in the
augmented-oracle construction below. -/
def IsSearchBitFlipOracle (f : Fin N → Fin 2)
    (O : Evolution ((qudit N).compose (qubit.compose qubit))) : Prop :=
  ∀ (x : Fin N) (a b : Fin 2),
    O.evolvePure ((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis b)))
      = (quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis (b + f x)))

/-- **The elementary gate `X_r`** on the augmented register: `pauliX` on the response qubit `r`,
identity on the index `x` and the extra qubit `q`, i.e. `1_x ⊗ (1_q ⊗ X_r)`. -/
def xFlipResponse : Evolution ((qudit N).compose (qubit.compose qubit)) :=
  (pauliXGate.onRight qubit).onRight (qudit N)

/-- **The elementary gate `CNOT_{q→r}`** on the augmented register: the controlled-`NOT` with the
extra qubit `q` as control and the response `r` as target, identity on the index `x`, i.e.
`1_x ⊗ CNOT_{q→r}`. -/
def cnotExtraResponse : Evolution ((qudit N).compose (qubit.compose qubit)) :=
  cnotGate.onRight (qudit N)

/-- **The elementary gate `H_r`** on the augmented register: the Hadamard on the response qubit `r`,
identity on the index `x` and the extra qubit `q`, i.e. `1_x ⊗ (1_q ⊗ H_r)`. -/
def hadResponse : Evolution ((qudit N).compose (qubit.compose qubit)) :=
  (hadamardGate.onRight qubit).onRight (qudit N)

/-- **The augmented search oracle `O'` from one oracle call.** In time order `X_r`, `CNOT_{q→r}`,
`H_r`, the single oracle call `O`, `H_r`, `CNOT_{q→r}`, `X_r` — a palindrome of the elementary
gates `X_r`, `CNOT_{q→r}`, `H_r` around a **single** call to the oracle `O`. Its net action is the
augmented-oracle mark (`augmentedSearchOracle_hasEigenstate`); the middle sandwich
`H_r · O · H_r` is grouped as a subterm so it collapses to `Z^{f(x)}` (`hadamardConj_oracle_op`). -/
def augmentedSearchOracle
    (O : Evolution ((qudit N).compose (qubit.compose qubit))) :
    Evolution ((qudit N).compose (qubit.compose qubit)) :=
  (xFlipResponse.comp cnotExtraResponse).comp
    ((hadResponse.comp (O.comp hadResponse)).comp
      (cnotExtraResponse.comp xFlipResponse))

/-- `X_r` on a computational-basis product state: `X_r|x⟩|a⟩|b⟩ = |x⟩|a⟩|b + 1⟩` (a bit flip on the
response, identity elsewhere). -/
theorem xFlipResponse_op_tmul (x : Fin N) (a b : Fin 2) :
    (xFlipResponse.op ((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis b))).vec)
      = ((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis (b + 1)))).vec := by
  rw [xFlipResponse, PureState.tmul_vec, PureState.tmul_vec]
  have h1 := Evolution.onRight_op_tmul (pauliXGate.onRight qubit) (qudit N)
    (quditBasis x).vec ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
  have h2 := Evolution.onRight_op_tmul pauliXGate qubit (qubitBasis a).vec (qubitBasis b).vec
  rw [h1, h2, pauliXGate_op_apply_qubitBasis, PureState.tmul_vec, PureState.tmul_vec]

/-- `CNOT_{q→r}` on a computational-basis product state: `CNOT|x⟩|a⟩|b⟩ = |x⟩|a⟩|b + a⟩` (flip the
response by the extra bit `a`, identity elsewhere). -/
theorem cnotExtraResponse_op_tmul (x : Fin N) (a b : Fin 2) :
    (cnotExtraResponse.op ((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis b))).vec)
      = ((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis (b + a)))).vec := by
  have hcnot : cnotGate.op ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
      = (qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis (b + a)).vec := by
    have h := congrArg PureState.vec (cnotGate_evolvePure_qubitBasis a b)
    rwa [Evolution.evolvePure_vec, PureState.tmul_vec, PureState.tmul_vec] at h
  rw [cnotExtraResponse, PureState.tmul_vec, PureState.tmul_vec]
  have h1 := Evolution.onRight_op_tmul cnotGate (qudit N)
    (quditBasis x).vec ((qubitBasis a).vec ⊗ₜ[ℂ] (qubitBasis b).vec)
  rw [h1, hcnot, PureState.tmul_vec, PureState.tmul_vec]

/-- `H_r` on a product state `|x⟩|a⟩ψ` acts only on the response: `H_r(|x⟩|a⟩ψ) = |x⟩|a⟩(Hψ)`, for
any response state `ψ`. -/
theorem hadResponse_op_tmul (x : Fin N) (a : Fin 2) (ψ : PureState qubit) :
    (hadResponse.op ((quditBasis x).tmul ((qubitBasis a).tmul ψ)).vec)
      = ((quditBasis x).tmul ((qubitBasis a).tmul (hadamardGate.evolvePure ψ))).vec := by
  rw [hadResponse, PureState.tmul_vec, PureState.tmul_vec]
  have h1 := Evolution.onRight_op_tmul (hadamardGate.onRight qubit) (qudit N)
    (quditBasis x).vec ((qubitBasis a).vec ⊗ₜ[ℂ] ψ.vec)
  have h2 := Evolution.onRight_op_tmul hadamardGate qubit (qubitBasis a).vec ψ.vec
  rw [h1, h2, ← Evolution.evolvePure_vec, PureState.tmul_vec, PureState.tmul_vec]

/-- `H` is an involution on pure states: `H(Hψ) = ψ`, from `H · H = 1`
(`hadamardGate_comp_self`). -/
theorem hadamardGate_evolvePure_evolvePure (ψ : PureState qubit) :
    hadamardGate.evolvePure (hadamardGate.evolvePure ψ) = ψ := by
  apply PureState.ext
  rw [Evolution.evolvePure_vec, Evolution.evolvePure_vec, ← ContinuousLinearMap.comp_apply,
    ← Evolution.comp_op, hadamardGate_comp_self]
  simp

/-- **Phase kickback on `|−⟩`** for the abstract oracle `O`: fed the response `X`-eigenstate `|−⟩`,
`O` acts as a *phase* oracle, `O(|x⟩|a⟩|−⟩) = (−1)^{f(x)} |x⟩|a⟩|−⟩` — the extra qubit `a` and the
index `x` ride along. Since `|−⟩ = (|0⟩ − |1⟩)/√2`, the bit flip `b ↦ b ⊕ f(x)` either fixes `|−⟩`
(`f(x) = 0`) or negates it (`f(x) = 1`). The `qudit N`-index, extra-qubit generalisation of
`IsDeutschOracle.op_tmul_qubitMinus`. -/
theorem IsSearchBitFlipOracle.op_tmul_qubitMinus (h : IsSearchBitFlipOracle f O)
    (x : Fin N) (a : Fin 2) :
    O.op ((quditBasis x).tmul ((qubitBasis a).tmul qubitMinus)).vec
      = ((-1 : ℂ) ^ (f x).val) • ((quditBasis x).tmul ((qubitBasis a).tmul qubitMinus)).vec := by
  have hO : ∀ b : Fin 2, O.op ((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis b))).vec
      = ((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis (b + f x)))).vec :=
    fun b => Evolution.op_vec_eq (h x a b)
  have key : ((quditBasis x).tmul ((qubitBasis a).tmul qubitMinus)).vec
      = Concrete.invSqrt2
          • (((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis 0))).vec
              - ((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis 1))).vec) := by
    rw [PureState.tmul_vec, PureState.tmul_vec, qubitMinus_vec_eq_smul_sub,
      TensorProduct.tmul_smul, TensorProduct.tmul_sub]
    erw [TensorProduct.tmul_smul, TensorProduct.tmul_sub]
    rfl
  rw [key, map_smul, map_sub, hO 0, hO 1]
  rcases (by omega : f x = 0 ∨ f x = 1) with hfx | hfx <;> rw [hfx] <;>
    simp only [Fin.isValue, zero_add, add_zero, Fin.reduceAdd, Fin.val_zero, Fin.val_one, pow_zero,
      pow_one, one_smul, neg_one_smul]
  module

/-- **Phase kickback on `|+⟩`** for the abstract oracle `O`: fed the response `X`-eigenstate `|+⟩`,
`O` acts trivially, `O(|x⟩|a⟩|+⟩) = |x⟩|a⟩|+⟩`. Since `|+⟩ = (|0⟩ + |1⟩)/√2`, the bit flip
`b ↦ b ⊕ f(x)` permutes `{|0⟩, |1⟩}` and so fixes `|+⟩` for either value of `f(x)`. The `+`-branch
of phase kickback (eigenvalue `+1`). -/
theorem IsSearchBitFlipOracle.op_tmul_qubitPlus (h : IsSearchBitFlipOracle f O)
    (x : Fin N) (a : Fin 2) :
    O.op ((quditBasis x).tmul ((qubitBasis a).tmul qubitPlus)).vec
      = ((quditBasis x).tmul ((qubitBasis a).tmul qubitPlus)).vec := by
  have hO : ∀ b : Fin 2, O.op ((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis b))).vec
      = ((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis (b + f x)))).vec :=
    fun b => Evolution.op_vec_eq (h x a b)
  have key : ((quditBasis x).tmul ((qubitBasis a).tmul qubitPlus)).vec
      = Concrete.invSqrt2
          • (((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis 0))).vec
              + ((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis 1))).vec) := by
    rw [PureState.tmul_vec, PureState.tmul_vec, qubitPlus_vec_eq_smul_add,
      TensorProduct.tmul_smul, TensorProduct.tmul_add]
    erw [TensorProduct.tmul_smul, TensorProduct.tmul_add]
    rfl
  rw [key, map_smul, map_add, hO 0, hO 1]
  rcases (by omega : f x = 0 ∨ f x = 1) with hfx | hfx <;> rw [hfx] <;>
    simp only [Fin.isValue, zero_add, add_zero, Fin.reduceAdd]
  module

/-- **The abstract-oracle Hadamard collapse** `H_r · O · H_r = Z^{f(x)}` on the response, on the
computational basis: `(H_r · O · H_r)(|x⟩|a⟩|b⟩) = (−1)^{f(x)·b} |x⟩|a⟩|b⟩`. The single oracle call
`O`, conjugated by the response Hadamards, becomes the diagonal phase `Z^{f(x)}`: `H_r` sends `|b⟩`
to `|±⟩`, `O` kicks the phase `(−1)^{f(x)}` on the `|−⟩` branch (`b = 1`) and nothing on the `|+⟩`
branch (`b = 0`) via `op_tmul_qubitMinus` / `op_tmul_qubitPlus`, and `H_r` returns `|±⟩` to `|b⟩`.
This is where the *one* oracle call becomes a phase — the one-call analogue of the block's gate
identity `hadamardConj_targetXPow` (`H X^c H = Z^c`). -/
theorem hadamardConj_oracle_op (h : IsSearchBitFlipOracle f O) (x : Fin N) (a b : Fin 2) :
    hadResponse.op (O.op (hadResponse.op
        ((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis b))).vec))
      = ((-1 : ℂ) ^ ((f x).val * b.val))
          • ((quditBasis x).tmul ((qubitBasis a).tmul (qubitBasis b))).vec := by
  rw [hadResponse_op_tmul]
  rcases (by omega : b = 0 ∨ b = 1) with hb | hb <;> subst hb
  · -- `b = 0`: `H|0⟩ = |+⟩`, and `O` fixes it (eigenvalue `+1 = (−1)^{f(x)·0}`).
    rw [hadamardGate_evolvePure_qubitBasis_zero, h.op_tmul_qubitPlus,
      ← hadamardGate_evolvePure_qubitBasis_zero, hadResponse_op_tmul,
      hadamardGate_evolvePure_evolvePure]
    simp only [Fin.isValue, PureState.tmul_vec, qudit_space, quditBasis_vec, qubitBasis_vec,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, mul_zero, pow_zero]
    exact (one_smul ℂ _).symm
  · -- `b = 1`: `H|1⟩ = |−⟩`, and `O` kicks `(−1)^{f(x)} = (−1)^{f(x)·1}`.
    rw [hadamardGate_evolvePure_qubitBasis_one, h.op_tmul_qubitMinus, map_smul,
      ← hadamardGate_evolvePure_qubitBasis_one, hadResponse_op_tmul,
      hadamardGate_evolvePure_evolvePure]
    simp

/-- **The augmented oracle from one oracle call (N&C Exercise 6.5).** For **any** one-call bit-flip
oracle `O` for `f` (`IsSearchBitFlipOracle f O`), the augmented circuit `augmentedSearchOracle O`,
on the response work qubit supplied in `|0⟩`, fixes `|x⟩|q⟩|0⟩` up to the augmented-oracle phase: it
is an eigenstate whose eigenvalue is `−1` exactly when the item is a solution (`f(x) = 1`) *and* the
extra bit is `q = 0`, and `+1` otherwise. Equivalently,
`augmentedSearchOracle O |x⟩|q⟩|0⟩ = (−1)^{f(x) ∧ (q = 0)} |x⟩|q⟩|0⟩` — the mark
"solution ∧ `q = 0`" defining `O'`, for **every** item `x` of the search space, using **one** call
to `O` and the `x`-independent elementary gates `X_r`, `CNOT_{q→r}`, `H_r`, with the work qubit
returned to `|0⟩`.

The proof reduces the middle sandwich to `Z^{f(x)}` (`hadamardConj_oracle_op`) and tracks
`|x⟩|q⟩|0⟩` through the flanking permutation gates: `X_r` then `CNOT_{q→r}` carry `r` to `|1 ⊕ q⟩`,
`Z^{f(x)}` imprints `(−1)^{f(x)·(1 ⊕ q)}` (which is `−1` exactly when `f(x) = 1` and `q = 0`), and
`CNOT_{q→r}` then `X_r` return the response to `|0⟩`. -/
theorem augmentedSearchOracle_hasEigenstate (h : IsSearchBitFlipOracle f O)
    (x : Fin N) (q : Fin 2) :
    (augmentedSearchOracle O).HasEigenstate (if f x = 1 ∧ q = 0 then -1 else 1)
      ((quditBasis x).tmul ((qubitBasis q).tmul (qubitBasis 0))) := by
  rw [Evolution.HasEigenstate, augmentedSearchOracle]
  simp only [Evolution.comp_op, ContinuousLinearMap.comp_apply]
  rw [xFlipResponse_op_tmul, cnotExtraResponse_op_tmul, hadamardConj_oracle_op h, map_smul,
    cnotExtraResponse_op_tmul, map_smul, xFlipResponse_op_tmul]
  congr 1
  · fin_cases q <;>
      rcases (show f x = 0 ∨ f x = 1 by omega) with hfx | hfx <;> rw [hfx] <;> simp
  · fin_cases q <;> rfl

end AxQM
