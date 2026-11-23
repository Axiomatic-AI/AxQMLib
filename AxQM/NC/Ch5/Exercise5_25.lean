/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuditTriplePermGate
import AxQM.Concrete.DiscreteLogOracle

/-!
# Nielsen & Chuang, Exercise 5.25 — the discrete-logarithm black box `U`

*(N&C p. 240, §5.4.2 "Discrete logarithms".)*

Construct quantum circuit for black box U:|x1>|x2>|y> -> |x1>|x2>|y XOR b^{x1}a^{x2}>; count
operations.

In the quantum discrete-logarithm algorithm (§5.4.2) the base `a` has multiplicative order `r`, the
target is `b = aˢ`, and the black box `U` evaluates the discrete-log function
`f(x₁, x₂) = b^{x₁} a^{x₂} = a^{s·x₁ + x₂} (mod N)` into a third register (step 2 supplies that
register in `|0⟩`; steps 3–6 Fourier-transform and measure to recover `s`).

## The formalisation

The two exponent registers `|x₁⟩`, `|x₂⟩` and the value register `|y⟩`
are the three qudit registers `qudit d₁`, `qudit d₂`, `qudit N`; the black box is the reversible
map of the *joint* computational basis

  `(x₁, x₂, y) ↦ (x₁, x₂, y ⊕ b^{x₁} a^{x₂})`

which fixes the two exponent registers and writes the discrete-log value into the value register.
The black box is this reversible operation, realised as a unitary `Evolution` (Postulate 5),
together with the theorem that it performs the stated transform on every basis state, and its
`|0⟩`-target specialisation (the form the algorithm actually invokes).

* `discreteLogOracle a b d₁ d₂` — **the black box `U`:** the unitary `Evolution` of
  `qudit d₁ ⊗ qudit d₂ ⊗ qudit N` that permutes the computational basis by
  `Concrete.dlogOraclePerm a b d₁ d₂`. It is the three-register basis-permutation gate
  `quditTriplePerm` (`AxQM/Postulates/API/QuditTriplePermGate.lean`) at that permutation — a genuine
  reversible quantum operation (unitarity is discharged in producing the `Evolution`).
* `discreteLogOracle_evolvePure_quditBasis` — **the exercise:**
  `U |x₁⟩ ⊗ |x₂⟩ ⊗ |y⟩ = |x₁⟩ ⊗ |x₂⟩ ⊗ |y ⊕ b^{x₁} a^{x₂}⟩` for all `x₁, x₂, y`, the full truth
  table of the black box (`⊕` the value register's additive group; see "On `⊕`" below).
* `discreteLogOracle_evolvePure_quditBasis_zero` — **the algorithm's use:** with the value register
  in `|0⟩`, `U |x₁⟩ ⊗ |x₂⟩ ⊗ |0⟩ = |x₁⟩ ⊗ |x₂⟩ ⊗ |b^{x₁} a^{x₂}⟩` — the oracle *computes* the
  discrete-log value state `|f(x₁,x₂)⟩`, the object steps 3–6 consume.

## Design notes

* **What "the circuit" is (fidelity).** The exercise's verifiable content is the
  *transformation*: `U` is a permutation of the joint computational basis (it sends basis states to
  basis states — the hallmark of a classical reversible circuit), and `discreteLogOracle` is that
  permutation realised as an explicitly-constructed unitary gate. The two exponent registers `x₁`,
  `x₂` and the value register `y` are all present as separate registers, with the value
  `b^{x₁} a^{x₂}` exactly as printed and no added hypotheses or dimension specialisation. The
  standard elementary-gate realisation is *modular exponentiation* — a running product register,
  multiplied by `b^{2ᵏ}` controlled on bit `k` of `x₁` and by `a^{2ᵏ}` controlled on bit `k` of `x₂`
  (reversible modular multiplication, then copy-out and uncompute) — but exhibiting that gate
  *decomposition* needs an elementary-gate circuit framework carrying reversible modular arithmetic
  over the registers, which is not expressed here (cf. the ripple-carry
  decomposition of Exercise 4.36 and the QFT gate counts of Problem 5.1). This file formalises the
  transformation the circuit performs — the exercise's verifiable content — over the
  three-register basis-permutation gate.

* **On `⊕` (the one fidelity choice, made explicit).** N&C fixes `⊕` in two places, and they point
  in the same direction. §5.4.2 writes "`⊕` denotes bitwise addition modulo 2" — a statement about a
  *qubit-string* value register; the general hidden-subgroup black box of §5.4.3 relaxes this to
  "`⊕` an appropriately chosen binary operation on `X`". Here the value register is `qudit N` (`Fin
  N`) — the exact-fit register that holds the mod-`N` value `b^{x₁} a^{x₂}` with no wasted states —
  and its natural reversible `⊕` is addition in the register's own additive group `Fin N ≅ ZMod N`.
  This is *forced by the register*, not a weakening: bitwise XOR is not even a closed operation on
  `Fin N` unless `N` is a power of two, so realising the literal §5.4.2 XOR would require enlarging
  the register to `Fin 2ᴸ` (`L = ⌈log₂ N⌉`) and carrying the representability bound `N ≤ 2ᴸ` — an
  *added hypothesis* — whereas `+ mod N` needs no hypothesis at all and keeps the claim over an
  arbitrary value register `Fin N`. The choice also matches the library's established oracle
  convention: the modular adder of Exercise 4.36 (`modFourAdder`, whose N&C statement is itself `|x,
  y⟩ → |x, x + y mod 4⟩`) takes its `⊕` to be the register's additive group, as do the single-bit
  `Fin 2` (= XOR) Deutsch (§1.4.3) and marking (Exercise 6.7) oracles. And it is physically
  inconsequential for the algorithm, which *always* supplies the target in `|0⟩`: there `0 ⊕ v = 0 +
  v = v` for either convention, so `U` writes exactly the value state `|b^{x₁} a^{x₂}⟩`
  (`discreteLogOracle_evolvePure_quditBasis_zero`) — the object steps 3–6 consume — independently of
  how `⊕` is modelled.

* **"How many elementary operations are required?"** This is a gate-count / circuit-complexity claim
  — the answer is `O(L³)` for `L = ⌈log N⌉` bits (two modular exponentiations, each `O(L³)`). Like
  the operation counts throughout §5.4 (and the "as useful as" reductions of Exercises 5.21–5.23),
  it is an efficiency statement that is not expressed here; it is recorded in
  prose, not as a Lean theorem.

## The declarations

The formalisation of this exercise is spread over three files:

* `AxQM/Concrete/DiscreteLogOracle.lean` — `Concrete.dlogValueIndex a b i j : Fin N` (the register
  index of `b^i a^j mod N`) and `Concrete.dlogOraclePerm a b d₁ d₂ : Equiv.Perm (Fin d₁ × Fin d₂ ×
  Fin N)` (`(x₁, x₂, y) ↦ (x₁, x₂, y + b^{x₁} a^{x₂})`, with `dlogOraclePerm_apply`).
* `AxQM/Postulates/API/QuditTriplePermGate.lean` — the general three-register basis-permutation
  gate: `quditTripleBasis` (with `quditTripleBasis_apply'` / `quditTripleBasis_apply`) and
  `quditTriplePerm σ` (with truth tables `quditTriplePerm_op_tmul` /
  `quditTriplePerm_evolvePure_quditBasis`), the three-register companion of `quditPairPerm`.
* `AxQM/NC/Ch5/Exercise5_25.lean` (this file) — `discreteLogOracle`, the exercise theorem
  `discreteLogOracle_evolvePure_quditBasis`, and its `|0⟩`-target corollary
  `discreteLogOracle_evolvePure_quditBasis_zero`, stated with the gate `quditTriplePerm`,
  `quditBasis`, `Evolution.evolvePure` and the product `⊗`, as `modFourAdder` is for Exercise 4.36.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **Exercise 5.25's black box `U`:** the discrete-logarithm oracle as a unitary `Evolution` of the
three registers `qudit d₁ ⊗ qudit d₂ ⊗ qudit N`. It permutes the joint computational basis by
`Concrete.dlogOraclePerm a b d₁ d₂` (`(x₁, x₂, y) ↦ (x₁, x₂, y ⊕ b^{x₁} a^{x₂})`), i.e. it is the
three-register basis-permutation gate `quditTriplePerm` at that permutation. Here `a, b : (ZMod N)ˣ`
are the base and target of the discrete logarithm (`b = aˢ`), supplied as parameters. -/
def discreteLogOracle {N : ℕ} [NeZero N] (a b : (ZMod N)ˣ) (d₁ d₂ : ℕ) :
    Evolution (qudit d₁ ⊗ qudit d₂ ⊗ qudit N) :=
  quditTriplePerm (Concrete.dlogOraclePerm a b d₁ d₂)

/-- **Nielsen & Chuang, Exercise 5.25.** The black box `U = discreteLogOracle a b d₁ d₂` performs
the transformation `|x₁⟩|x₂⟩|y⟩ → |x₁⟩|x₂⟩|y ⊕ b^{x₁} a^{x₂}⟩`: on every computational basis state
`|x₁⟩ ⊗ |x₂⟩ ⊗ |y⟩` it fixes the two exponent registers and shifts the value register by the
discrete-log value `b^{x₁} a^{x₂} (mod N)` (`Concrete.dlogValueIndex a b x₁ x₂`), the shift `⊕`
being addition in the value register's additive group `Fin N`. This full truth table is the content
of the exercise's "construct the black box `U`". -/
theorem discreteLogOracle_evolvePure_quditBasis {N : ℕ} [NeZero N] (a b : (ZMod N)ˣ) (d₁ d₂ : ℕ)
    (x₁ : Fin d₁) (x₂ : Fin d₂) (y : Fin N) :
    (discreteLogOracle a b d₁ d₂).evolvePure ((quditBasis x₁) ⊗ (quditBasis x₂) ⊗ (quditBasis y))
      = (quditBasis x₁) ⊗ (quditBasis x₂)
          ⊗ (quditBasis (y + Concrete.dlogValueIndex a b x₁.val x₂.val)) := by
  rw [discreteLogOracle, quditTriplePerm_evolvePure_quditBasis, Concrete.dlogOraclePerm_apply]

/-- **The black box computes the discrete-log value state** (the form the algorithm invokes, §5.4.2
step 2). With the value register supplied in `|0⟩`, `U |x₁⟩ ⊗ |x₂⟩ ⊗ |0⟩ = |x₁⟩ ⊗ |x₂⟩ ⊗ |f(x₁,x₂)⟩`
with `f(x₁,x₂) = b^{x₁} a^{x₂} (mod N)` (`Concrete.dlogValueIndex a b x₁ x₂`): the oracle *writes*
the discrete-log function into the value register. Since `0 ⊕ v = v`, this specialisation is
independent of the choice of `⊕` on the value register. -/
theorem discreteLogOracle_evolvePure_quditBasis_zero {N : ℕ} [NeZero N] (a b : (ZMod N)ˣ)
    (d₁ d₂ : ℕ) (x₁ : Fin d₁) (x₂ : Fin d₂) :
    (discreteLogOracle a b d₁ d₂).evolvePure ((quditBasis x₁) ⊗ (quditBasis x₂) ⊗ (quditBasis 0))
      = (quditBasis x₁) ⊗ (quditBasis x₂)
          ⊗ (quditBasis (Concrete.dlogValueIndex a b x₁.val x₂.val)) := by
  rw [discreteLogOracle_evolvePure_quditBasis, zero_add]

end AxQM
