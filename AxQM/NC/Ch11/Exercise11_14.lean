/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.ConditionalEntropy
import AxQM.Postulates.API.Entropy
import AxQM.NC.Ch11.Theorem11_8
import AxQM.NC.Ch2.Exercise2_78

/-!
# Nielsen & Chuang, Exercise 11.14 — entanglement and negative conditional entropy

**Exercise 11.14 (Entanglement and negative conditional entropy).** Suppose `|AB⟩` is a pure
state of a composite system belonging to Alice and Bob. Show that `|AB⟩` is entangled if and only
if `S(B|A) < 0`.

Here `S(B|A) = S(A,B) − S(A)` is the quantum conditional entropy (N&C eq. (11.62)), and a pure
bipartite state is **entangled** exactly when it is not a product state `|a⟩|b⟩`.

## The mathematics

For a pure joint state `|AB⟩` the joint entropy vanishes, `S(A,B) = 0`
(`PureState.vonNeumannEntropy_toState_eq_zero`), so the conditional entropy collapses to
`S(B|A) = S(A,B) − S(A) = −S(A)`, where `S(A) = S(ρ_A)` is the entropy of the reduced state
`ρ_A = Tr_B|AB⟩⟨AB|` (`State.reducedLeft`). The library's canonical conditional entropy
`State.condVonNeumannEntropy` is `S(A|B) = S(A,B) − S(B)`; for a *pure* state the two reduced
entropies coincide, `S(A) = S(B)` (Theorem 11.8(3),
`PureState.vonNeumannEntropy_reducedLeft_eq_reducedRight`), so `S(A|B) = S(B|A) = −S(A)` — the
conditioning direction is immaterial, and either equals `−S(ρ_A)`. This identification is the
bridge lemma `condVonNeumannEntropy_toState_eq_neg_reducedLeft`.

The equivalence then reduces to a statement about `S(ρ_A)`:

* `|AB⟩` entangled `⟺` `ρ_A` is **not** pure — a bipartite pure state is a product state iff its
  reduced state is pure (Exercise 2.78, `PureState.isProduct_iff_isPure_reducedLeft`);
* `ρ_A` not pure `⟺` `S(ρ_A) ≠ 0` — the von Neumann entropy vanishes exactly on pure states
  (Theorem 11.8(1), `State.vonNeumannEntropy_eq_zero_iff_isPure`);
* `S(ρ_A) ≠ 0 ⟺ S(ρ_A) > 0` — the entropy is non-negative (`State.vonNeumannEntropy_nonneg`);
* `S(ρ_A) > 0 ⟺ −S(ρ_A) < 0 ⟺ S(B|A) < 0`.

Chaining these gives `|AB⟩` entangled `⟺ S(B|A) < 0`.

## Results (the item's formalisation)

* `PureState.condVonNeumannEntropy_toState_eq_neg_reducedLeft` — the computation
  `S(B|A) = −S(ρ_A)` for a pure joint state (the bridge to N&C's `S(B|A) = S(A,B) − S(A)`).
* `PureState.not_isProduct_iff_condVonNeumannEntropy_neg` — **the exercise:** a bipartite pure
  state is entangled (`¬ IsProduct`) iff its conditional entropy is negative.

The proof uses the conditional entropy `State.condVonNeumannEntropy`
(`AxQM/Core/ConditionalEntropy.lean`), the purity/entropy characterisations of
`AxQM/NC/Ch11/Theorem11_8.lean`, and the product-state/reduced-purity equivalence of
`AxQM/NC/Ch2/Exercise2_78.lean`.
-/

noncomputable section

namespace AxQM

namespace PureState

variable {S T : QSystem}

/-- **The conditional entropy of a pure joint state equals `−S(ρ_A)`.** For a pure bipartite state
`|AB⟩` the joint entropy vanishes (`S(A,B) = 0`) and the two reduced entropies agree
(`S(ρ_A) = S(ρ_B)`, Theorem 11.8(3)), so the conditional entropy
`S(A|B) = S(A,B) − S(B) = −S(ρ_A)`. As `−S(ρ_A) = S(A,B) − S(A)` this is exactly N&C's
`S(B|A)`: for a pure state the conditioning direction is immaterial. -/
theorem condVonNeumannEntropy_toState_eq_neg_reducedLeft (ψ : PureState (S.compose T)) :
    ψ.toState.condVonNeumannEntropy = -ψ.toState.reducedLeft.vonNeumannEntropy := by
  rw [State.condVonNeumannEntropy_def, ψ.vonNeumannEntropy_toState_eq_zero,
    ψ.vonNeumannEntropy_reducedLeft_eq_reducedRight]
  ring

/-- **Nielsen & Chuang, Exercise 11.14.** A pure bipartite state `|AB⟩` is entangled — i.e. *not* a
product state `|a⟩|b⟩` (`¬ ψ.IsProduct`) — if and only if its conditional entropy is negative,
`S(B|A) < 0`. Since `S(B|A) = −S(ρ_A)` for a pure joint state
(`condVonNeumannEntropy_toState_eq_neg_reducedLeft`), this is negative exactly when `S(ρ_A) > 0`,
i.e. when the reduced state `ρ_A` is mixed, which (Exercise 2.78) is exactly the failure of `|AB⟩`
to factor. -/
theorem not_isProduct_iff_condVonNeumannEntropy_neg (ψ : PureState (S.compose T)) :
    ¬ ψ.IsProduct ↔ ψ.toState.condVonNeumannEntropy < 0 := by
  rw [ψ.condVonNeumannEntropy_toState_eq_neg_reducedLeft, ψ.isProduct_iff_isPure_reducedLeft,
    ← State.vonNeumannEntropy_eq_zero_iff_isPure, neg_lt_zero,
    (ψ.toState.reducedLeft.vonNeumannEntropy_nonneg).lt_iff_ne]
  exact ne_comm

end PureState

end AxQM
