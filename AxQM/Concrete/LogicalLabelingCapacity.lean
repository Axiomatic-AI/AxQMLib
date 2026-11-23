/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Card

/-!
# Logical labeling for `n` spins: the largest effective pure state (Nielsen & Chuang, Ex. 7.44)

*Logical labeling* (§7.7.1, p. 334–335) prepares an **effective pure state** from a high-entropy
thermal NMR state in a single experiment (unlike temporal labeling, Ex. 7.42). For `n` nearly
identical spins in thermal equilibrium, the high-temperature deviation density matrix is diagonal in
the computational basis with *signal population* on the basis state `|b⟩` proportional to the total
magnetization `n - 2·(Hamming weight of b)` (this is `Z₁ + ⋯ + Zₙ`; the isotropic background is
unobservable because NMR observables are traceless). Two basis states carry the **same** population
iff they have the same Hamming weight, and the population strictly decreases with Hamming weight.

An *effective pure state* of a `d`-level manifold is `ρ = (1-ε)/d · I + ε · |ψ⟩⟨ψ|` — a rank-one
bump on top of the maximally mixed state — so its eigenvalue populations are **one distinguished
value strictly above `d-1` equal values**. *Logical labeling* applies a permutation of the
computational basis (a genuine reversible circuit) and isolates a sub-manifold of basis states;
since a permutation merely relabels populations, the manifolds it can isolate are **arbitrary**
subsets of the `2ⁿ` basis states. So the effective pure states constructible from the thermal state
are exactly the subsets `S` of basis states whose populations have the one-large-rest-equal shape.

**Exercise 7.44** (*hint: use states of Hamming weight `n/2`*) asks for the **largest** such
effective pure state. The excited (equal-population) part must be a set of basis states of one
common Hamming weight `k`, of which there are `C(n, k) = n.choose k`; this is maximised at the
central weight `k = ⌊n/2⌋` (`Nat.choose_le_middle`), giving `n.choose (n/2)` excited states, plus
one distinguished ground state. Hence

Maximal dimension of an effective pure state obtainable by logical labeling.

In qubit terms that is `⌊log₂(n.choose (n/2) + 1)⌋` logical qubits; note the dimension need *not* be
a power of two, exactly as N&C remark. For `n = 3` it is `C(3,1) + 1 = 4`, matching the `4 × 4`
effective-pure block `8|00⟩⟨00| − 2I` of the worked three-spin example (Ex. 7.43,
`Concrete/LogicalLabeling.lean`).

## What is proved

Modelling a computational basis state `|b⟩` by the `Finset (Fin n)` of its spin-`|1⟩` positions
(Hamming weight = `Finset.card`), and a manifold of basis states by a `Finset (Finset (Fin n))`:

* `magPop n A` — the signal population `n − 2·|A|` of the basis state `A` (magnetization, N&C's
  `6 − 4w` for `n = 3` up to the physically irrelevant overall scale `2`);
  `magPop_eq_iff` — two basis states have equal population iff equal Hamming weight.
* `IsEffectivePureManifold n S` — `S` has the effective-pure population profile: a distinguished
  `g ∈ S` strictly above all others, and all the others mutually equal.
* `maxEffectivePureDim n := n.choose (n / 2) + 1` — the claimed answer.
* `IsEffectivePureManifold.card_le` — **optimality**: every effective-pure manifold has
  `S.card ≤ maxEffectivePureDim n` (the excited states share a Hamming weight, so there are at most
  `n.choose k ≤ n.choose (n/2)` of them, `Nat.choose_le_middle`).
* `exists_isEffectivePureManifold` — **achievability**: for `n ≥ 1` an effective-pure manifold of
  cardinality exactly `maxEffectivePureDim n` exists (excited = the `n.choose (n/2)` states of
  weight `⌈n/2⌉ = n − n/2 ≥ 1`, ground = `|0…0⟩ = ∅`, population `n`).
* `maxEffectivePureDim_one` / `_two` / `_three` — the answer for `n = 1, 2, 3` (`2, 3, 4`); `n = 3`
  reproduces the worked example.

The exercise's answer is a combinatorial optimisation over the population multiset of the thermal
state. The statements here are over `Finset (Fin n)`, `ℤ`, and `Nat.choose`. The statement of
Exercise 7.44 is in `AxQM/NC/Ch7/Exercise7_44.lean`. Compare the labeling exercises
`AxQM/Concrete/TemporalLabeling.lean` (7.42) and `AxQM/Concrete/LogicalLabeling.lean` (7.43).

## Fidelity

N&C's thermal populations are `n − 2w` up to the overall scale (`6 − 4w = 2(3 − 2w)` for `n = 3`),
which is physically irrelevant since only the traceless signal is measured; `magPop` records exactly
`n − 2w`. The effective-pure profile (one distinguished level strictly above `d − 1` equal levels)
is the eigenvalue structure of `(1-ε)/d · I + ε|ψ⟩⟨ψ|` for arbitrary `d` — capturing the
non-power-of-two generality N&C explicitly note. Both bounds are proved: the maximum is pinned
exactly at
`n.choose (n/2) + 1`, neither over- nor under-stated.
-/

namespace AxQM.Concrete

/-- **Signal population of an `n`-spin computational basis state** (Nielsen & Chuang §7.7.1).
Modelling the basis state `|b⟩` by the set `A : Finset (Fin n)` of its spin-`|1⟩` positions (so the
Hamming weight of `b` is `A.card`), its high-temperature deviation population is the total
magnetization `n − 2·|A|` (the eigenvalue of `Z₁ + ⋯ + Zₙ`). For `n = 3` this is `(3, 1, 1, −1, …)`,
i.e. N&C's `(6, 2, 2, −2, …)` up to the physically irrelevant overall scale `2`. -/
def magPop (n : ℕ) (A : Finset (Fin n)) : ℤ := (n : ℤ) - 2 * (A.card : ℤ)

/-- **Equal population iff equal Hamming weight.** Two `n`-spin basis states carry the same thermal
signal population exactly when they have the same Hamming weight `A.card` — the key degeneracy that
logical labeling exploits. -/
theorem magPop_eq_iff {n : ℕ} (A B : Finset (Fin n)) :
    magPop n A = magPop n B ↔ A.card = B.card := by
  simp only [magPop]
  omega

/-- **An effective-pure manifold.** A set `S` of `n`-spin computational basis states has the
population profile of an *effective pure state* `(1-ε)/d · I + ε|ψ⟩⟨ψ|`: there is a distinguished
ground state `g ∈ S` whose population strictly exceeds that of every other state of `S`, and all the
non-ground states of `S` share one common population. (Since logical labeling permutes the
populations, an arbitrary such subset is isolable, so these are exactly the effective pure states
constructible by logical labeling.) -/
def IsEffectivePureManifold (n : ℕ) (S : Finset (Finset (Fin n))) : Prop :=
  ∃ g ∈ S, (∀ A ∈ S, A ≠ g → magPop n A < magPop n g) ∧
    (∀ A ∈ S, ∀ B ∈ S, A ≠ g → B ≠ g → magPop n A = magPop n B)

/-- **The largest effective pure state constructible by logical labeling from `n` thermal spins**
(the answer to Exercise 7.44): dimension `n.choose (n/2) + 1` — the central binomial degeneracy
`C(n, ⌊n/2⌋)` of the Hamming-weight-`⌊n/2⌋` manifold, plus one distinguished ground state. -/
def maxEffectivePureDim (n : ℕ) : ℕ := n.choose (n / 2) + 1

/-- **Optimality (Exercise 7.44).** Every effective-pure manifold has at most
`maxEffectivePureDim n` states. Its non-ground states all share one Hamming weight `k` (equal
populations ⇒ equal weight, `magPop_eq_iff`), so they form a subset of the `n.choose k` weight-`k`
basis states (`Finset.card_powersetCard`), and `n.choose k ≤ n.choose (n/2)`
(`Nat.choose_le_middle`); adding the lone ground state gives the `+1`. -/
theorem IsEffectivePureManifold.card_le {n : ℕ} {S : Finset (Finset (Fin n))}
    (h : IsEffectivePureManifold n S) : S.card ≤ maxEffectivePureDim n := by
  obtain ⟨g, hgS, _hlt, heq⟩ := h
  have hcard : (S.erase g).card + 1 = S.card := Finset.card_erase_add_one hgS
  have hbound : (S.erase g).card ≤ n.choose (n / 2) := by
    rcases (S.erase g).eq_empty_or_nonempty with he | ⟨A₀, hA₀⟩
    · simp [he]
    · have hA₀S : A₀ ∈ S := (Finset.mem_erase.mp hA₀).2
      have hA₀g : A₀ ≠ g := (Finset.mem_erase.mp hA₀).1
      set k := A₀.card with hk
      have hsub : S.erase g ⊆ Finset.powersetCard k (Finset.univ : Finset (Fin n)) := by
        intro A hA
        have hAS : A ∈ S := (Finset.mem_erase.mp hA).2
        have hAg : A ≠ g := (Finset.mem_erase.mp hA).1
        have hpop : magPop n A = magPop n A₀ := heq A hAS A₀ hA₀S hAg hA₀g
        have hcardA : A.card = k := (magPop_eq_iff A A₀).mp hpop
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ A, hcardA⟩
      calc (S.erase g).card
          ≤ (Finset.powersetCard k (Finset.univ : Finset (Fin n))).card := Finset.card_le_card hsub
        _ = (Finset.univ : Finset (Fin n)).card.choose k := Finset.card_powersetCard k _
        _ = n.choose k := by rw [Finset.card_univ, Fintype.card_fin]
        _ ≤ n.choose (n / 2) := Nat.choose_le_middle k n
  unfold maxEffectivePureDim
  omega

/-- **Achievability (Exercise 7.44).** For `n ≥ 1` spins there is an effective-pure manifold of
cardinality exactly `maxEffectivePureDim n`. Take the excited manifold to be the `n.choose (n/2)`
basis states of Hamming weight `k = ⌈n/2⌉ = n − n/2 ≥ 1` (all with population `n − 2k < n`, using
`Nat.choose_symm` to rewrite `n.choose (n − n/2) = n.choose (n/2)`), and the ground state to be
`|0…0⟩ = ∅` (population `n`), which is heavier and distinct from every weight-`k` state. -/
theorem exists_isEffectivePureManifold {n : ℕ} (hn : 1 ≤ n) :
    ∃ S : Finset (Finset (Fin n)),
      IsEffectivePureManifold n S ∧ S.card = maxEffectivePureDim n := by
  have hk1 : 1 ≤ n - n / 2 := by omega
  set k := n - n / 2 with hk
  set P := Finset.powersetCard k (Finset.univ : Finset (Fin n)) with hP
  have hnotmem : (∅ : Finset (Fin n)) ∉ P := by
    rw [hP, Finset.mem_powersetCard]
    rintro ⟨-, hcard⟩
    rw [Finset.card_empty] at hcard
    omega
  refine ⟨insert ∅ P, ⟨∅, Finset.mem_insert_self _ _, ?_, ?_⟩, ?_⟩
  · intro A hA hA0
    have hAP : A ∈ P := (Finset.mem_insert.mp hA).resolve_left hA0
    have hcardA : A.card = k := (Finset.mem_powersetCard.mp hAP).2
    simp only [magPop, hcardA, Finset.card_empty]
    omega
  · intro A hA B hB hA0 hB0
    have hAP : A ∈ P := (Finset.mem_insert.mp hA).resolve_left hA0
    have hBP : B ∈ P := (Finset.mem_insert.mp hB).resolve_left hB0
    exact (magPop_eq_iff A B).mpr
      ((Finset.mem_powersetCard.mp hAP).2.trans (Finset.mem_powersetCard.mp hBP).2.symm)
  · rw [Finset.card_insert_of_notMem hnotmem, hP, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, maxEffectivePureDim, hk, Nat.choose_symm (by omega : n / 2 ≤ n)]

/-- The largest effective pure state from a single thermal spin has dimension `2` — the thermal
state of one spin is already an effective pure qubit. -/
theorem maxEffectivePureDim_one : maxEffectivePureDim 1 = 2 := by decide

/-- The largest effective pure state from two thermal spins has dimension `3`. -/
theorem maxEffectivePureDim_two : maxEffectivePureDim 2 = 3 := by decide

/-- The largest effective pure state from three thermal spins has dimension `4`, reproducing the
worked three-spin example: the `4 × 4` effective-pure block `8|00⟩⟨00| − 2I` (Exercise 7.43). -/
theorem maxEffectivePureDim_three : maxEffectivePureDim 3 = 4 := by decide

end AxQM.Concrete
