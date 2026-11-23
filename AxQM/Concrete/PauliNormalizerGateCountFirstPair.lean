/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliNormalizerGateCountPair
import AxQM.Concrete.PauliNormalizerFirstPair

/-!
# Concrete: the `O(n)` gate-count of the first-wire reduction (N&C Theorem 10.6)

*(Theorem 10.6, N&C §10.5.2, p. 461.)*

Nielsen & Chuang **Theorem 10.6** asserts that a Pauli normalizer `U ∈ N(Gₙ)` may be composed, up to
a global phase, from **`O(n²)`** Hadamard/phase/CNOT gates. The structural converse
(`isPauliNormalizer_eq_smul_cliffordCircuit`) gives the circuit; the quantitative part is the gate
count, bounded through the Figure 10.9 synthesis, using the length calculus of the definitions
(`AxQM/Concrete/PauliNormalizerGateCount.lean`), the constant gadget bounds
(`AxQM/Concrete/PauliNormalizerGateCountGadgets.lean`), the single-generator reduction bound
(`AxQM/Concrete/PauliNormalizerGateCountReduce.lean`, `≤ 2·n + 2`) and the anticommuting-pair
reduction bound (`AxQM/Concrete/PauliNormalizerGateCountPair.lean`,
`exists_cliffordCircuit_reducePair_length_le ≤ 6·n + 20`).

This file proves the **per-level linear bound** on the first-wire reduction
circuit `B` of `IsPauliNormalizer.exists_cliffordCircuit_fixFirstPair` (the opening move of
the Figure 10.9 inductive step, which left-composes an `(n+1)`-qubit normalizer `U` with a Clifford
circuit `B` so that `B·U` fixes the first-wire generators `X₀, Z₀` under conjugation). That circuit
is `B = G ++ (swapWires c 0 ++ E)`:

* `E` reduces the anticommuting image pair `(σ X₀, σ Z₀)` to the canonical `(X_c, Z_c)` on a pivot
  wire `c` (`exists_cliffordCircuit_reducePair_length_le`, `≤ 6·(n+1) + 20` here, as the pair lives
  on `Fin (n+1)`);
* `swapWires c 0` relocates the pivot to wire `0` (`length_swapWires_le`, `≤ 3`);
* `G` is one single-wire `onWire` sign gadget on wire `0` cancelling the residual `±1` signs
  `ε(X₀), ε(Z₀)` (`exists_cliffordCircuit_onWire_act_sign_length_le`, `≤ 9`).

So `|B| ≤ 9 + 3 + (6·(n+1) + 20) = 6·(n+1) + 32` — the per-level `O(n)` overhead in the `O(n²)`
unrolling of the Figure 10.9 recurrence.

The lemma `exists_cliffordCircuit_fixFirstPair` gives its circuit only existentially, so the length
bound reconstructs the reduction, using the length-annotated
`exists_cliffordCircuit_reducePair_length_le` for the pair reduction, and re-proves the two
conjugation-fixing facts. These follow from the plumbing lemma `normalizer_first_fix` (with its
helpers `conj_split`, `conj_circuit_smul`) of `AxQM/Concrete/PauliNormalizerFirstPair.lean`, which
is stated for an *arbitrary* reduction circuit `A` and sign gadget `G`, so the reconstructed
`B = G ++ A` fixes `X₀, Z₀` by the same matrix identity as the original lemma. The action/sign
content is identical to the original lemma; the length is additionally bounded.
-/

open Matrix

noncomputable section

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### The first-wire reduction costs `O(n)` gates -/

/-- **The first-wire reduction of a Pauli normalizer costs `≤ 6·(n+1) + 32` gates.** The
length-annotated companion of `IsPauliNormalizer.exists_cliffordCircuit_fixFirstPair` (N&C Exercise
10.40, Figure 10.9 setup): for any `(n+1)`-qubit Pauli normalizer `U`, there is a Clifford circuit
`B` such that `B.toMatrix * U` is again a Pauli normalizer, **fixes the first-wire generators
`X₀, Z₀` exactly** under conjugation, and has `B.length ≤ 6·(n+1) + 32`.

The circuit is `B = G ++ (swapWires c 0 ++ E)`, reconstructed with the length-annotated pair
reduction:

* the anticommuting image pair `p = σ X₀`, `q = σ Z₀` (anticommuting because `X₀, Z₀` do and the
  normalizer's signed permutation is symplectic, `exists_signedPerm_symplectic`) is reduced to
  `(X_c, Z_c)` by `exists_cliffordCircuit_reducePair_length_le`, whose `E : CliffordCircuit (n+1)`
  has `≤ 6·(n+1) + 20` gates;
* `swapWires c 0` relocates the pivot to wire `0` (`length_swapWires_le`, `≤ 3`, phase-free);
* one single-wire `onWire` sign gadget `G` on wire `0` cancels the residual `±1` signs
  `ε(X₀), ε(Z₀)` (`exists_cliffordCircuit_onWire_act_sign_length_le`, `≤ 9`; each sign squares to
  `1`).

so `|B| = |G| + |swapWires c 0| + |E| ≤ 9 + 3 + (6·(n+1) + 20) = 6·(n+1) + 32`. The action/sign
content (normalizer closure and the two fixing facts) is proved exactly as in
`exists_cliffordCircuit_fixFirstPair`; only the length is newly tracked. This is the per-level
`O(n)` overhead of the Figure 10.9 recurrence toward the `O(n²)` gate-count headline. -/
theorem IsPauliNormalizer.exists_cliffordCircuit_fixFirstPair_length_le
    {U : Matrix (Fin (n + 1) → Fin 2) (Fin (n + 1) → Fin 2) ℂ} (hU : IsPauliNormalizer U) :
    ∃ B : CliffordCircuit (n + 1),
      IsPauliNormalizer (B.toMatrix * U) ∧
        ((B.toMatrix * U) * pauliString (xGenPauli 0) * (B.toMatrix * U)ᴴ
            = pauliString (xGenPauli 0)) ∧
          ((B.toMatrix * U) * pauliString (zGenPauli 0) * (B.toMatrix * U)ᴴ
              = pauliString (zGenPauli 0)) ∧
            B.length ≤ 6 * (n + 1) + 32 := by
  obtain ⟨σ, ε, hε, hconj, hsymp⟩ := hU.exists_signedPerm_symplectic
  -- `X₀` and `Z₀` anticommute, hence so do their images `p = σ X₀`, `q = σ Z₀`.
  have hXZ : Odd (pauliAnticommCount (xGenPauli (0 : Fin (n + 1))) (zGenPauli 0)) := by
    rw [odd_pauliAnticommCount_zGenPauli_iff]; left; simp [xGenPauli]
  have hpq : Odd (pauliAnticommCount (σ (xGenPauli 0)) (σ (zGenPauli 0))) := by
    rw [← Nat.not_even_iff_odd]; rw [← Nat.not_even_iff_odd] at hXZ
    exact fun h => hXZ ((hsymp (xGenPauli 0) (zGenPauli 0)).mp h)
  -- Reduce the pair `(p, q)` to `(X_c, Z_c)` with a length-bounded circuit, then swap the pivot.
  obtain ⟨E, c, hEp, hEsp, hEq, hEsq, hElen⟩ :=
    exists_cliffordCircuit_reducePair_length_le (σ (xGenPauli 0)) (σ (zGenPauli 0)) hpq
  set A := swapWires c 0 ++ E with hA
  have hAp : A.act (σ (xGenPauli 0)) = xGenPauli 0 := by
    rw [hA, CliffordCircuit.act_append, hEp, act_swapWires_xGenPauli]
  have hAq : A.act (σ (zGenPauli 0)) = zGenPauli 0 := by
    rw [hA, CliffordCircuit.act_append, hEq, act_swapWires_zGenPauli]
  have hAsp : A.sign (σ (xGenPauli 0)) = 1 := by
    rw [hA, CliffordCircuit.sign_append, hEsp, sign_swapWires, mul_one]
  have hAsq : A.sign (σ (zGenPauli 0)) = 1 := by
    rw [hA, CliffordCircuit.sign_append, hEsq, sign_swapWires, mul_one]
  -- A single-wire sign gadget on wire `0` correcting the residual signs `ε(X₀), ε(Z₀)` (`≤ 9`).
  obtain ⟨G, hGaX, hGsX, hGaZ, hGsZ, -, hGlen⟩ :=
    exists_cliffordCircuit_onWire_act_sign_length_le (0 : Fin (n + 1)) (aX := 1) (aZ := 3)
      (by decide) (by decide) (by decide) (hε (xGenPauli 0)) (hε (zGenPauli 0))
  have hsq : ∀ a, ε a * ε a = 1 := fun a => by rcases hε a with h | h <;> rw [h] <;> ring
  refine ⟨G ++ A, (cliffordCircuit_isPauliNormalizer (G ++ A)).mul hU, ?_, ?_, ?_⟩
  · exact normalizer_first_fix G A U (xGenPauli 0) (σ (xGenPauli 0)) (ε (xGenPauli 0))
      (hsq (xGenPauli 0)) (hconj (xGenPauli 0)) hAp hAsp hGaX hGsX
  · exact normalizer_first_fix G A U (zGenPauli 0) (σ (zGenPauli 0)) (ε (zGenPauli 0))
      (hsq (zGenPauli 0)) (hconj (zGenPauli 0)) hAq hAsq hGaZ hGsZ
  · -- `|G ++ (swapWires c 0 ++ E)| = |G| + |swapWires c 0| + |E| ≤ 9 + 3 + (6·(n+1) + 20)`
    have hsw : (swapWires c (0 : Fin (n + 1))).length ≤ 3 := length_swapWires_le c 0
    rw [hA]
    simp only [List.length_append]
    omega

end AxQM.Concrete

end
