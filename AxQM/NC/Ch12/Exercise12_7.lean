/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.ArakiLiebEqualityConditions
import AxQM.Postulates.API.OrthogonalStateCloning
import AxQM.NC.Ch12.Theorem12_6
import ToMathlib.Analysis.SpecialFunctions.ShannonEntropy

/-!
# Nielsen & Chuang, Exercise 12.7 — the qubit data-compression source `ρ = p|0⟩⟨0| + (1−p)|1⟩⟨1|`

Outline circuit to compress qubit source rho = p|0><0|+(1-p)|1><1| into nR qubits.

## What is formalisable here

Its **headline verb** — "outline the construction
of a circuit" — is an open-ended engineering/description prompt with no canonical proposition
(the same reading as Exercise 12.6's parts 2–3). But, exactly as with Exercise 12.6 (part 1, the
explicit `C_X`) and Exercise 12.1, the exercise still carries a **genuine, verifiable mathematical
core**, which we formalise:

1. the entropy the exercise writes as its compression threshold, `S(ρ) = H(p)`; and
2. the achievability claim it actually asserts — reliable compression into `nR` qubits for every
   rate `R > H(p)`.

What is *not* formalised is the circuit outline itself (no proposition to state). N&C's pedagogical
point is precisely that this source is **diagonal in the computational basis**, so — unlike the
rotated typical basis of Box 12.4 (Exercise 12.6) — the compression is *classical*: one runs a
reversible classical compressor on the bit string. That structural observation is the content of the
"outline", but the concrete circuit is a description, not a claim.

## The mathematical residue, and why it is faithful (not a weakening)

The source `ρ = p|0⟩⟨0| + (1−p)|1⟩⟨1|` mixes the **orthogonal** computational states `|0⟩`, `|1⟩`.
This is the exact orthogonal counterpoint to Exercise 11.12's `ρ' = p|0⟩⟨0| + (1−p)|+⟩⟨+|`, which
mixes the **non-orthogonal** `|0⟩` and `|+⟩`:

* for `ρ'` (11.12) the classical bound is strict, `S(ρ') < H(p)`
  (`vonNeumannEntropy_entropyComparisonState_lt`);
* for `ρ` (12.7) the two states are orthogonal, so the classical bound is **saturated**,
  `S(ρ) = H(p)` exactly — the diagonal eigenvalues are `p` and `1 − p`.

`H(p)` is the binary Shannon entropy `Real.entropy ![p, 1 − p]` (in nats), and the achievability
threshold `R > H(p)` is `H(p) < R · log 2` (a qubit rate `R` converts to nats by `· log 2`), as in
the library's Schumacher convention. The compression claim is **Schumacher's theorem (Theorem 12.6)
applied to this source** — we *cite* the already-formalised direct part, not re-prove it.

## Contents (the item's formalisation)

* `qubitClassicalSource` — the source `ρ(p) = p|0⟩⟨0| + (1−p)|1⟩⟨1|`, as the mixture
  (`State.mix`) of the computational pure states `|0⟩, |1⟩` with weights `p, 1 − p`.
* `qubitClassicalSource_eq_mixPair` — its literal binary-mixture form
  `ρ(p) = mixPair p |0⟩⟨0| |1⟩⟨1|`, so the `State.mix` packaging is the two-outcome mixture the
  exercise writes.
* `qubitClassicalSource_vonNeumannEntropy` — **`S(ρ) = H(p)`.** The exercise's entropy identity: the
  von Neumann entropy of the source equals the binary Shannon entropy of the mixing weights, because
  `|0⟩, |1⟩` are orthonormal (`State.vonNeumannEntropy_mix_toState_orthonormal`).
* `qubitClassicalSource_reliablyCompressible` — **the achievability claim.** For every rate with
  `H(p) < R · log 2` (i.e. `R > H(p)`), the source is reliably compressible at rate `R`, by the
  direct part of Schumacher's theorem (`State.reliablyCompressible_of_vonNeumannEntropy_lt`) fed the
  entropy identity above.

## References

* [Nielsen and Chuang, *Quantum Computation and Quantum Information*][nielsen_chuang_2010],
  §12.2.2 (Exercise 12.7, p. 546; Theorem 12.6, p. 544).
-/

open scoped BigOperators

noncomputable section

namespace AxQM

/-- **The qubit data-compression source of N&C Exercise 12.7:** `ρ(p) = p|0⟩⟨0| + (1 − p)|1⟩⟨1|`,
the i.i.d. qubit source whose two computational levels `|0⟩, |1⟩` carry probabilities `p`, `1 − p`.
Packaged as the probabilistic mixture (`State.mix`) of the computational pure states
`(qubitBasis i).toState = |i⟩⟨i|` with weight vector `![p, 1 − p]`; equivalently the binary mixture
`mixPair p |0⟩⟨0| |1⟩⟨1|` (`qubitClassicalSource_eq_mixPair`). Because `|0⟩`, `|1⟩` are orthogonal
this source is *diagonal* in the computational basis, so its compression is classical (p. 546). -/
def qubitClassicalSource (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : State qubit :=
  State.mix ![p, 1 - p]
    (Fin.forall_fin_two.mpr ⟨hp0, by change (0 : ℝ) ≤ 1 - p; linarith⟩)
    (by rw [Fin.sum_univ_two]; change p + (1 - p) = 1; ring)
    (fun i => (qubitBasis i).toState)

/-- **The binary-mixture form of the source.** `ρ(p) = p|0⟩⟨0| + (1 − p)|1⟩⟨1|` as the two-outcome
mixture `State.mixPair p |0⟩⟨0| |1⟩⟨1|` — the literal density operator the exercise writes. The
`State.mix ![p, 1 − p]` packaging (over `Fin 2`) and the binary `mixPair` agree because the mixture
sum has two terms (`State.mix_op`, `Fin.sum_univ_two`). -/
theorem qubitClassicalSource_eq_mixPair (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    qubitClassicalSource p hp0 hp1
      = State.mixPair hp0 hp1 (qubitBasis 0).toState (qubitBasis 1).toState := by
  apply State.ext
  unfold qubitClassicalSource
  rw [State.mix_op, State.mixPair_op, Fin.sum_univ_two]
  simp

/-- **N&C Exercise 12.7, the entropy identity `S(ρ) = H(p)`.** For the source
`ρ(p) = p|0⟩⟨0| + (1 − p)|1⟩⟨1|`, the von Neumann entropy equals the binary Shannon entropy
`H(p) = Real.entropy ![p, 1 − p]` of the mixing weights. Equality holds — the classical Shannon
bound is *saturated* — because `|0⟩`, `|1⟩` are **orthonormal**, so `ρ` is diagonal with eigenvalues
`p, 1 − p` (`State.vonNeumannEntropy_mix_toState_orthonormal`). Contrast Exercise 11.12, where the
non-orthogonal `|0⟩, |+⟩` give the strict `S(ρ') < H(p)`. -/
theorem qubitClassicalSource_vonNeumannEntropy (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (qubitClassicalSource p hp0 hp1).vonNeumannEntropy = Real.entropy ![p, 1 - p] := by
  unfold qubitClassicalSource
  refine State.vonNeumannEntropy_mix_toState_orthonormal _ _ _ qubitBasis ?_
  rw [funext fun i => (qubitOrthonormalBasis_apply i).symm]
  exact qubitOrthonormalBasis.orthonormal

/-- **N&C Exercise 12.7, the achievability claim.** The source `ρ(p) = p|0⟩⟨0| + (1 − p)|1⟩⟨1|` is
**reliably compressible at every rate `R > H(p)`**: for a rate with `H(p) < R · log 2` (a qubit rate
`R` in nats), there is a family of rate-`R` compression schemes whose entanglement fidelity for
`ρ^⊗n` tends to `1`. This is the direct part of Schumacher's noiseless channel coding theorem
(`State.reliablyCompressible_of_vonNeumannEntropy_lt`, N&C Theorem 12.6) fed the entropy identity
`S(ρ) = H(p)` (`qubitClassicalSource_vonNeumannEntropy`) — the formalised half of the exercise's
"compress into `nR` qubits for any `R > S(ρ) = H(p)`". -/
theorem qubitClassicalSource_reliablyCompressible (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R : ℝ}
    (hR : Real.entropy ![p, 1 - p] < R * Real.log 2) :
    (qubitClassicalSource p hp0 hp1).ReliablyCompressible R := by
  refine (qubitClassicalSource p hp0 hp1).reliablyCompressible_of_vonNeumannEntropy_lt ?_
  rw [qubitClassicalSource_vonNeumannEntropy]
  exact hR

end AxQM
