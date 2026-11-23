/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Core.QftTowerBasis

/-!
# The transported QFT circuit read on the qubit tower (N&C Problem 5.2)

The register bridge `quditPowTower n : qudit (2ⁿ⁺¹) ≃ₛ qtower n qubit` carries the
quantum Fourier transform from the single `2ⁿ⁺¹`-level register — where `qftEvolution` and its
Figure 5.1 gate circuit `qftCircuitEvolution` live — onto the explicit `(n+1)`-qubit tensor tower,
as `qftTowerEvolution n := Evolution.congr (quditPowTower n) (qftEvolution (2ⁿ⁺¹))`. The
whole-circuit measured-QFT reduction (Problem 5.2) will defer a terminal per-wire measurement past
this circuit
gate by gate, so it must read the circuit **on the tower** in two complementary ways, both supplied
here:

* **gate by gate** — the transported circuit is the *product of the transported Figure 5.1 gates*
  (`qftTowerEvolution_eq_map_congr_prod`), obtained by pushing the transport through the
  `Evolution`-monoid product with `Evolution.congr_prod`. This is the list of one- and two-wire
  gates the semiclassical reduction defers the measurement past;
* **on a computational-basis state** — the transport of a gate reads any tower basis ket `towerKet n
  b` through the binary-expansion dictionary of `Core/QftTowerBasis.lean`: it is the transport of
  the gate's action on the register ket `|finFunctionFinEquiv (b ∘ Fin.rev)⟩`
  (`quditPowTower_congr_evolvePure_towerKet`), specialising for the whole QFT to
  `qftTowerEvolution_evolvePure_towerKet`.

## The reader `quditPowTower_congr_evolvePure_towerKet`

The dictionary `quditPowTower_congr_quditBasis_apply` says the bridge sends the register ket
`|finFunctionFinEquiv k⟩` to the tower state `towerKet n (k ∘ Fin.rev)`. Reading it at `k = b ∘
Fin.rev` (and using `Fin.rev`'s involutivity) presents `towerKet n b` itself as a transported
register ket, `towerKet n b = Φₙ |finFunctionFinEquiv (b ∘ Fin.rev)⟩` with `Φₙ = quditPowTower n`.
Then the gate-transport law `Evolution.congr_evolvePure_congr` — a transported gate acts on a
transported state as the transport of the original action — turns the transported gate's action on
`towerKet n b` into the transport of the register gate's action on `|finFunctionFinEquiv (b ∘
Fin.rev)⟩`. This holds for **any** gate `U : Evolution (qudit (2ⁿ⁺¹))`, so a single reader serves
every Figure 5.1 gate (and the whole circuit).

The general monoid-homomorphism lemmas `Evolution.congr_id` / `Evolution.congr_prod` it uses are in
`AxQM/Postulates/API/SystemIsoComm.lean`, beside `Evolution.congr_comp`.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

/-- **A gate transported onto the tower, read on a computational-basis ket.** For any gate
`U : Evolution (qudit (2ⁿ⁺¹))`, its transport `Evolution.congr (quditPowTower n) U` onto the
`(n+1)`-qubit tower acts on the tower basis state `towerKet n b` as the transport of `U`'s action on
the register ket `|finFunctionFinEquiv (b ∘ Fin.rev)⟩`:

  `(Φₙ • U).evolvePure (towerKet n b) = Φₙ • (U.evolvePure |finFunctionFinEquiv (b ∘ Fin.rev)⟩)`

with `Φₙ = quditPowTower n` and `Φₙ • (-)` the transport `PureState.congr Φₙ` /
`Evolution.congr Φₙ`. Proved by rewriting `towerKet n b` as the transported register ket via the
binary-expansion dictionary `quditPowTower_congr_quditBasis_apply` (at `k = b ∘ Fin.rev`, using
`Fin.rev_rev`), then
applying the gate-transport law `Evolution.congr_evolvePure_congr`. The `Fin.rev` reconciles the
big-endian register bridge with the little-endian `finFunctionFinEquiv` wire-indexing of the Figure
5.1 matrix gates. This is the single reader every Figure 5.1 gate — and the whole circuit — is read
through on the tower. -/
theorem quditPowTower_congr_evolvePure_towerKet (n : ℕ) (U : Evolution (qudit (2 ^ (n + 1))))
    (b : Fin (n + 1) → Fin 2) :
    (Evolution.congr (quditPowTower n) U).evolvePure (towerKet n b)
      = PureState.congr (quditPowTower n)
          (U.evolvePure (quditBasis (finFunctionFinEquiv (fun i => b i.rev)))) := by
  have hb := quditPowTower_congr_quditBasis_apply n (fun i => b i.rev)
  simp only [Fin.rev_rev] at hb
  rw [← hb, Evolution.congr_evolvePure_congr]

/-- **The transported QFT circuit is the product of the transported Figure 5.1 gates.** Transporting
the QFT circuit `qftCircuitEvolution (n+1)` onto the tower distributes over its gates: the tower QFT
`qftTowerEvolution n` equals the `Evolution`-monoid product of the transported Figure 5.1 gates
`(qftGateEvolutionSequence (n+1)).map (Evolution.congr (quditPowTower n))` — the wire-reversal swap,
and each target's Hadamard + controlled-`Rₖ` cascade, each carried onto the `(n+1)`-qubit tower.
From `qftTowerEvolution_eq_congr_qftCircuitEvolution` and the monoid-homomorphism law
`Evolution.congr_prod`. This exhibits the tower QFT as the explicit list of one- and two-wire gates
the whole-circuit reduction defers the terminal measurement past. -/
theorem qftTowerEvolution_eq_map_congr_prod (n : ℕ) :
    qftTowerEvolution n
      = ((qftGateEvolutionSequence (n + 1)).map (Evolution.congr (quditPowTower n))).prod := by
  rw [qftTowerEvolution_eq_congr_qftCircuitEvolution, qftCircuitEvolution, Evolution.congr_prod]

/-- **The tower QFT read on a computational-basis ket.** The transported quantum Fourier transform
`qftTowerEvolution n` acts on the tower basis state `towerKet n b` as the transport of the single
register QFT's action on the register ket `|finFunctionFinEquiv (b ∘ Fin.rev)⟩`:

  `(qftTowerEvolution n).evolvePure (towerKet n b)
     = quditPowTower n • ((qftEvolution (2ⁿ⁺¹)).evolvePure |finFunctionFinEquiv (b ∘ Fin.rev)⟩)`.

The reader `quditPowTower_congr_evolvePure_towerKet` at `U = qftEvolution (2ⁿ⁺¹)` (as
`qftTowerEvolution n = Evolution.congr (quditPowTower n) (qftEvolution (2ⁿ⁺¹))` definitionally): the
tower QFT genuinely *is* the quantum Fourier transform read through the register identification,
wire bits reversed by `Fin.rev`. -/
theorem qftTowerEvolution_evolvePure_towerKet (n : ℕ) (b : Fin (n + 1) → Fin 2) :
    (qftTowerEvolution n).evolvePure (towerKet n b)
      = PureState.congr (quditPowTower n)
          ((qftEvolution (2 ^ (n + 1))).evolvePure
            (quditBasis (finFunctionFinEquiv (fun i => b i.rev)))) :=
  quditPowTower_congr_evolvePure_towerKet n (qftEvolution (2 ^ (n + 1))) b

end AxQM
