/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.QuantumFourierTransform
import AxQM.Postulates.API.PeriodShift
import AxQM.Postulates.API.KitaevPhaseEstimation
import AxQM.Postulates.API.QuditPhaseGradient
import AxQM.Postulates.API.QuditMeasurement
import AxQM.Postulates.API.MeasurementTransportBornProb
import AxQM.Postulates.API.MeasurementCongrBornProb
import AxQM.Postulates.API.CompositeState
import AxQM.Postulates.PartialTraceTensor
import AxQM.Core.QtowerHadamardLayer
import AxQM.Core.QtowerPhaseGradient
import AxQM.Core.QtowerControlQft
import AxQM.Core.QtowerMeasurement
import AxQM.Core.QftTowerProductRep
import AxQM.NC.Ch5.Exercise5_7

/-!
# Nielsen & Chuang, Problem 5.1 (a quantum circuit for the quantum Fourier transform)

*(N&C p. 243.)*

Construct a quantum circuit performing the QFT |j> -> (1/sqrt p) sum e^{2pi ijk/p}|k> for p prime.

## The specification, and what "construct a circuit" adds to it

Equation (5.79) is the `p`-dimensional quantum Fourier transform of eq. (5.2) at dimension `p`. Its
exact mathematical content — a **unitary map with the stated action on the computational basis** —
is formalised in full, for every dimension `d ≥ 1`, in
`AxQM/Postulates/API/QuantumFourierTransform.lean`:

* `qftEvolution p : Evolution (qudit p)` — the transform as genuine closed-system dynamics; its
  unitarity is the discharged `Evolution.unitary` obligation (`qftMatrix_mem_unitaryGroup`);
* `qftEvolution_op_apply_quditBasis` — the action `F|j⟩ = ∑ₖ (1/√p)·e^{2πijk/p} |k⟩`, (5.79);
* `qftFourierImage p j` / `qftInverseFourierImage p j` — the (inverse-)Fourier image states.

But `qftEvolution p` is the transform's **specification** — the target unitary — not the **circuit**
Problem 5.1 asks us to build. "Construct a quantum circuit" means *exhibit a composition of gate
`Evolution`s that realises it*, and the point of restricting to prime `p` is that the standard route
is unavailable: the Figure 5.1 circuit rests on the product representation (5.4), which needs
`N = 2ⁿ`; for a prime `p` (never a power of two) the register `qudit p` is a single, indecomposable
`p`-dimensional system, with no nontrivial subgroup to factor through. The efficient QFT over `Z_p`
is instead **Kitaev's phase-estimation** construction (N&C p. 246 attributes the Fourier transform
over an arbitrary finite Abelian group, and phase estimation, to Kitaev).

## The construction: phase estimation of the cyclic shift

Kitaev's circuit reads the QFT off the spectrum of the **cyclic shift** `S = periodShift p 1`
(`|x⟩ ↦ |x+1 mod p⟩`, a permutation gate). Its eigenvectors are exactly the inverse-Fourier images
`F⁻¹|ℓ⟩ = qftInverseFourierImage p ℓ`, with eigenvalue `e^{2πiℓ/p}`
(`periodShift_hasEigenstate_qftInverseFourierImage`, N&C Exercise 5.21(1)). Phase estimation of `S`
on the eigenstate `F⁻¹|ℓ⟩` therefore reads the frequency `ℓ` into a control register — inverting
`F⁻¹`, i.e. realising the forward transform `F` on the eigenbasis. That is the sense in which the
circuit "performs the quantum Fourier transform": it is `F` re-expressed as *estimate the eigenphase
of the shift*.

**The phase-loading engine of that circuit** — the second stage of N&C Figure 5.2, the
controlled-`U`-power sequence, for the shift specifically:

* `seqCtrlPow_hasEigenstate_qtowerKet` — the **general phase-estimation eigenstate identity**: for
  any target eigenstate `U|u⟩ = μ|u⟩`, each computational-basis control register `|b⟩` (of integer
  value `j = bitsToNat t b`) is an eigenstate of the controlled-`U`-power sequence `seqCtrlPow U t`
  (Figure 5.2) with eigenvalue `μ^j`. This captures "phase estimation loads the eigenphase
  `j·μ`" — the exact refinement of Exercise 5.7's `seqCtrlPow_evolvePure` when the target is an
  eigenstate.
* `seqCtrlPow_periodShift_hasEigenstate_qtowerKet_qftInverseFourierImage` — its **shift
  specialisation**: `seqCtrlPow (periodShift p y) t` carries `|b⟩ ⊗ F⁻¹|ℓ⟩` to eigenphase
  `e^{2πi·j·(yℓ)/p}`, the phase gradient in `j` that an inverse QFT on the control register reads as
  the frequency `yℓ/p`.
* `seqCtrlPow_periodShift_one_hasEigenstate_qtowerKet_prime` — the **Problem 5.1 headline** (`p`
  prime, shift by the generator `y = 1`): the control register `|b⟩` (value `j`) sits at eigenphase
  `e^{2πi·jℓ/p}` of `seqCtrlPow (periodShift p 1) t` on `F⁻¹|ℓ⟩`. This is precisely the phase
  `e^{2πijk/p}` of (5.79), now generated *by the circuit* (a composition of controlled shift powers)
  rather than written into a matrix. Primality is the item's scope; here it supplies `1 < p`, so the
  shift amount `y = 1` is the genuine generator of `Z_p`.

`qftEvolution_evolvePure_quditBasis_prime` records the specification (5.79) at prime `p`.

## The state-preparation stage: the Hadamard layer

Before the controlled shift powers, the circuit puts the `t` control qubits into the equal
superposition with a **Hadamard layer** (the first gate of Figure 5.2). This step is that gate
and its action, over an arbitrary target register (in `AxQM/Core/QtowerHadamardLayer.lean`):

* `qtowerHadamardLayer t` — the Hadamard layer on `qtower t S` (a Hadamard on each control wire,
  identity on the target), and `qtowerPlusKet t u = |+⟩^{⊗t} ⊗ |u⟩` its output — the equal
  superposition `(1/√2ᵗ) ∑_b |b⟩ ⊗ |u⟩` (the all-`|+⟩` product built through `PureState.tmul`).
* `qtowerHadamardLayer_evolvePure_qtowerKet_zero` — the gate's action:
  `qtowerHadamardLayer t (|0…0⟩ ⊗ |u⟩) = |+⟩^{⊗t} ⊗ |u⟩`, the superposition the controlled-power
  sequence then acts on.
* `qtowerHadamardLayer_evolvePure_qtowerKet_zero_qftInverseFourierImage` (**this file**) — its
  Problem 5.1 instance at the shift eigenstate `F⁻¹|ℓ⟩`: the circuit's input preparation
  `qtowerHadamardLayer t (|0…0⟩ ⊗ F⁻¹|ℓ⟩) = |+⟩^{⊗t} ⊗ F⁻¹|ℓ⟩`.

## The phase-gradient stage: the controlled shift powers

The controlled-power sequence then acts on the prepared superposition. On an eigenstate input it
produces the **phase gradient** — each control wire `w` of weight `2^w` picks up the eigenphase on
its `|1⟩` branch. Formalised (in `AxQM/Core/QtowerPhaseGradient.lean`) by reformulating
the amplitude sum `(1/√2ᵗ) ∑_b e^{2πijℓ/p} |b⟩ ⊗ F⁻¹|ℓ⟩` as the equal **product** of phased-plus
states `⊗_w |+_{2^w·θ}⟩ ⊗ F⁻¹|ℓ⟩` (`qtowerPhaseGrad θ t u`), built through `PureState.tmul` from the
phased-plus combinator `qubitPhasePlus θ = P(θ)|+⟩` — so the normalization is inherited:

* `seqCtrlPow_hasEigenstate_qtowerPlusKet` (general, in `AxQM/Core/QtowerPhaseGradient.lean`) — for
  an eigenstate input `U|u⟩ = e^{iθ}|u⟩`, `seqCtrlPow U t (|+⟩^{⊗t} ⊗ |u⟩) = qtowerPhaseGrad θ t u`.
  Single-wire phase kickback (`controlledUnitary_evolvePure_qubitPlus_hasEigenstate`) inducted over
  the control wires.
* `seqCtrlPow_periodShift_one_qtowerPlusKet_prime` (**this file**) — its Problem 5.1 instance
  (`p` prime, shift `1`, eigenphase `θ = 2πℓ/p`): the controlled shift powers carry the prepared
  `|+⟩^{⊗t} ⊗ F⁻¹|ℓ⟩` to the phase gradient `⊗_w |+_{2ᵂ·2πℓ/p}⟩ ⊗ F⁻¹|ℓ⟩`.
* `qtowerHadamardLayer_seqCtrlPow_periodShift_one_prime` (**this file**) — the **two stages
  composed**: from the computational input `|0…0⟩ ⊗ F⁻¹|ℓ⟩`, the Hadamard layer then the controlled
  shift powers produce that phase gradient. This is Figure 5.2 up to the final inverse-QFT readout.

## The readout stage: the inverse QFT on the control register

The final gate of N&C Figure 5.2 applies the **inverse quantum Fourier transform to the control
register** (the `t = n+1` control qubits), reading the eigenphase gradient back into an estimate of
the frequency `ℓ`. The obstacle is structural: the phase-estimation stages live on the *nested*
register `qtower t S` (target `S` at the bottom), whereas the tower QFT `qftTowerEvolution` lives on
the *pure* qubit tower with no separate target. Separating them — `qtower (n+1) S ≃ₛ (qtower n
qubit) ⊗ S` — and assembling the readout gate is done, for an arbitrary target, in
`AxQM/Core/QtowerControlQft.lean` (`qtowerSplitControl`, `qtowerControlInverseQft`,
`qtowerControlInverseQft_evolvePure_qtowerPhaseGrad`). Its Problem 5.1 instances:

* `qtowerControlInverseQft_evolvePure_qtowerPhaseGrad_qftInverseFourierImage` (**this file**) — the
  readout of the phase gradient at the shift eigenstate: `qtowerControlInverseQft n (qudit p)` sends
  `⊗_w |+_{2ᵂ·2πℓ/p}⟩ ⊗ F⁻¹|ℓ⟩` to the inverse tower QFT of the *standalone* control gradient,
  `F⁻¹|ℓ⟩` untouched. The readout acts on the control register alone.
* `qtowerControlInverseQft_qtowerHadamardLayer_seqCtrlPow_periodShift_one_prime` (**this file**) —
  the **three stages composed**: from `|0…0⟩ ⊗ F⁻¹|ℓ⟩`, Hadamard layer → controlled shift powers →
  inverse-QFT readout. The whole Kitaev QFT-over-`Z_p` circuit up to reading the estimate register.

## The product-representation stage: reading the estimate off the gradient (N&C eq. 5.4)

The readout above leaves `qftTowerInverseEvolution n (towerPhaseGrad (2πℓ/p) n)` on the control
register — the inverse tower QFT of the *standalone* phase gradient. What that state *is* is the
content of N&C's **product representation** (eq. 5.4): multiplying out the per-wire phased-plus
factors `⊗_w |+_{2ᵂθ}⟩` reconstitutes the single Fourier sum `(1/√2ⁿ⁺¹) ∑ₖ e^{iθk}|k⟩`. This is
`towerPhaseGrad_eq_congr_quditPhaseGrad` (arbitrary slope `θ`, in
`AxQM/Core/QftTowerProductRep.lean`): `towerPhaseGrad θ n = Φₙ (quditPhaseGrad θ (2ⁿ⁺¹))` with `Φₙ =
PureState.congr (quditPowTower n)` the register bridge. Reducing the readout through it
(`qftTowerInverseEvolution_evolvePure_towerPhaseGrad`) turns the tower inverse QFT into the
single-register inverse QFT of the qudit phase gradient. Two consequences, here and in
`AxQM/Core/QftTowerProductRep.lean`:

* `qtowerControlInverseQft_qtowerHadamardLayer_seqCtrlPow_periodShift_one_prime_estimate`
  (**this file**) — the whole circuit's output as the **frequency estimate**: from `|0…0⟩ ⊗ F⁻¹|ℓ⟩`
  the three stages produce `(split⁻¹) ((Φₙ (F⁻¹ φ_{2πℓ/p})) ⊗ F⁻¹|ℓ⟩)`, the transported
  single-register inverse QFT `F⁻¹ = qftInverseEvolution (2ⁿ⁺¹)` of the qudit phase gradient
  `φ_{2πℓ/p} = quditPhaseGrad (2πℓ/p) (2ⁿ⁺¹)`.
* `qftTowerInverseEvolution_evolvePure_towerPhaseGrad_dyadic` (`AxQM/Core/QftTowerProductRep.lean`)
  — the **exact readout for a dyadic frequency**: at `θ = 2πM/2ⁿ⁺¹` the gradient is exactly `F|M⟩`,
  so the readout is the basis ket `towerKet n (i ↦ (bits M) i.rev)` on the nose. This is the precise
  sense in which the circuit *performs the QFT*; the prime-`p` estimate above is its
  finite-precision shadow (`ℓ/p` is never dyadic).

## The accuracy stage: nearest-bin concentration (N&C §5.2.1)

The read-out register holds a *finite-precision* estimate: because `p` is prime, `ℓ/p` has no finite
`(n+1)`-bit binary expansion, so the transported inverse QFT `F⁻¹ φ_{2πℓ/p}` is spread over many
bins rather than collapsing onto one. N&C's §5.2.1 accuracy analysis (eqs. 5.23–5.34) quantifies how
sharply it concentrates. The general apparatus, over the phase gradient, is in
`AxQM/Postulates/API/QuditPhaseGradient.lean`:

* `quditPhaseGrad_qftInverse_inner_quditBasis` / `…_geom` — the **read-out amplitude**
  `αₘ = ⟨m | F⁻¹ | φ_θ⟩ = (1/d) ∑ₖ e^{i(θ − 2πm/d)k}` (eqs. 5.23–5.24) and its closed form
  (eqs. 5.25–5.26).
* `quditPhaseGrad_qftInverse_norm_inner_quditBasis_ge` / `…_sq_ge` — the **nearest-bin
  concentration** `‖αₘ‖ ≥ 2/π`, hence `‖αₘ‖² ≥ 4/π²`, when the residual phase satisfies
  `|θ − 2πm/d| ≤ π/d` (eqs. 5.28–5.29), resting on the reverse chord bound `‖1 − e^{iθ}‖ ≥ 2|θ|/π`.
* `nearestBin θ d` + `quditPhaseGrad_qftInverse_norm_inner_nearestBin_sq_ge` — the concentration
  made **unconditional** by *choosing* the best bin `round(θd/2π) mod d`; the `2π`-periodicity of
  the gradient (`quditPhaseGrad_sub_intMul_two_pi`) folds the wrap-around bin back into range.

Its Problem 5.1 instances, giving the finite-precision correctness (**this file**):

* `bornProb_quditMeasurement_qftInverse_quditPhaseGrad_nearestBin_prime_ge` — the **standalone**
  single-register base case: measuring the read-out state `F⁻¹|φ_{2πℓ/p}⟩` on `qudit 2ⁿ⁺¹` in the
  computational basis, the best `(n+1)`-bit estimate `nearestBin (2πℓ/p) 2ⁿ⁺¹` of `ℓ/p` is obtained
  with probability `≥ 4/π²`.
* `bornProb_qtowerControlMeasurement_qftCircuit_nearestBin_prime_ge` — the **headline on the
  constructed circuit**: measuring the `n+1` control wires of the *assembled* Kitaev circuit's
  output (Hadamard layer → controlled shift powers → inverse-QFT read-out, on `|0…0⟩ ⊗ F⁻¹|ℓ⟩`) in
  the computational basis, the best `(n+1)`-bit estimate is obtained with probability `≥ 4/π²` — a
  bound independent of register size. Obtained from the standalone base by transporting the Born
  probability across the `quditPowTower`/`qtowerSplitControl` relabellings and the product-state
  control marginal (`Measurement.bornProb_congr_congr`, `bornProb_onLeft_reducedLeft`,
  `qtowerMeasurement_eq_congr_quditMeasurement`). This is the sense in which the Kitaev circuit
  *performs* the QFT over `Z_p`: for prime `p` no exact product-form circuit exists (5.4/Figure 5.1
  need `N = 2ⁿ`), so the transform is realised as phase estimation of the shift, reading the
  frequency to finite precision.

## The whole construction

Assembled from the preceding steps: the QFT unitary + action specification (5.79); the
state-preparation Hadamard layer; the phase-loading eigenstructure (`seqCtrlPow` diagonal on the
shift eigenbasis); the phase-gradient superposition; the inverse-QFT readout on the control
register; the product representation (N&C eq. 5.4), with the circuit's output identified as the
frequency
estimate (`qtowerControlInverseQft_qtowerHadamardLayer_seqCtrlPow_periodShift_one_prime_estimate`)
and the exact dyadic case discharged (`qftTowerInverseEvolution_evolvePure_towerPhaseGrad_dyadic`);
and finally the **accuracy** — the read-out amplitude (5.23–5.26), the nearest-bin concentration
`‖α₀‖² ≥ 4/π²` (5.28–5.29), and its prime-`p` instantiation as the Born-probability success bound of
measuring the **constructed circuit's control register**
(`bornProb_qtowerControlMeasurement_qftCircuit_nearestBin_prime_ge`, on the standalone base
`bornProb_quditMeasurement_qftInverse_quditPhaseGrad_nearestBin_prime_ge`). The gate circuit is
built and its finite-precision correctness proved as a theorem about the circuit itself.

## Where the ingredients are

The kickback `seqCtrlPow_hasEigenstate_qtowerKet` is stated for a general target evolution; its
proof uses Exercise 5.7's action lemma `seqCtrlPow_evolvePure`. The Hadamard-layer gate and its
action (any target `S`) are in `AxQM/Core/QtowerHadamardLayer.lean`; the phase-gradient register
`qtowerPhaseGrad` and the gradient action `seqCtrlPow_hasEigenstate_qtowerPlusKet` are in
`AxQM/Core/QtowerPhaseGradient.lean` (with the phased-plus state `qubitPhasePlus` in
`AxQM/Postulates/API/PhasedPlus.lean`); the control–target split `qtowerSplitControl`, the inverse
tower QFT `qftTowerInverseEvolution`, and the readout gate `qtowerControlInverseQft` with its
gradient action are in `AxQM/Core/QtowerControlQft.lean`; the product representation
`towerPhaseGrad_eq_congr_quditPhaseGrad` (eq. 5.4), the readout reduction
`qftTowerInverseEvolution_evolvePure_towerPhaseGrad`, and the exact dyadic readout are in
`AxQM/Core/QftTowerProductRep.lean`. Their `qftInverseFourierImage`/prime-`p` instances are stated
here as the state-preparation, phase-loading, readout, and estimate stages. The accuracy apparatus
(`quditPhaseGrad_qftInverse_*`, `nearestBin`) is in `AxQM/Postulates/API/QuditPhaseGradient.lean`;
the Born-probability transport lemma `Measurement.bornProb_congr_congr` is in
`AxQM/Postulates/API/MeasurementCongrBornProb.lean`. The finite-precision results are Born
probabilities `(quditMeasurement 2ⁿ⁺¹).bornProb …` and
`(Measurement.congr … ((qtowerMeasurement n).onLeft …)).bornProb …` for `quditPhaseGrad`,
`qftInverseEvolution`, `nearestBin`, `qtowerMeasurement` and `qtowerSplitControl`.
-/

noncomputable section

namespace AxQM

/-- **Nielsen & Chuang, Problem 5.1 (eq. 5.79):** for `p` prime, the quantum Fourier transform
evolution sends the computational-basis state `|j⟩` of the register `qudit p` to the Fourier image
state `∑ₖ (1/√p)·e^{2πijk/p} |k⟩`: `evolvePure (qftEvolution p) |j⟩ = qftFourierImage p j`.

The primality hypothesis `[Fact p.Prime]` is the exact scope of Problem 5.1; here it is consumed to
supply the `NeZero p` instance the qudit register requires (`p` prime ⇒ `p ≠ 0`). This is the
specification (5.79) the circuit must realise; the specialization of the general-dimension result
`qftEvolution_evolvePure_quditBasis`. -/
theorem qftEvolution_evolvePure_quditBasis_prime {p : ℕ} [Fact p.Prime] (j : Fin p) :
    (qftEvolution p).evolvePure (quditBasis j) = qftFourierImage p j :=
  qftEvolution_evolvePure_quditBasis p j

/-- **Phase estimation loads the eigenphase.** If `|u⟩` is an eigenstate of
`U` with eigenvalue `μ` (`U.HasEigenstate μ u`), then for every computational-basis control register
`|b⟩` (a bit-string `b : Fin t → Fin 2` of integer value `j = bitsToNat t b`) the input `|b⟩ ⊗ |u⟩`
is an eigenstate of the controlled-`U`-power sequence `seqCtrlPow U t` (N&C Figure 5.2) with
eigenvalue `μ^j`: `seqCtrlPow U t (|b⟩ ⊗ |u⟩) = μ^j (|b⟩ ⊗ |u⟩)`.

This is the exact-eigenstate refinement of Exercise 5.7 (`seqCtrlPow_evolvePure`, which sends
`|b⟩ ⊗ |u⟩` to `|b⟩ ⊗ Uʲ|u⟩` with no eigenstate hypothesis): when `|u⟩` is an eigenstate, `Uʲ|u⟩` is
the *global phase* `μʲ` times `|u⟩`, so the phase `μʲ` — the datum phase estimation reads out —
factors onto the whole tower ket. The engine of Kitaev's phase-estimation construction.

Proof: `seqCtrlPow_evolvePure` reduces the goal to `(qtowerKet t b (Uʲ|u⟩)).vec = μʲ •
(qtowerKet t b u).vec`; since `Uʲ|u⟩ = μʲ • |u⟩` at the vector level (`HasEigenstate.pow`) and
`qtowerKet` is linear in its target factor (the `vecscale` induction, `|b⟩ ⊗ (μʲ • ·) =
μʲ • (|b⟩ ⊗ ·)`), the phase factors out. -/
theorem seqCtrlPow_hasEigenstate_qtowerKet {S : QSystem} (U : Evolution S) {μ : ℂ}
    {u : PureState S} (h : U.HasEigenstate μ u) (t : ℕ) (b : Fin t → Fin 2) :
    (seqCtrlPow U t).HasEigenstate (μ ^ Concrete.bitsToNat t b) (qtowerKet t b u) := by
  -- `qtowerKet` is linear in its target argument at the vector level.
  have vecscale : ∀ (c : ℂ) (v w : PureState S), w.vec = c • v.vec →
      ∀ (s : ℕ) (b' : Fin s → Fin 2),
        (qtowerKet s b' w).vec = c • (qtowerKet s b' v).vec := by
    intro c v w hvw s
    induction s with
    | zero => intro b'; exact hvw
    | succ s ih =>
        intro b'
        rw [qtowerKet_succ, qtowerKet_succ, PureState.tmul_vec, PureState.tmul_vec,
          ih (Fin.tail b')]
        exact TensorProduct.tmul_smul _ _ _
  change (seqCtrlPow U t).op (qtowerKet t b u).vec
      = (μ ^ Concrete.bitsToNat t b) • (qtowerKet t b u).vec
  rw [← Evolution.evolvePure_vec, seqCtrlPow_evolvePure]
  have hpow : ((U ^ Concrete.bitsToNat t b).evolvePure u).vec
      = (μ ^ Concrete.bitsToNat t b) • u.vec := by
    rw [Evolution.evolvePure_vec]
    exact Evolution.HasEigenstate.pow h (Concrete.bitsToNat t b)
  exact vecscale (μ ^ Concrete.bitsToNat t b) u
    ((U ^ Concrete.bitsToNat t b).evolvePure u) hpow t b

/-- **Phase estimation of the cyclic shift loads the frequency phase** (the Kitaev QFT engine,
general shift amount). For the shift `U_y = periodShift p y` and its Fourier eigenstate
`F⁻¹|ℓ⟩ = qftInverseFourierImage p ℓ` (eigenvalue `e^{2πiyℓ/p}`, N&C Exercise 5.21(1)), the control
register `|b⟩` (integer value `j = bitsToNat t b`) is an eigenstate of `seqCtrlPow (periodShift p y)
t` with eigenvalue `e^{2πi·j·(yℓ)/p}`:
`seqCtrlPow U_y t (|b⟩ ⊗ F⁻¹|ℓ⟩) = e^{2πi·j·yℓ/p} (|b⟩ ⊗ F⁻¹|ℓ⟩)`.

This is `seqCtrlPow_hasEigenstate_qtowerKet` at the shift's known eigenpair, with the eigenvalue
`(e^{2πiyℓ/p})^j` collapsed to a single exponential `e^{2πi·j·yℓ/p}` (`Complex.exp_natCast_mul`).
The resulting phase is *linear in the control value `j`* — the gradient a later inverse QFT on
the control register reads as the frequency `yℓ/p`; this is "phase estimation on `U_y` samples the
eigenphases `ℓy/r`" of Exercise 5.21(2), made quantitative. -/
theorem seqCtrlPow_periodShift_hasEigenstate_qtowerKet_qftInverseFourierImage (p : ℕ) [NeZero p]
    (y ℓ : Fin p) (t : ℕ) (b : Fin t → Fin 2) :
    (seqCtrlPow (periodShift p y) t).HasEigenstate
      (Complex.exp (2 * Real.pi * Complex.I *
        ((Concrete.bitsToNat t b : ℕ) * ((y : ℕ) * (ℓ : ℕ))) / p))
      (qtowerKet t b (qftInverseFourierImage p ℓ)) := by
  have h := seqCtrlPow_hasEigenstate_qtowerKet (periodShift p y)
    (periodShift_hasEigenstate_qftInverseFourierImage p y ℓ) t b
  rwa [← Complex.exp_natCast_mul,
    show (Concrete.bitsToNat t b : ℂ) * (2 * Real.pi * Complex.I * ((y : ℕ) * (ℓ : ℕ)) / p)
        = 2 * Real.pi * Complex.I * ((Concrete.bitsToNat t b : ℕ) * ((y : ℕ) * (ℓ : ℕ))) / p
      from by ring] at h

/-- **Nielsen & Chuang, Problem 5.1 — the phase-estimation engine of the prime-`p` QFT.** For
`p` prime and the cyclic shift by the generator `1` of `Z_p` (`U = periodShift p 1`), the control
register `|b⟩` (integer value `j = bitsToNat t b`) is an eigenstate of the controlled-shift-power
sequence `seqCtrlPow (periodShift p 1) t` on the Fourier eigenstate `F⁻¹|ℓ⟩`, with eigenvalue
the phase `e^{2πijℓ/p}` of (5.79):
`seqCtrlPow U t (|b⟩ ⊗ F⁻¹|ℓ⟩) = e^{2πijℓ/p} (|b⟩ ⊗ F⁻¹|ℓ⟩)`.

So the phase `e^{2πijk/p}` that (5.79) writes into the QFT *matrix* is produced *by the circuit*
— a composition of controlled shift powers — as the eigenphase phase estimation loads onto the
control register. Reading it out (inverse QFT on the control register, to finite precision) recovers
`ℓ`, realising the forward transform `F` on the shift's eigenbasis. `[Fact p.Prime]` is the exact
scope of Problem 5.1; here it gives `1 < p`, so the shift amount `1` is the genuine `Z_p` generator
(`(1 : Fin p) = 1`). Specialises the general-`y`
`seqCtrlPow_periodShift_hasEigenstate_qtowerKet_qftInverseFourierImage` at `y = 1`. -/
theorem seqCtrlPow_periodShift_one_hasEigenstate_qtowerKet_prime (p : ℕ) [Fact p.Prime]
    (ℓ : Fin p) (t : ℕ) (b : Fin t → Fin 2) :
    (seqCtrlPow (periodShift p 1) t).HasEigenstate
      (Complex.exp (2 * Real.pi * Complex.I * ((Concrete.bitsToNat t b : ℕ) * (ℓ : ℕ)) / p))
      (qtowerKet t b (qftInverseFourierImage p ℓ)) := by
  have hp : ((1 : Fin p) : ℕ) = 1 := by
    have h1 : 1 < p := (Fact.out : p.Prime).one_lt
    rw [Fin.val_one' p, Nat.mod_eq_of_lt h1]
  have h := seqCtrlPow_periodShift_hasEigenstate_qtowerKet_qftInverseFourierImage p 1 ℓ t b
  rwa [hp, Nat.cast_one, one_mul] at h

/-- **Nielsen & Chuang, Problem 5.1 — the state-preparation stage of the prime-`p` QFT circuit.**
Before the controlled shift powers, the circuit applies a Hadamard layer to the `t` control qubits.
On the computational input `|0…0⟩ ⊗ F⁻¹|ℓ⟩` — the all-zero control register tensored with the shift
eigenstate `F⁻¹|ℓ⟩` (N&C Exercise 5.21(1)) — the Hadamard layer `qtowerHadamardLayer t` produces the
equal superposition `|+⟩^{⊗t} ⊗ F⁻¹|ℓ⟩ = (1/√2ᵗ) ∑_b |b⟩ ⊗ F⁻¹|ℓ⟩`:
`qtowerHadamardLayer t (|0…0⟩ ⊗ F⁻¹|ℓ⟩) = qtowerPlusKet t (F⁻¹|ℓ⟩)`.

This is the first gate of the circuit (N&C Figure 5.2) instantiated at the QFT eigenstate input: it
spreads the control register over all `2ᵗ` values, so that the subsequent controlled-shift-power
sequence loads the eigenphase `e^{2πijℓ/p}` onto each control value `j`
(`seqCtrlPow_periodShift_one_hasEigenstate_qtowerKet_prime`). Specialises the general Hadamard-layer
action `qtowerHadamardLayer_evolvePure_qtowerKet_zero` (in `Core/QtowerHadamardLayer.lean`) at the
target `u = qftInverseFourierImage p ℓ`. -/
theorem qtowerHadamardLayer_evolvePure_qtowerKet_zero_qftInverseFourierImage (p : ℕ) [NeZero p]
    (ℓ : Fin p) (t : ℕ) :
    (qtowerHadamardLayer t).evolvePure (qtowerKet t (fun _ => 0) (qftInverseFourierImage p ℓ))
      = qtowerPlusKet t (qftInverseFourierImage p ℓ) :=
  qtowerHadamardLayer_evolvePure_qtowerKet_zero t (qftInverseFourierImage p ℓ)

/-- **Nielsen & Chuang, Problem 5.1 — the phase-gradient superposition of the prime-`p` QFT
circuit.** The controlled shift powers `seqCtrlPow (periodShift p 1) t` act on the prepared equal
superposition `|+⟩^{⊗t} ⊗ F⁻¹|ℓ⟩` and load the eigenphase `e^{2πiℓ/p}` (eigenvalue of the shift on
`F⁻¹|ℓ⟩`, N&C Exercise 5.21(1)) onto every control value, producing the **phase gradient** — the
per-wire product of phased-plus states `⊗_w |+_{2ᵂ·2πℓ/p}⟩ ⊗ F⁻¹|ℓ⟩`
(`qtowerPhaseGrad (2πℓ/p) t (F⁻¹|ℓ⟩)`):
`seqCtrlPow (periodShift p 1) t (|+⟩^{⊗t} ⊗ F⁻¹|ℓ⟩) = qtowerPhaseGrad (2πℓ/p) t (F⁻¹|ℓ⟩)`.

The phase `e^{2πijℓ/p}` of (5.79) is now realised *coherently across the superposition* — the
control register carries the linear-in-`j` phase gradient a subsequent inverse QFT reads as the
frequency `ℓ/p`. `[Fact p.Prime]` supplies `1 < p` (so the shift amount `1` is the genuine `Z_p`
generator) and `NeZero p`. Specialises the general gradient action
`seqCtrlPow_hasEigenstate_qtowerPlusKet` (in `Core/QtowerPhaseGradient.lean`) at the shift's known
eigenpair, with the real eigenphase `θ = 2πℓ/p`. -/
theorem seqCtrlPow_periodShift_one_qtowerPlusKet_prime (p : ℕ) [Fact p.Prime] (ℓ : Fin p) (t : ℕ) :
    (seqCtrlPow (periodShift p 1) t).evolvePure (qtowerPlusKet t (qftInverseFourierImage p ℓ))
      = qtowerPhaseGrad (2 * Real.pi * (ℓ : ℕ) / p) t (qftInverseFourierImage p ℓ) := by
  have hp : ((1 : Fin p) : ℕ) = 1 := by
    have h1 : 1 < p := (Fact.out : p.Prime).one_lt
    rw [Fin.val_one' p, Nat.mod_eq_of_lt h1]
  have heig : (periodShift p 1).HasEigenstate
      (Complex.exp (((2 * Real.pi * (ℓ : ℕ) / p : ℝ) : ℂ) * Complex.I))
      (qftInverseFourierImage p ℓ) := by
    have h := periodShift_hasEigenstate_qftInverseFourierImage p 1 ℓ
    rw [hp] at h
    rwa [show (((2 * Real.pi * (ℓ : ℕ) / p : ℝ) : ℂ) * Complex.I)
        = 2 * Real.pi * Complex.I * ((1 : ℕ) * (ℓ : ℕ)) / p from by push_cast; ring]
  exact seqCtrlPow_hasEigenstate_qtowerPlusKet (periodShift p 1)
    (2 * Real.pi * (ℓ : ℕ) / p) (qftInverseFourierImage p ℓ) heig t

/-- **Nielsen & Chuang, Problem 5.1 — the first two gates of the prime-`p` QFT circuit, composed.**
From the computational input `|0…0⟩ ⊗ F⁻¹|ℓ⟩`, the state-preparation Hadamard layer followed by the
controlled shift powers produce the phase gradient `⊗_w |+_{2ᵂ·2πℓ/p}⟩ ⊗ F⁻¹|ℓ⟩`:
`seqCtrlPow (periodShift p 1) t (qtowerHadamardLayer t (|0…0⟩ ⊗ F⁻¹|ℓ⟩))
  = qtowerPhaseGrad (2πℓ/p) t (F⁻¹|ℓ⟩)`.

This is N&C Figure 5.2 up to the final inverse-QFT readout: the Hadamard layer spreads the control
register (`qtowerHadamardLayer_evolvePure_qtowerKet_zero_qftInverseFourierImage`), then the
controlled powers imprint the eigenphase gradient
(`seqCtrlPow_periodShift_one_qtowerPlusKet_prime`). The remaining inverse QFT on the control
register (recovering `ℓ` to finite precision) and its accuracy are treated below. -/
theorem qtowerHadamardLayer_seqCtrlPow_periodShift_one_prime (p : ℕ) [Fact p.Prime]
    (ℓ : Fin p) (t : ℕ) :
    (seqCtrlPow (periodShift p 1) t).evolvePure
        ((qtowerHadamardLayer t).evolvePure
          (qtowerKet t (fun _ => 0) (qftInverseFourierImage p ℓ)))
      = qtowerPhaseGrad (2 * Real.pi * (ℓ : ℕ) / p) t (qftInverseFourierImage p ℓ) := by
  rw [qtowerHadamardLayer_evolvePure_qtowerKet_zero_qftInverseFourierImage]
  exact seqCtrlPow_periodShift_one_qtowerPlusKet_prime p ℓ t

/-- **Nielsen & Chuang, Problem 5.1 — the inverse-QFT readout of the prime-`p` QFT circuit.** The
terminal stage of N&C Figure 5.2 applies the inverse quantum Fourier transform to the `t = n+1`
control qubits. On the phase gradient `⊗_w |+_{2ᵂ·2πℓ/p}⟩ ⊗ F⁻¹|ℓ⟩` produced by the controlled shift
powers (`seqCtrlPow_periodShift_one_qtowerPlusKet_prime`), the readout gate
`qtowerControlInverseQft n (qudit p)` acts on the control register alone — leaving the shift
eigenstate `F⁻¹|ℓ⟩` untouched — and reduces to the inverse tower QFT of the *standalone* control
gradient `towerPhaseGrad (2πℓ/p) n`:
`qtowerControlInverseQft n (qudit p) (qtowerPhaseGrad (2πℓ/p) (n+1) F⁻¹|ℓ⟩)
  = (split⁻¹) ((qftTowerInverseEvolution n (towerPhaseGrad (2πℓ/p) n)) ⊗ F⁻¹|ℓ⟩)`.

The eigenphase `e^{2πijℓ/p}` of (5.79), spread coherently across the control register as the phase
gradient, is now fed to the inverse QFT that reads out the frequency `ℓ`. Because `p` is prime,
`ℓ/p` has no finite binary expansion, so the standalone image
`qftTowerInverseEvolution n (towerPhaseGrad (2πℓ/p) n)` is the finite-precision *estimate* of `ℓ`,
not `|ℓ⟩` exactly — its identification with the computational-basis estimate (the product
representation, eq. 5.4, exact only for a dyadic phase) and the accuracy bound are treated
below. Specialises the general readout action
`qtowerControlInverseQft_evolvePure_qtowerPhaseGrad` (`Core/QtowerControlQft.lean`) at the shift
eigenstate. `[NeZero p]` is all this stage needs; primality enters through the eigenphase read. -/
theorem qtowerControlInverseQft_evolvePure_qtowerPhaseGrad_qftInverseFourierImage (p : ℕ) [NeZero p]
    (ℓ : Fin p) (n : ℕ) :
    (qtowerControlInverseQft n (qudit p)).evolvePure
        (qtowerPhaseGrad (2 * Real.pi * (ℓ : ℕ) / p) (n + 1) (qftInverseFourierImage p ℓ))
      = PureState.congr (qtowerSplitControl n (qudit p)).symm
          (((qftTowerInverseEvolution n).evolvePure
              (towerPhaseGrad (2 * Real.pi * (ℓ : ℕ) / p) n)).tmul (qftInverseFourierImage p ℓ)) :=
  qtowerControlInverseQft_evolvePure_qtowerPhaseGrad _ n _

/-- **Nielsen & Chuang, Problem 5.1 — the first three gates of the prime-`p` QFT circuit,
composed.** From the computational input `|0…0⟩ ⊗ F⁻¹|ℓ⟩`, the three stages of N&C Figure 5.2 — the
state-preparation Hadamard layer, the controlled shift powers, and the inverse-QFT readout on the
`t = n+1` control qubits — produce, on the control register alone, the inverse tower QFT of the
standalone phase gradient (the shift eigenstate `F⁻¹|ℓ⟩` untouched):
`qtowerControlInverseQft n (qudit p) (seqCtrlPow … (qtowerHadamardLayer … (|0…0⟩ ⊗ F⁻¹|ℓ⟩)))
  = (split⁻¹) ((qftTowerInverseEvolution n (towerPhaseGrad (2πℓ/p) n)) ⊗ F⁻¹|ℓ⟩)`.

This is the whole Kitaev QFT-over-`Z_p` circuit up to reading the estimate register: the Hadamard
layer spreads the control register (`qtowerHadamardLayer_seqCtrlPow_periodShift_one_prime` gives the
first two stages), then the inverse QFT reads the eigenphase gradient
(`qtowerControlInverseQft_evolvePure_qtowerPhaseGrad`). What remains is the identification of the
standalone image with the frequency estimate and its accuracy. -/
theorem qtowerControlInverseQft_qtowerHadamardLayer_seqCtrlPow_periodShift_one_prime
    (p : ℕ) [Fact p.Prime] (ℓ : Fin p) (n : ℕ) :
    (qtowerControlInverseQft n (qudit p)).evolvePure
        ((seqCtrlPow (periodShift p 1) (n + 1)).evolvePure
          ((qtowerHadamardLayer (n + 1)).evolvePure
            (qtowerKet (n + 1) (fun _ => 0) (qftInverseFourierImage p ℓ))))
      = PureState.congr (qtowerSplitControl n (qudit p)).symm
          (((qftTowerInverseEvolution n).evolvePure
              (towerPhaseGrad (2 * Real.pi * (ℓ : ℕ) / p) n)).tmul
            (qftInverseFourierImage p ℓ)) := by
  rw [qtowerHadamardLayer_seqCtrlPow_periodShift_one_prime,
    qtowerControlInverseQft_evolvePure_qtowerPhaseGrad]

/-- **Nielsen & Chuang, Problem 5.1 — the whole prime-`p` circuit's readout as the frequency
estimate.** Composing the previous theorem with the **product representation** (N&C eq. 5.4,
`towerPhaseGrad_eq_congr_quditPhaseGrad`), the three-stage circuit output on the control register is
the *transported single-register inverse QFT of the qudit phase gradient* at slope `2πℓ/p`: from the
computational input `|0…0⟩ ⊗ F⁻¹|ℓ⟩`, Hadamard layer → controlled shift powers → inverse-QFT readout
produce

`qtowerControlInverseQft n (qudit p) (seqCtrlPow … (qtowerHadamardLayer … (|0…0⟩ ⊗ F⁻¹|ℓ⟩)))
  = (split⁻¹) ((Φₙ (F⁻¹ φ_{2πℓ/p})) ⊗ F⁻¹|ℓ⟩)`,

where `φ_{2πℓ/p} = quditPhaseGrad (2πℓ/p) (2ⁿ⁺¹)` is the single-register phase gradient the product
representation identifies the tower gradient with, `F⁻¹ = qftInverseEvolution (2ⁿ⁺¹)` the
single-register inverse QFT, and `Φₙ = PureState.congr (quditPowTower n)` the register bridge.

So the phase `e^{2πijℓ/p}` of (5.79), spread as the control-register gradient, is fed to the inverse
QFT and read out as the transported estimate `Φₙ(F⁻¹|φ_{2πℓ/p}⟩)` of the frequency `ℓ`. Because `p`
is prime, `ℓ/p` has no finite `(n+1)`-bit binary expansion, so `φ_{2πℓ/p}` is *not* the Fourier
image `F|m⟩` of any integer `m` and the readout is a genuine finite-precision estimate rather than a
computational-basis ket — contrast the general
`qftTowerInverseEvolution_evolvePure_towerPhaseGrad_dyadic`, which reads out `|M⟩` exactly for a
*dyadic* frequency `M/2ⁿ⁺¹`. The quantitative accuracy of the prime-`p` estimate is proved
below. -/
theorem qtowerControlInverseQft_qtowerHadamardLayer_seqCtrlPow_periodShift_one_prime_estimate
    (p : ℕ) [Fact p.Prime] (ℓ : Fin p) (n : ℕ) :
    (qtowerControlInverseQft n (qudit p)).evolvePure
        ((seqCtrlPow (periodShift p 1) (n + 1)).evolvePure
          ((qtowerHadamardLayer (n + 1)).evolvePure
            (qtowerKet (n + 1) (fun _ => 0) (qftInverseFourierImage p ℓ))))
      = PureState.congr (qtowerSplitControl n (qudit p)).symm
          ((PureState.congr (quditPowTower n)
              ((qftInverseEvolution (2 ^ (n + 1))).evolvePure
                (quditPhaseGrad (2 * Real.pi * (ℓ : ℕ) / p) (2 ^ (n + 1))))).tmul
            (qftInverseFourierImage p ℓ)) := by
  rw [qtowerControlInverseQft_qtowerHadamardLayer_seqCtrlPow_periodShift_one_prime,
    qftTowerInverseEvolution_evolvePure_towerPhaseGrad]

/-- **Nielsen & Chuang, Problem 5.1 — the prime-`p` circuit reads out the best frequency estimate**
(the phase-estimation accuracy at the prime-`p` slope, N&C §5.2.1). This is the **standalone
single-register** read-out concentration: measuring the phase-estimation read-out state
`F⁻¹|φ_{2πℓ/p}⟩` — the inverse QFT `F⁻¹ = qftInverseEvolution 2ⁿ⁺¹` of the gradient
`|φ_{2πℓ/p}⟩ = quditPhaseGrad (2πℓ/p) 2ⁿ⁺¹` on the single `2ⁿ⁺¹`-level register `qudit 2ⁿ⁺¹` — in
the computational basis, the outcome is the **nearest `(n+1)`-bit bin** to the frequency `ℓ/p` with
probability at least `4/π²`:
`4/π² ≤ (quditMeasurement 2ⁿ⁺¹).bornProb (F⁻¹|φ_{2πℓ/p}⟩).toState (nearestBin (2πℓ/p) 2ⁿ⁺¹)`.

This is the reusable *base* case of the item's finite-precision correctness; the theorem that
attaches it to the **constructed circuit's own control register** — measuring the `n+1` control
wires of the assembled Kitaev circuit — is
`bornProb_qtowerControlMeasurement_qftCircuit_nearestBin_prime_ge` below, obtained by transporting
this bound across the `quditPowTower`/`qtowerSplitControl` relabellings. Because `p` is prime the
frequency `ℓ/p` is non-dyadic — the read-out never collapses onto a single bin — yet a constant
fraction `4/π² ≈ 0.405` of the probability still concentrates on the best `(n+1)`-bit estimate
`nearestBin (2πℓ/p) 2ⁿ⁺¹`, a bound *independent of the register size*. This is the `l = 0`
nearest-bin concentration of N&C's accuracy analysis (eqs. 5.28–5.29, `|α₀|² ≥ 4/π²`) at the
prime-`p` slope.

`[Fact p.Prime]` is the exact scope of Problem 5.1: primality is precisely what forces `ℓ/p` to be
non-dyadic (never `m/2ⁿ⁺¹`), so the read-out is a genuine finite-precision estimate rather than an
exact basis ket — contrast `qftTowerInverseEvolution_evolvePure_towerPhaseGrad_dyadic`. Proof: the
Born rule `bornProb_quditMeasurement_toState` turns the probability into `‖⟨m | F⁻¹ | φ⟩‖²`, closed
by the general nearest-bin concentration `quditPhaseGrad_qftInverse_norm_inner_nearestBin_sq_ge` at
slope `θ = 2πℓ/p`, `d = 2ⁿ⁺¹`. -/
theorem bornProb_quditMeasurement_qftInverse_quditPhaseGrad_nearestBin_prime_ge
    (p : ℕ) [Fact p.Prime] (ℓ : Fin p) (n : ℕ) :
    4 / Real.pi ^ 2
      ≤ (quditMeasurement (2 ^ (n + 1))).bornProb
          ((qftInverseEvolution (2 ^ (n + 1))).evolvePure
              (quditPhaseGrad (2 * Real.pi * (ℓ : ℕ) / p) (2 ^ (n + 1)))).toState
          (nearestBin (2 * Real.pi * (ℓ : ℕ) / p) (2 ^ (n + 1))) := by
  rw [bornProb_quditMeasurement_toState]
  exact quditPhaseGrad_qftInverse_norm_inner_nearestBin_sq_ge
    (2 * Real.pi * (ℓ : ℕ) / p) (2 ^ (n + 1))

/-- **Nielsen & Chuang, Problem 5.1 — the constructed prime-`p` circuit reads out the best frequency
estimate** (the item's terminal finite-precision correctness, N&C §5.2.1). Running the whole Kitaev
circuit — the Hadamard layer, the controlled shift powers, and the inverse-QFT read-out — on the
computational input `|0…0⟩ ⊗ F⁻¹|ℓ⟩`, and then **measuring its `n+1` control wires in the
computational basis** (the terminal measurement of N&C Figure 5.2/5.3), the outcome is the
bit-string of the **nearest `(n+1)`-bit estimate** of the frequency `ℓ/p` with probability at least
`4/π²`:
```
4/π² ≤ p(best (n+1)-bit estimate of ℓ/p).
```
The measured object is the *constructed circuit's own output* — the full
`qtowerControlInverseQft ∘ seqCtrlPow ∘ qtowerHadamardLayer` chain on `|0…0⟩ ⊗ F⁻¹|ℓ⟩`, a state on
`qtower (n+1) (qudit p)` — and the measurement
`Measurement.congr (qtowerSplitControl n (qudit p)).symm ((qtowerMeasurement n).onLeft (qudit p))`
is the joint computational-basis measurement of exactly the `n+1` control wires (the target
`qudit p` left untouched). The best-estimate bin `nearestBin (2πℓ/p) 2ⁿ⁺¹ : Fin 2ⁿ⁺¹` is read as its
wire bit-string via `towerMeasurementOutcomeEquiv`.

This is the sense in which the constructed circuit *performs* the QFT over `Z_p`: for prime `p` no
exact product-form circuit exists (5.4/Figure 5.1 need `N = 2ⁿ`), so `ℓ/p` is non-dyadic and the
read-out is a genuine finite-precision estimate — yet a constant fraction `4/π² ≈ 0.405` of the
probability, independent of register size, still concentrates on the best `(n+1)`-bit estimate.

Proof: the circuit output is identified as `(split⁻¹)((Φ(F⁻¹φ)) ⊗ F⁻¹|ℓ⟩)` by
`…_prime_estimate`; the control-wire Born probability is then transported to the standalone
single-register read-out — `Measurement.bornProb_congr_congr` across the `split`/`quditPowTower`
relabellings, `bornProb_onLeft_reducedLeft` + `State.reducedLeft_tmul` for the product-state
control marginal, and `qtowerMeasurement_eq_congr_quditMeasurement` identifying the per-wire
measurement with the register measurement — landing on
`bornProb_quditMeasurement_qftInverse_quditPhaseGrad_nearestBin_prime_ge`. -/
theorem bornProb_qtowerControlMeasurement_qftCircuit_nearestBin_prime_ge
    (p : ℕ) [Fact p.Prime] (ℓ : Fin p) (n : ℕ) :
    4 / Real.pi ^ 2
      ≤ (Measurement.congr (qtowerSplitControl n (qudit p)).symm
            ((qtowerMeasurement n).onLeft (qudit p))).bornProb
          ((qtowerControlInverseQft n (qudit p)).evolvePure
              ((seqCtrlPow (periodShift p 1) (n + 1)).evolvePure
                ((qtowerHadamardLayer (n + 1)).evolvePure
                  (qtowerKet (n + 1) (fun _ => 0) (qftInverseFourierImage p ℓ))))).toState
          ((towerMeasurementOutcomeEquiv n).symm
            (nearestBin (2 * Real.pi * (ℓ : ℕ) / p) (2 ^ (n + 1)))) := by
  rw [qtowerControlInverseQft_qtowerHadamardLayer_seqCtrlPow_periodShift_one_prime_estimate,
    Measurement.bornProb_congr_congr, Measurement.bornProb_onLeft_reducedLeft,
    PureState.toState_tmul, State.reducedLeft_tmul, qtowerMeasurement_eq_congr_quditMeasurement,
    Measurement.reindexOutcome_bornProb, Equiv.apply_symm_apply, Measurement.bornProb_congr_congr]
  exact bornProb_quditMeasurement_qftInverse_quditPhaseGrad_nearestBin_prime_ge p ℓ n

end AxQM
