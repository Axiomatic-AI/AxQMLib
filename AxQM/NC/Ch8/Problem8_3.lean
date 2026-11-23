/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.RandomUnitaryChannel
import AxQM.Postulates.API.WernerHolevoRandomUnitary
import AxQM.Postulates.API.BlochState
import AxQM.Postulates.API.UnitalChannelBloch
import AxQM.Postulates.API.UnitaryBlochRotation
import AxQM.NC.Ch2.Exercise2_72
import AxQM.NC.Ch4.Exercise4_6
import AxQM.Concrete.BlochPauliTwirl
import AxQM.Concrete.BlochSVD
import AxQM.Concrete.SpecialOrthogonalAxisAngle

/-!
# Nielsen & Chuang, Problem 8.3 (Random unitary channels)

*(N&C p. 396.)*

Show all unital channels are random-unitary averages for single qubits but not for larger systems.

## The qubit Pauli channel and its diagonal Bloch action

The single-qubit **Pauli channel** `E(ρ) = ∑ₖ pₖ σₖ ρ σₖ` (mixing the Pauli unitaries `I, X, Y, Z`
with a probability distribution `pₖ`) is the canonical family of random-unitary qubit channels. It
realises exactly the qubit channels whose **Bloch-sphere action is a diagonal contraction**
`(r₀, r₁, r₂) ↦ (mₓ r₀, m_y r₁, m_z r₂)` — the "diagonal case" of the qubit converse of Problem 8.3.
This is the **constructive `⇐` half** of the converse: a large, explicit sub-family of unital qubit
channels that *is* random-unitary, on the way to the full statement "*every* unital qubit channel is
random-unitary".

* `AxQM.pauliChannelUnitary` — the four Pauli conjugations as `Evolution`s of the qubit,
  realised as `I` and the `π`-rotations `R_x̂(π), R_ŷ(π), R_ẑ(π)` (which equal `X, Y, Z` up to a
  global phase that cancels in the conjugation `U ρ U†`, so this *is* the Pauli channel).
* `AxQM.pauliChannelUnitary_evolve_blochState` — each Pauli conjugation acts on a Bloch
  state by the corresponding sign-flip of the Bloch vector (`Concrete.pauliBlochFlip`).
* `AxQM.pauliChannel` — the Pauli channel `∑ₖ pₖ σₖ ρ σₖ` as a `RandomUnitaryChannel`.
* `AxQM.pauliChannel_apply_blochState` — **its Bloch action is the diagonal contraction**
  `blochState r ↦ blochState (Concrete.pauliTwirlVec p r)`, i.e. `rⱼ ↦ mⱼ rⱼ` with the
  Pauli-transfer coefficients `mⱼ = ∑ₖ ±pₖ`. This is the heart of the "diagonal" converse.
* `AxQM.pauliChannel_isUnital` / `_isChannel` / `_isRandomUnitary` — the Pauli channel is a
  **unital channel that is random-unitary** (instantiating the easy direction of the framework
  at the Pauli family). So these diagonal unital qubit channels confirm the "tempting belief".
* `AxQM.isRandomUnitary_of_blochState_eq` — **the assembly reduction:** a qubit channel
  that agrees with a random-unitary channel *on every Bloch state* is itself random-unitary (every
  qubit state is a Bloch state, `State.exists_blochState`). This lifts the converse's Bloch-vector
  reasoning back to the global claim `IsRandomUnitary f`.
* `AxQM.isRandomUnitary_of_blochState_eq_evolve_comp` /
  `isRandomUnitary_of_blochState_eq_evolve_pauliChannel_comp` — **the assembly step:** a channel
  acting on Bloch states as `conj U₁ ∘ g ∘ conj U₂` (resp. `conj U₁ ∘ Pauli ∘ conj U₂`) for a
  random-unitary `g` is random-unitary — the composite-with-rotations form the converse produces.
* `Concrete.pauliTwirlInvProb` and `AxQM.isRandomUnitary_of_blochState_eq_diagonalScaling`
  — **the diagonal case of the converse, for a *general* CP-realisable `d`.** The inverse
  Pauli-transfer transform `pauliTwirlInvProb d` (`Concrete/BlochPauliTwirl.lean`) gives the four
  Pauli weights realising a prescribed diagonal contraction `r ↦ (d₀ r₀, d₁ r₁, d₂ r₂)`; they are a
  probability distribution iff `d` lies in the Fujiwara–Algoet tetrahedron
  (`Concrete.pauliTwirlInvProb_nonneg_iff`). This lemma then shows that *any* channel matching
  such a realisable diagonal action is random-unitary — generalising `pauliChannel_isRandomUnitary`
  from the Pauli family to every CP-realisable diagonal channel, and reducing the whole qubit
  converse to the single concrete inequality `pauliTwirlInvProb d ≥ 0` for the SVD diagonal.

* `AxQM.isRandomUnitary_of_isChannel_isUnital` — **the qubit converse of Problem 8.3, in
  full: every unital qubit channel is random-unitary.** It assembles the entire Bloch-sphere
  development below into `IsChannel f → IsUnital f → IsRandomUnitary f`; the geometric assembly is
  documented on the theorem itself.

## The qubit converse (dim 2)

The first half of Problem 8.3 is proved here as
`AxQM.isRandomUnitary_of_isChannel_isUnital`: *every* unital qubit **channel**
(`IsChannel`) is random-unitary — for a single qubit, unitality forces the mixed-unitary form
(Landau & Streater). Its proof is the geometric assembly of the whole development, chaining:

* the **affine-map representation** `AxQM.exists_channelBlochMatrix` — a unital qubit
  channel acts on Bloch states by a real-linear map `r ↦ M r`
  (`Postulates/API/UnitalChannelBloch.lean`, built on `Concrete.sum_conj_blochMatrix`);
* the **singular-value factorisation** `M = O₁ · diagonal d · O₂` into `SO(3)` factors
  (`Concrete.exists_specialOrthogonalGroup_diagonal_factor`);
* the **`SU(2) → SO(3)` cover surjectivity**
  `AxQM.exists_evolution_evolve_blochState_of_mem_specialOrthogonalGroup` (every
  `O ∈ SO(3)` is a qubit unitary conjugation) applied to `O₁, O₂` **and their transposes**
  (`Concrete.mem_specialOrthogonalGroup_transpose`), the rotated Bloch vectors staying in the ball
  by `Concrete.mem_orthogonalGroup_mulVec_sq_sum`;
* the **channel-composition closure** (`isChannel_comp` / `isUnital_comp`, unitary conjugations
  being unital channels), which diagonalises the channel to `g = conj V₁ ∘ f ∘ conj V₂` with
  diagonal Bloch action `d`;
* the **complete-positivity criterion**
  `AxQM.pauliTwirlInvProb_nonneg_of_channel_blochDiagonal` (complete positivity of `g`
  forces `Concrete.pauliTwirlInvProb d ≥ 0`, the Fujiwara–Algoet inequalities);
* the **diagonal case** `isRandomUnitary_of_blochState_eq_diagonalScaling` (making `g`
  random-unitary) and the **assembly bridge** `isRandomUnitary_of_blochState_eq_evolve_comp`
  (lifting random-unitarity from `g` back to `f`, since `f` agrees with `conj U₁ ∘ g ∘ conj U₂` on
  every Bloch state — the SVD `O₁ · diagonal d · O₂ = M` reassembled).

## The counterexample in dimension ≥ 3

The second half of Problem 8.3 — that the "tempting belief" *fails* in dimension
`≥ 3` (Landau & Streater) — is proved here as
`AxQM.exists_unital_channel_not_isRandomUnitary`: there is a unital CPTP channel on a
qutrit that is **not** a random-unitary average. The witness is the **Werner–Holevo channel**
`Φ(ρ) = ½(tr(ρ)·I − ρᵀ)` on `qudit 3` (`wernerHolevoChannel`, built and certified a unital channel —
`IsChannel ∧ IsUnital` — in `Postulates/API/WernerHolevoChannel.lean`):

* `AxQM.wernerHolevoChannel_not_isRandomUnitary` — the statement
  `¬ IsRandomUnitary wernerHolevoChannel`. Its proof pairs a hypothetical random-unitary
  representation `Φ = ∑ₖ pₖ Uₖ ρ Uₖ†` against a conjugated pure state: the Werner–Holevo side
  `⟨ψ̄, Φ(|ψ⟩⟨ψ|) ψ̄⟩` vanishes while the mixture side is `∑ₖ pₖ ‖⟨ψ̄, Uₖ ψ⟩‖² ≥ 0`, so some `Uₖ₀`
  has `⟨ψ̄, Uₖ₀ ψ⟩ = ψᵀ Uₖ₀ ψ = 0` for every `ψ`; but that would make `Uₖ₀` antisymmetric, and an
  antisymmetric matrix in **odd** dimension `3` is singular — impossible for a unitary. The
  sesquilinear computation lives in
  `Postulates/API/WernerHolevoRandomUnitary.lean`
  (`RandomUnitaryChannel.sum_prob_normSq_eq_zero_of_apply_eq_wernerHolevoChannel`,
  `Evolution.not_forall_inner_conjVec_op_eq_zero`).
* `AxQM.exists_unital_channel_not_isRandomUnitary` — the main result, assembling
  `wernerHolevoChannel_isChannel`, `wernerHolevoChannel_isUnital` and
  `wernerHolevoChannel_not_isRandomUnitary`, a *unital channel that is not random-unitary* exists.
  Together with the qubit converse `isRandomUnitary_of_isChannel_isUnital` above, this is the full
  Problem 8.3: the belief holds for a single qubit but fails for larger systems.
-/

open scoped InnerProductSpace ComplexOrder Matrix

noncomputable section

namespace AxQM

/-- **The four Pauli conjugations of the qubit, as unitary `Evolution`s.** Index `k : Fin 4`
selects `I, X, Y, Z`, realised as the identity and the axis `π`-rotations
`R_x̂(π), R_ŷ(π), R_ẑ(π)`. Since `R_n̂(π) = −i (n̂·σ)`, conjugation `R_n̂(π) ρ R_n̂(π)†` equals the
Pauli conjugation `σ ρ σ` (the global phase `−i` cancels), so mixing these is the **Pauli channel**
`∑ₖ pₖ σₖ ρ σₖ`. Using rotation gates lets the Bloch action reuse
`rotAxisGate_evolve_blochState` (Nielsen & Chuang, Exercise 4.6). -/
def pauliChannelUnitary : Fin 4 → Evolution qubit
  | 0 => rotAxisGate ![1, 0, 0] 0
  | 1 => rotAxisGate ![1, 0, 0] Real.pi
  | 2 => rotAxisGate ![0, 1, 0] Real.pi
  | 3 => rotAxisGate ![0, 0, 1] Real.pi

/-- **The Bloch action of each Pauli conjugation.** Conjugating a Bloch state `½(I + r·σ)` by the
`k`-th Pauli sends its Bloch vector `r` to `Concrete.pauliBlochFlip k r` — the identity fixes `r`,
and `X, Y, Z` each negate the two Bloch coordinates orthogonal to their axis. Immediate from
`rotAxisGate_evolve_blochState` and the `π`-rotation computations `Concrete.rot3D_axis*_pi`. -/
theorem pauliChannelUnitary_evolve_blochState (i : Fin 4) (v : Fin 3 → ℝ)
    (h : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 ≤ 1) :
    (pauliChannelUnitary i).evolve (blochState v h)
      = blochState (Concrete.pauliBlochFlip i v)
          (by rw [Concrete.pauliBlochFlip_sq_sum]; exact h) := by
  fin_cases i <;>
    simp only [pauliChannelUnitary] <;>
    rw [rotAxisGate_evolve_blochState (by simp) _ v h] <;>
    apply State.ext <;>
    simp only [blochState_op, Concrete.rot3D_angle_zero, Concrete.rot3D_axisX_pi,
      Concrete.rot3D_axisY_pi, Concrete.rot3D_axisZ_pi, Concrete.pauliBlochFlip] <;>
    rfl

/-- **The qubit Pauli channel** `E(ρ) = ∑ₖ pₖ σₖ ρ σₖ` as a `RandomUnitaryChannel`, for a
probability distribution `p : Fin 4 → ℝ` over the four Paulis (`pₖ ≥ 0`, `∑ pₖ = 1`). Its unitaries
are `pauliChannelUnitary`. This is the running family of unital, random-unitary qubit channels of
Problem 8.3. -/
def pauliChannel (p : Fin 4 → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1) :
    RandomUnitaryChannel qubit where
  card := 4
  prob := p
  unitary := pauliChannelUnitary
  prob_nonneg := hp0
  sum_prob := hp

/-- **The Bloch action of the Pauli channel is a diagonal contraction.** The Pauli channel
`∑ₖ pₖ σₖ ρ σₖ` sends the Bloch state with vector `r` to the Bloch state with vector
`Concrete.pauliTwirlVec p r = (mₓ r₀, m_y r₁, m_z r₂)`, where the Pauli-transfer coefficients
`mⱼ = ∑ₖ ±pₖ` satisfy `|mⱼ| ≤ 1`. This is the **constructive `⇐` direction of Problem 8.3's qubit
converse for diagonal channels**: every diagonal contraction of the Bloch ball realised by these
coefficients comes from a genuine random-unitary (Pauli) channel.

The proof averages the per-Pauli sign-flips (`pauliChannelUnitary_evolve_blochState`) and transports
the concrete matrix identity `Concrete.blochMatrix_pauliTwirl` through the `⋆`-algebra isomorphism
`Matrix.toEuclideanCLM`. -/
theorem pauliChannel_apply_blochState (p : Fin 4 → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    (v : Fin 3 → ℝ) (h : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 ≤ 1) :
    (pauliChannel p hp0 hp).apply (blochState v h)
      = blochState (Concrete.pauliTwirlVec p v)
          (le_trans (Concrete.pauliTwirlVec_sq_sum_le p v hp0 hp) h) := by
  apply State.ext
  rw [RandomUnitaryChannel.apply_op, blochState_op]
  simp only [pauliChannel, pauliChannelUnitary_evolve_blochState, blochState_op]
  rw [← Concrete.blochMatrix_pauliTwirl p v hp, map_sum]
  exact Finset.sum_congr rfl fun i _ => (map_smul Matrix.toEuclideanCLM _ _).symm

/-- **The qubit Pauli channel is unital**, `E(I/2) = I/2` (the easy direction, at the Pauli family).
Immediate from `RandomUnitaryChannel.isUnital`: every random-unitary channel fixes `I/d`. -/
theorem pauliChannel_isUnital (p : Fin 4 → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1) :
    IsUnital (pauliChannel p hp0 hp).apply :=
  (pauliChannel p hp0 hp).isUnital

/-- **The qubit Pauli channel is a genuine CPTP channel.** Immediate from
`RandomUnitaryChannel.isChannel` (Kraus operators `√pₖ σₖ`). -/
theorem pauliChannel_isChannel (p : Fin 4 → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1) :
    IsChannel (pauliChannel p hp0 hp).apply :=
  (pauliChannel p hp0 hp).isChannel

/-- **The qubit Pauli channel is random-unitary** — tautologically, being a `RandomUnitaryChannel`.
Together with `pauliChannel_isUnital` and `pauliChannel_isChannel`, this exhibits the Pauli channels
as *unital channels that are random-unitary*: the constructive confirmation, for the whole Pauli
family, of Problem 8.3's "tempting belief" (the full qubit converse, for every unital qubit
channel, is
`isRandomUnitary_of_isChannel_isUnital` below). -/
theorem pauliChannel_isRandomUnitary (p : Fin 4 → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1) :
    IsRandomUnitary (pauliChannel p hp0 hp).apply :=
  ⟨pauliChannel p hp0 hp, fun _ => rfl⟩

/-! ### Assembly of the qubit converse — from Bloch action to random-unitarity

The Bloch-sphere strategy of Problem 8.3's qubit converse operates entirely on **Bloch vectors**: a
unital qubit channel `f` acts as `r ↦ M r` (`exists_channelBlochMatrix`), its Bloch matrix factors
`M = O₁ · diag d · O₂` into proper rotations
(`Concrete.exists_specialOrthogonalGroup_diagonal_factor`), the diagonal contraction is a Pauli
channel (`pauliChannel`), and the rotations `O₁, O₂ ∈ SO(3)` become unitary conjugations
(`exists_evolution_evolve_blochState_of_mem_specialOrthogonalGroup`). The
following two lemmas are the bridge back from that Bloch-vector reasoning to the global claim
`IsRandomUnitary f`: a channel matching a random-unitary channel *on Bloch states* is random-unitary
(every qubit state is a Bloch state, `State.exists_blochState`, N&C Exercise 2.72). -/

/-- **`IsRandomUnitary` is determined by the action on Bloch states.** A qubit channel `f` that
agrees with a random-unitary channel `c` on every Bloch state — `f (blochState r) = c (blochState
r)` for all `r` in the closed Bloch ball — is itself random-unitary. Immediate from surjectivity of
the Bloch state map (`State.exists_blochState`, N&C Exercise 2.72(1)): every qubit state is a Bloch
state, so `f` and `c` agree on *all* states, and `c`'s witnessing `RandomUnitaryChannel` witnesses
`f`. This is the reduction that lets the qubit converse of Problem 8.3 be carried out purely at the
Bloch-vector level, where the singular-value decomposition and the `SU(2) → SO(3)` cover operate. -/
theorem isRandomUnitary_of_blochState_eq {f c : State qubit → State qubit}
    (hc : IsRandomUnitary c)
    (hfc : ∀ (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1),
        f (blochState r h) = c (blochState r h)) :
    IsRandomUnitary f := by
  obtain ⟨C, hC⟩ := hc
  refine ⟨C, fun ρ => ?_⟩
  obtain ⟨r, h, rfl⟩ := ρ.exists_blochState
  rw [hC]
  exact (hfc r h).symm

/-- **Assembly step of the qubit converse: conjugating a random-unitary channel by two qubit
unitaries.** If a qubit channel `f` acts on Bloch states as `conj U₁ ∘ g ∘ conj U₂` —
`f (blochState r) = U₁.evolve (g (U₂.evolve (blochState r)))` for a random-unitary channel `g` and
unitary evolutions `U₁, U₂` — then `f` is random-unitary. The composite `conj U₁ ∘ g ∘ conj U₂` is
random-unitary because `IsRandomUnitary` contains every unitary conjugation
(`isRandomUnitary_evolve`) and is closed under composition (`isRandomUnitary_comp`);
`isRandomUnitary_of_blochState_eq` transfers this to `f`.

In the qubit converse of Problem 8.3, `g` is the diagonal Pauli channel `pauliChannel p` and
`U₁, U₂` are the qubit unitaries realising the pre/post rotations `O₁, O₂ ∈ SO(3)` of the
Bloch-matrix singular-value decomposition `M = O₁ · diag d · O₂` (through the `SU(2) → SO(3)`
surjectivity `exists_evolution_evolve_blochState_of_mem_specialOrthogonalGroup`). What then remains
of the converse is the concrete fact that the diagonal `d` is a Pauli-transfer vector
`Concrete.pauliTwirlVec p` of a probability distribution `p` (the Fujiwara–Algoet /
complete-positivity conditions). -/
theorem isRandomUnitary_of_blochState_eq_evolve_comp {f g : State qubit → State qubit}
    (U₁ U₂ : Evolution qubit) (hg : IsRandomUnitary g)
    (hf : ∀ (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1),
        f (blochState r h) = U₁.evolve (g (U₂.evolve (blochState r h)))) :
    IsRandomUnitary f :=
  isRandomUnitary_of_blochState_eq
    (isRandomUnitary_comp (isRandomUnitary_evolve U₁)
      (isRandomUnitary_comp hg (isRandomUnitary_evolve U₂)))
    hf

/-- **The Pauli-channel form of the assembly (Problem 8.3, qubit converse).** A qubit channel `f`
acting on Bloch states as `conj U₁ ∘ (Pauli channel p) ∘ conj U₂` is random-unitary. This is exactly
the shape the qubit converse produces once a unital qubit channel's Bloch matrix
`M = O₁ · diag (Concrete.pauliTwirlVec p) · O₂` is factored and the rotations `O₁, O₂` are realised
as the unitary conjugations `U₁, U₂`. Specialisation of
`isRandomUnitary_of_blochState_eq_evolve_comp` to the random-unitary `pauliChannel p`
(`pauliChannel_isRandomUnitary`). -/
theorem isRandomUnitary_of_blochState_eq_evolve_pauliChannel_comp
    {f : State qubit → State qubit} (U₁ U₂ : Evolution qubit)
    (p : Fin 4 → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    (hf : ∀ (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1),
        f (blochState r h)
          = U₁.evolve ((pauliChannel p hp0 hp).apply (U₂.evolve (blochState r h)))) :
    IsRandomUnitary f :=
  isRandomUnitary_of_blochState_eq_evolve_comp U₁ U₂ (pauliChannel_isRandomUnitary p hp0 hp) hf

/-- **The CP-realisable diagonal case of the qubit converse (Problem 8.3).** A qubit channel `f`
whose Bloch action is a *diagonal contraction* `r ↦ (d₀ r₀, d₁ r₁, d₂ r₂)`, with the coefficient
triple `d` satisfying the complete-positivity (Fujiwara–Algoet) condition
`Concrete.pauliTwirlInvProb d ≥ 0`, is random-unitary. The realising channel is the Pauli channel
with the inverse-transform weights `Concrete.pauliTwirlInvProb d` — a genuine probability
distribution by `hd` and `Concrete.pauliTwirlInvProb_sum` — whose Bloch action *is* that diagonal
contraction (`Concrete.pauliTwirlVec_pauliTwirlInvProb`); `isRandomUnitary_of_blochState_eq` then
transfers random-unitarity from that Pauli channel to `f`.

This generalises `pauliChannel_isRandomUnitary` from a channel *presented as* a Pauli channel to
*any* channel matching an arbitrary CP-realisable diagonal Bloch action — the diagonal core of the
converse. The full converse reduces to this diagonal case through the singular-value decomposition
`M = O₁ · diag d · O₂` (`Concrete.exists_specialOrthogonalGroup_diagonal_factor`) of a unital qubit
channel's Bloch matrix (`exists_channelBlochMatrix`), the rotations `O₁, O₂` being realised as
unitary conjugations (`exists_evolution_evolve_blochState_of_mem_specialOrthogonalGroup`); the
`Concrete.pauliTwirlInvProb d ≥ 0` hypothesis `hd` is then discharged from complete positivity by
`AxQM.pauliTwirlInvProb_nonneg_of_channel_blochDiagonal` (applied to the diagonalised
channel), so only the geometric assembly remains. -/
theorem isRandomUnitary_of_blochState_eq_diagonalScaling
    {f : State qubit → State qubit} (d : Fin 3 → ℝ)
    (hd : ∀ i, 0 ≤ Concrete.pauliTwirlInvProb d i)
    (hf : ∀ (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1)
        (h' : (d 0 * r 0) ^ 2 + (d 1 * r 1) ^ 2 + (d 2 * r 2) ^ 2 ≤ 1),
        f (blochState r h) = blochState ![d 0 * r 0, d 1 * r 1, d 2 * r 2] h') :
    IsRandomUnitary f := by
  refine isRandomUnitary_of_blochState_eq
    (pauliChannel_isRandomUnitary (Concrete.pauliTwirlInvProb d) hd
      (Concrete.pauliTwirlInvProb_sum d)) ?_
  intro r h
  have hround := Concrete.pauliTwirlVec_pauliTwirlInvProb d r
  have hle := Concrete.pauliTwirlVec_sq_sum_le (Concrete.pauliTwirlInvProb d) r hd
    (Concrete.pauliTwirlInvProb_sum d)
  rw [hround] at hle
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hle
  have h' : (d 0 * r 0) ^ 2 + (d 1 * r 1) ^ 2 + (d 2 * r 2) ^ 2 ≤ 1 := le_trans hle h
  rw [hf r h h', pauliChannel_apply_blochState]
  apply State.ext
  simp only [blochState_op, hround]
  rfl

/-! ### The qubit converse of Problem 8.3 — *every* unital qubit channel is random-unitary

Assembling all the ingredients above gives the first half of Problem 8.3: for a
single qubit, unitality really does force the random-unitary form `E(ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†` on a
channel — the "tempting belief" is *true* in dimension two (Landau & Streater). -/

set_option maxHeartbeats 400000 in
-- Since Lean v4.36 the final reassembly step needs more than the default heartbeats.
/-- **Problem 8.3, qubit converse (dimension two): every unital qubit channel is random-unitary.**
A CPTP quantum channel `f` of the `qubit` (`IsChannel`) that is **unital** (`IsUnital`, `f (I/2) =
I/2`) is a **random-unitary** (mixed-unitary) channel `f (ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†` (`IsRandomUnitary`).
This is the direction of Nielsen & Chuang, Problem 8.3 that *holds*: for one qubit the tempting
belief is correct.

The proof is the geometric assembly of the Bloch-sphere strategy, chaining the ingredients built up
across this development:

* `exists_channelBlochMatrix` — the unital channel acts on Bloch states by a real-linear map
  `r ↦ M r` (its Bloch matrix `M`);
* `Concrete.exists_specialOrthogonalGroup_diagonal_factor` — the singular-value decomposition
  `M = O₁ · diagonal d · O₂` into proper rotations `O₁, O₂ ∈ SO(3)`;
* `exists_evolution_evolve_blochState_of_mem_specialOrthogonalGroup` — the `SU(2) → SO(3)` cover
  realises `O₁, O₂` **and their transposes** `O₁ᵀ, O₂ᵀ`
  (`Concrete.mem_specialOrthogonalGroup_transpose`) as qubit unitary conjugations `U₁, U₂, V₁, V₂`.

Conjugating `f` by the inverse rotations produces the **diagonalised channel**
`g = V₁ ∘ f ∘ V₂`, a unital channel (`isChannel_comp` / `isUnital_comp`, unitary conjugations being
unital channels) whose Bloch action is the pure diagonal contraction `r ↦ (d₀ r₀, d₁ r₁, d₂ r₂)`
(the outer rotations cancel, `O₁ᵀ · M · O₂ᵀ = diagonal d`; the rotated Bloch vectors stay in the
ball by `Concrete.mem_orthogonalGroup_mulVec_sq_sum`). Complete positivity of `g` then forces
the Fujiwara–Algoet inequalities `Concrete.pauliTwirlInvProb d ≥ 0`
(`pauliTwirlInvProb_nonneg_of_channel_blochDiagonal`), so the diagonal case
`isRandomUnitary_of_blochState_eq_diagonalScaling` makes `g` random-unitary. Finally `f` agrees on
every Bloch state with `conj U₁ ∘ g ∘ conj U₂` (again the SVD, now reassembled:
`O₁ · diagonal d · O₂ = M`), so `isRandomUnitary_of_blochState_eq_evolve_comp` lifts
random-unitarity from `g` back to `f`.

The complementary claim — that this *fails* in dimension `≥ 3` (the Landau–Streater / Werner–Holevo
counterexample) — is `wernerHolevoChannel_not_isRandomUnitary` below. -/
theorem isRandomUnitary_of_isChannel_isUnital {f : State qubit → State qubit}
    (hf : IsChannel f) (hu : IsUnital f) : IsRandomUnitary f := by
  obtain ⟨M, hM⟩ := exists_channelBlochMatrix hf hu
  obtain ⟨O₁, O₂, d, hO₁, hO₂, hMfac⟩ := Concrete.exists_specialOrthogonalGroup_diagonal_factor M
  have hO1T := Concrete.mem_specialOrthogonalGroup_transpose hO₁
  have hO2T := Concrete.mem_specialOrthogonalGroup_transpose hO₂
  obtain ⟨U₁, hU₁⟩ := exists_evolution_evolve_blochState_of_mem_specialOrthogonalGroup hO₁
  obtain ⟨U₂, hU₂⟩ := exists_evolution_evolve_blochState_of_mem_specialOrthogonalGroup hO₂
  obtain ⟨V₁, hV₁⟩ := exists_evolution_evolve_blochState_of_mem_specialOrthogonalGroup hO1T
  obtain ⟨V₂, hV₂⟩ := exists_evolution_evolve_blochState_of_mem_specialOrthogonalGroup hO2T
  -- Orthogonality of the four rotations (used for the ball-preservation and the cancellations).
  have hO₁o : O₁ ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp hO₁).1
  have hO₂o : O₂ ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp hO₂).1
  have hO1To : O₁ᵀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp hO1T).1
  have hO2To : O₂ᵀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp hO2T).1
  -- Orthogonality cancellations for the diagonalisation `O₁ᵀ · M · O₂ᵀ = diagonal d`.
  have hO1tO1 : O₁ᵀ * O₁ = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hO₁o
  have hO2tO2 : O₂ᵀ * O₂ = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hO₂o
  have hO2O2t : O₂ * O₂ᵀ = 1 := mul_eq_one_comm.mp hO2tO2
  -- The diagonalised channel `g = conj V₁ ∘ f ∘ conj V₂`.
  set g : State qubit → State qubit := fun ρ => V₁.evolve (f (V₂.evolve ρ)) with hgdef
  have hgchan : IsChannel g :=
    isChannel_comp (isChannel_of_isRandomUnitary (isRandomUnitary_evolve V₁))
      (isChannel_comp hf (isChannel_of_isRandomUnitary (isRandomUnitary_evolve V₂)))
  have hgunit : IsUnital g :=
    isUnital_comp (isUnital_of_isRandomUnitary (isRandomUnitary_evolve V₁))
      (isUnital_comp hu (isUnital_of_isRandomUnitary (isRandomUnitary_evolve V₂)))
  -- `g` acts as the diagonal contraction `d`: the ball-membership of `d ⊙ r` and the operator
  -- identity share one derivation (chaining `V₂`, `f`, `V₁` and cancelling the rotations).
  have hgstep : ∀ (r : Fin 3 → ℝ) (h : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 ≤ 1),
      (d 0 * r 0) ^ 2 + (d 1 * r 1) ^ 2 + (d 2 * r 2) ^ 2 ≤ 1 ∧
      (g (blochState r h)).op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
        (Concrete.blochMatrix ![d 0 * r 0, d 1 * r 1, d 2 * r 2]) := by
    intro r h
    have hb : (O₂ᵀ.mulVec r) 0 ^ 2 + (O₂ᵀ.mulVec r) 1 ^ 2 + (O₂ᵀ.mulVec r) 2 ^ 2 ≤ 1 := by
      rw [Concrete.mem_orthogonalGroup_mulVec_sq_sum hO2To]; exact h
    obtain ⟨hc, hfeq⟩ := hM (O₂ᵀ.mulVec r) hb
    have he : (O₁ᵀ.mulVec (M.mulVec (O₂ᵀ.mulVec r))) 0 ^ 2
        + (O₁ᵀ.mulVec (M.mulVec (O₂ᵀ.mulVec r))) 1 ^ 2
        + (O₁ᵀ.mulVec (M.mulVec (O₂ᵀ.mulVec r))) 2 ^ 2 ≤ 1 := by
      rw [Concrete.mem_orthogonalGroup_mulVec_sq_sum hO1To]; exact hc
    have hvec : O₁ᵀ.mulVec (M.mulVec (O₂ᵀ.mulVec r)) = ![d 0 * r 0, d 1 * r 1, d 2 * r 2] := by
      have hcancel : O₁ᵀ * M * O₂ᵀ = Matrix.diagonal d := by
        rw [hMfac]
        rw [show O₁ᵀ * (O₁ * Matrix.diagonal d * O₂) * O₂ᵀ
            = (O₁ᵀ * O₁) * Matrix.diagonal d * (O₂ * O₂ᵀ) by noncomm_ring,
          hO1tO1, hO2O2t, one_mul, mul_one]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcancel]
      funext i; fin_cases i <;> simp [Matrix.mulVec_diagonal]
    refine ⟨?_, ?_⟩
    · rw [hvec] at he; simpa using he
    · change (V₁.evolve (f (V₂.evolve (blochState r h)))).op = _
      rw [hV₂ r h hb, hfeq, hV₁ (M.mulVec (O₂ᵀ.mulVec r)) hc he, blochState_op, hvec]
  -- Complete positivity of the diagonal action gives the Fujiwara–Algoet inequalities.
  have hd : ∀ i, 0 ≤ Concrete.pauliTwirlInvProb d i :=
    pauliTwirlInvProb_nonneg_of_channel_blochDiagonal hgchan hgunit d (fun r h => (hgstep r h).2)
  -- The diagonalised channel is random-unitary (diagonal case).
  have hgru : IsRandomUnitary g :=
    isRandomUnitary_of_blochState_eq_diagonalScaling d hd (fun r h h' => by
      apply State.ext
      rw [(hgstep r h).2,
        blochState_op ![d 0 * r 0, d 1 * r 1, d 2 * r 2] h'])
  -- Reassemble: `f` agrees on Bloch states with `conj U₁ ∘ g ∘ conj U₂`.
  refine isRandomUnitary_of_blochState_eq_evolve_comp U₁ U₂ hgru (fun r h => ?_)
  have hb : (O₂.mulVec r) 0 ^ 2 + (O₂.mulVec r) 1 ^ 2 + (O₂.mulVec r) 2 ^ 2 ≤ 1 := by
    rw [Concrete.mem_orthogonalGroup_mulVec_sq_sum hO₂o]; exact h
  obtain ⟨hMr, hfeq⟩ := hM r h
  have hdm := (hgstep (O₂.mulVec r) hb).1
  have hgstate : g (blochState (O₂.mulVec r) hb)
      = blochState ![d 0 * (O₂.mulVec r) 0, d 1 * (O₂.mulVec r) 1, d 2 * (O₂.mulVec r) 2] hdm := by
    apply State.ext
    rw [(hgstep (O₂.mulVec r) hb).2,
      blochState_op ![d 0 * (O₂.mulVec r) 0, d 1 * (O₂.mulVec r) 1, d 2 * (O₂.mulVec r) 2] hdm]
  have hh3 :
      (O₁.mulVec ![d 0 * (O₂.mulVec r) 0, d 1 * (O₂.mulVec r) 1, d 2 * (O₂.mulVec r) 2]) 0 ^ 2
        + (O₁.mulVec ![d 0 * (O₂.mulVec r) 0, d 1 * (O₂.mulVec r) 1, d 2 * (O₂.mulVec r) 2]) 1 ^ 2
        + (O₁.mulVec ![d 0 * (O₂.mulVec r) 0, d 1 * (O₂.mulVec r) 1, d 2 * (O₂.mulVec r) 2]) 2 ^ 2
        ≤ 1 := by
    rw [Concrete.mem_orthogonalGroup_mulVec_sq_sum hO₁o]; exact hdm
  have hvec2 : O₁.mulVec ![d 0 * (O₂.mulVec r) 0, d 1 * (O₂.mulVec r) 1, d 2 * (O₂.mulVec r) 2]
      = M.mulVec r := by
    have hdiagvec :
        (![d 0 * (O₂.mulVec r) 0, d 1 * (O₂.mulVec r) 1, d 2 * (O₂.mulVec r) 2] : Fin 3 → ℝ)
        = (Matrix.diagonal d).mulVec (O₂.mulVec r) := by
      funext i; fin_cases i <;> simp [Matrix.mulVec_diagonal]
    rw [hdiagvec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hMfac]
  change f (blochState r h) = U₁.evolve (g (U₂.evolve (blochState r h)))
  rw [hU₂ r h hb, hgstate, hU₁ _ hdm hh3, hfeq]
  apply State.ext
  rw [blochState_op (M.mulVec r) hMr,
    blochState_op
      (O₁.mulVec ![d 0 * (O₂.mulVec r) 0, d 1 * (O₂.mulVec r) 1, d 2 * (O₂.mulVec r) 2]) hh3,
    hvec2]

/-! ### The counterexample in dimension `≥ 3` — *not* every unital channel is random-unitary

The second half of Problem 8.3: the "tempting belief" *fails* for systems larger than a
qubit. The witness is the qutrit **Werner–Holevo channel** `Φ(ρ) = ½(tr(ρ)·I − ρᵀ)`
(`wernerHolevoChannel`), a unital CPTP channel that admits no random-unitary representation. -/

/-- **Problem 8.3, larger-system direction: the Werner–Holevo channel is not random-unitary.** The
qutrit channel `Φ(ρ) = ½(tr(ρ)·I − ρᵀ)` (`wernerHolevoChannel`) — a genuine *unital* CPTP channel —
is **not** a random-unitary (mixed-unitary) average `∑ₖ pₖ Uₖ ρ Uₖ†` (`¬ IsRandomUnitary`). This is
the direction of Nielsen & Chuang, Problem 8.3 that *fails*: the "tempting belief" is false in
dimension `≥ 3` (Landau & Streater).

The proof pairs a hypothetical representation `Φ = ∑ₖ pₖ Uₖ ρ Uₖ†` against a conjugated pure state
`ψ̄ = ψ.vec.conjVec`. Two evaluations of `⟨ψ̄, Φ(|ψ⟩⟨ψ|) ψ̄⟩` disagree unless every unitary is
degenerate:

* the Werner–Holevo side is `0` (`Φ(|ψ⟩⟨ψ|) = ½(I − |ψ̄⟩⟨ψ̄|)`, so the diagonal element on `ψ̄`
  cancels), while
* the mixture side is `∑ₖ pₖ ‖⟨ψ̄, Uₖ ψ⟩‖²`
  (`RandomUnitaryChannel.sum_prob_normSq_eq_zero_of_apply_eq_wernerHolevoChannel`).

A sum of nonnegative terms being zero forces each `pₖ ‖⟨ψ̄, Uₖ ψ⟩‖² = 0`; picking `k₀` with
`pₖ₀ > 0` (some weight is positive, as they sum to one) gives `⟨ψ̄, Uₖ₀ ψ⟩ = ψᵀ Uₖ₀ ψ = 0` for
**every** pure state `ψ`. But no qutrit unitary can annihilate that bilinear form on every vector
(`Evolution.not_forall_inner_conjVec_op_eq_zero`): it would be antisymmetric, and an antisymmetric
matrix in **odd** dimension `3` is singular, contradicting unitarity. The whole
computation lives in `AxQM/Postulates/API/WernerHolevoRandomUnitary.lean`. -/
theorem wernerHolevoChannel_not_isRandomUnitary : ¬ IsRandomUnitary wernerHolevoChannel := by
  rintro ⟨C, hC⟩
  -- Some weight `pₖ₀` is positive, because the weights sum to one.
  obtain ⟨k₀, hk₀⟩ : ∃ k, 0 < C.prob k := by
    by_contra h
    have hle : ∀ k, C.prob k ≤ 0 := fun k => not_lt.mp (fun hlt => h ⟨k, hlt⟩)
    have hsum : ∑ i, C.prob i ≤ 0 := Finset.sum_nonpos (fun i _ => hle i)
    rw [C.sum_prob] at hsum; linarith
  -- It suffices to show the `k₀`-unitary annihilates the conjugate bilinear form on every state.
  refine (C.unitary k₀).not_forall_inner_conjVec_op_eq_zero (fun ψ => ?_)
  have hsum := C.sum_prob_normSq_eq_zero_of_apply_eq_wernerHolevoChannel hC ψ
  have hnn : ∀ k ∈ Finset.univ,
      0 ≤ C.prob k * ‖(inner ℂ (pureConjVec ψ) ((C.unitary k).op ψ.vec) : ℂ)‖ ^ 2 :=
    fun k _ => mul_nonneg (C.prob_nonneg k) (sq_nonneg _)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum k₀ (Finset.mem_univ k₀)
  have hnorm2 : ‖(inner ℂ (pureConjVec ψ) ((C.unitary k₀).op ψ.vec) : ℂ)‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hk₀)
  exact norm_eq_zero.mp (by simpa using hnorm2)

/-- **Problem 8.3, headline of the larger-system direction: a unital channel that is not
random-unitary exists.** In dimension `3` there is a completely-positive trace-preserving,
**unital** quantum channel (`IsChannel ∧ IsUnital`) that is *not* a random-unitary average
`∑ₖ pₖ Uₖ ρ Uₖ†` (`¬ IsRandomUnitary`) — the qutrit **Werner–Holevo channel**
`Φ(ρ) = ½(tr(ρ)·I − ρᵀ)` (`wernerHolevoChannel`). Assembles its three certificates
(`wernerHolevoChannel_isChannel`, `wernerHolevoChannel_isUnital`,
`wernerHolevoChannel_not_isRandomUnitary`).

Together with the qubit converse `isRandomUnitary_of_isChannel_isUnital` (every unital *qubit*
channel *is* random-unitary), this is the full content of Nielsen & Chuang, Problem 8.3: all unital
channels are random-unitary averages for a single qubit, but not for larger systems (Landau &
Streater). -/
theorem exists_unital_channel_not_isRandomUnitary :
    ∃ f : State (qudit 3) → State (qudit 3), IsChannel f ∧ IsUnital f ∧ ¬ IsRandomUnitary f :=
  ⟨wernerHolevoChannel, wernerHolevoChannel_isChannel, wernerHolevoChannel_isUnital,
    wernerHolevoChannel_not_isRandomUnitary⟩

end AxQM
