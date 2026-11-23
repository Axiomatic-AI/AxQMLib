/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.PauliStringCliffordCircuit
import AxQM.Concrete.PauliGroup

/-!
# Concrete: the Pauli normalizer, and uniqueness up to global phase (Theorem 10.6, part 1)

This file opens the formalisation of
Nielsen & Chuang **Theorem 10.6** — *any unitary `U` on `n` qubits with `U Gₙ U† ⊆ Gₙ` is, up to a
global phase, a product of `O(n²)` Hadamard/phase/CNOT gates*. It supplies the **framework** (the
matrix-level normalizer predicate), the **easy direction** (every Clifford circuit is a Pauli
normalizer), and the **reduction that gives the theorem its "up to a global phase" shape**: two
unitaries with the *same conjugation action* on the Pauli group agree up to a unit scalar. Every
statement is about raw matrix / index data (`Matrix`, `Concrete.pauliString`,
`Concrete.PauliGroup`, `Matrix.unitaryGroup`, `Fin n → Fin 4`).

## What is proved

* `exists_smul_one_of_commute_pauliString` — **the Pauli commutant is the scalars.** A matrix `W`
  commuting with every Pauli string `P_g` is a scalar `c • 1`. This is *Schur's lemma for the Pauli
  group*: since the `4ⁿ` Pauli strings are a basis of the `2ⁿ×2ⁿ` matrices (`pauliBasis`), `W`
  commutes with every matrix, hence lies in the centre of the matrix ring, which is the scalars
  (`Matrix.center_eq_scalar_image`). It is the linear-algebraic engine of the whole reduction.

* `IsPauliNormalizer U` — **the normalizer predicate.** `U` is unitary and conjugates every element
  of the Pauli group `Gₙ` (via its faithful representation `PauliGroup.toMat`) back into `Gₙ`. This
  is exactly N&C's hypothesis "if `g ∈ Gₙ` then `U g U† ∈ Gₙ`", i.e. membership in the normalizer
  `N(Gₙ)`.

* `unitary_eq_smul_of_conj_pauliString_eq` — **uniqueness up to global phase (the reduction).** If
  two unitaries `U, V` conjugate every Pauli string identically (`U P_g U† = V P_g V†` for all `g`),
  then `U = c • V` for a unit scalar `c` (`‖c‖ = 1`). Hence a normalizer unitary is determined, up
  to a global phase, by its conjugation action on `Gₙ` — the precise sense of Theorem 10.6's "up to
  a global phase", and what reduces the theorem to realising that action by a Clifford circuit.

* `unitary_isGlobalPhase_of_conj_pauliString_eq_self` — **Nielsen & Chuang Exercise 10.38 (core).**
  A unitary that fixes every Pauli string under conjugation (`U P_g U† = P_g`) is a global phase
  `c • 1`, `‖c‖ = 1`. The `V = 1` special case of the reduction; the physical statement that only
  scalars commute with the whole Pauli group.

* `CliffordCircuit.sign_eq_one_or_neg_one` / `cliffordCircuit_isPauliNormalizer` — **the easy
  direction of Theorem 10.6.** The conjugation phase of a Clifford circuit is `±1`, and therefore
  every Clifford circuit is a Pauli normalizer: `U P_a U† = ±P_{U.act a}`, so `U (iˢ P_a) U† =
  i^{s'} P_{U.act a} ∈ Gₙ` (`CliffordCircuit.conj_pauliString`). This is the containment
  `⟨H, S, CNOT⟩ ⊆ N(Gₙ)`; Theorem 10.6 is the converse.

* `IsPauliNormalizer.exists_sign_conj_pauliString` — **the sign is `±1`.** A normalizer conjugates
  each phase-free Pauli string to a `±1` multiple of a Pauli string, `U P_a U† = z • P_b` with
  `z ∈ {1, -1}`. The phase is real because `P_a` is an involution, so `(U P_a U†)² = 1` forces
  `z² = 1`; this is the shape (signs `±1`, never `±i`) the synthesis of Exercise 10.40 uses.

* `IsPauliNormalizer.exists_signedPerm` — **a normalizer is a `±1`-signed permutation of the Pauli
  strings.** Bundles the per-string data into a permutation `σ : Equiv.Perm (Fin n → Fin 4)` and a
  sign function `ε` valued in `{1, -1}` with `U P_a U† = ε a • P_{σ a}`. Injectivity of the action
  (hence bijectivity, on the finite index set) comes from conjugating back by `U` and
  Hilbert–Schmidt orthogonality. It is the combinatorial object Exercise 10.40 synthesises.

* `unitary_eq_smul_cliffordCircuit_of_conj_eq` — **the converse reduces to synthesis.** If a unitary
  conjugates the Pauli strings exactly as a Clifford circuit `C` does, it equals `C` up to a global
  phase. With `exists_signedPerm` this reduces the converse of Theorem 10.6 to a combinatorial
  problem: synthesise a Clifford circuit realising the normalizer's signed permutation.

* `unitaryConj_commute_iff` / `IsPauliNormalizer.exists_signedPerm_symplectic` — **a normalizer's
  signed permutation is symplectic.** Conjugation by a unitary preserves commutation (it is an
  algebra automorphism), so a normalizer's induced permutation `σ` of the Pauli-string indices
  preserves the binary symplectic form (`pauliAnticommCount`, mod 2) of Exercise 10.33 — in
  particular it maps anticommuting Pauli strings to anticommuting ones. This is the structural
  invariant the multi-qubit inductive synthesis of Exercise 10.40 (parts 2–3) rests on (N&C part 2
  opens by noting the images of the anticommuting `Z₁, X₁` anticommute).

## Design notes

* The reduction is stated over `pauliString` (the phase-free Pauli operators) because that is where
  `pauliBasis`/`CliffordCircuit.conj_pauliString` live; the normalizer *predicate* is stated over
  the full group `PauliGroup.toMat = iˢ • P_a` (phases included) to be faithful to N&C's `Gₙ`. The
  two match because conjugation is `ℂ`-linear, so acting on `iˢ P_a` is acting on `P_a` scaled.
* `unitary_eq_smul_of_conj_pauliString_eq` needs no normalizer hypothesis: it holds for *any* two
  unitaries with equal conjugation action. The normalizer only enters when one shows the action is
  realised by a Clifford circuit (the converse, developed later — the inductive synthesis of
  N&C Exercise 10.40 and its `O(n²)` gate count).
-/

open Matrix

noncomputable section

namespace AxQM.Concrete

variable {n : ℕ}

/-! ### Schur's lemma for the Pauli group: the commutant is the scalars -/

/-- **The Pauli commutant is the scalars.** If `W` commutes with every Pauli string `P_g`, then
`W = c • 1` for some scalar `c`. Because the `4ⁿ` Pauli strings form a basis of the `2ⁿ×2ⁿ`
matrices (`sum_repr_smul_pauliString`), `W` commutes with *every* matrix, so it lies in the centre
of the matrix ring, which is the scalar matrices (`Matrix.center_eq_scalar_image`). -/
theorem exists_smul_one_of_commute_pauliString
    (W : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (h : ∀ g, Commute (pauliString g) W) : ∃ c : ℂ, W = c • 1 := by
  have hz : W ∈ Set.center (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) := by
    rw [Semigroup.mem_center_iff]
    intro M
    rw [← sum_repr_smul_pauliString M, Finset.sum_mul, Matrix.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by
      rw [smul_mul_assoc, mul_smul_comm, (h g).eq]
  rw [Matrix.center_eq_scalar_image, Set.center_eq_univ] at hz
  obtain ⟨c, -, rfl⟩ := hz
  exact ⟨c, Algebra.algebraMap_eq_smul_one c⟩

/-! ### The normalizer predicate -/

/-- **The Pauli normalizer** `N(Gₙ)`. `U` is unitary and conjugates every element of the `n`-qubit
Pauli group `Gₙ` (through its faithful matrix representation `PauliGroup.toMat`, `p ↦ iˢ • P_a`)
back into `Gₙ`. This is exactly Nielsen & Chuang's hypothesis in Theorem 10.6: "if `g ∈ Gₙ` then
`U g U† ∈ Gₙ`". -/
def IsPauliNormalizer (U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ ∧
    ∀ p : PauliGroup n, ∃ q : PauliGroup n, U * p.toMat * Uᴴ = q.toMat

/-! ### Uniqueness up to global phase (the reduction) -/

/-- **Uniqueness up to a global phase.** If two unitaries `U, V` conjugate every Pauli string
identically — `U P_g U† = V P_g V†` for all `g` — then they differ by a unit global phase:
`∃ c, ‖c‖ = 1 ∧ U = c • V`. Setting `W = V† U`, the hypothesis says `W` commutes with every `P_g`
(cancelling `V†V = U†U = 1`), so `W = c • 1` by `exists_smul_one_of_commute_pauliString`; unitarity
forces `‖c‖ = 1`, and `U = V W = c • V`. This is the precise content of Theorem 10.6's "up to a
global phase": a normalizer unitary is determined, up to a scalar, by its conjugation action. -/
theorem unitary_eq_smul_of_conj_pauliString_eq
    {U V : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ)
    (h : ∀ g, U * pauliString g * Uᴴ = V * pauliString g * Vᴴ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ U = c • V := by
  -- basic unitarity facts (`star = ᴴ`)
  have hVV : V * Vᴴ = 1 := by simpa [star_eq_conjTranspose] using (mem_unitaryGroup_iff).mp hV
  have hVV' : Vᴴ * V = 1 := by simpa [star_eq_conjTranspose] using (mem_unitaryGroup_iff').mp hV
  set W := Vᴴ * U with hW
  have hWH : Wᴴ = Uᴴ * V := by rw [hW, conjTranspose_mul, conjTranspose_conjTranspose]
  -- W is a product of unitaries, hence unitary (submonoid closure)
  have hWmem : W ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ := by
    rw [hW]; exact mul_mem (by rw [← star_eq_conjTranspose]; exact Unitary.star_mem hV) hU
  have hWW : W * Wᴴ = 1 := by simpa [star_eq_conjTranspose] using (mem_unitaryGroup_iff).mp hWmem
  have hWW' : Wᴴ * W = 1 := by simpa [star_eq_conjTranspose] using (mem_unitaryGroup_iff').mp hWmem
  -- W commutes with every Pauli string
  have hcomm : ∀ g, Commute (pauliString g) W := by
    intro g
    have hconj : W * pauliString g * Wᴴ = pauliString g := by
      rw [hW, hWH]
      calc Vᴴ * U * pauliString g * (Uᴴ * V)
            = Vᴴ * (U * pauliString g * Uᴴ) * V := by simp [Matrix.mul_assoc]
        _ = Vᴴ * (V * pauliString g * Vᴴ) * V := by rw [h g]
        _ = (Vᴴ * V) * pauliString g * (Vᴴ * V) := by simp [Matrix.mul_assoc]
        _ = pauliString g := by rw [hVV', Matrix.one_mul, Matrix.mul_one]
    -- multiply `hconj` on the right by `W` and cancel `Wᴴ W = 1`
    have key : W * pauliString g = pauliString g * W := by
      have hmulW := congrArg (· * W) hconj
      simpa [Matrix.mul_assoc, hWW'] using hmulW
    exact key.symm
  -- so W is a scalar, and unitarity pins its modulus to 1
  obtain ⟨c, hc⟩ := exists_smul_one_of_commute_pauliString W hcomm
  -- unitarity of `W = c • 1` pins the modulus of `c` to `1`
  have hWform : W * Wᴴ = (c * star c) • 1 := by
    rw [hc, conjTranspose_smul, conjTranspose_one, smul_mul_smul_comm, Matrix.mul_one]
  have hcc : c * star c = 1 := by
    have he : ((c * star c) • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)) = 1 := by
      rw [← hWform]; exact hWW
    have h11 := congrFun (congrFun he (fun _ => (0 : Fin 2))) (fun _ => (0 : Fin 2))
    simpa [Matrix.smul_apply, Matrix.one_apply] using h11
  have hmod : ‖c‖ = 1 := by
    have hnorm : ‖c‖ * ‖c‖ = 1 := by
      have hn : ‖c * star c‖ = ‖(1 : ℂ)‖ := by rw [hcc]
      rwa [norm_mul, norm_star, norm_one] at hn
    rcases mul_self_eq_one_iff.mp hnorm with h1 | h1
    · exact h1
    · linarith [norm_nonneg c]
  refine ⟨c, hmod, ?_⟩
  -- U = V W = c • V
  have hVWU : V * W = U := by rw [hW, ← Matrix.mul_assoc, hVV, Matrix.one_mul]
  rw [← hVWU, hc, mul_smul_comm, Matrix.mul_one]

/-- **Nielsen & Chuang Exercise 10.38 (core).** A unitary `U` that *fixes* every Pauli string under
conjugation (`U P_g U† = P_g` for all `g`) is a global phase: `∃ c, ‖c‖ = 1 ∧ U = c • 1`. The
`V = 1` special case of `unitary_eq_smul_of_conj_pauliString_eq`. -/
theorem unitary_isGlobalPhase_of_conj_pauliString_eq_self
    {U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ)
    (h : ∀ g, U * pauliString g * Uᴴ = pauliString g) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ U = c • 1 :=
  unitary_eq_smul_of_conj_pauliString_eq hU (Submonoid.one_mem _)
    (fun g => by rw [h g, conjTranspose_one, Matrix.one_mul, Matrix.mul_one])

/-! ### The easy direction: every Clifford circuit is a Pauli normalizer -/

/-- The single-gate Hadamard conjugation phase is `±1`: `hadamardPauliSign a ∈ {1, -1}`. -/
private theorem hadamardPauliSign_eq_one_or_neg_one (a : Fin 4) :
    hadamardPauliSign a = 1 ∨ hadamardPauliSign a = -1 := by
  fin_cases a <;> simp [hadamardPauliSign]

/-- The single-gate phase-gate conjugation phase is `±1`: `phasePauliSign a ∈ {1, -1}`. -/
private theorem phasePauliSign_eq_one_or_neg_one (a : Fin 4) :
    phasePauliSign a = 1 ∨ phasePauliSign a = -1 := by
  fin_cases a <;> simp [phasePauliSign]

/-- The single-gate CNOT conjugation phase is `±1`: `cnotPauliSign a b ∈ {1, -1}`. -/
private theorem cnotPauliSign_eq_one_or_neg_one (a b : Fin 4) :
    cnotPauliSign a b = 1 ∨ cnotPauliSign a b = -1 := by
  fin_cases a <;> fin_cases b <;> simp [cnotPauliSign]

/-- An elementary Clifford gate conjugates a Pauli string with a `±1` phase. -/
theorem CliffordGate.sign_eq_one_or_neg_one (γ : CliffordGate n) (g : Fin n → Fin 4) :
    γ.sign g = 1 ∨ γ.sign g = -1 := by
  cases γ with
  | had j => simpa [CliffordGate.sign] using hadamardPauliSign_eq_one_or_neg_one (g j)
  | phase j => simpa [CliffordGate.sign] using phasePauliSign_eq_one_or_neg_one (g j)
  | cnot c t _ => simpa [CliffordGate.sign] using cnotPauliSign_eq_one_or_neg_one (g c) (g t)

/-- **A Clifford circuit conjugates a Pauli string with a `±1` phase**: `U.sign g ∈ {1, -1}`, since
it is a product of the per-gate `±1` phases (`CliffordGate.sign_eq_one_or_neg_one`). -/
theorem CliffordCircuit.sign_eq_one_or_neg_one (U : CliffordCircuit n) (g : Fin n → Fin 4) :
    CliffordCircuit.sign U g = 1 ∨ CliffordCircuit.sign U g = -1 := by
  induction U with
  | nil => left; rfl
  | cons γ U ih =>
      rw [CliffordCircuit.sign]
      rcases ih with hU | hU <;>
        rcases γ.sign_eq_one_or_neg_one (CliffordCircuit.act U g) with hγ | hγ <;>
        simp [hU, hγ]

/-- The Clifford-circuit conjugation phase is a fourth root of unity: `U.sign g = iᵏ` for some
`k : ZMod 4` (indeed `k ∈ {0, 2}`, i.e. `±1`). Packaging `sign_eq_one_or_neg_one` in the phase
form `zmod4Pow` needed to land the conjugate back in the Pauli group `Gₙ`. -/
theorem CliffordCircuit.sign_eq_zmod4Pow (U : CliffordCircuit n) (g : Fin n → Fin 4) :
    ∃ k : ZMod 4, CliffordCircuit.sign U g = zmod4Pow k := by
  rcases CliffordCircuit.sign_eq_one_or_neg_one U g with h | h
  · exact ⟨0, by rw [h, zmod4Pow_zero]⟩
  · exact ⟨2, by rw [h, zmod4Pow_two]⟩

/-- **The easy direction of Nielsen & Chuang Theorem 10.6**: every Clifford circuit `U` (a sequence
of Hadamard/phase/CNOT gates) is a Pauli normalizer. It is unitary (`CliffordCircuit.
mul_conjTranspose`), and for a group element `iˢ • P_a` its conjugate is `iˢ • (±P_{U.act a}) =
i^{s'} • P_{U.act a} ∈ Gₙ`, the `±1` phase folded into the fourth-root-of-unity factor
(`CliffordCircuit.conj_pauliString` + `CliffordCircuit.sign_eq_zmod4Pow`). This is the containment
`⟨H, S, CNOT⟩ ⊆ N(Gₙ)`; Theorem 10.6 asserts the converse. -/
theorem cliffordCircuit_isPauliNormalizer (U : CliffordCircuit n) :
    IsPauliNormalizer (CliffordCircuit.toMatrix U) := by
  refine ⟨?_, fun p => ?_⟩
  · rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
    exact CliffordCircuit.mul_conjTranspose U
  · obtain ⟨k, hk⟩ := CliffordCircuit.sign_eq_zmod4Pow U p.idx
    refine ⟨⟨p.phase + k, CliffordCircuit.act U p.idx⟩, ?_⟩
    simp only [PauliGroup.toMat]
    rw [mul_smul_comm, smul_mul_assoc, CliffordCircuit.conj_pauliString, smul_smul, hk,
      ← zmod4Pow_add]

/-! ### The induced signed permutation of a normalizer, and the reduction to Clifford synthesis -/

/-- **A Pauli normalizer conjugates each phase-free Pauli string to a `±1` multiple of a Pauli
string.** For `U ∈ N(Gₙ)` and any index `a`, there are an index `b` and a sign `z ∈ {1, -1}` with
`U P_a U† = z • P_b`. Two facts combine: the normalizer hypothesis applied to the group element
`⟨0, a⟩ = P_a` gives `U P_a U† = iˢ • P_b` for a Pauli-group element `⟨s, b⟩`; and `P_a` is an
involution (`pauliString_mul_self`), so `(U P_a U†)² = 1` (unitarity cancels the inner `U† U`),
forcing `(iˢ)² = 1`, i.e. `iˢ = ±1` (`mul_self_eq_one_iff`). This `±1`-signed shape of the
conjugation action is what the inductive synthesis of Nielsen & Chuang Exercise 10.40 relies on
(the encoded generators pick up `±1` signs, never `±i`). -/
theorem IsPauliNormalizer.exists_sign_conj_pauliString
    {U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ} (hU : IsPauliNormalizer U) (a : Fin n → Fin 4) :
    ∃ (b : Fin n → Fin 4) (z : ℂ), (z = 1 ∨ z = -1) ∧
      U * pauliString a * Uᴴ = z • pauliString b := by
  obtain ⟨hUmem, hUnorm⟩ := hU
  obtain ⟨q, hq⟩ := hUnorm ⟨0, a⟩
  have hpa : (⟨0, a⟩ : PauliGroup n).toMat = pauliString a := by simp [PauliGroup.toMat]
  rw [hpa] at hq
  refine ⟨q.idx, zmod4Pow q.phase, ?_, hq⟩
  -- unitarity of `U`, both handed
  have hUUH : U * Uᴴ = 1 := by simpa [star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hUmem
  have hUHU : Uᴴ * U = 1 := by simpa [star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hUmem
  -- `(U P_a U†)² = 1` because `P_a` is an involution and `U† U = 1`
  have hsq : (U * pauliString a * Uᴴ) * (U * pauliString a * Uᴴ) = 1 :=
    calc U * pauliString a * Uᴴ * (U * pauliString a * Uᴴ)
          = U * pauliString a * (Uᴴ * U) * pauliString a * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by
            rw [hUHU, Matrix.mul_one, Matrix.mul_assoc U (pauliString a) (pauliString a),
              pauliString_mul_self, Matrix.mul_one, hUUH]
  -- rewrite the square as `(iˢ)² • 1 = 1` and read off `(iˢ)² = 1`
  rw [hq] at hsq
  simp only [PauliGroup.toMat] at hsq
  rw [smul_mul_smul_comm, pauliString_mul_self] at hsq
  have hz2 : zmod4Pow q.phase * zmod4Pow q.phase = 1 := by
    have h00 := congrFun (congrFun hsq (fun _ => 0)) (fun _ => 0)
    simpa [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] using h00
  exact mul_self_eq_one_iff.mp hz2

/-- **A Pauli normalizer induces a `±1`-signed permutation of the Pauli-string indices.** For
`U ∈ N(Gₙ)` there are a permutation `σ` of the index set `Fin n → Fin 4` and a sign function `ε`
valued in `{1, -1}` with `U P_a U† = ε a • P_{σ a}` for every `a`. The per-index datum comes from
`exists_sign_conj_pauliString`; the induced map is *injective* — conjugating back by `U`
(`Uᴴ · U = 1`) expresses `P_a` and `P_{a'}` as the *same* operator scaled by `ε a`, `ε a'`, so
`P_a = ±P_{a'}`, and Hilbert–Schmidt orthogonality (`pauliString_trace_mul`) forces `a = a'` — hence
a bijection on the finite index set `Fin n → Fin 4` (`Finite.injective_iff_bijective`). This is the
combinatorial object that Nielsen & Chuang Exercise 10.40 synthesises by a Clifford circuit: a
signed permutation of the `4ⁿ` Pauli strings. -/
theorem IsPauliNormalizer.exists_signedPerm
    {U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ} (hU : IsPauliNormalizer U) :
    ∃ (σ : Equiv.Perm (Fin n → Fin 4)) (ε : (Fin n → Fin 4) → ℂ),
      (∀ a, ε a = 1 ∨ ε a = -1) ∧ ∀ a, U * pauliString a * Uᴴ = ε a • pauliString (σ a) := by
  have hUmem : U ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ := hU.1
  choose f ε hcond using hU.exists_sign_conj_pauliString
  have hε : ∀ a, ε a = 1 ∨ ε a = -1 := fun a => (hcond a).1
  have hconj : ∀ a, U * pauliString a * Uᴴ = ε a • pauliString (f a) := fun a => (hcond a).2
  have hUHU : Uᴴ * U = 1 := by simpa [star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hUmem
  -- conjugating back by `U` recovers a matrix from its `U`-conjugate
  have hback : ∀ M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ, Uᴴ * (U * M * Uᴴ) * U = M := by
    intro M
    calc Uᴴ * (U * M * Uᴴ) * U = (Uᴴ * U) * M * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hUHU, Matrix.one_mul, Matrix.mul_one]
  have hinj : Function.Injective f := by
    intro a a' hff
    have ha : pauliString a = ε a • (Uᴴ * pauliString (f a) * U) := by
      have hb := hback (pauliString a)
      rw [hconj a, mul_smul_comm, smul_mul_assoc] at hb
      exact hb.symm
    have ha' : pauliString a' = ε a' • (Uᴴ * pauliString (f a) * U) := by
      have hb := hback (pauliString a')
      rw [hconj a', ← hff, mul_smul_comm, smul_mul_assoc] at hb
      exact hb.symm
    have hεsq : ε a' * ε a' = 1 := by rcases hε a' with h | h <;> rw [h] <;> ring
    have hcoef : ε a * ε a' * ε a' = ε a := by rw [mul_assoc, hεsq, mul_one]
    have hrel : pauliString a = (ε a * ε a') • pauliString a' := by
      rw [ha, ha', smul_smul, hcoef]
    by_contra hne
    have t1 : (pauliString a * pauliString a).trace = (2 : ℂ) ^ n := by
      rw [pauliString_trace_mul, ite_eq_left rfl]
    have t2 : (pauliString a * pauliString a').trace = 0 := by
      rw [pauliString_trace_mul, ite_eq_right hne]
    have hcong := congrArg (fun M => (pauliString a * M).trace) hrel
    rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul, t1, t2, mul_zero] at hcong
    exact absurd hcong (pow_ne_zero n (by norm_num))
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ε, hε, fun a => hconj a⟩

/-- **The converse of Theorem 10.6 reduces to Clifford synthesis.** If a unitary `U` conjugates the
Pauli strings exactly as a Clifford circuit `C` does — `U P_g U† = C.sign g • P_{C.act g}` for all
`g`, i.e. `U` realises `C`'s signed permutation — then `U` equals `C` up to a unit global phase:
`∃ c, ‖c‖ = 1 ∧ U = c • C.toMatrix`. Immediate from the uniqueness reduction
`unitary_eq_smul_of_conj_pauliString_eq` once `C`'s conjugation is folded back through
`CliffordCircuit.conj_pauliString`. Combined with `IsPauliNormalizer.exists_signedPerm`, it turns
the converse of Theorem 10.6 into a purely combinatorial task: *synthesise a Clifford circuit whose
signed permutation matches the normalizer's* — the content of Nielsen & Chuang Exercise 10.40. -/
theorem unitary_eq_smul_cliffordCircuit_of_conj_eq
    {U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ) (C : CliffordCircuit n)
    (h : ∀ g, U * pauliString g * Uᴴ
        = CliffordCircuit.sign C g • pauliString (CliffordCircuit.act C g)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ U = c • CliffordCircuit.toMatrix C := by
  refine unitary_eq_smul_of_conj_pauliString_eq hU ?_ (fun g => ?_)
  · rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
    exact CliffordCircuit.mul_conjTranspose C
  · rw [h g, ← CliffordCircuit.conj_pauliString C g]

/-! ### Multiplicativity of conjugation by an isometry -/

/-- **Conjugation by an isometry is multiplicative.** If `Mᴴ * M = 1`, then
`(M * P * Mᴴ) * (M * Q * Mᴴ) = M * (P * Q) * Mᴴ`: the middle `Mᴴ * M` collapses to `1`. This is the
homomorphism property behind a Pauli normalizer's conjugation action — reused wherever a synthesised
circuit's `Y`-image is forced by its `X`- and `Z`-images (Exercise 10.40). -/
theorem conj_mul_conj_of_conjTranspose_mul_self
    {N : Type*} [Fintype N] [DecidableEq N] {M : Matrix N N ℂ} (hM : Mᴴ * M = 1)
    (P Q : Matrix N N ℂ) :
    (M * P * Mᴴ) * (M * Q * Mᴴ) = M * (P * Q) * Mᴴ := by
  calc (M * P * Mᴴ) * (M * Q * Mᴴ)
        = M * P * (Mᴴ * M) * Q * Mᴴ := by simp only [Matrix.mul_assoc]
    _ = M * (P * Q) * Mᴴ := by rw [hM, Matrix.mul_one]; simp only [Matrix.mul_assoc]

/-! ### Single-qubit case: `X` and `Z` determine the conjugation action (Exercise 10.40 part 1) -/

/-- **On a single qubit, `Y = i · X Z`**: `pauliString (fun _ => 2) = i • (pauliString (fun _ => 1)
· pauliString (fun _ => 3))`. From the Pauli-string product law `pauliString_mul_eq_smul` the single
factor is `P_X P_Z = (-i) • P_Y` (`pauliMulPhase 1 3 = -i`, product index `pauliMul 1 3 = 2`), and
`i · (-i) = 1`. This writes the third single-qubit Pauli through the two generators `X, Z`, so a
conjugation action is fixed by its values on `X` and `Z` alone. -/
theorem pauliString_two_eq_smul_mul :
    pauliString (fun _ : Fin 1 => (2 : Fin 4))
      = Complex.I • (pauliString (fun _ : Fin 1 => (1 : Fin 4)) * pauliString (fun _ => 3)) := by
  rw [pauliString_mul_eq_smul, smul_smul]
  have hidx : pauliMulIndex (fun _ : Fin 1 => (1 : Fin 4)) (fun _ => 3) = fun _ => 2 := by
    funext k; fin_cases k; rfl
  rw [hidx]
  have hph : Complex.I * ∏ k : Fin 1, pauliMulPhase ((fun _ : Fin 1 => (1 : Fin 4)) k)
        ((fun _ : Fin 1 => (3 : Fin 4)) k) = 1 := by
    simp [pauliMulPhase, Complex.I_mul_I]
  rw [hph, one_smul]

/-- **A single-qubit unitary is determined, up to a global phase, by how it conjugates `X` and
`Z`.** If two unitaries `U, V` on one qubit agree on conjugating the Pauli `X` (`P_{fun _ => 1}`)
and the Pauli `Z` (`P_{fun _ => 3}`), then `U = c • V` for a unit scalar `c` (`‖c‖ = 1`). The
generators `X, Z` fix the whole conjugation action: `I ↦ I` (unitarity) and `Y = i X Z ↦
i (U X U†)(U Z U†)` by multiplicativity of conjugation (`Uᴴ U = 1` cancels in the middle,
`pauliString_two_eq_smul_mul`), so agreement on `X, Z` forces agreement on every single-qubit Pauli;
`unitary_eq_smul_of_conj_pauliString_eq` then concludes. This reduces the single-qubit case of
Nielsen & Chuang Theorem 10.6 (Exercise 10.40 part 1) from *matching the full signed permutation* to
*matching the images of `X` and `Z`* — the two generators an `H/S`-word Clifford synthesis must
hit. -/
theorem unitary_eq_smul_of_conj_singleQubit_XZ
    {U V : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 1 → Fin 2) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin 1 → Fin 2) ℂ)
    (hX : U * pauliString (fun _ => 1) * Uᴴ = V * pauliString (fun _ => 1) * Vᴴ)
    (hZ : U * pauliString (fun _ => 3) * Uᴴ = V * pauliString (fun _ => 3) * Vᴴ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ U = c • V := by
  have hUUH : U * Uᴴ = 1 := by simpa [star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hU
  have hVVH : V * Vᴴ = 1 := by simpa [star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hV
  have hUHU : Uᴴ * U = 1 := by simpa [star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hU
  have hVHV : Vᴴ * V = 1 := by simpa [star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hV
  refine unitary_eq_smul_of_conj_pauliString_eq hU hV (fun g => ?_)
  obtain ⟨a, rfl⟩ : ∃ a : Fin 4, g = fun _ => a := ⟨g 0, by funext i; fin_cases i; rfl⟩
  fin_cases a
  · -- `a = 0` : the identity Pauli, both conjugates equal `1`
    change U * pauliString (fun _ : Fin 1 => (0 : Fin 4)) * Uᴴ
      = V * pauliString (fun _ : Fin 1 => (0 : Fin 4)) * Vᴴ
    rw [pauliString_const_zero, Matrix.mul_one, Matrix.mul_one, hUUH, hVVH]
  · -- `a = 1` : `X`
    exact hX
  · -- `a = 2` : `Y`, through `Y = i X Z` and multiplicativity
    change U * pauliString (fun _ : Fin 1 => (2 : Fin 4)) * Uᴴ
      = V * pauliString (fun _ : Fin 1 => (2 : Fin 4)) * Vᴴ
    rw [pauliString_two_eq_smul_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
    refine congrArg (_ • ·) ?_
    rw [← conj_mul_conj_of_conjTranspose_mul_self hUHU,
      ← conj_mul_conj_of_conjTranspose_mul_self hVHV, hX, hZ]
  · -- `a = 3` : `Z`
    exact hZ

/-! ### Single-qubit synthesis: `H`/`S` generate the normalizer up to phase (Exercise 10.40 part 1)

The base case of the converse of Theorem 10.6. A single-qubit normalizer `U` induces a `±1`-signed
permutation of the four Pauli-string indices `{I, X, Y, Z}` (`exists_signedPerm`); it fixes `I`, so
it sends `X` and `Z` to a *distinct* pair of non-identity strings with `±1` signs. By the
`X, Z`-determinacy reduction `unitary_eq_smul_of_conj_singleQubit_XZ` it suffices to realise those
two images by a Clifford circuit — and the single-qubit `H`, `S` gates already do: their phase-free
action is a transposition of the index set (`H : X ↔ Z`, `S : X ↔ Y`), so their words realise every
permutation of `{X, Y, Z}` (`⟨(X Z), (X Y)⟩ = S₃`, `exists_cliffordCircuit_singleQubit_act`), and
the trivial-action Pauli-conjugation words (`Z = S²`, `X = H S² H`, `Y = X · Z`) realise every
`±1` sign pattern on `X, Z` (`exists_cliffordCircuit_singleQubit_signFix`). Gluing a permutation
word to a sign-fix word (`act_append` / `sign_append`) hits an arbitrary valid `(X, Z)` image, and
the determinacy reduction upgrades that to `U = c • C.toMatrix` for an `H`/`S`-word `C`, `‖c‖ = 1`
— Theorem 10.6 for `n = 1`. (The `n + 1` inductive step and the `O(n²)` gate count are the remaining
parts of Exercise 10.40.) -/

/-- **A unitary conjugates a non-identity Pauli string to a non-identity one.** If `U` is an
isometry (`Uᴴ U = 1`) and `U P_a U† = z • P_b` with `z ≠ 0` and `a` not the all-identity index
(`a ≠ 0`), then the image index is non-identity too (`b ≠ 0`). Trace argument: an isometry preserves
the trace, so `tr (U P_a U†) = tr P_a = 0` because a non-identity Pauli string is traceless
(`pauliString_trace`); but were `b = 0`, then `tr (z • P_b) = z · 2ⁿ ≠ 0`. This is what forces a
single-qubit normalizer to send `X` and `Z` to genuine (non-identity) Pauli strings. -/
theorem conj_pauliString_index_ne_zero
    {U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ} (hUHU : Uᴴ * U = 1)
    {a b : Fin n → Fin 4} {z : ℂ}
    (h : U * pauliString a * Uᴴ = z • pauliString b) (hz : z ≠ 0) (ha : a ≠ 0) : b ≠ 0 := by
  intro hb
  have e1 : (U * pauliString a * Uᴴ).trace = 0 := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUHU, Matrix.one_mul, pauliString_trace,
      ite_eq_right ha]
  have e2 : (U * pauliString a * Uᴴ).trace = z * 2 ^ n := by
    rw [h, Matrix.trace_smul, hb, pauliString_trace, ite_eq_left rfl, smul_eq_mul]
  rw [e1] at e2
  exact mul_ne_zero hz (pow_ne_zero n two_ne_zero) e2.symm

/-- **`H` and `S` realise every permutation of the single-qubit Pauli indices.** For distinct
non-identity targets `aX, aZ` (i.e. `aX, aZ ∈ {X, Y, Z}`, `aX ≠ aZ`), there is an `H`/`S` Clifford
circuit `p` whose phase-free action sends `X ↦ aX` and `Z ↦ aZ`. Since `H`'s action is the
transposition `X ↔ Z` and `S`'s is `X ↔ Y`, their words generate all of `S₃` on `{X, Y, Z}`; the six
permutations are the six explicit words below (`[]`, `[H]`, `[S]`, `[H,S,H]`, `[H,S]`, `[S,H]`),
selected by `fin_cases` and verified by `decide` on the computable action, the invalid index
combinations being ruled out by the distinctness/non-identity hypotheses. -/
theorem exists_cliffordCircuit_singleQubit_act {aX aZ : Fin 4}
    (h0X : aX ≠ 0) (h0Z : aZ ≠ 0) (hne : aX ≠ aZ) :
    ∃ p : CliffordCircuit 1, CliffordCircuit.act p (fun _ => 1) = (fun _ => aX) ∧
      CliffordCircuit.act p (fun _ => 3) = (fun _ => aZ) := by
  fin_cases aX <;> fin_cases aZ <;>
    first
      | exact absurd rfl h0X
      | exact absurd rfl h0Z
      | exact absurd rfl hne
      | exact ⟨[], by decide, by decide⟩
      | exact ⟨[.had 0], by decide, by decide⟩
      | exact ⟨[.phase 0], by decide, by decide⟩
      | exact ⟨[.had 0, .phase 0, .had 0], by decide, by decide⟩
      | exact ⟨[.had 0, .phase 0], by decide, by decide⟩
      | exact ⟨[.phase 0, .had 0], by decide, by decide⟩

/-- **Every `±1` sign pattern on `X, Z` is realised by a trivial-action `H`/`S` word.** For target
signs `sX, sZ ∈ {1, -1}` there is a Clifford circuit `f` that fixes the `X` and `Z` indices under
conjugation (`f.act X = X`, `f.act Z = Z`) with `f.sign X = sX`, `f.sign Z = sZ`. These are the
Pauli-conjugation words: `[]` (no flip); `X = H S² H` conjugation flips the sign of `Z` only;
`Z = S²` conjugation flips `X` only; and their composite `Y`-type word flips both. The four cases
are verified by `decide` (action) and `simp` (the `±1` sign, a product of the per-gate phases). -/
theorem exists_cliffordCircuit_singleQubit_signFix {sX sZ : ℂ}
    (hsX : sX = 1 ∨ sX = -1) (hsZ : sZ = 1 ∨ sZ = -1) :
    ∃ f : CliffordCircuit 1, CliffordCircuit.act f (fun _ => 1) = (fun _ => 1) ∧
      CliffordCircuit.act f (fun _ => 3) = (fun _ => 3) ∧
      CliffordCircuit.sign f (fun _ => 1) = sX ∧ CliffordCircuit.sign f (fun _ => 3) = sZ := by
  rcases hsX with rfl | rfl <;> rcases hsZ with rfl | rfl
  · exact ⟨[], by decide, by decide, by simp [CliffordCircuit.sign], by simp [CliffordCircuit.sign]⟩
  · exact ⟨[.had 0, .phase 0, .phase 0, .had 0], by decide, by decide,
      by simp [CliffordCircuit.sign, CliffordCircuit.act, CliffordGate.sign, CliffordGate.act,
        hadamardPauli, hadamardPauliSign, phasePauli, phasePauliSign, Function.update],
      by simp [CliffordCircuit.sign, CliffordCircuit.act, CliffordGate.sign, CliffordGate.act,
        hadamardPauli, hadamardPauliSign, phasePauli, phasePauliSign, Function.update]⟩
  · exact ⟨[.phase 0, .phase 0], by decide, by decide,
      by simp [CliffordCircuit.sign, CliffordCircuit.act, CliffordGate.sign, CliffordGate.act,
        phasePauli, phasePauliSign, Function.update],
      by simp [CliffordCircuit.sign, CliffordCircuit.act, CliffordGate.sign, CliffordGate.act,
        phasePauli, phasePauliSign, Function.update]⟩
  · exact ⟨[.had 0, .phase 0, .phase 0, .had 0, .phase 0, .phase 0], by decide, by decide,
      by simp [CliffordCircuit.sign, CliffordCircuit.act, CliffordGate.sign, CliffordGate.act,
        hadamardPauli, hadamardPauliSign, phasePauli, phasePauliSign, Function.update],
      by simp [CliffordCircuit.sign, CliffordCircuit.act, CliffordGate.sign, CliffordGate.act,
        hadamardPauli, hadamardPauliSign, phasePauli, phasePauliSign, Function.update]⟩

/-- **Single-qubit synthesis (the combinatorial core of Exercise 10.40 part 1).** For any valid
single-qubit signed permutation — distinct non-identity targets `aX, aZ` and signs `zX, zZ` in
`{1, -1}` — there is an `H`/`S` Clifford circuit `C` realising it exactly: `C.act X = aX`,
`C.act Z = aZ`,
`C.sign X = zX`, `C.sign Z = zZ`. Take a permutation word `p` hitting the target *indices*
(`exists_cliffordCircuit_singleQubit_act`); its `X, Z` signs are some `pX, pZ ∈ {±1}`
(`CliffordCircuit.sign_eq_one_or_neg_one`). Append a sign-fix word `f` for the signs `zX · pX`,
`zZ · pZ` (`exists_cliffordCircuit_singleQubit_signFix`): since `f` fixes the indices,
`(p ++ f).act = p.act` (`act_append`) and `(p ++ f).sign X = f.sign X · p.sign X = (zX · pX) · pX =
zX` (`sign_append`, using `pX² = 1`). All 24 valid signed permutations are covered, matching the
order of the single-qubit Clifford group modulo global phase. -/
theorem exists_cliffordCircuit_singleQubit_act_sign {aX aZ : Fin 4} {zX zZ : ℂ}
    (h0X : aX ≠ 0) (h0Z : aZ ≠ 0) (hne : aX ≠ aZ)
    (hzX : zX = 1 ∨ zX = -1) (hzZ : zZ = 1 ∨ zZ = -1) :
    ∃ C : CliffordCircuit 1,
      CliffordCircuit.act C (fun _ => 1) = (fun _ => aX) ∧
        CliffordCircuit.sign C (fun _ => 1) = zX ∧
      CliffordCircuit.act C (fun _ => 3) = (fun _ => aZ) ∧
        CliffordCircuit.sign C (fun _ => 3) = zZ := by
  obtain ⟨p, hpX, hpZ⟩ := exists_cliffordCircuit_singleQubit_act h0X h0Z hne
  have hpXpm := CliffordCircuit.sign_eq_one_or_neg_one p (fun _ => 1)
  have hpZpm := CliffordCircuit.sign_eq_one_or_neg_one p (fun _ => 3)
  obtain ⟨f, hfaX, hfaZ, hfsX, hfsZ⟩ :=
    exists_cliffordCircuit_singleQubit_signFix (sX := zX * CliffordCircuit.sign p (fun _ => 1))
      (sZ := zZ * CliffordCircuit.sign p (fun _ => 3))
      (by rcases hzX with h | h <;> rcases hpXpm with h' | h' <;> rw [h, h'] <;> norm_num)
      (by rcases hzZ with h | h <;> rcases hpZpm with h' | h' <;> rw [h, h'] <;> norm_num)
  refine ⟨p ++ f, ?_, ?_, ?_, ?_⟩
  · rw [CliffordCircuit.act_append, hfaX, hpX]
  · rw [CliffordCircuit.sign_append, hfaX, hfsX]; rcases hpXpm with h | h <;> rw [h] <;> ring
  · rw [CliffordCircuit.act_append, hfaZ, hpZ]
  · rw [CliffordCircuit.sign_append, hfaZ, hfsZ]; rcases hpZpm with h | h <;> rw [h] <;> ring

/-- **Nielsen & Chuang Theorem 10.6 for a single qubit.** Every single-qubit Pauli normalizer `U`
equals a global phase times an `H`/`S` Clifford circuit: `∃ C, c, ‖c‖ = 1 ∧ U = c • C.toMatrix`.
`U`'s conjugation action is a `±1`-signed permutation of the Pauli indices (`exists_signedPerm`)
that fixes the identity; its `X` and `Z` images are therefore distinct non-identity Pauli strings
(`conj_pauliString_index_ne_zero` for non-identity, `σ` injective for distinctness) carrying `±1`
signs. Synthesise a Clifford circuit `C` realising exactly those images
(`exists_cliffordCircuit_singleQubit_act_sign`); then `U` and `C.toMatrix` conjugate `X` and `Z`
identically, so `unitary_eq_smul_of_conj_singleQubit_XZ` gives `U = c • C.toMatrix` with `‖c‖ = 1`.
This is the base case (`n = 1`) of the converse of Theorem 10.6; the `n + 1` inductive step and the
`O(n²)` gate-count bound (the rest of Exercise 10.40) remain. -/
theorem isPauliNormalizer_singleQubit_eq_smul_cliffordCircuit
    {U : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ} (hU : IsPauliNormalizer U) :
    ∃ (C : CliffordCircuit 1) (c : ℂ), ‖c‖ = 1 ∧ U = c • CliffordCircuit.toMatrix C := by
  obtain ⟨σ, ε, hε, hconj⟩ := hU.exists_signedPerm
  have hUmem : U ∈ Matrix.unitaryGroup (Fin 1 → Fin 2) ℂ := hU.1
  have hUHU : Uᴴ * U = 1 := by
    simpa [star_eq_conjTranspose] using (mem_unitaryGroup_iff').mp hUmem
  have hzX0 : ε (fun _ => 1) ≠ 0 := by rcases hε (fun _ => 1) with h | h <;> rw [h] <;> norm_num
  have hzZ0 : ε (fun _ => 3) ≠ 0 := by rcases hε (fun _ => 3) with h | h <;> rw [h] <;> norm_num
  have hbX0 : σ (fun _ => 1) ≠ 0 :=
    conj_pauliString_index_ne_zero hUHU (hconj (fun _ => 1)) hzX0 (by decide)
  have hbZ0 : σ (fun _ => 3) ≠ 0 :=
    conj_pauliString_index_ne_zero hUHU (hconj (fun _ => 3)) hzZ0 (by decide)
  obtain ⟨aX, haX⟩ : ∃ a, σ (fun _ => 1) = fun _ => a :=
    ⟨σ (fun _ => 1) 0, by funext i; fin_cases i; rfl⟩
  obtain ⟨aZ, haZ⟩ : ∃ a, σ (fun _ => 3) = fun _ => a :=
    ⟨σ (fun _ => 3) 0, by funext i; fin_cases i; rfl⟩
  have h0X : aX ≠ 0 := by intro h; exact hbX0 (by rw [haX, h]; rfl)
  have h0Z : aZ ≠ 0 := by intro h; exact hbZ0 (by rw [haZ, h]; rfl)
  have hbne : σ (fun _ => 1) ≠ σ (fun _ => 3) := fun h =>
    (by decide : (fun _ : Fin 1 => (1 : Fin 4)) ≠ fun _ => 3) (σ.injective h)
  have hne : aX ≠ aZ := by intro h; exact hbne (by rw [haX, haZ, h])
  obtain ⟨C, hCaX, hCsX, hCaZ, hCsZ⟩ :=
    exists_cliffordCircuit_singleQubit_act_sign h0X h0Z hne (hε (fun _ => 1)) (hε (fun _ => 3))
  have hCmem : CliffordCircuit.toMatrix C ∈ Matrix.unitaryGroup (Fin 1 → Fin 2) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose]; exact CliffordCircuit.mul_conjTranspose C
  have hXeq : U * pauliString (fun _ => 1) * Uᴴ
      = CliffordCircuit.toMatrix C * pauliString (fun _ => 1) * (CliffordCircuit.toMatrix C)ᴴ := by
    rw [hconj (fun _ => 1), CliffordCircuit.conj_pauliString, hCsX, hCaX, haX]
  have hZeq : U * pauliString (fun _ => 3) * Uᴴ
      = CliffordCircuit.toMatrix C * pauliString (fun _ => 3) * (CliffordCircuit.toMatrix C)ᴴ := by
    rw [hconj (fun _ => 3), CliffordCircuit.conj_pauliString, hCsZ, hCaZ, haZ]
  obtain ⟨c, hc, hUc⟩ := unitary_eq_smul_of_conj_singleQubit_XZ hUmem hCmem hXeq hZeq
  exact ⟨C, c, hc, hUc⟩

/-! ### A normalizer preserves the commutation (symplectic) structure of the Pauli strings

The structural invariant driving the multi-qubit inductive synthesis (Nielsen & Chuang Exercise
10.40 parts 2–3): conjugation by a unitary is a `*`-algebra automorphism, hence preserves
commutation and anticommutation. A Pauli normalizer therefore acts on the Pauli strings by a
transformation that respects the **binary symplectic form** (`pauliAnticommCount`, mod 2) of
Exercise 10.33 — its induced `±1`-signed permutation `σ` of the Pauli-string indices is a
*symplectic* permutation. In particular it sends anticommuting Pauli strings to anticommuting ones,
which is precisely how Nielsen & Chuang open part 2: "since `Z₁` and `X₁` anticommute, `U Z₁ U†` and
`U X₁ U†` anticommute". -/

/-- **Conjugation by a unitary preserves commutation.** For a unitary `U` and any matrices `P, Q`,
the conjugates `U P U†` and `U Q U†` commute iff `P` and `Q` do. Conjugation `M ↦ U M U†` is the
`*`-algebra automorphism `Unitary.conjStarAlgAut ℂ _ ⟨U, hU⟩` (a `StarAlgEquiv`, so a bijective
ring homomorphism), and commutation is transported along any multiplicative map both ways
(`Commute.map`, using the inverse `f.symm` for the reverse direction). This is the algebraic reason
a Pauli normalizer preserves the commutation structure of `Gₙ`. -/
theorem unitaryConj_commute_iff {N : Type*} [Fintype N] [DecidableEq N]
    {U : Matrix N N ℂ} (hU : U ∈ Matrix.unitaryGroup N ℂ) (P Q : Matrix N N ℂ) :
    Commute (U * P * Uᴴ) (U * Q * Uᴴ) ↔ Commute P Q := by
  set f := Unitary.conjStarAlgAut ℂ (Matrix N N ℂ) ⟨U, hU⟩ with hf_def
  have hf : ∀ M : Matrix N N ℂ, f M = U * M * Uᴴ := fun M => by
    rw [hf_def, Unitary.conjStarAlgAut_apply]
    simp only [star_eq_conjTranspose, Matrix.mul_assoc]
  rw [← hf P, ← hf Q]
  exact ⟨fun h => by simpa using h.map (f.symm : _ ≃⋆ₐ[ℂ] _), fun h => h.map f⟩

/-- **A Pauli normalizer's signed permutation preserves the binary symplectic form.** Strengthening
`exists_signedPerm`: for `U ∈ N(Gₙ)` the induced permutation `σ` of the Pauli-string indices
preserves the mod-2 symplectic pairing of Nielsen & Chuang Exercise 10.33 —
`Even (pauliAnticommCount (σ a) (σ b)) ↔ Even (pauliAnticommCount a b)` for all `a, b`. Conjugation
by `U` preserves commutation (`unitaryConj_commute_iff`), and `U P_a U† = ε a • P_{σ a}` with
`ε a ∈ {±1}` nonzero, so the ±1 scalars cancel and `P_{σ a}, P_{σ b}` commute iff `P_a, P_b` do; the
symplectic commutation criterion `pauliString_commute_iff` then translates this into the parity
statement. This is the *symplectic-transformation* structure of a normalizer's action — the
invariant that the inductive Clifford synthesis of Exercise 10.40 (parts 2–3) must reproduce, and
the reason a normalizer maps anticommuting generators to anticommuting Pauli strings. -/
theorem IsPauliNormalizer.exists_signedPerm_symplectic
    {U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ} (hU : IsPauliNormalizer U) :
    ∃ (σ : Equiv.Perm (Fin n → Fin 4)) (ε : (Fin n → Fin 4) → ℂ),
      (∀ a, ε a = 1 ∨ ε a = -1) ∧
      (∀ a, U * pauliString a * Uᴴ = ε a • pauliString (σ a)) ∧
      (∀ a b, Even (pauliAnticommCount (σ a) (σ b)) ↔ Even (pauliAnticommCount a b)) := by
  obtain ⟨σ, ε, hε, hconj⟩ := hU.exists_signedPerm
  refine ⟨σ, ε, hε, hconj, fun a b => ?_⟩
  have hne : ε a * ε b ≠ 0 :=
    mul_ne_zero (by rcases hε a with h | h <;> rw [h] <;> norm_num)
      (by rcases hε b with h | h <;> rw [h] <;> norm_num)
  -- conjugation by `U` preserves the commutation of `P_a, P_b`; the `±1` scalars cancel
  have hstep : Commute (U * pauliString a * Uᴴ) (U * pauliString b * Uᴴ)
      ↔ Commute (pauliString (σ a)) (pauliString (σ b)) := by
    rw [hconj a, hconj b]
    constructor
    · intro h
      have he := h.eq
      rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (ε b) (ε a)] at he
      exact smul_right_injective _ hne he
    · intro h
      exact (h.smul_left (ε a)).smul_right (ε b)
  have hcomm : Commute (pauliString (σ a)) (pauliString (σ b))
      ↔ Commute (pauliString a) (pauliString b) :=
    hstep.symm.trans (unitaryConj_commute_iff hU.1 (pauliString a) (pauliString b))
  rw [pauliString_commute_iff, pauliString_commute_iff] at hcomm
  exact hcomm

end AxQM.Concrete

end
