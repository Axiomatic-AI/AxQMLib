/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.LinearOpticalUniversality
import AxQM.Concrete.TwoLevelLowerBound
import AxQM.Postulates.API.QuditGate
import AxQM.Postulates.API.DeutschAlgorithm
import AxQM.Postulates.API.Reflection
import AxQM.Postulates.API.UniformSuperposition
import AxQM.Postulates.API.QuditTensorFactor

/-!
# N&C Problem 7.2 (Computing with linear optics) — universality and the exponential lower bound

Nielsen & Chuang, Problem 7.2 (p. 346). In single-photon quantum computation with the **unary**
mode representation, an `n`-qubit computational-basis state `|k⟩` is a single photon in mode `k` of
`d = 2ⁿ` optical modes, so the system is `qudit d` and an arbitrary `n`-qubit gate is a unitary
`Evolution (qudit d)` on the mode amplitudes. Part 1 asks to show that **any** such unitary can be
built completely from just two passive linear-optical elements — **beamsplitters** and **phase
shifters** — and no nonlinear media.

This file packages the two elements as `Evolution (qudit d)` gates, proves
that they suffice for **any** gate (Part 1), that in particular they build the one-qubit
Deutsch–Jozsa (Part 2) and two-qubit quantum-search (Part 3) circuits with **no nonlinear media**,
and that in general they are needed in **exponential** number (Part 4):

* `phaseShifterGate p φ` — the **phase shifter** on optical mode `p`, the gate whose operator is the
  phase-shifter matrix `Concrete.phaseMode p φ` (multiply the amplitude of mode `p` by `e^{iφ}`,
  fix the rest).
* `beamSplitterGate p q θ h` — the **beamsplitter** mixing modes `p ≠ q`, the gate whose operator is
  the beamsplitter matrix `Concrete.beamSplitter p q θ` (a real `2 × 2` rotation `R_y(θ)` on the
  amplitudes of modes `p, q`).
* `IsLinearOpticalGate V` — `V` is one of these two: a beamsplitter (on a genuine pair `p ≠ q`) or a
  phase shifter.
* `linearOptics_universal` — **Part 1**: for `d ≥ 2`, every unitary `Evolution (qudit d)` is the
  ordered composition (monoid product of a finite list) of linear-optical gates.
* `unaryEncoding` — the **unary encoding** of a two-qubit register: the system isomorphism
  `qubit ⊗ qubit ≃ₛ qudit 4` identifying a computational basis state `|k⟩` (`k = 0,1,2,3`) with a
  single photon in mode `k` of four optical modes. `deutschCircuitUnary Uf` is Deutsch's circuit,
  transported along it into the four-mode picture.
* `linearOptics_deutschJozsa` — **Part 2**: for every oracle `Uf`, the unary-encoded Deutsch–Jozsa
  circuit `deutschCircuitUnary Uf` is a beamsplitter/phase-shifter product — **no nonlinear media**.
* `searchOracleUnary` / `searchDiffusionUnary` / `twoQubitSearchStep` — the two-qubit quantum-search
  circuit in the unary encoding: the oracle `O_x = I − 2|x⟩⟨x|`, the inversion-about-the-mean
  diffusion, and the Grover iterate `G = D · O_x` (all `Evolution (qudit 4)`).
* `linearOptics_twoQubitSearch` — **Part 3**: for every marked mode `x`, the Grover iterate
  `twoQubitSearchStep x` is a beamsplitter/phase-shifter product — again **no nonlinear media**.
* `linearOptics_lower_bound` — **Part 4** (general form): for every `d`, *some* unitary
  `Evolution (qudit d)` needs at least `d − 1` linear-optical gates in any realization.
* `linearOptics_exponential_lower_bound` — **Part 4** (the `n`-qubit reading): on the physical
  `d = 2ⁿ`-mode system, some unitary needs at least `2ⁿ − 1` gates — **exponentially many in `n`**.

## Proof

The matrix-level content is already established in `Concrete/`: `Concrete`'s
`exists_linearOpticalList_prod_eq` says every `d × d` unitary matrix (`d ≥ 2`) is the product of a
list of linear-optical element matrices (via the §4.5.1 two-level decomposition and the Z–Y /
Reck–Zeilinger realization of each factor). The physics proof reads off the matrix `M` of the given
evolution `E` (`M = Matrix.toEuclideanCLM.symm E.op`, unitary because `E.op` is and
`Matrix.toEuclideanCLM` is a `⋆`-isomorphism), decomposes `M` with the `Concrete` result, and lifts
each linear-optical element matrix back to a gate via `quditGate`. Because `Evolution.op` is a
monoid morphism (`comp_op`, `id_op`) and `Matrix.toEuclideanCLM` is multiplicative
(`map_mul`, `map_one`), the operator of the lifted gate list equals
`Matrix.toEuclideanCLM M = E.op`, so the lifted list's product is `E` by `Evolution.ext`.

## Scope of Problem 7.2

The problem has four parts, all formalised here. Part 1 is the universality statement
(`linearOptics_universal`). Parts 2–3 ask for beamsplitter/phase-shifter circuits realizing the
one-qubit Deutsch–Jozsa and two-qubit quantum-search algorithms; the content N&C is after — and the
answer it expects — is precisely that **Part 1 hands you those circuits with no nonlinear media**.
We make that a *proved proposition* rather than prose: we name the actual DJ and Grover circuits as
unitaries on the four unary modes `qudit 4` (`deutschCircuitUnary`, built by transporting the
Deutsch circuit `deutschCircuit` along the unary encoding `unaryEncoding`; and
`twoQubitSearchStep`, the Grover iterate `D · O_x` built from the reflection
`reflectionEvolution`), and prove each a beamsplitter/phase-shifter product by instantiating Part 1.
So the DJ / search circuits
being *passive linear-optical networks* — the striking contrast with the dual-rail encoding of
Exercise 7.13, where the same algorithms need a nonlinear **Kerr** medium for the entangling gate —
is carried by a Lean statement. What Parts 2–3 do **not** demand, and what we do not manufacture, is
a *specific* beamsplitter angle sequence: N&C fixes no unique circuit, the decomposition is
non-unique, and its existence (the actual claim) is exactly `linearOptics_universal`. The
algorithms' *correctness* — that the DJ circuit reads off `f(0) ⊕ f(1)` and that one search
iteration finds the marked mode — is the separate §1.4 / §6.1 content, carried by
`IsDeutschOracle.deutschCircuit_bornProb` for the Deutsch circuit; Parts 2–3 concern only their
optical *realizability*, which is what these theorems establish. Part 4 (an arbitrary unitary
requires exponentially many components in `n`) is the complementary quantitative statement,
`linearOptics_lower_bound` /
`linearOptics_exponential_lower_bound` below.

The lower bound is proved *elementarily* from the §4.5.1 two-level structure: each beamsplitter /
phase-shifter matrix is a two-level unitary, and Exercise 4.38
(`Concrete.exists_unitary_two_level_decomposition_length_ge`) exhibits a `d × d` unitary — the
all-ones reflection — needing `≥ d − 1` two-level factors, hence `≥ d − 1 = 2ⁿ − 1` optical
components, which is exponential in `n`. This gives the exponential bound Problem 7.2 asks for. (A
parameter/dimension count against `dim U(d) = d²` would yield the sharper `Ω(d²) = Ω(4ⁿ)`, but needs
smooth-manifold–dimension machinery; the `d − 1` connectivity bound is already exponential in `n`
and suffices for the stated claim, so we take it. A lower bound proved from only the two-level
property is a fortiori a lower bound for genuine linear-optical gates.)

`linearOptics_universal` is stated for a general dimension `d ≥ 2`, which strictly subsumes the
physical case `d = 2ⁿ` (`n ≥ 1`) of the unary encoding, so no faithfulness is lost by the
generalization.

## Supporting results

The statements above involve only `Evolution`, `qudit`, `qubit`, the composite `⊗` and system
isomorphism `≃ₛ`, `Fin`, `ℝ`, `ℕ`, `List` and the predicate `IsLinearOpticalGate`. They build on
`quditGate`, the reflection `reflectionEvolution`, the uniform superposition
`uniformSuperposition`, the Deutsch circuit `deutschCircuit`, the tensor-factoring isomorphism
`quditProdIso` (in `AxQM/Postulates/API/`), and on the matrix-level lemmas in `AxQM/Concrete/`
(the two-level decomposition, and the Exercise 4.38 two-level lower bound
`exists_unitary_two_level_decomposition_length_ge`). The step that reads off each gate's
underlying matrix, via `Evolution.op` and `Matrix.toEuclideanCLM`, is done inside the lower-bound
proof.
-/

open AxQM.Concrete Matrix

noncomputable section

namespace AxQM

variable {d : ℕ}

/-! ### The two linear-optical gates -/

/-- **Phase shifter on optical mode `p`** as an `Evolution (qudit d)`: the gate whose operator is
the phase-shifter matrix `Concrete.phaseMode p φ = diag(…, e^{iφ}, …)`. It multiplies the amplitude
of
mode `p` by the phase `e^{iφ}` and fixes every other mode. -/
def phaseShifterGate (p : Fin d) (φ : ℝ) : Evolution (qudit d) :=
  quditGate (phaseMode_mem_unitaryGroup p φ)

/-- **Beamsplitter mixing optical modes `p ≠ q`** as an `Evolution (qudit d)`: the gate whose
operator is the beamsplitter matrix `Concrete.beamSplitter p q θ`, applying the real `2 × 2`
rotation `R_y(θ)` to the amplitudes of modes `p, q` and fixing the rest. -/
def beamSplitterGate (p q : Fin d) (θ : ℝ) (h : p ≠ q) : Evolution (qudit d) :=
  quditGate (beamSplitter_mem_unitaryGroup h θ)

/-- **A linear-optical gate** is a beamsplitter (on a genuine pair `p ≠ q`) or a phase shifter — the
two passive optical elements Problem 7.2 allows. -/
def IsLinearOpticalGate (V : Evolution (qudit d)) : Prop :=
  (∃ (p q : Fin d) (θ : ℝ) (h : p ≠ q), V = beamSplitterGate p q θ h) ∨
    (∃ (p : Fin d) (φ : ℝ), V = phaseShifterGate p φ)

/-- A beamsplitter gate is a linear-optical gate. -/
theorem isLinearOpticalGate_beamSplitterGate (p q : Fin d) (θ : ℝ) (h : p ≠ q) :
    IsLinearOpticalGate (beamSplitterGate p q θ h) :=
  Or.inl ⟨p, q, θ, h, rfl⟩

/-- A phase shifter gate is a linear-optical gate. -/
theorem isLinearOpticalGate_phaseShifterGate (p : Fin d) (φ : ℝ) :
    IsLinearOpticalGate (phaseShifterGate p φ) :=
  Or.inr ⟨p, φ, rfl⟩

/-! ### Universality (Problem 7.2, Part 1) -/

/-- **Universality of linear optics (Nielsen & Chuang, Problem 7.2, Part 1).** For `d ≥ 2`, every
unitary `Evolution (qudit d)` is a finite ordered composition of linear-optical gates: there is a
list `L` of `Evolution (qudit d)`, each of which `IsLinearOpticalGate` (a beamsplitter or a phase
shifter), whose monoid product `L.prod` equals `E`. Physically, on the unary-encoded single-photon
system (`d = 2ⁿ` modes) an arbitrary `n`-qubit unitary is realized entirely by beamsplitters and
phase shifters, with no nonlinear media.

The proof reads off the matrix `M` of `E`, decomposes it with the matrix-level universality
`Concrete.exists_linearOpticalList_prod_eq`, and lifts each linear-optical element matrix back to a
gate via `quditGate`; `Evolution.op` being a monoid morphism and `Matrix.toEuclideanCLM` being
multiplicative make the lifted list's product operator equal `E.op`, so it equals `E`. -/
theorem linearOptics_universal (hd : 2 ≤ d) (E : Evolution (qudit d)) :
    ∃ L : List (Evolution (qudit d)), (∀ V ∈ L, IsLinearOpticalGate V) ∧ L.prod = E := by
  -- The matrix of `E`, obtained by inverting the `⋆`-isomorphism `Matrix.toEuclideanCLM`.
  set M : Matrix (Fin d) (Fin d) ℂ := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)).symm E.op
    with hM_def
  have hEop : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) M = E.op := by
    rw [hM_def]; exact StarAlgEquiv.apply_symm_apply _ _
  have hMU : M ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)).symm E.unitary
  obtain ⟨L, hL, hLprod⟩ := exists_linearOpticalList_prod_eq hd hMU
  -- Lift a list of linear-optical element matrices to a list of gates with the same operator
  -- product. Induction on the list keeps the per-element unitarity proof local.
  have bridge : ∀ (K : List (Matrix (Fin d) (Fin d) ℂ)), (∀ V ∈ K, IsLinearOpticalElement V) →
      ∃ K' : List (Evolution (qudit d)), (∀ W ∈ K', IsLinearOpticalGate W) ∧
        K'.prod.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) K.prod := by
    intro K
    induction K with
    | nil =>
      intro _
      refine ⟨[], by simp, ?_⟩
      rw [List.prod_nil, Evolution.one_def, Evolution.id_op, List.prod_nil, map_one]
      rfl
    | cons N rest ih =>
      intro hK
      -- turn the head element matrix into the corresponding gate
      obtain ⟨g, hg_lo, hg_op⟩ : ∃ g : Evolution (qudit d), IsLinearOpticalGate g ∧
          g.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) N := by
        rcases hK N (by simp) with ⟨p, q, θ, hpq, rfl⟩ | ⟨p, φ, rfl⟩
        · exact ⟨beamSplitterGate p q θ hpq, isLinearOpticalGate_beamSplitterGate p q θ hpq, rfl⟩
        · exact ⟨phaseShifterGate p φ, isLinearOpticalGate_phaseShifterGate p φ, rfl⟩
      obtain ⟨K', hK', hK'op⟩ := ih (fun V hV => hK V (List.mem_cons_of_mem _ hV))
      refine ⟨g :: K', ?_, ?_⟩
      · intro W hW
        rcases List.mem_cons.mp hW with rfl | hW
        · exact hg_lo
        · exact hK' W hW
      · rw [List.prod_cons, Evolution.mul_def, Evolution.comp_op, hg_op, hK'op, List.prod_cons,
          map_mul]
        rfl
  obtain ⟨L', hL', hL'op⟩ := bridge L hL
  refine ⟨L', hL', Evolution.ext ?_⟩
  rw [hL'op, hLprod, hEop]

/-! ### Deutsch–Jozsa in the unary encoding (Problem 7.2, Part 2) -/

/-- **The unary encoding of a two-qubit register.** The system isomorphism
`qubit ⊗ qubit ≃ₛ qudit 4` identifying the two-qubit computational basis state `|k⟩`
(`k ∈ {0,1,2,3}`) with a single photon in mode `k` of four optical modes — Problem 7.2's unary
representation for `n = 2` (`|01⟩ = 0`, `|10⟩ = 1`, …). It is `quditProdIso 2 2` reversed
(`qubit = qudit 2` definitionally and `2 · 2 = 4`), i.e. the computational-basis identification
`|x⟩ ⊗ |y⟩ ↦ |2x + y⟩`. -/
def unaryEncoding : (qubit ⊗ qubit) ≃ₛ qudit 4 := (quditProdIso 2 2).symm

/-- **Deutsch's circuit in the unary encoding.** Deutsch's circuit `(H ⊗ I) · U_f · (H ⊗ H)`
(`deutschCircuit Uf`, the reviewed §1.4 engine) transported along the unary encoding `unaryEncoding`
into the four-mode picture, as an `Evolution (qudit 4)`. This is "the one-qubit Deutsch–Jozsa
algorithm" of Problem 7.2 Part 2 expressed on the unary optical modes; the transport is a relabeling
of the register, so it runs the identical computation (its measured outcome is the reviewed engine's
`IsDeutschOracle.deutschCircuit_bornProb`, transported through `unaryEncoding`). -/
def deutschCircuitUnary (Uf : Evolution (qubit ⊗ qubit)) : Evolution (qudit 4) :=
  Evolution.congr unaryEncoding (deutschCircuit Uf)

/-- **Optical realization of the Deutsch–Jozsa circuit (Nielsen & Chuang, Problem 7.2, Part 2).**
For *every* oracle `Uf`, the unary-encoded Deutsch–Jozsa circuit `deutschCircuitUnary Uf` is a
finite beamsplitter/phase-shifter product: a list `L` of linear-optical gates (each
`IsLinearOpticalGate`) whose monoid product is `deutschCircuitUnary Uf`. So the one-qubit
Deutsch–Jozsa algorithm — including its oracle, whatever it is — is realized in the unary encoding
by beamsplitters and phase
shifters alone, **with no nonlinear media** (contrast Exercise 7.13, where the dual-rail encoding
needs a Kerr medium for the entangling gate). This is the instance of the universality theorem
`linearOptics_universal` at the particular unitary `deutschCircuitUnary Uf` on `qudit 4` — exactly
N&C's intended construction for Part 2: Part 1's universality *is* the circuit. -/
theorem linearOptics_deutschJozsa (Uf : Evolution (qubit ⊗ qubit)) :
    ∃ L : List (Evolution (qudit 4)), (∀ V ∈ L, IsLinearOpticalGate V) ∧
      L.prod = deutschCircuitUnary Uf :=
  linearOptics_universal (by norm_num) (deutschCircuitUnary Uf)

/-! ### Two-qubit quantum search in the unary encoding (Problem 7.2, Part 3) -/

/-- **The two-qubit search oracle in the unary encoding.** For a marked mode `x : Fin 4`, the oracle
`O_x = I − 2|x⟩⟨x|` (Nielsen & Chuang §6.1.1) that flips the phase of the marked computational basis
state `|x⟩` and fixes the others, as an `Evolution (qudit 4)` — the reflection `reflectionEvolution`
about `|x⟩`. -/
def searchOracleUnary (x : Fin 4) : Evolution (qudit 4) := reflectionEvolution (quditBasis x)

/-- **The inversion-about-the-mean diffusion in the unary encoding.** The reflection about the
uniform superposition `|ψ⟩ = ½ ∑ₖ |k⟩` of the four modes (Nielsen & Chuang eq. 6.6), as an
`Evolution (qudit 4)`. `reflectionEvolution` gives `I − 2|ψ⟩⟨ψ|`, which is N&C's `2|ψ⟩⟨ψ| − I` up to
the physically irrelevant global phase `−1` — the same reflection of the two-dimensional Grover
plane spanned by `|ψ⟩` and the marked state. -/
def searchDiffusionUnary : Evolution (qudit 4) := reflectionEvolution (uniformSuperposition 4)

/-- **One Grover iteration of the two-qubit search algorithm, in the unary encoding.** The Grover
iterate `G = D · O_x` (Nielsen & Chuang §6.1.2): the search oracle `searchOracleUnary x` followed by
the inversion-about-the-mean diffusion `searchDiffusionUnary`, as an `Evolution (qudit 4)`. For a
two-qubit (`N = 4`) search a single iteration rotates the uniform superposition onto the marked
mode; this is the active step of "the two-qubit quantum search algorithm" of Problem 7.2 Part 3. -/
def twoQubitSearchStep (x : Fin 4) : Evolution (qudit 4) :=
  searchDiffusionUnary.comp (searchOracleUnary x)

/-- **Optical realization of the two-qubit quantum-search circuit (Nielsen & Chuang, Problem 7.2,
Part 3).** For *every* marked mode `x`, the Grover iterate `twoQubitSearchStep x` is a finite
beamsplitter/phase-shifter product: a list `L` of linear-optical gates (each `IsLinearOpticalGate`)
whose monoid product is `twoQubitSearchStep x`. So the two-qubit quantum-search algorithm — oracle
*and* diffusion — is realized in the unary encoding by beamsplitters and phase shifters alone,
**with no nonlinear media**. Like Part 2 it is the instance of `linearOptics_universal` at the
particular unitary `twoQubitSearchStep x` on `qudit 4`. (The uniform-superposition state preparation
`H^{⊗2}` preceding the iterate is likewise a unitary on `qudit 4`, hence also a
beamsplitter/phase-shifter product by Part 1.) -/
theorem linearOptics_twoQubitSearch (x : Fin 4) :
    ∃ L : List (Evolution (qudit 4)), (∀ V ∈ L, IsLinearOpticalGate V) ∧
      L.prod = twoQubitSearchStep x :=
  linearOptics_universal (by norm_num) (twoQubitSearchStep x)

/-! ### Exponential lower bound (Problem 7.2, Part 4) -/

/-- **Exponential component lower bound (Nielsen & Chuang, Problem 7.2, Part 4), general form.** For
every dimension `d`, there is a unitary `Evolution (qudit d)` that *no* short list of linear-optical
gates realizes: some `E` such that every list `L` of linear-optical gates (each
`IsLinearOpticalGate` — a beamsplitter or phase shifter) with `L.prod = E` has `d − 1 ≤ L.length`.
Together with `linearOptics_universal` (Part 1: every unitary *is* such a product) this shows the
two passive elements are universal but, in the worst case, costly: the component count is forced up
to `d − 1`.

The witness is `quditGate` of the all-ones reflection `Concrete.allOnesReflection d`, which by
Exercise 4.38 needs `≥ d − 1` two-level factors. The proof extracts, from a linear-optical
realization `L`, the list of the gates' underlying matrices: each beamsplitter/phase-shifter gate's
operator is `Matrix.toEuclideanCLM` of a two-level unitary matrix (a `beamSplitter` / `phaseMode`
matrix, two-level by `Concrete.isTwoLevelUnitary_beamSplitter` / `isTwoLevelUnitary_phaseMode`).
Because `Evolution.op` is a monoid morphism (`comp_op`, `id_op`) and `Matrix.toEuclideanCLM` is
multiplicative, the extracted matrices' product is carried by `Matrix.toEuclideanCLM` to `E.op`,
hence equals the witness matrix `U` (`Matrix.toEuclideanCLM` is injective). The matrix two-level
lower bound `Concrete.exists_unitary_two_level_decomposition_length_ge` then forces
`d − 1 ≤ (matrices).length = L.length`. -/
theorem linearOptics_lower_bound (d : ℕ) :
    ∃ E : Evolution (qudit d), ∀ L : List (Evolution (qudit d)),
      (∀ V ∈ L, IsLinearOpticalGate V) → L.prod = E → d - 1 ≤ L.length := by
  obtain ⟨U, hU, hbound⟩ := exists_unitary_two_level_decomposition_length_ge d
  refine ⟨quditGate hU, fun L hL hprod => ?_⟩
  -- Each linear-optical gate's operator is `toEuclideanCLM` of a two-level unitary matrix.
  have gateMatrix : ∀ {V : Evolution (qudit d)}, IsLinearOpticalGate V →
      ∃ M : Matrix (Fin d) (Fin d) ℂ, IsTwoLevelUnitary M ∧
        V.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) M := by
    rintro V (⟨p, q, θ, hpq, rfl⟩ | ⟨p, φ, rfl⟩)
    · exact ⟨beamSplitter p q θ, isTwoLevelUnitary_beamSplitter hpq θ, rfl⟩
    · exact ⟨phaseMode p φ, isTwoLevelUnitary_phaseMode p φ, rfl⟩
  -- Extract from `L` a same-length list of two-level unitary matrices whose product's operator
  -- (under `toEuclideanCLM`) equals `L.prod.op`. Induction keeps per-element bookkeeping local.
  have bridge : ∀ (K : List (Evolution (qudit d))), (∀ V ∈ K, IsLinearOpticalGate V) →
      ∃ K' : List (Matrix (Fin d) (Fin d) ℂ), K'.length = K.length ∧
        (∀ M ∈ K', IsTwoLevelUnitary M) ∧
        K.prod.op = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) K'.prod := by
    intro K
    induction K with
    | nil =>
      intro _
      refine ⟨[], rfl, by simp, ?_⟩
      rw [List.prod_nil, Evolution.one_def, Evolution.id_op, List.prod_nil, map_one]
      rfl
    | cons V rest ih =>
      intro hK
      obtain ⟨M, hM, hMop⟩ := gateMatrix (hK V (by simp))
      obtain ⟨K', hlen, hK'two, hK'op⟩ := ih (fun W hW => hK W (List.mem_cons_of_mem _ hW))
      refine ⟨M :: K', by rw [List.length_cons, List.length_cons, hlen], ?_, ?_⟩
      · intro N hN
        rcases List.mem_cons.mp hN with rfl | hN
        · exact hM
        · exact hK'two N hN
      · rw [List.prod_cons, Evolution.mul_def, Evolution.comp_op, hMop, hK'op, List.prod_cons,
          map_mul]
        rfl
  obtain ⟨K, hlen, hKtwo, hKop⟩ := bridge L hL
  -- `K.prod = U`, since `toEuclideanCLM K.prod = L.prod.op = (quditGate hU).op = toEuclideanCLM U`.
  have hKU : K.prod = U := by
    have himg : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) K.prod
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) U := by
      rw [← hKop, hprod, quditGate_op]
    have := congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)).symm himg
    rwa [StarAlgEquiv.symm_apply_apply, StarAlgEquiv.symm_apply_apply] at this
  calc d - 1 ≤ K.length := hbound K hKtwo hKU
    _ = L.length := hlen

/-- **Exponential component lower bound in the number of qubits (Nielsen & Chuang, Problem 7.2,
Part 4).** In the unary encoding of Problem 7.2, an `n`-qubit register is `d = 2ⁿ` optical modes
(`qudit (2ⁿ)`). Specializing `linearOptics_lower_bound` to `d = 2ⁿ`: there is a unitary `Evolution`
whose every realization as a list of linear-optical gates (beamsplitters and phase shifters) uses at
least `2ⁿ − 1` gates — **exponentially many in the number of qubits `n`**. So although Part 1
(`linearOptics_universal`) shows any unitary *can* be built from just these two passive elements, in
general doing so requires an exponential number of components, as Problem 7.2 Part 4 asks. -/
theorem linearOptics_exponential_lower_bound (n : ℕ) :
    ∃ E : Evolution (qudit (2 ^ n)), ∀ L : List (Evolution (qudit (2 ^ n))),
      (∀ V ∈ L, IsLinearOpticalGate V) → L.prod = E → 2 ^ n - 1 ≤ L.length :=
  linearOptics_lower_bound (2 ^ n)

end AxQM
