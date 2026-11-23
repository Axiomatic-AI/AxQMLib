/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.API.DeutschGate
import AxQM.Postulates.API.ControlledControlledUnitary
import AxQM.Postulates.API.DeutschGateReachable
import AxQM.Postulates.API.DeutschUniversality

/-!
# Nielsen & Chuang, Exercise 4.44 (universality of the three-qubit Deutsch gate)

*(N&C p. 198.)*

Show the three-qubit gate G is universal whenever alpha is irrational.

The gate `G` is the **Deutsch gate** `C²(iR_x(πα))`: the operation `iR_x(πα) = i·R_x(πα)` is applied
to the target qubit exactly when both control qubits are `|1⟩`. This file formalises the gate and
the two physical facts underlying N&C's universality argument.

## The formalisation

* `deutschGate α` — the **three-qubit Deutsch gate** `G = C²(iR_x(πα))`, the doubly-controlled
  (`ccontrolledUnitary`) Deutsch target gate `iRxGate (πα)`
  (`AxQM/Postulates/API/DeutschGate.lean`).
* `deutschGate_evolvePure_ketOne_ketOne` — **the mechanism**: with both controls set to `|1⟩`, the
  gate applies its target operation `iR_x(πα)` to the target qubit,
  `G(|1⟩⊗|1⟩⊗φ) = |1⟩⊗|1⟩⊗(iR_x(πα)φ)`. Iterating `G` on this doubly-controlled subspace therefore
  applies the powers `(iR_x(πα))^k`, whose `x`-rotation content is *dense* precisely when `α` is
  irrational (the analytic core `Concrete.rotX_mem_closure_cyclic_iRx`).
* `deutschGate_one_eq_toffoliGate` — **the boundary case** `G|_{α=1} = C²(X)`: at `α = 1`,
  `iR_x(π) = X` (`iRxGate_pi_eq_pauliXGate`), so `G` is the **Toffoli gate**. The Deutsch gate is
  thus a continuous `α`-deformation of Toffoli; at the *rational* value `α = 1` it degenerates to a
  gate that is not, on its own, universal — witnessing why irrationality of `α` is essential.
* `deutschGate_conj_mem_deutschReachableEvolutions` — **the universality naming** (the terminal):
  the physical gate `deutschGate α`, placed on register wires, is a generator of the reachable
  submonoid `deutschReachableEvolutions` whose data-register actions are dense in `U(2ⁿ)` up to a
  global phase
  (`exists_phase_smul_toEuclideanCLM_mem_closure_dataRegisterOp_deutschReachableEvolutions`,
  `AxQM/Postulates/API/DeutschUniversality.lean`) — so `G` with ancillas is universal for `α`
  irrational.

## The universality reduction

N&C's argument that `G` is universal turns on iterating `G` to reach a universal gate set. The
pieces are built up in order.

1. **Density of the doubly-controlled `x`-rotations.** Fixing the controls at `|1⟩` and
   iterating `G` runs the single-qubit orbit `(iR_x(πα))^k`; because `(iR_x(θ))^4 = R_x(4θ)` the
   global phase `i` cancels every four steps, and the resulting `x`-rotations are dense in *all*
   `x`-rotations exactly when `α` is irrational (`Concrete.rotX_mem_closure_cyclic_iRx`).
   This is now lifted to the physics gate: every doubly-controlled `x`-rotation `C²(R_x(β))` lies in
   the closure of the Deutsch gate's iterates
   (`ccontrolledUnitary_rotXGate_op_mem_closure_deutschReachableOps`,
   `AxQM/Postulates/API/DeutschGateReachable.lean`), whose members are grounded in `G` by
   `ccontrolledUnitary_iRxGate_pow_op_mem` (which names the gate in its unfolded form
   `ccontrolledUnitary (iRxGate (πα))`, definitionally equal to `deutschGate α`). These reachability
   statements are in terms of the operators `.op` and their closure.
2. **A second single-qubit axis: the phase gate `S`.** The `x`-rotations are one abelian
   axis; the second axis is the phase gate `S = diag(1, i)`, obtained from the *once*-controlled
   Deutsch gate. Fixing one control of `G` at `|1⟩` leaves `C(iR_x(πα))`; iterating it and taking
   the `iⁿ = i`, `R_x = I` limit reaches the controlled global phase `C(i · I) = S ⊗ I` (the
   accumulated `i` becomes a phase on the control). The concrete fact that `i · I` is a closure
   limit of the cyclic orbit is `Concrete.iScalar_mem_closure_cyclic_iRx`, lifted to the physics
   gate as `sGate_onLeft_op_mem_closure_deutschControlledReachableOps`
   (`AxQM/Postulates/API/DeutschGatePhaseGate.lean`): `S ⊗ I` lies in the closure of the
   once-controlled
   Deutsch iterates. Because `S` conjugates the `x`-axis to the perpendicular `y`-axis
   (`Concrete.sMatrix_mul_rotX_mul_conjTranspose`), a dense `x`-axis together with `S` gives a
   second dense axis — hence, by the Euler decomposition, every single-qubit unitary up to a global
   phase. That single-qubit core (over an abstract gate submonoid supplied with a dense `x`-axis and
   `S`) is `Concrete.exists_phase_smul_mem_closure_of_forall_rotX_sMatrix`
   (`AxQM/Concrete/DeutschSingleQubitUniversality.lean`).
3. **The reversible gates `CNOT` and `Toffoli` from `G`.** Universality via the §4.5
   assembly needs, besides the single-qubit gates, the reversible gates `CNOT` and `Toffoli` (an
   arbitrary unitary decomposes into a product of Toffoli/`CNOT`/`NOT` and single-qubit gates). The
   Deutsch gate densely reaches both: the Pauli `X` is the `β = π` value of the phased
   `x`-rotations, `X = i·R_x(π)` (`Concrete.pauliX_mem_closure_cyclic_iRx`, the `iⁿ = i` coset of
   the orbit at angle `π`, a new corollary of the general `i`-coset density
   `Concrete.iScaledRotX_mem_closure_cyclic_iRx` that also subsumes the phase-gate's `i·I`). Lifting
   through the controlled embeddings gives
   `CNOT = C(X)` in the closure of the once-controlled iterates
   (`cnotGate_op_mem_closure_deutschControlledReachableOps`) and `Toffoli = C²(X)` in the closure of
   the Deutsch gate's iterates (`toffoliGate_op_mem_closure_deutschReachableOps`,
   `AxQM/Postulates/API/DeutschGateReversible.lean`). This is the density counterpart of
   `deutschGate_one_eq_toffoliGate`, which gives `Toffoli` *exactly* but only at the rational value
   `α = 1`; for irrational `α`, `G` never equals `Toffoli`, yet its iterates approximate it.
4. **Single-qubit universality of `G` on a register wire, and circuit completeness.**
   The single-qubit gates `G` reaches on a wire are collected into the submonoid
   `Concrete.deutschWireGateSubmonoid α` — generated by the target orbit `⟨iR_x(πα)⟩` (the dense
   `x`-axis) and the phase gate `S` (with `S†`) — and instantiating the single-qubit core
   (`Concrete.exists_phase_smul_mem_closure_of_forall_rotX_sMatrix`) at this submonoid gives every
   single-qubit unitary on a chosen register wire up to a global phase, kept phase-clean
   (`Concrete.exists_phase_smul_singleQubitOnWire_mem_closure_deutschWireGateSubmonoid`,
   `AxQM/Concrete/DeutschWireUniversality.lean`) — the Deutsch counterpart of Exercise 4.43's
   `exists_phase_smul_singleQubitOnWire_mem_closure`.

   The **circuit-completeness assembly over this abstract gate set.**
   `Concrete.exists_phase_smul_mem_closure_deutschReachableCircuits`
   (`AxQM/Concrete/DeutschReachableCircuits.lean`) adapts Exercise 4.43's `FourGateUniversality`:
   the
   reachable gate set `deutschReachableGateSet enc α` collects the `≤ 2`-control reversible gates
   `IsToffoliPermGate` together with, on every wire, the single-qubit gates
   `singleQubitOnWire enc j g` with `g ∈ deutschWireGateSubmonoid α`; every unitary decomposes into
   these terminal gates (the shared generic `Concrete.exists_isToffoliOrSingleQubit_list_prod_eq`),
   each is approximated up to a global phase by the reachable circuits (single-qubit via the wire
   density above, reversible exactly), and the phases combine — so the circuits these gates generate
   are dense in `U(2ⁿ)` up to a global phase when `α` is irrational. This is the **universality
   density core**.

   The **realisation of the reachable gates from `G`**: the single-qubit
   generators of `deutschReachableGateSet` are realised from `G` only *with control ancillas* (the
   `x`-axis needs the two control wires held at `|1⟩`, the phase gate `S` a control-wire placement),
   so the faithful statement is universality *with ancillas* — compressing an actual
   `G`-placement circuit to its data-register action on the ancilla-`|1…1⟩`
   subspace — and naming the `Evolution` gate `deutschGate α` in the conclusion.

   The object `G` becomes when *placed on
   three register wires* — two control wires `a, b` and a target wire `j` — is the two-control
   instance `Concrete.mcCtrlSingleQubit enc {a, b} j g` of the existing subset-controlled
   single-qubit wire gate (`AxQM/Concrete/MultiControlledSingleQubit.lean`; the density facts are in
   `AxQM/Concrete/DeutschWirePlacement.lean`). One object realises **both** dense single-qubit axes
   at
   two wire assignments: the dense `x`-axis with the controls on two ancillas held at `|1⟩` and the
   target on the data wire, and the phase gate `S` with one control on an ancilla and the *other
   control on the data wire* (the controlled global phase `i · I` on the target becoming `S` on the
   control). It is a continuous `*`-homomorphism in its block (its algebra
   `mcCtrlSingleQubit_{one,mul,conjTranspose,mem_unitaryGroup}` and the new
   `continuous_mcCtrlSingleQubit` are shared, inherited from the fibrewise `wireGate` family), and
   its `x`-rotation, `i · I` and Pauli-`X` content is densely reachable from the placed Deutsch
   iterates (`mcCtrlSingleQubit_rotX_mem_closure_deutschWirePlacedReachable` /
   `_iScalar_mem_closure_…` / `_pauliX_mem_closure_…`, `α` irrational) — the placement-level
   counterpart of the `2 × 2` orbit-density core.

   The **ancilla-compression bridge** — identifying the compressed `G`-placements with the density
   core's single-qubit / reversible generators. The generic subspace compression
   `compress ι M = M.submatrix ι ι` to the ancilla-`|1⟩` coordinate subspace is a continuous monoid
   homomorphism on the range-preserving matrices (`AxQM/Concrete/SubspaceCompression.lean`), and the
   register layout `regExtend`/`regEmbed` embeds the data basis with the ancillas held `|1⟩`
   (`AxQM/Concrete/RegisterCompressionBridge.lean`). Against that layout the compressed placements
   are
   read off (`AxQM/Concrete/RegisterCompressionBridgeAncilla.lean`): a dense `x`-axis gate on a data
   wire
   with its two controls on ancillas compresses to the bare single-qubit gate
   (`compress_mcCtrlSingleQubit_of_ancilla_controls`); the controlled global phase `C(z · I)` with
   the target on a throwaway ancilla and one control on the data wire `w` compresses to
   `singleQubitOnWire dataEnc w (phaseGate z)` — the phase gate `S` for `z = i`, `S†` for `z = -i`
   (`compress_mcCtrlSingleQubit_smul_one_ancillaTarget[_eq_sMatrix]`, via the diagonal route since
   the target is an ancilla); and a data-target `X` whose controls descend to `≤ 2` data controls
   compresses to a `Toffoli`/`CNOT`/`NOT` on the data register
   (`isToffoliPermGate_compress_mcCtrlSingleQubit_pauliX`).

   The **single-qubit half of the compressed realisation**
   (`AxQM/Concrete/DeutschCompressedReachable.lean`). The `G`-placement circuits that are both
   reachable
   from `G` and preserve the ancilla-`|1⟩` subspace form a submonoid
   `Concrete.deutschAncillaReachableCircuits`, whose compression to the data register
   `Concrete.deutschDataReachableCircuits` is again a submonoid (`compress` being a monoid
   homomorphism on the range-preserving matrices), and every single-qubit gate
   `singleQubitOnWire dataEnc j g` with `g ∈ deutschWireGateSubmonoid α` lies in it
   (`Concrete.singleQubitOnWire_mem_deutschDataReachableCircuits`, `α` irrational): the dense
   `x`-axis orbit blocks are compressed ancilla-controlled data-target placements, the phase gate
   `S` the compressed controlled global phase `C(i · I)`, and `S† = S³` a product of the latter.
   This realises `G`'s two dense single-qubit axes as data-register actions of
   `G`-placement circuits with ancillas.

   The **reversible half and the matrix universality**
   (`AxQM/Concrete/DeutschCompressedUniversality.lean`). Every `≤ 2`-control reversible gate
   `IsToffoliPermGate dataEnc N` is also a compressed `G`-placement
   (`Concrete.isToffoliPermGate_mem_deutschDataReachableCircuits`, `α` irrational): place the
   Pauli-`X` orbit member on a data target with `G`'s **two** control wires assigned so the
   `|C| ≤ 2` data controls sit on data wires and the remaining `2 - |C|` on ancillas held `|1⟩`
   (transparent, so a `Toffoli` acts as the reduced `C^{2-|C|}(X)` on the data wires — N&C's
   realisation of the lower-arity reversible gates from a Toffoli, with
   `Concrete.exists_control_pair_descend_of_card_le_two` producing genuinely *distinct* control
   wires). With both halves of the abstract gate set `deutschReachableGateSet dataEnc α` inside the
   compressed submonoid `deutschDataReachableCircuits`, the abstract reachable circuits are `≤` it
   (`Submonoid.closure_le`), so the abstract density core transports along the closure containment
   to the **matrix headline**
   `Concrete.exists_phase_smul_mem_closure_deutschDataReachableCircuits`: for `α` irrational and a
   data register of `≥ 1` qubit, the data-register actions of `G`-placement circuits with ancillas
   are dense in `U(2ⁿ)` up to a global phase — **universality of `G` with ancillas at the matrix
   level**.

   The **bridge to the matrix development.** The whole matrix development
   above lives on the `2ⁿ`-level register `qudit d`, while the physical Deutsch gate
   `deutschGate α = ccontrolledUnitary (iRxGate (πα))` is a gate on the composite three-qubit system
   `qubit ⊗ (qubit ⊗ qubit)`. These two register models are identified by the system isomorphism
   `threeQuditIso : qubit ⊗ (qubit ⊗ qubit) ≃ₛ qudit 8`
   (`AxQM/Postulates/API/DeutschGateMatrix.lean`),
   and against it the transported Deutsch gate is read off as an explicit `Fin 8` matrix:
   `deutschGate_congr_threeQuditIso_op` proves
   `(Evolution.congr threeQuditIso (deutschGate α)).op = toEuclideanCLM (Concrete.ccontrolledMatFin8
   (Concrete.iRxMat (πα)))` — the doubly-controlled matrix `C²(iR_x(πα))` on `qudit 8` that the
   entire reachability/compression development is built from. (Stated over the unfolded
   `ccontrolledUnitary (iRxGate (πα))`, definitionally `deutschGate α`; the general form
   `ccontrolledUnitary_congr_threeQuditIso_op` gives it for an arbitrary
   single-qubit gate whose matrix is known.) This connects the physical gate `deutschGate α` to the
   concrete matrix reachability results.

   The **base-register placement bridge.** The whole reachability/compression development iterates
   the wire-addressed matrix
   gate `Concrete.mcCtrlSingleQubit enc S j g`; naming `G` in the conclusion needs that register
   placement tied back to `deutschGate α`. On the *base register* of three wires this tie is
   `congr_threeQuditIso_deutschGate_eq_quditGate_mcCtrlSingleQubit`
   (`AxQM/Postulates/API/DeutschGateRegisterBridge.lean`): the reachability-family placement
   `quditGate (mcCtrlSingleQubit finThreeRegEnc {0, 1} 2 (iRxMat (πα)))` — the exact `quditGate`
   shape the development iterates — *equals* `deutschGate α` transported to `qudit 8`
   (`Evolution.congr threeQuditIso (ccontrolledUnitary (iRxGate (πα)))`). It chains the
   operator–matrix
   bridge `ccontrolledUnitary_congr_threeQuditIso_op` with the new pure-matrix identity
   `Concrete.ccontrolledMatFin8_eq_mcCtrlSingleQubit`
   (`AxQM/Concrete/DeutschRegisterBridge.lean`) — the doubly-controlled `Fin 8` matrix `C²(g)` *is*
   the
   two-control `mcCtrlSingleQubit` placement of `g` on the canonical three-wire encoding
   `finThreeRegEnc` — through `Evolution.ext` (an evolution is determined by its operator).

   The **wire relabelling for the general-wire embedding**
   (`AxQM/Concrete/WireGateRelabel.lean`). The reachable placements
   `mcCtrlSingleQubit fullEnc {a, b} j g` range over *arbitrary* distinct control/target wires,
   whereas the base-register bridge names only
   the canonical wires `{0, 1}`, `2`; the matrix wire-move that reconciles them is: a fibrewise gate
   is unchanged if the wires are permuted, provided the encoding is correspondingly relabelled. A
   wire permutation `σ` induces the bit-string relabel `Concrete.wireStringPerm σ`
   (`y ↦ y ∘ σ.symm`), and precomposing the encoding with it moves each wire index by `σ.symm`:
   `Concrete.wireGate_wireStringPerm` for the general fibrewise gate,
   `Concrete.mcCtrlSingleQubit_wireStringPerm` moving the control set to `S.map σ.symm.toEmbedding`
   and the target to `σ.symm j`, and the uncontrolled `Concrete.singleQubitOnWire_wireStringPerm`.
   Choosing `σ` so that `σ.symm` sends the arbitrary wires `a, b, j` to `0, 1, 2` reduces an
   arbitrary-wire placement to the base three-wire placement.

   The **register tensor-split and the general-wire naming.** Against the
   tensor-split encoding `regTensorEnc e restEnc` (leading three wires plus a `rest` block), the
   canonical placement factors as the doubly-controlled `Fin 8` matrix tensored with the identity,
   `Concrete.mcCtrlSingleQubit_regTensorEnc_eq_kroneckerFin`
   (`= kroneckerFin (ccontrolledMatFin8 g) 1`, `AxQM/Concrete/DeutschTensorSplit.lean`); through the
   generic `quditGate`-of-Kronecker physics bridge `quditGate_kroneckerFin_eq_congr_tmul`
   (`AxQM/Postulates/API/QuditKroneckerGate.lean`) this reads the promoted placement as
   `Evolution.congr (quditProdIso 8 r).symm ((Evolution.congr threeQuditIso (deutschGate α)).tmul
   Evolution.id)` — the physical Deutsch gate on the leading three wires, tensored with the identity
   (`quditGate_mcCtrlSingleQubit_regTensorEnc_eq_congr_tmul_ccontrolledUnitary`,
   `AxQM/Postulates/API/DeutschGateTensorSplit.lean`). This is lifted off the specific tensor-split
   encoding to **any** register encoding by a change of encoding: `wireGate` reads its encoding only
   through `enc.symm`, so two encodings differ by a `submatrix` reindex
   (`Concrete.mcCtrlSingleQubit_encoding_change`, `AxQM/Concrete/WireGateEncodingChange.lean`),
   which
   promotes through `quditGate` to conjugation by the register-permutation gate `quditPerm`
   (`quditGate_submatrix_eq_conj`, `AxQM/Postulates/API/QuditGateSubmatrix.lean`). Composing the
   two,
   `quditGate_mcCtrlSingleQubit_eq_conj_congr_tmul_ccontrolledUnitary`
   (`AxQM/Postulates/API/DeutschGateWirePlacement.lean`) names `deutschGate α` for the placement on
   the
   leading wires `e.symm (Sum.inl 0/1/2)` of *any* encoding
   `fullEnc`, transported to `qudit 8`, tensored with the identity, and conjugated by the encoding
   permutation.

   The **arbitrary-triple form of the naming.** The reachable placements `mcCtrlSingleQubit fullEnc
   {a, b} j g`
   range over an *arbitrary* distinct control/target triple `a, b, j`, existentially bound with no
   reference to a wire-splitting `e`; the leading-wire naming above names `deutschGate α` only when
   the triple leads a given splitting. The gap is a pure combinatorial construction: three distinct
   wires `a, b, j` are the leading wires of *some* splitting `e : Fin M ≃ Fin 3 ⊕ Fin (M - 3)`
   (`Concrete.exists_wireSplitEquiv_of_distinct`, `AxQM/Concrete/WireTripleSplit.lean` — built from
   the
   injective `![a, b, j] : Fin 3 ↪ Fin M` via `Equiv.ofInjective` and `Equiv.Set.sumCompl`).
   Instantiating the leading-wire naming at that `e` gives
   `quditGate_mcCtrlSingleQubit_distinct_eq_conj_congr_tmul_ccontrolledUnitary`
   (`AxQM/Postulates/API/DeutschGateArbitraryWirePlacement.lean`): for *any* distinct `a, b, j`, the
   placement `mcCtrlSingleQubit fullEnc {a, b} j (iRxMat (πα))` promoted to a `quditGate` is
   `deutschGate α` transported to `qudit 8`, tensored with the identity, and conjugated by the
   encoding permutation. This is the naming the reachable-`Evolution`-submonoid op-identification
   consumes for every `G`-placement generator (whose control/target wires are existentially bound).

**Step 4's conclusion: universality of `G` with ancillas.** The reachable full-register
`G`-circuit matrices are first exhibited as the operators of a submonoid of register `Evolution`s:
`deutschReachableEvolutions fullEnc dataEnc e α`
(`AxQM/Postulates/API/DeutschReachableEvolutions.lean`),
the submonoid of `Evolution (qudit D)` generated by the `quditGate` promotions of the reachable
ancilla-preserving `G`-placements, with `exists_deutschReachableEvolution_op_eq` identifying every
matrix `N ∈ deutschAncillaReachableCircuits` as the operator of one of its members. The matrix
universality headline `Concrete.exists_phase_smul_mem_closure_deutschDataReachableCircuits` then
transports through the continuous `⋆`-algebra isomorphism `Matrix.toEuclideanCLM` onto the
data-register actions `dataRegisterOp ι` of that submonoid (`ι` the ancilla-`|1⟩` embedding),
giving `exists_phase_smul_toEuclideanCLM_mem_closure_dataRegisterOp_deutschReachableEvolutions`
(`AxQM/Postulates/API/DeutschUniversality.lean`): for `α` irrational, `≥ 1` data qubit and `≥ 2`
ancillas, the data-register actions of the physical `G`-circuits are dense in `U(2ⁿ)` up to a global
phase —
**universality of `G` with ancillas for the physical gate**. Finally, that the reachable submonoid
is
genuinely *about* `deutschGate α` is `deutschGate_conj_mem_deutschReachableEvolutions` (below): the
physical Deutsch gate `deutschGate α`, transported to `qudit 8`, tensored with the identity, and
conjugated by a register-permutation gate, is a member of `deutschReachableEvolutions` — the
`G`-placement with the two controls on ancillas held `|1⟩` and the target on a data wire. Steps 1–3
give the two dense single-qubit axes, the
single-qubit universality core, and the reversible gates `CNOT`/`Toffoli`; the single-qubit-on-wire
density and the abstract density core give single-qubit universality on a wire and the
circuit-completeness assembly over the abstract gate set; and the honest compressed realisation —
single-qubit *and* reversible — gives the matrix-level universality of `G` *with ancillas*.

**Faithfulness note.** The hypothesis is `Irrational α`, exactly as the exercise states — *not*
"`α` not a rational multiple of `2π`". The latter would admit `α = 1` (rational),
where `G` is the Toffoli gate and *not* universal; density of `{R_x(n·4πα)}` needs `(4πα)/(2π) = 2α`
irrational, i.e. `α` irrational, so `Irrational α` is both the literal reading and the one the
mathematics needs.
-/

noncomputable section

namespace AxQM

/-- The **three-qubit Deutsch gate** `G = C²(iR_x(πα))` (Nielsen & Chuang, Exercise 4.44): the
doubly-controlled application of the Deutsch target gate `iRxGate (πα) = iR_x(πα)` to the target
qubit, i.e. `iR_x(πα)` fires on the third qubit exactly when both control qubits are `|1⟩`. Built as
`ccontrolledUnitary (iRxGate (π·α))`, so it is automatically a unitary `Evolution`. -/
def deutschGate (α : ℝ) : Evolution (qubit.compose (qubit.compose qubit)) :=
  ccontrolledUnitary (iRxGate (Real.pi * α))

/-- **The Deutsch gate's mechanism.** With both control qubits set to `|1⟩`, the Deutsch gate
applies its target operation `iR_x(πα)` to the target qubit:
`G(|1⟩ ⊗ |1⟩ ⊗ φ) = |1⟩ ⊗ |1⟩ ⊗ (iR_x(πα) φ)`. Iterating `G` on this doubly-controlled subspace
thus runs the single-qubit orbit `(iR_x(πα))^k`, whose `x`-rotation content is dense when `α` is
irrational (`Concrete.rotX_mem_closure_cyclic_iRx`) — the density that drives universality. -/
theorem deutschGate_evolvePure_ketOne_ketOne (α : ℝ) (φ : PureState qubit) :
    (deutschGate α).evolvePure ((qubitBasis 1).tmul ((qubitBasis 1).tmul φ)) =
      (qubitBasis 1).tmul ((qubitBasis 1).tmul ((iRxGate (Real.pi * α)).evolvePure φ)) := by
  rw [deutschGate, ccontrolledUnitary_evolvePure_ketOne_left, controlledUnitary_evolvePure_ketOne]

/-- **The boundary case `α = 1`: the Deutsch gate is the Toffoli gate.** Since `iR_x(π) = X`
(`iRxGate_pi_eq_pauliXGate`), the Deutsch gate `G = C²(iR_x(π·1))` is the doubly-controlled `X`, the
Toffoli gate `C²(X)`. The Deutsch gate is therefore a continuous `α`-deformation of Toffoli; at this
rational value it is not, by itself, universal, which is why irrationality of `α` is required. -/
theorem deutschGate_one_eq_toffoliGate : deutschGate 1 = toffoliGate := by
  unfold deutschGate toffoliGate
  rw [mul_one, iRxGate_pi_eq_pauliXGate]

/-- **The Deutsch gate `G` generates the universal register submonoid.** For a register encoding
`fullEnc : (Fin M → Fin 2) ≃ Fin (8·r)`, a `rest`-encoding
`restEnc : (Fin (M - 3) → Fin 2) ≃ Fin r`, a data encoding `dataEnc : (Fin m → Fin 2) ≃ Fin d`, a
data-ancilla wire split `e : Fin M ≃ Fin m ⊕ Fin n`, two distinct ancilla wires `a₀ ≠ a₁` and a data
wire `j`, the physical Deutsch gate `deutschGate α` — transported to `qudit 8` (`threeQuditIso`),
tensored with the identity on the remaining `qudit r`, and conjugated by the register-permutation
gate `quditPerm ρ` — is a member of the reachable `G`-circuit submonoid
`deutschReachableEvolutions fullEnc dataEnc e α` (the submonoid whose data-register actions are
dense in `U(2ⁿ)` up to a global phase,
`exists_phase_smul_toEuclideanCLM_mem_closure_dataRegisterOp_deutschReachableEvolutions`).

This is the naming that makes the universality statement genuinely about `deutschGate α`: the
reachable submonoid is generated by the wire-placements of `deutschGate α` itself. The member is the
`G`-placement with the two controls on the ancilla wires `a₀, a₁` (held `|1⟩`) and the target on the
data wire `j`. The conjugation and tensor factors are the physical relabelling of the three
placement wires among the `M` register wires; they are unavoidable because `deutschGate α` acts on
three qubits of a larger register. Immediate from the naming
`exists_conj_ccontrolledUnitary_mem_deutschReachableEvolutions`
(`AxQM/Postulates/API/DeutschUniversality.lean`), since
`deutschGate α = ccontrolledUnitary (iRxGate (π·α))` by definition. -/
theorem deutschGate_conj_mem_deutschReachableEvolutions {M m n r d : ℕ}
    (fullEnc : (Fin M → Fin 2) ≃ Fin (8 * r)) (restEnc : (Fin (M - 3) → Fin 2) ≃ Fin r)
    (dataEnc : (Fin m → Fin 2) ≃ Fin d) (e : Fin M ≃ Fin m ⊕ Fin n) (α : ℝ)
    (a₀ a₁ : Fin n) (ha : a₀ ≠ a₁) (j : Fin m) :
    ∃ e₃ : Fin M ≃ Fin 3 ⊕ Fin (M - 3),
      quditPerm (fullEnc.symm.trans (Concrete.regTensorEnc e₃ restEnc)).symm
          * Evolution.congr (quditProdIso 8 r).symm
              ((Evolution.congr threeQuditIso (deutschGate α)).tmul Evolution.id)
          * quditPerm (fullEnc.symm.trans (Concrete.regTensorEnc e₃ restEnc))
        ∈ deutschReachableEvolutions fullEnc dataEnc e α :=
  exists_conj_ccontrolledUnitary_mem_deutschReachableEvolutions
    fullEnc restEnc dataEnc e α a₀ a₁ ha j

end AxQM
