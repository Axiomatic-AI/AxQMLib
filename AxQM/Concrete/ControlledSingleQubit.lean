/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Concrete.TwoLevelEmbedding
import AxQM.Concrete.GrayCode

/-!
# Concrete: the controlled single-qubit gate (N&C §4.5.2, the controlled-`Ũ` step)

(Nielsen & Chuang §4.5.2, p. 191–193.)

The §4.5.2 realisation of a two-level unitary `U` (acting non-trivially only on two computational
basis states `|s⟩`, `|t⟩`) as a circuit of single-qubit and `CNOT` gates walks a Gray code to bring
the two active states onto a pair `|g_{m-1}⟩`, `|g_m⟩ = |t⟩` **differing in exactly one bit** `j`,
then applies a *controlled-`Ũ`* operation — apply the `2 × 2` unitary `Ũ` to qubit `j`, conditional
on the other qubits matching the values shared by the two active states. The Gray-code relocation is
already in the library (`swapConj_swapChain_grayCode_support`, the first stage); this file provides
that controlled-`Ũ` object as an explicit matrix and identifies it with a bit-adjacent two-level
unitary.

## The construction

Fix an encoding `enc : (Fin m → Fin 2) ≃ Fin d` of the `m`-bit strings as the `d = 2 ^ m`
computational basis indices. For a target bit `j`, a control pattern `c : Fin m → Fin 2` (its `j`-th
entry is ignored — the two active states are `c` with bit `j` set to `0` and to `1`), and a `2 × 2`
matrix `Ũ`:

* `AxQM.Concrete.ctrlSingleQubit enc j c Ũ` — on the basis state `|enc x⟩` it applies `Ũ`
  to bit `j` of `x` when the other bits of `x` agree with `c`, and fixes `|enc x⟩` otherwise.

The key identity is that this **is** a two-level embedding at the bit-adjacent pair:

* `AxQM.Concrete.ctrlSingleQubit_eq_twoLevelEmbed` —
  `ctrlSingleQubit enc j c Ũ = twoLevelEmbed (enc (c[j↦0])) (enc (c[j↦1])) Ũ`, an entrywise
  identification. Via `isTwoLevelUnitary_twoLevelEmbed` it follows that a controlled single-qubit
  gate with unitary `Ũ` is a two-level unitary (`isTwoLevelUnitary_ctrlSingleQubit`) whose
  distinguished pair `{c[j↦0], c[j↦1]}` differs in a single bit (`differsInOneBit_update_zero_one`)
  — the §4.5.2 controlled-`Ũ` gate. Its action is read off from `twoLevelEmbed_mulVec`:
  `ctrlSingleQubit_mulVec` mixes only the two active components through `Ũ`, and
  `ctrlSingleQubit_mulVec_of_not_ctrl` fixes every basis state outside the controlled subspace.

Used by the §4.5.2 development of Exercise 4.43's `n`-qubit lift; the statement of Exercise 4.43
is in `AxQM/NC/Ch4/Exercise4_43.lean`.
-/

namespace AxQM.Concrete

open Matrix

variable {m d : ℕ}

/-- If a bit-string does not match the control pattern `c` off bit `j`, it is neither of the two
active states `c[j↦0]`, `c[j↦1]` — a thin wrapper reading off `Function.eq_update_iff`. -/
theorem ne_update_of_not_ctrl {j : Fin m} {v : Fin 2} {c y : Fin m → Fin 2}
    (h : ¬ ∀ k, k ≠ j → y k = c k) : y ≠ Function.update c j v :=
  fun he => h (Function.eq_update_iff.mp he).2

/-- If `z` matches the control pattern `c` off bit `j`, then `z = c[j↦v]` iff `z j = v`. -/
theorem eq_update_iff_of_off {j : Fin m} {c z : Fin m → Fin 2}
    (h : ∀ k, k ≠ j → z k = c k) (v : Fin 2) :
    (z = Function.update c j v) ↔ z j = v :=
  Function.eq_update_iff.trans (and_iff_left h)

/-- The two active states `c[j↦0]` and `c[j↦1]` differ (at bit `j`), hence are distinct. -/
theorem update_zero_ne_update_one {j : Fin m} (c : Fin m → Fin 2) :
    Function.update c j 0 ≠ Function.update c j 1 := by
  intro h
  have := congrFun h j
  simp only [Function.update_self] at this
  exact absurd this (by decide)

/-- The two active states of a controlled single-qubit gate differ in exactly one bit (bit `j`) —
the adjacency the Gray-code relocation produces. -/
theorem differsInOneBit_update_zero_one {j : Fin m} (c : Fin m → Fin 2) :
    differsInOneBit (Function.update c j 0) (Function.update c j 1) := by
  refine ⟨j, ?_, fun k hk => ?_⟩
  · simp only [Function.update_self]; decide
  · simp [Function.update_of_ne hk]

/-- **The controlled single-qubit gate** (N&C §4.5.2's controlled-`Ũ`). Relative to an encoding
`enc : (Fin m → Fin 2) ≃ Fin d`, target bit `j`, control pattern `c`, and `2 × 2` matrix `Ũ`, it
applies `Ũ` to bit `j` of `x` on the basis state `|enc x⟩` when the other bits of `x` match `c`, and
acts as the identity otherwise. -/
def ctrlSingleQubit (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m) (c : Fin m → Fin 2)
    (Ũ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i i' =>
    if ∀ k, k ≠ j → enc.symm i k = enc.symm i' k then
      (if ∀ k, k ≠ j → enc.symm i k = c k then Ũ (enc.symm i j) (enc.symm i' j)
        else if enc.symm i j = enc.symm i' j then 1 else 0)
    else 0

/-- The entrywise heart of `ctrlSingleQubit_eq_twoLevelEmbed`, phrased on bare bit-strings `x`, `y`:
the controlled-gate entry (LHS) equals the two-level-embedding entry at the pair
`{c[j↦0], c[j↦1]}` (RHS). -/
theorem ctrlSingleQubit_entry_eq {j : Fin m} {c : Fin m → Fin 2}
    (Ũ : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin m → Fin 2) :
    (if ∀ k, k ≠ j → x k = y k then
        (if ∀ k, k ≠ j → x k = c k then Ũ (x j) (y j) else if x j = y j then 1 else 0)
      else 0)
      = (if x = Function.update c j 0 then
            (if y = Function.update c j 0 then Ũ 0 0 else if y = Function.update c j 1 then Ũ 0 1
              else 0)
          else if x = Function.update c j 1 then
            (if y = Function.update c j 0 then Ũ 1 0 else if y = Function.update c j 1 then Ũ 1 1
              else 0)
          else if x = y then 1 else 0) := by
  by_cases hcx : ∀ k, k ≠ j → x k = c k
  · -- `x` matches the control pattern off bit `j`.
    have hxa := eq_update_iff_of_off hcx 0
    have hxb := eq_update_iff_of_off hcx 1
    by_cases hcy : ∀ k, k ≠ j → y k = c k
    · -- both `x, y` match: the gate acts through `Ũ (x j) (y j)`.
      have hPi : ∀ k, k ≠ j → x k = y k := fun k hk => (hcx k hk).trans (hcy k hk).symm
      have hya := eq_update_iff_of_off hcy 0
      have hyb := eq_update_iff_of_off hcy 1
      rw [ite_eq_left hPi, ite_eq_left hcx]
      rcases (by omega : x j = 0 ∨ x j = 1) with hx | hx <;>
        rcases (by omega : y j = 0 ∨ y j = 1) with hy | hy
      · rw [ite_eq_left (hxa.2 hx), ite_eq_left (hya.2 hy), hx, hy]
      · rw [ite_eq_left (hxa.2 hx), ite_eq_right (by rw [hya]; omega), ite_eq_left (hyb.2 hy), hx,
            hy]
      · rw [ite_eq_right (by rw [hxa]; omega), ite_eq_left (hxb.2 hx), ite_eq_left (hya.2 hy), hx,
            hy]
      · rw [ite_eq_right (by rw [hxa]; omega), ite_eq_left (hxb.2 hx),
            ite_eq_right (by rw [hya]; omega),
          ite_eq_left (hyb.2 hy), hx, hy]
    · -- `y` does not match: both sides are `0` at the `y`-column.
      have hPi : ¬ ∀ k, k ≠ j → x k = y k :=
        fun hPi => hcy fun k hk => (hPi k hk).symm.trans (hcx k hk)
      have hy0 : ¬ (y = Function.update c j 0) := ne_update_of_not_ctrl hcy
      have hy1 : ¬ (y = Function.update c j 1) := ne_update_of_not_ctrl hcy
      rw [ite_eq_right hPi]
      rcases (by omega : x j = 0 ∨ x j = 1) with hx | hx
      · rw [ite_eq_left (hxa.2 hx), ite_eq_right hy0, ite_eq_right hy1]
      · rw [ite_eq_right (by rw [hxa]; omega), ite_eq_left (hxb.2 hx), ite_eq_right hy0,
            ite_eq_right hy1]
  · -- `x` does not match: the gate is the identity at the `x`-row.
    have hx0 : ¬ (x = Function.update c j 0) := ne_update_of_not_ctrl hcx
    have hx1 : ¬ (x = Function.update c j 1) := ne_update_of_not_ctrl hcx
    rw [ite_eq_right hcx, ite_eq_right hx0, ite_eq_right hx1]
    by_cases hxy : x = y
    · subst hxy
      rw [ite_eq_left (fun _ _ => rfl), ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right hxy]
      by_cases hoff : ∀ k, k ≠ j → x k = y k
      · have hne : x j ≠ y j := fun hj => hxy (funext fun k => by
          rcases eq_or_ne k j with rfl | hk
          · exact hj
          · exact hoff k hk)
        rw [ite_eq_left hoff, ite_eq_right hne]
      · rw [ite_eq_right hoff]

/-- **A controlled single-qubit gate is a two-level embedding at a bit-adjacent pair.**
`ctrlSingleQubit enc j c Ũ` places `Ũ` into the `{enc (c[j↦0]), enc (c[j↦1])}` block, an entrywise
identity. This routes the controlled-`Ũ` gate through the §4.5.1 embedding machinery. -/
theorem ctrlSingleQubit_eq_twoLevelEmbed (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (c : Fin m → Fin 2) (Ũ : Matrix (Fin 2) (Fin 2) ℂ) :
    ctrlSingleQubit enc j c Ũ
      = twoLevelEmbed (enc (Function.update c j 0)) (enc (Function.update c j 1)) Ũ := by
  ext i i'
  have hi0 : (i = enc (Function.update c j 0)) ↔ (enc.symm i = Function.update c j 0) := by
    rw [Equiv.symm_apply_eq]
  have hi1 : (i = enc (Function.update c j 1)) ↔ (enc.symm i = Function.update c j 1) := by
    rw [Equiv.symm_apply_eq]
  have hi'0 : (i' = enc (Function.update c j 0)) ↔ (enc.symm i' = Function.update c j 0) := by
    rw [Equiv.symm_apply_eq]
  have hi'1 : (i' = enc (Function.update c j 1)) ↔ (enc.symm i' = Function.update c j 1) := by
    rw [Equiv.symm_apply_eq]
  have hii' : (i = i') ↔ (enc.symm i = enc.symm i') := enc.symm.injective.eq_iff.symm
  simp only [ctrlSingleQubit, Matrix.of_apply, twoLevelEmbed_apply, hi0, hi1, hi'0, hi'1, hii']
  exact ctrlSingleQubit_entry_eq Ũ (enc.symm i) (enc.symm i')

/-- **A controlled single-qubit gate with unitary `Ũ` is a two-level unitary.** -/
theorem isTwoLevelUnitary_ctrlSingleQubit (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (c : Fin m → Fin 2) {Ũ : Matrix (Fin 2) (Fin 2) ℂ} (hŨ : Ũ ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    IsTwoLevelUnitary (ctrlSingleQubit enc j c Ũ) := by
  rw [ctrlSingleQubit_eq_twoLevelEmbed]
  exact isTwoLevelUnitary_twoLevelEmbed (enc.injective.ne (update_zero_ne_update_one c)) hŨ

/-- **The action of a controlled single-qubit gate on a vector.** It mixes only the two active
components `enc (c[j↦0])`, `enc (c[j↦1])` through `Ũ`, fixing every other component — the
controlled-`Ũ` action. -/
theorem ctrlSingleQubit_mulVec (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m) (c : Fin m → Fin 2)
    (Ũ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin d → ℂ) (i : Fin d) :
    (ctrlSingleQubit enc j c Ũ *ᵥ v) i =
      if enc.symm i = Function.update c j 0 then
        Ũ 0 0 * v (enc (Function.update c j 0)) + Ũ 0 1 * v (enc (Function.update c j 1))
      else if enc.symm i = Function.update c j 1 then
        Ũ 1 0 * v (enc (Function.update c j 0)) + Ũ 1 1 * v (enc (Function.update c j 1))
      else v i := by
  rw [ctrlSingleQubit_eq_twoLevelEmbed,
    twoLevelEmbed_mulVec (enc.injective.ne (update_zero_ne_update_one c))]
  simp only [← Equiv.symm_apply_eq]

/-- Outside the controlled subspace — when the other bits of `x = enc.symm i` do not match the
control pattern `c` — the controlled single-qubit gate fixes `|enc x⟩`. -/
theorem ctrlSingleQubit_mulVec_of_not_ctrl (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (c : Fin m → Fin 2) (Ũ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin d → ℂ) (i : Fin d)
    (h : ¬ ∀ k, k ≠ j → enc.symm i k = c k) :
    (ctrlSingleQubit enc j c Ũ *ᵥ v) i = v i := by
  rw [ctrlSingleQubit_mulVec, ite_eq_right (ne_update_of_not_ctrl h),
      ite_eq_right (ne_update_of_not_ctrl h)]

/-! ## The fibrewise-gate abstraction

Both `ctrlSingleQubit enc j c` (above) and `singleQubitOnWire enc j` (`SingleQubitWire.lean`)
are **fibrewise**: they preserve each two-dimensional `j`-bit fibre
`{x[j↦0], x[j↦1]}` and act on it by a `2 × 2` block determined by the *other* bits. `wireGate`
captures that common shape here, at the common ancestor of both gates, so each gate's action /
multiplicativity lemmas are one-line consequences of the general `wireGate_*` lemmas (rather than
parallel hand-proofs). -/

/-- **A fibrewise gate on wire `j`.** For an encoding `enc : (Fin m → Fin 2) ≃ Fin d`, a wire `j`,
and a family `f : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ` of `2 × 2` blocks indexed by the
off-`j` bit-pattern, `wireGate enc j f` is the `d × d` matrix that, on the basis state `|enc x⟩`,
acts on the `j`-th bit's two-dimensional fibre by the block `f x` (read at the pattern with bit `j`
normalised to `0`), fixing the other bits. It is the common shape of `singleQubitOnWire` (a constant
block) and `ctrlSingleQubit` (a block that is `Ũ` on the controlled fibres and `1` elsewhere). -/
def wireGate (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (f : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i i' =>
    if ∀ k, k ≠ j → enc.symm i k = enc.symm i' k then
      f (Function.update (enc.symm i) j 0) (enc.symm i j) (enc.symm i' j)
    else 0

/-- Unfolding lemma for `wireGate` entries. -/
theorem wireGate_apply (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (f : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) (i i' : Fin d) :
    wireGate enc j f i i' =
      if ∀ k, k ≠ j → enc.symm i k = enc.symm i' k then
        f (Function.update (enc.symm i) j 0) (enc.symm i j) (enc.symm i' j)
      else 0 := rfl

/-- **The action of a fibrewise gate on a vector.** It mixes only the two components whose
bit-strings agree off wire `j`, through the block `f` (read at the fibre representative). -/
theorem wireGate_mulVec (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (f : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin d → ℂ) (i : Fin d) :
    (wireGate enc j f *ᵥ v) i =
      f (Function.update (enc.symm i) j 0) (enc.symm i j) 0
          * v (enc (Function.update (enc.symm i) j 0))
        + f (Function.update (enc.symm i) j 0) (enc.symm i j) 1
          * v (enc (Function.update (enc.symm i) j 1)) := by
  classical
  simp only [Matrix.mulVec, dotProduct, wireGate, Matrix.of_apply]
  set X := enc.symm i with hX
  set p := enc (Function.update X j 0) with hp
  set q := enc (Function.update X j 1) with hq
  have hpq : p ≠ q := enc.injective.ne (update_zero_ne_update_one X)
  have hp' : enc.symm p = Function.update X j 0 := by rw [hp, Equiv.symm_apply_apply]
  have hq' : enc.symm q = Function.update X j 1 := by rw [hq, Equiv.symm_apply_apply]
  rw [Finset.sum_eq_add p q hpq (fun c _ hc => ?_) (by simp) (by simp)]
  · -- the two surviving terms `p`, `q`
    have hcondp : ∀ k, k ≠ j → X k = enc.symm p k := by
      intro k hk; rw [hp', Function.update_of_ne hk]
    have hcondq : ∀ k, k ≠ j → X k = enc.symm q k := by
      intro k hk; rw [hq', Function.update_of_ne hk]
    rw [ite_eq_left hcondp, ite_eq_left hcondq, hp', hq', Function.update_self,
        Function.update_self]
  · -- every other index contributes `0`
    have hcond : ¬ ∀ k, k ≠ j → X k = enc.symm c k := by
      intro hcond
      have hupd : enc.symm c = Function.update X j (enc.symm c j) := by
        funext k
        rcases eq_or_ne k j with rfl | hk
        · rw [Function.update_self]
        · rw [Function.update_of_ne hk, ← hcond k hk]
      rcases (show enc.symm c j = 0 ∨ enc.symm c j = 1 from by omega) with h0 | h1
      · exact hc.1 (by rw [← Equiv.symm_apply_eq, hupd, h0])
      · exact hc.2 (by rw [← Equiv.symm_apply_eq, hupd, h1])
    rw [ite_eq_right hcond, zero_mul]

/-- **Fibrewise gates multiply blockwise.** Since a fibrewise gate preserves each `j`-bit fibre,
different fibres never mix, so a matrix product of two of them multiplies their `2 × 2` blocks
fibre-by-fibre: `wireGate enc j f * wireGate enc j g = wireGate enc j (fun y => f y * g y)`. -/
theorem wireGate_mul (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (f g : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) :
    wireGate enc j f * wireGate enc j g = wireGate enc j (fun y => f y * g y) := by
  have key : ∀ (v : Fin d → ℂ) (i : Fin d),
      ((wireGate enc j f * wireGate enc j g) *ᵥ v) i
        = (wireGate enc j (fun y => f y * g y) *ᵥ v) i := by
    intro v i
    rw [← Matrix.mulVec_mulVec]
    simp only [wireGate_mulVec, Equiv.symm_apply_apply, Function.update_self,
      Function.update_idem, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  ext i i'
  have h1 := key (fun x => if x = i' then (1 : ℂ) else 0) i
  simpa only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h1

/-- **The fibrewise gate with the constant identity block is the identity.** -/
theorem wireGate_one (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m) :
    wireGate enc j (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  ext i i'
  simp only [wireGate_apply, Matrix.one_apply]
  by_cases h : i = i'
  · subst h; simp
  · rw [ite_eq_right h]
    by_cases hoff : ∀ k, k ≠ j → enc.symm i k = enc.symm i' k
    · rw [ite_eq_left hoff, ite_eq_right]
      intro hj
      exact h (enc.symm.injective (funext fun k => by
        rcases eq_or_ne k j with rfl | hk
        · exact hj
        · exact hoff k hk))
    · rw [ite_eq_right hoff]

/-- **A fibrewise gate commutes with the conjugate transpose**:
`(wireGate enc j f)ᴴ = wireGate enc j (fun y => (f y)ᴴ)`. Each fibre's `2 × 2` block is transposed;
the fibre representative is unaffected because the two indices agree off wire `j` exactly when the
entry is non-zero. The adjoint counterpart of `wireGate_mul`. -/
theorem wireGate_conjTranspose (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (f : (Fin m → Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) :
    (wireGate enc j f)ᴴ = wireGate enc j (fun y => (f y)ᴴ) := by
  ext i i'
  rw [Matrix.conjTranspose_apply, wireGate_apply, wireGate_apply]
  by_cases hoff : ∀ k, k ≠ j → enc.symm i k = enc.symm i' k
  · rw [ite_eq_left hoff, ite_eq_left (fun k hk => (hoff k hk).symm)]
    have hrep : Function.update (enc.symm i') j 0 = Function.update (enc.symm i) j 0 := by
      funext k
      rcases eq_or_ne k j with rfl | hk
      · rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk, hoff k hk]
    rw [hrep, Matrix.conjTranspose_apply]
  · rw [ite_eq_right hoff, ite_eq_right (fun h => hoff (fun k hk => (h k hk).symm)), star_zero]

/-- **`ctrlSingleQubit` is the fibrewise gate whose block is `Ũ` on the controlled fibres and `1`
elsewhere.** -/
theorem ctrlSingleQubit_eq_wireGate (enc : (Fin m → Fin 2) ≃ Fin d) (j : Fin m)
    (c : Fin m → Fin 2) (Ũ : Matrix (Fin 2) (Fin 2) ℂ) :
    ctrlSingleQubit enc j c Ũ
      = wireGate enc j (fun y => if ∀ k, k ≠ j → y k = c k then Ũ else 1) := by
  ext i i'
  simp only [ctrlSingleQubit, wireGate, Matrix.of_apply]
  by_cases hfib : ∀ k, k ≠ j → enc.symm i k = enc.symm i' k
  · rw [ite_eq_left hfib, ite_eq_left hfib]
    have hcond : (∀ k, k ≠ j → Function.update (enc.symm i) j 0 k = c k)
        ↔ (∀ k, k ≠ j → enc.symm i k = c k) :=
      forall_congr' fun k => imp_congr_right fun hk => by rw [Function.update_of_ne hk]
    by_cases hc : ∀ k, k ≠ j → enc.symm i k = c k
    · rw [ite_eq_left hc, ite_eq_left (hcond.mpr hc)]
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hcond.mp h)), Matrix.one_apply]
  · rw [ite_eq_right hfib, ite_eq_right hfib]

end AxQM.Concrete
