/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Evolution
import AxQM.Postulates.API.MaximallyMixed
import AxQM.Postulates.API.QuantumChannel

/-!
# AxQM.Postulates.API — random-unitary (mixed-unitary) channels

A **random-unitary channel** (also *mixed-unitary channel*) is a quantum operation of the form
`E(ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†` where the `Uₖ` are unitaries and `{pₖ}` is a probability distribution:
the channel applies a *randomly chosen* unitary `Uₖ` with probability `pₖ`. It is the running
object of **Nielsen & Chuang, Problem 8.3** (*Random unitary channels*): it is "tempting to
believe that all unital channels — those with `E(I) = I` — are of this form", and the problem is to
show this holds for single qubits but *fails* for larger systems.

This file provides the **framework** and the easy half of the Problem 8.3 story:

* `AxQM.RandomUnitaryChannel` — the bundled data of a random-unitary channel of `S`:
  a finite family of unitary `Evolution`s `Uₖ` together with a probability distribution `pₖ`.
* `AxQM.RandomUnitaryChannel.apply` — its action `E(ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†` on states,
  a genuine `State S` (a convex combination of the states `Uₖ ρ Uₖ†`).
* `AxQM.IsUnital` — a state-map is **unital** when it fixes the maximally mixed state
  `I/d` (equivalently `E(I) = I`, since a channel is linear).
* `AxQM.IsRandomUnitary` — a state-map is **random-unitary** when it is realised by some
  `RandomUnitaryChannel`. This is the predicate in which Problem 8.3's two claims are phrased.
* `AxQM.RandomUnitaryChannel.isUnital` / `AxQM.isUnital_of_isRandomUnitary` —
  **the easy direction of Problem 8.3:** every random-unitary channel is unital (the concrete and
  the `IsRandomUnitary`-predicate forms). This is the `⇐` half of the "tempting belief"; the
  problem's actual content is the *converse* — true on a qubit, false in dimension `≥ 3`.

The lemma `AxQM.Evolution.evolve_maximallyMixedState` — every unitary conjugation fixes
`I/d` (`U (I/d) U† = I/d`), the atomic reason a random-unitary channel is unital — is in
`AxQM/Postulates/API/MaximallyMixed.lean`, a general `Evolution` fact independent of the channel
construction.

## Scope of this file vs. the full problem

Problem 8.3's two claims — (i) *every unital qubit channel is random-unitary* and (ii) *there
is a unital channel in dimension `≥ 3` that is not random-unitary* — are **not** proved here.
(i)'s `∀`-form is not even statable without a general completely-positive **channel** object and
the Bloch affine-map representation of a unital qubit channel; (ii)'s non-membership proof requires
convex **extreme-point** / Choi-matrix analysis (the Landau–Streater argument). Neither is
formalised here. This file proves the easy direction: every random-unitary channel is unital.

The statement of Problem 8.3 is in `AxQM/NC/Ch8/Problem8_3.lean`. The helper
`AxQM.isDensityOp_sum_prob_smul` (a probability-weighted sum of density operators is a
density operator — the `n`-ary companion of the binary
`ContinuousLinearMap.IsDensityOp.convex_combination`) is stated fully generally (over any complex
inner-product space `E`, not pinned to `S.space`).

## Design notes

* **Why `State → State` and a bundled structure.** `apply` produces a genuine `State`, so
  **trace preservation is automatic** — no separate theorem is needed. Bundling the family
  `{pₖ, Uₖ}` (mirroring `Ensemble`) makes a channel a first-class value one can quantify over,
  which is what Problem 8.3's "∃ a unital channel that is not random-unitary" needs.
* **Why `IsUnital` via `I/d`.** N&C states unitality as `E(I) = I` for the (unnormalised) identity
  operator; for a linear channel this is equivalent to fixing the maximally mixed state `I/d`, which
  *is* a `State`. Phrasing unitality as `E(I/d) = I/d` therefore states it over
  `maximallyMixedState` instead of a bare identity operator. The equivalence
  `E(I) = I ↔ E(I/d) = I/d` is the linear rescaling by `1/d`.
-/

open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace AxQM

variable {S : QSystem}

/-- **A probability-weighted sum of density operators is a density operator.** The `n`-ary
convex-combination closure of the density operators (the finite companion of the binary
`ContinuousLinearMap.IsDensityOp.convex_combination`): if each `ρ i` is a density operator, `p` is a
probability distribution (`0 ≤ p i`, `∑ p i = 1`), then `∑ᵢ pᵢ ρᵢ` is again a density operator.
Positivity is closure of positive operators under nonnegative scaling and finite sums; the trace is
`∑ᵢ pᵢ · tr ρᵢ = ∑ᵢ pᵢ · 1 = 1`. Stated for an arbitrary complex inner-product space `E` (the proof
uses nothing specific to `S.space`), so it applies at `E := S.space`. -/
theorem isDensityOp_sum_prob_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} [Fintype ι]
    {ρ : ι → E →L[ℂ] E} (hρ : ∀ i, (ρ i).IsDensityOp)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, (p i : ℂ) • ρ i).IsDensityOp := by
  rw [ContinuousLinearMap.isDensityOp_iff]
  refine ⟨?_, ?_⟩
  · -- positivity: a finite sum of nonnegative multiples of positive operators is positive
    exact ContinuousLinearMap.isPositive_sum Finset.univ
      fun i _ => (hρ i).isPositive.smul_of_nonneg (by exact_mod_cast hp i)
  · -- trace: `tr (∑ᵢ pᵢ ρᵢ) = ∑ᵢ pᵢ · tr ρᵢ = ∑ᵢ pᵢ = 1`
    have h : (LinearMap.trace ℂ E) ↑(∑ i, (p i : ℂ) • ρ i) = ∑ i, (p i : ℂ) := by
      rw [ContinuousLinearMap.toLinearMap_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ContinuousLinearMap.toLinearMap_smul, map_smul, (hρ i).trace_eq_one, smul_eq_mul, mul_one]
    rw [h, ← Complex.ofReal_sum, hsum, Complex.ofReal_one]

/-- **A random-unitary (mixed-unitary) channel** of the system `S` (Nielsen & Chuang, Problem 8.3):
a finite family of unitary `Evolution`s `unitary k` together with a probability distribution
`prob k` (nonnegative, summing to one). Its action `∑ₖ pₖ Uₖ ρ Uₖ†` is `RandomUnitaryChannel.apply`.
The data mirrors `Ensemble` (a probability distribution over a finite family), here of unitaries
rather than pure states. -/
structure RandomUnitaryChannel (S : QSystem) where
  /-- The number of unitaries in the mixture. -/
  card : ℕ
  /-- The probability weights `pₖ`. -/
  prob : Fin card → ℝ
  /-- The unitary evolutions `Uₖ` that are mixed over. -/
  unitary : Fin card → Evolution S
  /-- Each probability is nonnegative. -/
  prob_nonneg : ∀ i, 0 ≤ prob i
  /-- The probabilities sum to one. -/
  sum_prob : ∑ i, prob i = 1

namespace RandomUnitaryChannel

/-- **The action of a random-unitary channel** on a state: `E(ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†`, the
probability-weighted mixture of the conjugated states `Uₖ ρ Uₖ† = (Uₖ).evolve ρ`. It is a genuine
`State S` — a convex combination of states — by `isDensityOp_sum_prob_smul`, so the channel is
automatically trace preserving. -/
def apply (C : RandomUnitaryChannel S) (ρ : State S) : State S where
  op := ∑ i, (C.prob i : ℂ) • ((C.unitary i).evolve ρ).op
  isDensity :=
    isDensityOp_sum_prob_smul (fun i => ((C.unitary i).evolve ρ).isDensity) C.prob_nonneg C.sum_prob

/-- The operator of `C.apply ρ` is the operator sum `∑ₖ pₖ Uₖ ρ Uₖ†`. -/
@[simp]
theorem apply_op (C : RandomUnitaryChannel S) (ρ : State S) :
    (C.apply ρ).op = ∑ i, (C.prob i : ℂ) • ((C.unitary i).evolve ρ).op := rfl

/-- **The sesquilinear form of a random-unitary channel is the probability-weighted mixture of the
per-unitary forms:** `⟨φ, C(ρ) φ⟩ = ∑ₖ pₖ ⟨φ, Uₖ ρ Uₖ† φ⟩`. Immediate additivity / `ℂ`-linearity of
`⟨φ, · φ⟩` over the operator sum `apply_op`. Pairing this identity against a specific vector `φ` is
the entry point for reasoning about a random-unitary channel via matrix elements — e.g. the
pure-state non-membership argument for Nielsen & Chuang, Problem 8.3
(`Postulates/API/WernerHolevoRandomUnitary`). -/
theorem inner_apply_op_eq_sum (C : RandomUnitaryChannel S) (ρ : State S) (φ : S.space) :
    (inner ℂ φ ((C.apply ρ).op φ) : ℂ)
      = ∑ k, (C.prob k : ℂ) * (inner ℂ φ (((C.unitary k).evolve ρ).op φ) : ℂ) := by
  rw [RandomUnitaryChannel.apply_op, sum_apply, inner_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_apply, inner_smul_right]

end RandomUnitaryChannel

/-- **A state-map (channel) `f` is unital** if it fixes the maximally mixed state `I/d`:
`f (I/d) = I/d`. For a **linear** channel this is Nielsen & Chuang's `E(I) = I` (the two differ by
the linear rescaling `I = d · (I/d)`); phrasing it over `maximallyMixedState` states the property
for states. This is the fixed-point form of the "unital channels" of Problem 8.3.

Note the predicate is stated on an arbitrary `f : State S → State S` — it captures only the fixed
point, not linearity/complete-positivity. That is exactly what the easy direction here needs (it is
applied only to the *linear* `RandomUnitaryChannel.apply`). A formalisation of the *converse* claim
of Problem 8.3 must have its hypothesis range over a genuine (linear, completely-positive,
trace-preserving) **channel** — a bundled object the library does not yet have (see
`Problem8_3.lean`) — not over an arbitrary `I/d`-fixing state-map, or the ∀-statement would not be
N&C's claim. -/
def IsUnital [Nontrivial S.space] (f : State S → State S) : Prop :=
  f (maximallyMixedState S) = maximallyMixedState S

/-- **A state-map (channel) `f` is random-unitary (mixed-unitary)** if it agrees with the action of
some `RandomUnitaryChannel`, i.e. `f(ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†` for a probability distribution `pₖ` and
unitaries `Uₖ`. This is the predicate in which **both** claims of Nielsen & Chuang, Problem 8.3 are
phrased: for a *unital channel* `f`, is `f` random-unitary? — true for a qubit, false in dimension
`≥ 3`. (`Evolution.evolve_maximallyMixedState` — every unitary conjugation fixes `I/d` — is in
`AxQM/Postulates/API/MaximallyMixed.lean`.) -/
def IsRandomUnitary (f : State S → State S) : Prop :=
  ∃ C : RandomUnitaryChannel S, ∀ ρ, C.apply ρ = f ρ

/-- **Unital state-maps are closed under composition.** If `f` and `g` each fix the maximally mixed
state `I/d` (`IsUnital`), so does their composite `f ∘ g`, `fun ρ ↦ f (g ρ)`: `f (g (I/d)) = f (I/d)
= I/d`. The first argument `f` is the *outer* map, matching the convention of `isRandomUnitary_comp`
(and `isChannel_comp`). Paired with `isChannel_comp` (channels are closed under composition), this
lets the qubit converse of Nielsen & Chuang, Problem 8.3 conjugate a *unital channel* by unitary
rotations and keep both properties — the diagonalisation step of the converse. -/
theorem isUnital_comp [Nontrivial S.space] {f g : State S → State S}
    (hf : IsUnital f) (hg : IsUnital g) : IsUnital (fun ρ => f (g ρ)) := by
  change f (g (maximallyMixedState S)) = maximallyMixedState S
  rw [hg, hf]

/-- **The easy direction of Nielsen & Chuang, Problem 8.3:** every random-unitary channel
`E(ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†` is **unital**, `E(I/d) = I/d`. Each unitary conjugation fixes `I/d`
(`Evolution.evolve_maximallyMixedState`), so the channel maps `I/d` to `∑ₖ pₖ · (I/d) = I/d` (the
weights sum to one). The problem's real content is the *converse* — that unitality forces the
random-unitary form on a qubit but not in dimension `≥ 3` — which this framework supports. -/
theorem RandomUnitaryChannel.isUnital [Nontrivial S.space] (C : RandomUnitaryChannel S) :
    IsUnital C.apply := by
  apply State.ext
  simp only [RandomUnitaryChannel.apply_op, Evolution.evolve_maximallyMixedState,
    ← Finset.sum_smul, ← Complex.ofReal_sum, C.sum_prob, Complex.ofReal_one, one_smul]

/-- **The easy direction of Nielsen & Chuang, Problem 8.3, over `IsRandomUnitary`:** every
random-unitary state-map is unital. This is the `⇐` half of the "tempting belief" — the direction
that N&C presents as *background*, whose *converse* is the problem. Immediate from
`RandomUnitaryChannel.isUnital` and the witnessing channel. -/
theorem isUnital_of_isRandomUnitary [Nontrivial S.space] {f : State S → State S}
    (hf : IsRandomUnitary f) : IsUnital f := by
  obtain ⟨C, hC⟩ := hf
  exact funext hC ▸ C.isUnital

/-- **A random-unitary channel is a genuine CPTP quantum channel.** The operator-sum
`E(ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†` is realised by the Kraus operators `Eₖ = √pₖ · Uₖ`, whose completeness
relation is `∑ₖ Eₖ† Eₖ = ∑ₖ pₖ Uₖ† Uₖ = (∑ₖ pₖ) · I = I` (each `Uₖ` unitary, the weights sum to
one). By `isChannel_of_kraus` this exhibits `E` as a completely-positive trace-preserving map:
random-unitary channels are honest channels, so the framework's easy direction strengthens from
"random-unitary ⟹ unital" (`RandomUnitaryChannel.isUnital`) to "random-unitary ⟹ *unital
channel*". -/
theorem RandomUnitaryChannel.isChannel (C : RandomUnitaryChannel S) : IsChannel C.apply := by
  -- the adjoint of a *real*-scalar multiple pulls the scalar out unchanged (it is self-conjugate)
  have hadj : ∀ (c : ℝ) (A : S.space →L[ℂ] S.space),
      ContinuousLinearMap.adjoint ((c : ℂ) • A) = (c : ℂ) • ContinuousLinearMap.adjoint A := by
    intro c A
    simp only [← ContinuousLinearMap.star_eq_adjoint, star_smul]
    norm_num
  refine isChannel_of_kraus (fun k => (Real.sqrt (C.prob k) : ℂ) • (C.unitary k).op) ?_ ?_
  · -- completeness relation `∑ₖ Eₖ† Eₖ = ∑ₖ pₖ Uₖ† Uₖ = (∑ₖ pₖ) • 1 = 1`
    have key : ∀ k, (ContinuousLinearMap.adjoint
        ((Real.sqrt (C.prob k) : ℂ) • (C.unitary k).op)).comp
        ((Real.sqrt (C.prob k) : ℂ) • (C.unitary k).op) = (C.prob k : ℂ) • 1 := by
      intro k
      rw [hadj, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
        (C.unitary k).adjoint_comp_self, ← Complex.ofReal_mul, Real.mul_self_sqrt (C.prob_nonneg k)]
    rw [Finset.sum_congr rfl fun k _ => key k, ← Finset.sum_smul, ← Complex.ofReal_sum,
      C.sum_prob, Complex.ofReal_one, one_smul]
  · -- the operator sum reproduces `E(ρ) = ∑ₖ pₖ Uₖ ρ Uₖ†`
    intro ρ
    rw [ContinuousLinearMap.krausSumₗ_apply, RandomUnitaryChannel.apply_op]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Evolution.evolve_op, hadj]
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (C.prob_nonneg k)]

/-- **A random-unitary state-map is a genuine CPTP quantum channel** (the
`IsRandomUnitary`-predicate form of `RandomUnitaryChannel.isChannel`). Together with
`isUnital_of_isRandomUnitary` this says a
random-unitary map is a *unital channel* — sharpening the easy half of Nielsen & Chuang, Problem 8.3
to the very hypothesis (`IsChannel`) under which the problem's converse is posed. -/
theorem isChannel_of_isRandomUnitary {f : State S → State S} (hf : IsRandomUnitary f) :
    IsChannel f := by
  obtain ⟨C, hC⟩ := hf
  exact funext hC ▸ C.isChannel

/-! ### Closure of the random-unitary channels

The random-unitary channels form a *submonoid* of the state-maps: they contain every single unitary
conjugation and are closed under composition. This is the algebraic glue for the **qubit converse**
of Problem 8.3: a unital qubit channel factors on the Bloch sphere as `conj U₁ ∘ Pauli ∘ conj U₂`
(pre/post rotations `O₁, O₂` from the singular-value decomposition of its Bloch matrix, each a
unitary conjugation by `SU(2) → SO(3)`), so once the diagonal `Pauli` part is known random-unitary
(`pauliChannel_isRandomUnitary`), these closure facts assemble the general case. -/

/-- **A single unitary conjugation is a random-unitary channel.** The one-point mixture
`E(ρ) = 1 · U ρ U†` (all the weight on the single unitary `U`) realises the conjugation `U.evolve`,
so `U.evolve` is `IsRandomUnitary`. This is the base case of the random-unitary closure used in the
qubit converse of Nielsen & Chuang, Problem 8.3. -/
theorem isRandomUnitary_evolve (U : Evolution S) : IsRandomUnitary U.evolve := by
  refine ⟨⟨1, fun _ => 1, fun _ => U, fun _ => zero_le_one, by simp⟩, fun ρ => ?_⟩
  apply State.ext
  simp [RandomUnitaryChannel.apply_op]

/-- **A unitary conjugation is a CPTP quantum channel.** The map `ρ ↦ U ρ U†` induced by a unitary
evolution `U` (`Evolution.evolve`) is a completely-positive trace-preserving quantum channel
(`IsChannel`): it is the one-point random-unitary channel (`isRandomUnitary_evolve`), and every
random-unitary channel is a channel (`isChannel_of_isRandomUnitary`). This is the fact that makes
the pre- and post-composition unitaries `U`, `V` of a *channel equivalence* `E₂ = U ∘ E₁ ∘ V`
(Nielsen & Chuang, Problem 10.1) themselves channels, so `isChannel_comp` transfers the CPTP
property from `E₁` to the equivalent `E₂`. -/
theorem isChannel_evolve (U : Evolution S) : IsChannel U.evolve :=
  isChannel_of_isRandomUnitary (isRandomUnitary_evolve U)

/-- **The composite of two random-unitary channels.** Given random-unitary channels `C` (unitaries
`Uᵢ`, weights `pᵢ`) and `D` (unitaries `Vⱼ`, weights `qⱼ`), the composite mixes the
`C.card * D.card` composite unitaries `Uᵢ ∘ Vⱼ` (`Evolution.comp`) with the product distribution
`pᵢ qⱼ`. Its action is exactly the functional composition `C.apply ∘ D.apply`
(`RandomUnitaryChannel.apply_comp`), so random-unitary channels are closed under composition. The
index set `Fin (C.card * D.card)` is identified with the product `Fin C.card × Fin D.card` via
`finProdFinEquiv`. -/
def RandomUnitaryChannel.comp (C D : RandomUnitaryChannel S) : RandomUnitaryChannel S where
  card := C.card * D.card
  prob k := C.prob (finProdFinEquiv.symm k).1 * D.prob (finProdFinEquiv.symm k).2
  unitary k := (C.unitary (finProdFinEquiv.symm k).1).comp (D.unitary (finProdFinEquiv.symm k).2)
  prob_nonneg k := mul_nonneg (C.prob_nonneg _) (D.prob_nonneg _)
  sum_prob := by
    rw [Fintype.sum_equiv finProdFinEquiv.symm
        (fun k => C.prob (finProdFinEquiv.symm k).1 * D.prob (finProdFinEquiv.symm k).2)
        (fun ij : Fin C.card × Fin D.card => C.prob ij.1 * D.prob ij.2) fun _ => rfl,
      Fintype.sum_prod_type]
    rw [← Finset.sum_mul_sum, C.sum_prob, D.sum_prob, mul_one]

/-- **The composite channel acts by functional composition:** `(C.comp D).apply ρ = C.apply
(D.apply ρ)`. Averaging the `Uᵢ ∘ Vⱼ`-conjugations against the product distribution `pᵢ qⱼ` equals
first averaging the `Vⱼ`-conjugations (that is `D.apply`) and then the `Uᵢ`-conjugations (that is
`C.apply`), because each `Uᵢ`-conjugation is linear in the state operator and so commutes past the
`D`-mixture. -/
theorem RandomUnitaryChannel.apply_comp (C D : RandomUnitaryChannel S) (ρ : State S) :
    (C.comp D).apply ρ = C.apply (D.apply ρ) := by
  apply State.ext
  -- Reindex the composite sum over the product `Fin C.card × Fin D.card` (defeq to
  -- `Fin (C.card * D.card)` via `finProdFinEquiv`); `exact` matches up to definitional unfolding of
  -- `RandomUnitaryChannel.comp`, so no fragile `rw` on `(C.comp D).card` is needed.
  have hLHS : ((C.comp D).apply ρ).op
      = ∑ ij : Fin C.card × Fin D.card,
          ((C.prob ij.1 * D.prob ij.2 : ℝ) : ℂ) •
            (((C.unitary ij.1).comp (D.unitary ij.2)).evolve ρ).op := by
    rw [RandomUnitaryChannel.apply_op]
    exact Fintype.sum_equiv finProdFinEquiv.symm _ _ fun _ => rfl
  rw [hLHS, Fintype.sum_prod_type, RandomUnitaryChannel.apply_op]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Evolution.evolve_op (C.unitary i) (D.apply ρ), RandomUnitaryChannel.apply_op,
    ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Evolution.evolve_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ← Evolution.evolve_op, smul_smul, ← Complex.ofReal_mul]

/-- **`IsRandomUnitary` is closed under composition:** if `f` and `g` are random-unitary state-maps,
so is `ρ ↦ f (g ρ)`, witnessed by the composite channel `RandomUnitaryChannel.comp`. Together with
`isRandomUnitary_evolve` this is the closure used to reduce the qubit converse of Nielsen & Chuang,
Problem 8.3 (`conj U₁ ∘ Pauli ∘ conj U₂`) to its diagonal (Pauli) case. -/
theorem isRandomUnitary_comp {f g : State S → State S}
    (hf : IsRandomUnitary f) (hg : IsRandomUnitary g) :
    IsRandomUnitary fun ρ => f (g ρ) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  exact ⟨C.comp D, fun ρ => by simp only [RandomUnitaryChannel.apply_comp, hC, hD]⟩

end AxQM
