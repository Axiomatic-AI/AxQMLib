/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.NC.Ch12.Proposition12_18
import AxQM.Postulates.API.BB84

/-!
# Nielsen & Chuang, Exercise 12.38 (distinguishing non-orthogonal states breaks QKD)

Show ability to distinguish non-orthogonal states would break BB84 and QKD.

The statements use `PureState`, `Evolution`, `Evolution.evolvePure`, `PureState.overlap`,
`PureState.tmul` (`⊗`) and the BB84 signal states `bb84State`.

## What the exercise asks, and how it is formalised

Exercise 12.38 is a **counterfactual reduction**: it asks us to show the forward implication
*"the ability to distinguish non-orthogonal states ⟹ BB84 (and every QKD protocol) can be
broken."* The physical mechanism securing BB84 (N&C §12.6) is **Proposition 12.18 —
information gain implies disturbance** (`AxQM.informationGain_implies_disturbance`):
in any attempt to distinguish two *non-orthogonal* states, information is gained only at the
expense of disturbing the signal, a disturbance the honest parties detect as an elevated error
rate. The hypothesised "ability to distinguish non-orthogonal states" is exactly the ability
to *evade* this tradeoff, and the exercise asks us to exhibit the attack it enables.

The file has two halves — the **attack** (the exercise's forward claim) and the **security
side** (why its hypothesis is physically false, hence why BB84 is in fact secure).

### The attack — a distinguisher breaks BB84 (the exercise's forward reduction)

We model "the ability to distinguish" abstractly, as a classical read-out `identify` that
correctly labels each transmitted signal (`StateDistinguisher`), generic in the signal family
`signal : ι → PureState S`. This is deliberately *not* the concrete unitary-probe model of the
security side: as an abstract oracle it is not bound by Proposition 12.18, so the reduction it
drives is genuine rather than vacuous. Knowing the classical label, Eve re-prepares the
identified state and forwards it — an **intercept–resend** attack (`StateDistinguisher.intercept`).

* `StateDistinguisher.intercept_signal` — the forwarded state *equals* the transmitted one, so
  the attack is **undetectable**: Bob's statistics, and the check-bit comparison meant to catch
  an eavesdropper, are unchanged.
* `StateDistinguisher.intercept_reveals` — the read-out recovers the full label, so the attack
  is **informative**: Eve learns which signal was sent.
* `bb84_distinguisher_compromises_security` — the two together at Alice's four signals: Eve
  learns her data bit `a` *and* Bob receives the identical `bb84State a b`. She reads the raw
  key while inducing no detectable error — BB84 is compromised. Because the reduction is generic
  in `signal`, the same conclusion holds for **every** QKD protocol "we have described" (B92, the
  six-state protocol, …), as the exercise demands.

### The security side — why the distinguisher cannot physically exist

* `bb84State_overlap_ne_zero` — **the crux.** Alice's two encoding bases are *conjugate*: any
  computational-basis signal `|ψ_{a,Z}⟩ ∈ {|0⟩, |1⟩}` and any Hadamard-basis signal
  `|ψ_{a',X}⟩ ∈ {|+⟩, |−⟩}` are non-orthogonal, `⟨ψ_{a,Z}|ψ_{a',X}⟩ = ±1/√2 ≠ 0`. (Within a
  single basis the two signals *are* orthogonal, hence perfectly distinguishable — it is only
  the *cross-basis* pairs, which Eve cannot avoid since she does not know the basis, that are
  non-orthogonal.)
* `bb84_undisturbed_probe_ancilla_eq` — a *physical* eavesdropping probe (a unitary `U` coupling
  the signal to an ancilla prepared in `u`) that leaves two cross-basis BB84 signals
  *undisturbed* ends with the ancilla in the **same** state `v = v'` regardless of which signal
  was sent: it has learned nothing. This is `ancilla_eq_of_undisturbed_probe` (Prop. 12.18, Eqs.
  12.177–12.178) fed the non-orthogonality above.
* `bb84_no_covert_distinguisher` — there is *no* physical probe that both distinguishes two
  cross-basis BB84 signals (its ancilla outcomes `v ≠ v'`) and leaves both undisturbed. The
  distinguisher the attack hypothesises has no unitary realisation — which is *precisely why*
  BB84 is secure. The security side is basis-agnostic (it uses only non-orthogonality), so the
  same Proposition 12.18 secures every QKD protocol encoding in non-orthogonal states.
-/

open scoped InnerProductSpace TensorProduct

noncomputable section

namespace AxQM

variable {A : QSystem}

/-- **BB84 uses non-orthogonal states (the crux of Exercise 12.38).** Any computational-basis
signal `|ψ_{a,Z}⟩ = bb84State a 0 ∈ {|0⟩, |1⟩}` and any Hadamard-basis signal
`|ψ_{a',X}⟩ = bb84State a' 1 ∈ {|+⟩, |−⟩}` have nonzero overlap:
`⟨ψ_{a,Z}|ψ_{a',X}⟩ = ±1/√2 ≠ 0` (the four values are `⟨0|+⟩ = ⟨0|−⟩ = ⟨1|+⟩ = 1/√2` and
`⟨1|−⟩ = −1/√2`). Because Alice's two bases are conjugate, an eavesdropper who does not know
the basis unavoidably faces genuinely non-orthogonal alternatives — the hypothesis on which
Proposition 12.18 (information gain implies disturbance) bites, and hence the source of BB84's
security.

Proved by reducing `overlap` to the inner product (`PureState.overlap_def`) and evaluating the
computational-vs-`X`-basis amplitudes `⟨i|±⟩` (`inner_qubitBasis_qubitPlus` /
`inner_qubitBasis_qubitMinus`, each `±1/√2 ≠ 0`). -/
theorem bb84State_overlap_ne_zero (a a' : Fin 2) :
    (bb84State a 0).overlap (bb84State a' 1) ≠ 0 := by
  rw [PureState.overlap_def]
  fin_cases a <;> fin_cases a'
  · change inner ℂ (qubitBasis 0).vec qubitPlus.vec ≠ 0
    rw [inner_qubitBasis_qubitPlus]; simp [Concrete.xPlus_apply, Concrete.invSqrt2_ne_zero]
  · change inner ℂ (qubitBasis 0).vec qubitMinus.vec ≠ 0
    rw [inner_qubitBasis_qubitMinus]; simp [Concrete.xMinus, Concrete.invSqrt2_ne_zero]
  · change inner ℂ (qubitBasis 1).vec qubitPlus.vec ≠ 0
    rw [inner_qubitBasis_qubitPlus]; simp [Concrete.xPlus_apply, Concrete.invSqrt2_ne_zero]
  · change inner ℂ (qubitBasis 1).vec qubitMinus.vec ≠ 0
    rw [inner_qubitBasis_qubitMinus]; simp [Concrete.xMinus, Concrete.invSqrt2_ne_zero]

/-- **An undisturbed BB84 eavesdropper learns nothing (Exercise 12.38).** Model Eve's
information-gathering attempt as a unitary `U` on `qubit ⊗ A` coupling the signal to an
ancilla prepared in the standard state `u` (the Stinespring/§8.2 reduction used by Proposition
12.18). If the probe leaves *both* cross-basis signals `|ψ_{a,Z}⟩` and `|ψ_{a',X}⟩`
undisturbed — the joint output stays a product state with the signal factor unchanged,
`U(ψ_{a,Z} ⊗ u) = ψ_{a,Z} ⊗ v` and `U(ψ_{a',X} ⊗ u) = ψ_{a',X} ⊗ v'` — then the ancilla ends
in the **same** state `v = v'` in both cases, so it carries no information about which signal
was sent. Immediate from `ancilla_eq_of_undisturbed_probe` (Prop. 12.18) and the
non-orthogonality `bb84State_overlap_ne_zero`. -/
theorem bb84_undisturbed_probe_ancilla_eq
    {a a' : Fin 2} {u v v' : PureState A} {U : Evolution (qubit ⊗ A)}
    (hψ : U.evolvePure (bb84State a 0 ⊗ u) = bb84State a 0 ⊗ v)
    (hφ : U.evolvePure (bb84State a' 1 ⊗ u) = bb84State a' 1 ⊗ v') :
    v = v' :=
  ancilla_eq_of_undisturbed_probe (bb84State_overlap_ne_zero a a') hψ hφ

/-- **No covert distinguisher for BB84 (Exercise 12.38, security side).** There is no *physical*
eavesdropping probe `U` on `qubit ⊗ A` that both *distinguishes* two cross-basis BB84 signals —
its two possible ancilla outcomes `v, v'` differ, so Eve learns which signal was sent — and
leaves *both* signals undisturbed. Any information gain about the non-orthogonal signals costs a
disturbance Bob detects; so the distinguisher the exercise hypothesises has no unitary
realisation. This is why the attack of `bb84_distinguisher_compromises_security` below is a
*counterfactual*: were such a device available, Eve could read Alice's raw key while inducing no
detectable error, compromising BB84 (and, by the same non-orthogonality argument, every QKD
protocol encoding in non-orthogonal states); its physical impossibility is exactly the
protocol's security. Contrapositive of `bb84_undisturbed_probe_ancilla_eq`. -/
theorem bb84_no_covert_distinguisher (a a' : Fin 2) (u : PureState A)
    (U : Evolution (qubit ⊗ A)) :
    ¬ ∃ v v' : PureState A, v ≠ v' ∧
      U.evolvePure (bb84State a 0 ⊗ u) = bb84State a 0 ⊗ v ∧
      U.evolvePure (bb84State a' 1 ⊗ u) = bb84State a' 1 ⊗ v' := by
  rintro ⟨v, v', hgain, hψ, hφ⟩
  exact hgain (bb84_undisturbed_probe_ancilla_eq hψ hφ)

/-! ### The attack: distinguishing non-orthogonal states breaks BB84

The impossibility results above are the *security* side of Exercise 12.38 — no physical
(unitary-probe) eavesdropper can covertly distinguish the non-orthogonal BB84 signals. The
exercise itself asks for the **forward** direction: *were* the (physically unavailable) ability
to distinguish nevertheless in hand, it would break the protocol. We model that ability
abstractly as a classical read-out `identify` correctly labelling each transmitted signal, and
exhibit the undetectable eavesdropping attack it enables. Being an abstract oracle rather than a
unitary probe, it is not constrained by Proposition 12.18, so the reduction is genuine, not
vacuous. The model is generic in the signal family `signal : ι → PureState S`, so the same
reduction breaks **every** QKD protocol encoding data in a family of signal states. -/

variable {ι : Type*} {S : QSystem} {signal : ι → PureState S}

/-- **The hypothesised ability to distinguish the transmitted states (Exercise 12.38).** A
device that, presented with a transmitted signal `signal i`, returns its classical label `i` —
the counterfactual "ability to distinguish non-orthogonal states". The read-out alone captures
the ability: knowing the classical label, an eavesdropper can re-prepare the identified state
and forward it. Physically no such device exists for non-orthogonal signals
(`bb84_no_covert_distinguisher`, Proposition 12.18); the content of the exercise is what it
*would* enable. -/
structure StateDistinguisher (signal : ι → PureState S) where
  /-- Eve's classical read-out of which signal state was transmitted. -/
  identify : PureState S → ι
  /-- The read-out is correct: it recovers the label of every transmitted signal state. -/
  identify_signal : ∀ i, identify (signal i) = i

/-- **Eve's intercept–resend attack (Exercise 12.38).** Using the distinguisher `D`, Eve reads
the classical label of the intercepted signal and re-prepares — hence forwards to Bob — the
identified state `signal (D.identify ψ)`. -/
def StateDistinguisher.intercept (D : StateDistinguisher signal) (ψ : PureState S) : PureState S :=
  signal (D.identify ψ)

/-- **The intercept–resend attack is undetectable (Exercise 12.38).** Bob receives *exactly* the
state Alice sent, `D.intercept (signal i) = signal i`. Because the forwarded state is identical
to the original, Bob's measurement statistics — and hence the check-bit comparison that would
reveal an eavesdropper — are unchanged: the distinguisher lets Eve evade detection by
reconstructing the state perfectly from its known classical identity. -/
theorem StateDistinguisher.intercept_signal (D : StateDistinguisher signal) (i : ι) :
    D.intercept (signal i) = signal i := by
  rw [StateDistinguisher.intercept, D.identify_signal]

/-- **The intercept–resend attack reveals the transmitted label (Exercise 12.38).** Eve's
read-out recovers the full classical label `i` of the transmitted signal — for BB84 this is
Alice's `(data, basis)` pair, so Eve learns the raw key bit. -/
theorem StateDistinguisher.intercept_reveals (D : StateDistinguisher signal) (i : ι) :
    D.identify (signal i) = i :=
  D.identify_signal i

/-- **The hypothesised distinguisher is a genuine object for any family of *distinct* signal
states (Exercise 12.38).** If the signal states are pairwise distinct — `signal` injective — then
Eve's read-out can be realised as a left inverse of `signal`, so `StateDistinguisher signal` is
inhabited. The obstruction to distinguishing *non-orthogonal quantum* states is therefore not
logical (the abstract oracle is a perfectly good function of distinct states) but **physical**:
it admits no unitary realisation (`bb84_no_covert_distinguisher`, Proposition 12.18). That gap
between "logically definable" and "physically realisable" is exactly the counterfactual force of
the exercise — and since Alice's four BB84 signals are distinct, the reduction below is applied
to a genuinely inhabited hypothesis, not a vacuous one. -/
def StateDistinguisher.ofInjective [Nonempty ι] (h : Function.Injective signal) :
    StateDistinguisher signal where
  identify := Function.invFun signal
  identify_signal := Function.leftInverse_invFun h

/-- **The BB84 signal family** as a map of Alice's `(data, basis)` bits to her encoding state,
`bb84Signal (a, b) = bb84State a b` (N&C eqs. 12.180–12.183). Packaging the four signals as one
family `Fin 2 × Fin 2 → PureState qubit` lets the generic distinguisher reduction apply to
BB84. -/
def bb84Signal (p : Fin 2 × Fin 2) : PureState qubit := bb84State p.1 p.2

/-- **A distinguisher makes BB84 eavesdropping undetectable (Exercise 12.38).** If Eve holds a
distinguisher `D` for Alice's four signal states, then for every `(a, b)` the qubit Bob receives
is exactly `bb84State a b` — Alice's original — so no disturbance is introduced and the check-bit
test cannot reveal Eve. -/
theorem bb84_intercept_undetectable (D : StateDistinguisher bb84Signal) (a b : Fin 2) :
    D.intercept (bb84State a b) = bb84State a b :=
  D.intercept_signal (a, b)

/-- **A distinguisher reveals Alice's key bit (Exercise 12.38).** Eve's read-out on
`bb84State a b` recovers Alice's data bit `a` (indeed the full pair `(a, b)`), so she learns the
raw key. -/
theorem bb84_intercept_reveals_data (D : StateDistinguisher bb84Signal) (a b : Fin 2) :
    (D.identify (bb84State a b)).1 = a :=
  congrArg Prod.fst (D.identify_signal (a, b))

/-- **The ability to distinguish non-orthogonal states compromises BB84 (Exercise 12.38, the
counterfactual headline).** Given the hypothesised distinguisher `D`, for every choice `(a, b)`
of Alice's data and basis bits Eve simultaneously (i) learns Alice's data bit `a` and (ii)
forwards to Bob the *identical* state `bb84State a b`, introducing no detectable disturbance. An
eavesdropper wielding the ability to distinguish non-orthogonal states therefore reads Alice's
raw key while passing the check-bit test — the security of BB84 is compromised. By the
genericity of the reduction in `signal`, the same holds for every QKD protocol encoding in
non-orthogonal states, "and indeed, all of the QKD protocols we have described". That this
ability is physically unavailable (`bb84_no_covert_distinguisher`) is exactly why BB84 is, in
fact, secure. -/
theorem bb84_distinguisher_compromises_security
    (D : StateDistinguisher bb84Signal) (a b : Fin 2) :
    (D.identify (bb84State a b)).1 = a ∧ D.intercept (bb84State a b) = bb84State a b :=
  ⟨bb84_intercept_reveals_data D a b, bb84_intercept_undetectable D a b⟩

end AxQM
