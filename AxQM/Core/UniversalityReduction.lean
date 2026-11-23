/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
import AxQM.Postulates.Evolution

/-!
# The universality-reduction principle

Nielsen & Chuang's universality arguments repeatedly take the shape *"gate family `𝒢` is already
universal; a new resource can perform every gate of `𝒢`; therefore the new resource is universal"*.
This is the reduction behind **Problem 4.6** (a resource of single-qubit unitaries, Bell-basis
measurements and four-qubit state preparation performing `CNOT` and single-qubit gates), Exercise
7.52 (`√SWAP` with single-qubit gates performing `CNOT`), and every "complete the gate set" argument
in §4.5. This file isolates that reduction as one reusable theorem, independent of *which* resource,
gate family, or register is in play.

"Universality of a family `IsGenerator` on a register `S`" is expressed in the library's standard
list-decomposition form (the shape of `linearOptics_universal`): every `E : Evolution S` is a finite
ordered product `L.prod` of gates each satisfying `IsGenerator`. "A resource *realizes* `U`" is
modelled by an arbitrary predicate `Realizes` that contains the identity and is closed under
composition — the algebraic shell shared by every concrete notion of deterministic implementation (a
single available gate, a measurement-based gadget, a whole circuit). The reduction then says: a
resource that realizes each generator of a universal family realizes *every* evolution.

## What is formalised

* `Evolution.realizes_of_universal` — the reduction in predicate form: if `Realizes 1`, `Realizes`
  is closed under `Evolution.comp`, and every `IsGenerator` gate is realized, then every evolution
  of a universal family is realized.
* `Evolution.submonoid_eq_top_of_universal` — the `Submonoid` phrasing: a submonoid of `Evolution S`
  containing a universal generating family is `⊤` (all evolutions).

## Design notes

* The `Realizes` predicate is deliberately abstract. A concrete universality result supplies the
  register `S`, the generating family `IsGenerator`, and the realizability notion `Realizes`, then
  discharges the three hypotheses. For Problem 4.6, the `hgen` obligation splits into: single-qubit
  generators, realized by direct application (resource #1); and the `CNOT` generator, realized by
  the gate-teleportation gadget
  (`bellPairsMeasurement_corrected_reducedRight_gateTeleportResourceRegister`). `hUniversal` is
  N&C's *given* that `{CNOT, single-qubit}` is a universal gate set.
-/

namespace AxQM

variable {S : QSystem}

/-- **The universality reduction (predicate form).** Let `Realizes` be a predicate on `Evolution S`
that holds for the identity (`hone`) and is closed under composition (`hcomp`) — the algebraic shape
of "the resource can deterministically perform this unitary operation". If the resource realizes
every gate of a family `IsGenerator` (`hgen`), and that family is *universal* — every evolution is a
finite ordered product of its gates (`hUniversal`, the library's `linearOptics_universal`-style
statement) — then the resource realizes **every** evolution `E`.

This is the logical core of "adding the missing gate makes a set universal": one instantiates
`IsGenerator` with `{CNOT, single-qubit gates}` (universal by hypothesis, N&C's given) and shows the
new resource realizes each — whence, by this theorem, it realizes all of `U(S)`. The proof feeds
the decomposition into `List.prod_induction`: the empty product is the identity (`hone`) and each
factor, realized by `hgen`, is folded in by `hcomp`. -/
theorem Evolution.realizes_of_universal
    {Realizes : Evolution S → Prop} {IsGenerator : Evolution S → Prop}
    (hone : Realizes 1)
    (hcomp : ∀ {U V : Evolution S}, Realizes U → Realizes V → Realizes (U.comp V))
    (hgen : ∀ V : Evolution S, IsGenerator V → Realizes V)
    (hUniversal : ∀ E : Evolution S,
        ∃ L : List (Evolution S), (∀ V ∈ L, IsGenerator V) ∧ L.prod = E)
    (E : Evolution S) : Realizes E := by
  obtain ⟨L, hL, rfl⟩ := hUniversal E
  exact List.prod_induction Realizes (fun _ _ => hcomp) hone fun V hV => hgen V (hL V hV)

/-- **The universality reduction (submonoid form).** If a submonoid `M` of the evolution monoid
`Evolution S` contains every gate of a universal generating family `IsGenerator` (`hgen`; universal
via `hUniversal`), then `M = ⊤`: it contains every evolution. This is `realizes_of_universal`
specialised to `Realizes := (· ∈ M)`, whose `hone`/`hcomp` are `M.one_mem`/`M.mul_mem`. Use it when
the realizable operations are literally the circuits over a gate family (their `Submonoid.closure`),
so "universal" reads as "the closure is everything". -/
theorem Evolution.submonoid_eq_top_of_universal
    {M : Submonoid (Evolution S)} {IsGenerator : Evolution S → Prop}
    (hgen : ∀ V : Evolution S, IsGenerator V → V ∈ M)
    (hUniversal : ∀ E : Evolution S,
        ∃ L : List (Evolution S), (∀ V ∈ L, IsGenerator V) ∧ L.prod = E) :
    M = ⊤ := by
  rw [eq_top_iff]
  intro E _
  exact Evolution.realizes_of_universal M.one_mem M.mul_mem hgen hUniversal E

end AxQM
