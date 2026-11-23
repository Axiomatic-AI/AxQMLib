/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Topology.Order.OrderClosed

/-!
# Monotonicity/antitonicity passes through pointwise limits

Extends `Mathlib.Topology.Order.OrderClosed` with lemmas transporting (eventual)
monotonicity/antitonicity of a family of functions through a pointwise limit.
-/

public section

variable {α : Type*} {β : Type*} [TopologicalSpace α] [Preorder α] [OrderClosedTopology α]

section Preorder

/-- If a family of functions converges pointwise on `s` to `f`, and the family is eventually
monotone on `s`, then `f` is monotone on `s`. -/
theorem MonotoneOn.of_tendsto_pointwise_on {ι : Type*} {l : Filter ι} [l.NeBot]
    [Preorder β] {s : Set β} {F : ι → β → α} {f : β → α}
    (h_eventually : ∀ᶠ n in l, MonotoneOn (F n) s)
    (h_tendsto : ∀ x ∈ s, Filter.Tendsto (F · x) l (nhds (f x))) :
    MonotoneOn f s :=
  fun _ hx _ hy hxy ↦ le_of_tendsto_of_tendsto (h_tendsto _ hx) (h_tendsto _ hy)
    (h_eventually.mono fun _ hn ↦ hn hx hy hxy)

/-- If a family of functions converges pointwise to `f`, and the family is eventually monotone,
then `f` is monotone. -/
theorem Monotone.of_tendsto_pointwise {ι : Type*} {l : Filter ι} [l.NeBot]
    [Preorder β] {F : ι → β → α} {f : β → α}
    (h_eventually : ∀ᶠ n in l, Monotone (F n))
    (h_tendsto : ∀ x, Filter.Tendsto (F · x) l (nhds (f x))) :
    Monotone f :=
  monotoneOn_univ.mp <| .of_tendsto_pointwise_on
    (h_eventually.mono fun _ hn ↦ hn.monotoneOn _) fun x _ ↦ h_tendsto x

/-- If a family of functions converges pointwise on `s` to `f`, and the family is eventually
antitone on `s`, then `f` is antitone on `s`. -/
theorem AntitoneOn.of_tendsto_pointwise_on {ι : Type*} {l : Filter ι} [l.NeBot]
    [Preorder β] {s : Set β} {F : ι → β → α} {f : β → α}
    (h_eventually : ∀ᶠ n in l, AntitoneOn (F n) s)
    (h_tendsto : ∀ x ∈ s, Filter.Tendsto (F · x) l (nhds (f x))) :
    AntitoneOn f s :=
  MonotoneOn.of_tendsto_pointwise_on (α := αᵒᵈ) h_eventually h_tendsto

/-- If a family of functions converges pointwise to `f`, and the family is eventually antitone,
then `f` is antitone. -/
theorem Antitone.of_tendsto_pointwise {ι : Type*} {l : Filter ι} [l.NeBot]
    [Preorder β] {F : ι → β → α} {f : β → α}
    (h_eventually : ∀ᶠ n in l, Antitone (F n))
    (h_tendsto : ∀ x, Filter.Tendsto (F · x) l (nhds (f x))) :
    Antitone f :=
  Monotone.of_tendsto_pointwise (α := αᵒᵈ) h_eventually h_tendsto

end Preorder
