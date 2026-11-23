/-
Copyright (c) 2026 Axiomatic_AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin, Frank Koppens
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Constant families converge locally uniformly

A constant family of functions converges locally uniformly to that constant function.
-/

@[expose] public section

open Topology Uniformity Filter Set Uniform

variable {α β ι : Type*} [TopologicalSpace α] [UniformSpace β]
variable {s : Set α} {p : Filter ι}

/-- A constant family of functions `fun _ ↦ h` converges locally uniformly to `h` on any set. -/
theorem tendstoLocallyUniformlyOn_const_fn (h : α → β) :
    TendstoLocallyUniformlyOn (fun _ : ι => h) h p s :=
  fun _u hu _x _hx ↦ ⟨s, self_mem_nhdsWithin,
    .of_forall fun _ _ _ ↦ refl_mem_uniformity hu⟩

/-- A constant family of functions `fun _ ↦ h` converges locally uniformly to `h`. -/
theorem tendstoLocallyUniformly_const_fn (h : α → β) :
    TendstoLocallyUniformly (fun _ : ι => h) h p :=
  tendstoLocallyUniformlyOn_univ.mp <| tendstoLocallyUniformlyOn_const_fn h
