import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "8b36beaad4bfbdbc36285e5df5e95964af6b2545"

/-- Mathlib's build options, so `ToMathlib` stays upstreamable. -/
abbrev mathlibOptions : Array LeanOption := #[
  ⟨`pp.unicode.fun, true⟩,
  ⟨`autoImplicit, false⟩,
  ⟨`maxSynthPendingDepth, .ofNat 3⟩,
  ⟨`weak.linter.mathlibStandardSet, true⟩,
  ⟨`weak.linter.style.longFile, .ofNat 1500⟩
]

package axqm

/-- General mathematics this library adds to Mathlib, awaiting upstreaming. -/
@[default_target]
lean_lib ToMathlib where
  leanOptions := mathlibOptions

/-- The Nielsen & Chuang formalization, grounded in postulate primitives. -/
@[default_target]
lean_lib AxQM where
  leanOptions := mathlibOptions
  -- Its files are not modules; Mathlib's `requiresModuleSystem` would warn on each import.
  allowNonModules := true
