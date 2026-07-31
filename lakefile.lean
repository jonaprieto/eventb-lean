import Lake
open Lake DSL

package «eventb» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- Pinned by SHA, not `main`: corpus gate numbers are only reproducible if the
-- parser underneath them is too.
require grip from git
  "https://github.com/jonaprieto/grip" @ "8413dc0c14afcdda2578dc3da0acc3cabe0b85c3"

@[default_target]
lean_lib «EventB» where
  -- Build every module under EventB/, so no submodule can hide unbuilt.
  globs := #[.andSubmodules `EventB]

/-- The ratchet. `lake exe gates` diffs the corpus against `baseline/*.tsv`. -/
lean_exe «gates» where
  root := `Gates
  srcDir := "test"

lean_exe «bench» where
  root := `Bench
  srcDir := "bench"

-- Spike tooling: dumps parsed formulas as JSON so the discharge experiment works from
-- the real parser rather than a second implementation of it.
lean_exe «astdump» where
  root := `AstDump
  srcDir := "spike/tools"
