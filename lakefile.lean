import Lake
open Lake DSL

package «eventb» where
  version := v!"4.0.2"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- Pinned release tags, not `main`: corpus gate numbers are only reproducible if the
-- parser underneath them is too.
require grip from git
  "https://github.com/jonaprieto/lean-grip" @ "v0.1.0"

require argus from git
  "https://github.com/jonaprieto/lean-argus.git" @ "v0.4.6"

require «termcolor-diagnostics» from git
  "https://github.com/jonaprieto/lean-termcolor-diagnostics.git"
  @ "v0.1.9"

require "leanprover-community" / "proofwidgets" @ git "v0.0.105"

@[default_target]
lean_lib «EventB» where
  -- Build every module under EventB/, so no submodule can hide unbuilt.
  globs := #[.andSubmodules `EventB]

lean_lib «EventBWidgets» where
  globs := #[.one `Widgets]

/-- The ratchet. `lake exe gates` diffs the corpus against `baseline/*.tsv`. -/
lean_lib «Examples» where
  srcDir := "examples"
  globs := #[.one `Counter, .one `BookBridge, .one `BookSystems, .one `BookPrograms,
    .one `WidgetDemo, .one `TheoryDemo, .one `TranslateDemo, .one `TheoryValidateDemo,
    .one `RodinTheoryDemo, .one `TheoryEmbedDemo, .one `TrustRodinDemo,
    .one `RossiDemo, .one `RossiBoundaryDemo, .one `LspDemo, .one `ProverDemo]

lean_exe «gates» where
  root := `Gates
  srcDir := "test"

lean_exe «rossi-dump» where
  root := `RossiDump
  srcDir := "test"

lean_exe «bench» where
  root := `Bench
  srcDir := "bench"

-- Spike tooling: dumps parsed formulas as JSON so the discharge experiment works from
-- the real parser rather than a second implementation of it.
lean_exe «astdump» where
  root := `AstDump
  srcDir := "spike/tools"

lean_exe «showpo» where
  root := `ShowPO
  srcDir := "spike/tools"

lean_exe «eventb» where
  root := `Cli
  srcDir := "cli"
