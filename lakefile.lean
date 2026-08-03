import Lake
open Lake DSL

package «eventb» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- Pinned by SHA, not `main`: corpus gate numbers are only reproducible if the
-- parser underneath them is too.
require grip from git
  "https://github.com/jonaprieto/lean-grip" @ "00e7a251cdceb39c3c0b12d91b0f66e923e1c724"

require argus from git
  "https://github.com/jonaprieto/lean-argus.git" @ "13f6936ead5d8774c5619b356ac5d8d847ec0cc4"

require «termcolor-diagnostics» from git
  "https://github.com/jonaprieto/lean-termcolor-diagnostics.git"
  @ "9d5285a793fcad9d2ec0e14ebcd000b4d47ec488"

require "leanprover-community" / "proofwidgets" @ git "v0.0.87"

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
