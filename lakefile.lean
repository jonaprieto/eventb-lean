import Lake
open Lake DSL

package «eventb» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- Pinned by SHA, not `main`: corpus gate numbers are only reproducible if the
-- parser underneath them is too.
require grip from git
  "https://github.com/jonaprieto/lean-grip" @ "17bed154d8188650bf8dd458ec44385ce72d6ba4"

require argus from git
  "https://github.com/jonaprieto/lean-argus.git" @ "d1db1a027768d42fbf16e6198efcb404d126dcee"

require «termcolor-diagnostics» from git
  "https://github.com/jonaprieto/lean-termcolor-diagnostics.git"
  @ "dd016af716eece82535fbfd082522dbe1c5478e4"

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
