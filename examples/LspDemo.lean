/- A compile-time regression fixture for native Event-B source locations. -/
import EventB.DSL

open Lean Elab Command

eventb_theory LspTheory where
  constant LIMIT : ℤ

eventb_context LspContext where
  uses LspTheory
  constants cars
  axiom bounded : cars < LIMIT
  axiom boolean : TRUE = TRUE

private def symbolName (owner symbol : String) : Name :=
  Name.mkSimple ("EventB.DSL.symbol." ++ owner ++ "." ++ symbol)

private def requireRange (owner symbol : String) : CommandElabM Unit := do
  unless (← Lean.findDeclarationRanges? (symbolName owner symbol)).isSome do
    throwError s!"missing native Event-B source range for `{owner}.{symbol}`"

syntax (name := eventbLspChecks) "#eventb_lsp_checks" : command

@[command_elab eventbLspChecks]
private def elabLspChecks : CommandElab := fun stx =>
  match stx with
  | `(command| #eventb_lsp_checks) => do
      requireRange "LspTheory" "LIMIT"
      requireRange "LspContext" "cars"
  | _ => throwUnsupportedSyntax

#eventb_lsp_checks
