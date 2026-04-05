/-
  Generate lean_constants from the current Lean environment.

  Usage:
    lake env lean library/gen_lean_constants.lean > library/lean_constants

  This extracts all top-level names from Lean's Init library (auto-imported)
  that could conflict with Lem-generated identifiers. The output is used by
  Lem's renaming machinery to avoid name collisions.

  Filtering rules:
  - Skip internal prefixes: inst*, _aux_*, term*, tactic*, stx*, prec*, prio*, command*
  - Skip names with special characters (operators, Unicode symbols)
  - Skip names longer than 30 characters (unlikely in Lem code)
  - Skip lowercase names containing underscores (Lean lemma naming convention)
  - Include Lean 4 keywords (hardcoded, not in the environment)
-/
import Lean

def hasSpecialChar (s : String) : Bool :=
  s.any (fun c => c == '(' || c == '!' || c == '*' || c == '+' ||
                   c == ',' || c == '|' || c == '<' || c == '>' ||
                   c == '[' || c == '{' || c == '?' || c == '\'' ||
                   c.val > 127)

def isLowerWithUnderscore (s : String) : Bool :=
  !s.isEmpty && (s.get ⟨0⟩).isLower && s.toList.any (· == '_')

def hasSkipPrefix (s : String) : Bool :=
  s.startsWith "_aux_" || s.startsWith "inst" || s.startsWith "term" ||
  s.startsWith "tactic" || s.startsWith "stx" || s.startsWith "prec" ||
  s.startsWith "prio" || s.startsWith "command" || s.startsWith "unexpand" ||
  s.startsWith "reduce" || s.startsWith "boolIfThenElse"

-- Lean 4 keywords are not declarations, so they must be listed manually.
def keywords : List String := [
  "def", "theorem", "lemma", "example", "inductive", "structure", "class",
  "instance", "where", "namespace", "section", "open", "import", "variable",
  "universe", "axiom", "noncomputable", "partial", "unsafe", "private",
  "protected", "abbrev", "deriving", "match", "with", "let", "have", "show",
  "by", "do", "return", "if", "then", "else", "for", "in", "fun", "sorry",
  "Prop", "Type", "Sort", "true", "false", "calc", "suffices", "assume",
  "this", "extends", "opaque", "mutual", "notation", "macro", "syntax",
  "set_option", "attribute", "export", "end", "rec", "scoped", "local",
  "nomatch", "nofun", "infix", "infixl", "infixr", "prefix", "postfix",
  "where"
]

open Lean in
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {}
  let namesRef ← IO.mkRef (Array.empty : Array String)
  env.constants.map₁.forM fun name _ => do
    match name with
    | .str .anonymous s =>
      if !hasSkipPrefix s && !hasSpecialChar s && s.length ≤ 30 && !isLowerWithUnderscore s then
        namesRef.modify (·.push s)
    | _ => pure ()
  let names ← namesRef.get
  let envNames := names.toList.mergeSort (· < ·) |>.eraseDups
  let allNames := (keywords ++ envNames).mergeSort (· < ·) |>.eraseDups
  let stdout ← IO.getStdout
  for n in allNames do
    stdout.putStrLn n
