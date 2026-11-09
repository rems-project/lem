/-
  Generate lean_constants from the current Lean environment.

  Usage (the committed file is the UNION over every toolchain the output
  has been built with — names a later toolchain dropped are KEPT, so the
  rename pass stays stable and generated output does not change at a bump;
  run under the current `lean-lib/lean-toolchain` and ADD the names new to
  it; a root name present in any of them must be avoided):
    cd lean-lib && lake env lean --run ../library/gen_lean_constants.lean
    ~/.elan/bin/lean +leanprover/lean4:v4.35.0 --run library/gen_lean_constants.lean
  2026-10-21 (4.35.0): 2 new root names (`Erased`, `repeatM`) and 2 new
  tokens (`monotonicity_by`, `recall`, from scripts/lean_keyword_probe.sh);
  117 committed names are absent from 4.35.0's Init and kept.

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
  !s.isEmpty && s.front.isLower && s.toList.any (· == '_')

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
  -- contextual / newer tokens and root names the environment walk does not
  -- surface (parity-fix slice 2026-09-03, F8): `from`, `termination_by`,
  -- `decreasing_by`, `elab` are Lean 4 tokens that cannot head a `def`;
  -- `main` is checked by Lean for the entry-point type wherever it is
  -- declared; the rest were hand-added to lean_constants before this
  -- generator carried them and are kept so regeneration is reproducible.
  "at", "from", "termination_by", "decreasing_by", "elab", "main", "omit",
  "unless", "break", "continue", "try", "catch", "finally", "nonrec",
  "public", "meta", "coinductive", "forall", "admit", "decide", "default",
  "none", "some", "pure", "bind", "get", "set", "throw", "run", "mapM",
  "macro_rules", "elab_rules", "initialize", "builtin_initialize",
  "declare_syntax_cat", "register_option", "include", "exposed"
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
