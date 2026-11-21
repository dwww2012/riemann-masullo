import Lean
open Lean Parser

/-!
Prints the tokens that can begin a command in the environment of the given modules, one per
line as `command <token>`, and after them one line `tail <text>` for every token that ends in
letters, digits or `_` after some other character (Lean can split a word right after such a
token, so `≤idef` is `≤i` followed by the keyword `def`).

`scripts/ci/plain_proof.py` reads the list (`scripts/ci/command_keywords.txt`) to decide which
commands a pull request touches without running Lean. `scripts/ci/keywords.sh --check` compares
the list with what this prints, and fails if the checked-in list is out of date.

The program stops with an error if the parser stops satisfying what `plain_proof.py` relies on:
every command begins with a fixed token, `in` is the only token that continues a command, and no
token contains a space, a double quote, a French quote or a comment delimiter (two hyphens, or a
hyphen next to a slash), apart from the two tokens that open a doc comment.

    lake env lean --run scripts/ci/CommandKeywords.lean RiemannMasullo.AppA_AlgebraicNT.Sec1 ...
-/

def wordChar (c : Char) : Bool := c.isAlphanum && c.toNat < 128 || c == '_'

/-- The longest suffix of letters, digits and `_`, when it is a proper, non-empty suffix. -/
def tail? (t : String) : Option String :=
  let cs := t.toList.reverse.takeWhile wordChar |>.reverse
  if cs.isEmpty || cs.length == t.length then none else some (String.ofList cs)

unsafe def main (args : List String) : IO UInt32 := do
  -- Syntax extensions are only loaded when initializers run; every module given is ours or a
  -- dependency's, already built.
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let modules := args.toArray.map (·.toName)
  let env ← importModules (modules.map ({ module := · })) {} (trustLevel := 1024) (loadExts := true)
  let state := parserExtension.getState env
  let some cat := state.categories.find? `command
    | throw <| IO.userError "no `command` syntax category"
  let leading := cat.tables.leadingTable.toList.map (·.1.toString (escape := false))
  let trailing := cat.tables.trailingTable.toList.map (·.1.toString (escape := false))
  let tokens := state.tokens.findPrefix ""
  let mut problems : Array String := #[]
  unless cat.tables.leadingParsers.isEmpty do
    problems := problems.push "a command parser does not begin with a fixed token"
  unless cat.tables.trailingParsers.isEmpty && trailing == ["in"] do
    problems := problems.push s!"commands can be continued by tokens other than `in`: {trailing}"
  for t in tokens do
    if t.contains ' ' || t.contains '"' || t.contains '«' then
      problems := problems.push s!"token with a space, quote or «: {t}"
    if (t.splitOn "--").length > 1 && t != "/--" then
      problems := problems.push s!"token containing --: {t}"
    if (t.splitOn "-/").length > 1 then
      problems := problems.push s!"token containing -/: {t}"
    if (t.splitOn "/-").length > 1 && t != "/--" && t != "/-!" then
      problems := problems.push s!"token containing /-: {t}"
  unless problems.isEmpty do
    for p in problems do IO.eprintln s!"CommandKeywords: {p}"
    IO.eprintln "CommandKeywords: scripts/ci/plain_proof.py relies on these not happening; \
      it has to be revisited before the list is regenerated"
    return 1
  for t in leading.toArray.qsort (· < ·) do
    IO.println s!"command {t}"
  let tails := tokens.filterMap tail? |>.qsort (· < ·)
  let mut last := ""
  for t in tails do
    if t != last then IO.println s!"tail {t}"
    last := t
  return 0
