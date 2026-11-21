#!/usr/bin/env python3
"""Decide, from the text alone, whether a change to a Lean file touches only theorems.

    scripts/ci/plain_proof.py OLD.lean NEW.lean    prints the reasons it is not; status 1 if any

A pull request can be merged without being read only if all it does is fill in proofs and add
lemmas. This decides that without running Lean, so that the same answer can be computed twice:
by the pull request check before it builds anything, and again by the workflow that merges,
from file contents fetched through the GitHub API. It must not be fooled, so it is deliberately
crude and errs towards "a human should read this".

How it works. Every Lean command begins with one of a fixed set of tokens (`theorem`, `def`,
`variable`, `open`, `notation`, `#eval`, `@[`, ...), listed in command_keywords.txt, which is
generated from Lean's own parser tables by keywords.sh. The file is cut at every place such a
token occurs, and each piece is named after the token that starts it. A change is plain when

  * every line it adds or removes lies in a piece that starts with `theorem` or `lemma`
    (optionally `private`, `protected` or `nonrec`, a doc comment, and lines of the form
    `open ... in`, `omit ... in`, `include ... in`, `set_option linter.x false in` before it),
    or is an `import` of a Mathlib or library module;
  * every line it leaves alone still lies in a piece of the same kind, and is still a comment
    exactly where it was one;
  * the added lines contain no `sorry`, none of the constructs in `DANGEROUS` or `EYES`, no
    citation of the paper, and (outside ForMathlib/) no new declaration that is not `private`.
    These last rules are those of scripts/proof_review.sh.

So a line slipped into a `variable` block, a second command put on the same line as a proof,
a comment opened or closed around existing text, or a `def` renamed `private def` all count as
not plain. Whether an existing statement changed is not decided here: that needs the build
(scripts/signatures.sh).

Text is treated as a comment, and ignored, only where it is one whatever came before it:

  * from `--` to the end of the line, when `--` follows a space or starts the line and the line
    has no `"` and no `-/`;
  * a block comment that opens at the start of a line and has no `"` in it, up to the `-/`
    that closes it. A doc comment (`/--`) still counts as the beginning of the command after it.

Anything else, including a comment this does not recognize and the inside of a string, is read
as code. That only ever makes the answer stricter.

Two things are assumed about the project, and verdict.py checks both on main before it trusts
this: command_keywords.txt is current, and the option `doc.verso` is not in use (with it, Lean
elaborates code written inside doc comments, so a comment would no longer be inert).
"""
import difflib
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

THEOREM = {"theorem", "lemma"}
# Tokens that begin a command only as a prefix of the keyword after them.
MODIFIERS = {"private", "protected", "nonrec", "partial", "local", "scoped"}
THEOREM_MODIFIERS = {"private", "protected", "nonrec"}
# `?` begins only `binder_predicate`, `$` only an antiquotation; both are everywhere in proofs.
IGNORED = {"?", "$"}
SCOPED_BY_IN = {"open", "omit", "include"}

WORD = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_")
ID_REST = WORD | set("'!?")
IDENT = r"[A-Za-z_][A-Za-z0-9_.']*"

# Constructs that run code when the file is built, or that weaken what the kernel checks. They
# are looked for anywhere in an added line, comments included.
DANGEROUS = re.compile(
    r"eval%|elabToSyntax%|private_decl%|by_elab|run_tac|run_cmd|run_elab|run_meta|from_lrat"
    r"|native_decide|bv_decide|ofReduceBool|reduceBool|trustCompiler|implemented_by|extern"
    r"|skipKernelTC|sorryAx|debug\.|(?<![A-Za-z0-9_])(?:unsafe|Lean|Elab|Meta|IO|System)(?![A-Za-z0-9_])")
# Other ways of leaving a proof unfinished.
UNFINISHED = re.compile(r"(?<![A-Za-z0-9_.'])(?:sorry|admit|stop)(?![A-Za-z0-9_'])")
# What scripts/proof_review.sh looks for in added lines (there with a leading `+`), repeated
# here because the workflow that merges has only the text to go by: its `eyes` and `routine`
# patterns, the citation of the paper, and the names of new declarations. (verdict.py also
# runs proof_review.sh itself, so a rule added there holds a pull request back at once.)
EYES = re.compile(
    r"^[ \t]*(#|@\[|open Lean|attribute|macro|syntax|notation|elab|initialize"
    r"|unsafe|instance|def |abbrev |structure|class |inductive|axiom|opaque|noncomputable)"
    r"|run_|by_elab|simproc|Lean\.|Elab|Meta\.|IO\.|extern|implemented_by|native"
    r"|^[ \t]*(import|set_option) ")
# Importing Mathlib or this library, and silencing a linter for one command, are routine.
ROUTINE_IMPORT = re.compile(r"[ \t]*(public )?import (Mathlib|RiemannMasullo)\.[A-Za-z0-9_.]+[ \t]*")
ROUTINE_OPTION = re.compile(r"[ \t]*set_option linter\.[A-Za-z0-9_.]+ (true|false) in[ \t]*")
DECLARATION = re.compile(
    r"\s*(@\[[^\]]*\]\s*)*((public|protected|noncomputable|nonrec|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+")

# A Lean file of the library that is not vendored code. Plain ASCII names only, so that the path
# is also a module name and can be shown and compared without care.
LIBRARY_FILE = re.compile(r"RiemannMasullo(/[A-Za-z0-9_]+)*/[A-Za-z0-9_]+\.lean")
MAX_FILE_BYTES = 4 * 1024 * 1024


def library_file(path):
    return bool(LIBRARY_FILE.fullmatch(path)) and not path.startswith("RiemannMasullo/External/")


def load_keywords(path=None):
    """The tokens that can begin a command, and the word endings of other tokens."""
    commands, tails = set(), set()
    text = (path or HERE / "command_keywords.txt").read_text(encoding="utf-8")
    for line in text.split("\n"):
        if line.startswith("command "):
            commands.add(line[len("command "):])
        elif line.startswith("tail "):
            tails.add(line[len("tail "):])
    if not {"theorem", "def", "variable", "open", "@[", "/--"} <= commands:
        raise ValueError("command_keywords.txt is missing or incomplete")
    return commands, tails


class Scanner:
    def __init__(self, keywords=None):
        self.commands, self.tails = keywords or load_keywords()
        self.by_first = {}
        for token in self.commands:
            if token in ("/--", "/-!"):
                continue  # comment openers are handled with the comments
            self.by_first.setdefault(token[0], []).append(token)
        for tokens in self.by_first.values():
            tokens.sort(key=len, reverse=True)

    # -- comments ---------------------------------------------------------------------------

    def strip_comments(self, lines):
        """The lines with recognized comments blanked out, and where doc comments begin.

        Returns (code, docs): `code[i]` has the length of `lines[i]`; `docs` lists
        (line, column, kind) for each recognized block comment opened by `/--` or `/-!`.
        """
        code, docs = [], []
        depth = 0  # inside a recognized block comment
        for n, line in enumerate(lines):
            out = []
            i = 0
            if depth == 0 and re.match(r"[ \t]*/-", line) and self._block_has_no_quote(lines, n):
                i = line.index("/-")
                out.append(" " * i)
                opener = line[i:i + 3]
                if opener in ("/--", "/-!"):
                    docs.append((n, i, opener))
                depth = 1
                out.append("  ")
                i += 2
            while depth > 0 and i < len(line):
                two = line[i:i + 2]
                if two == "-/":
                    depth -= 1
                    out.append("  ")
                    i += 2
                elif two == "/-":
                    depth += 1
                    out.append("  ")
                    i += 2
                else:
                    out.append(" ")
                    i += 1
            if depth == 0 and i < len(line):
                out.append(self._strip_line_comment(line[i:], whole_line=(i == 0)))
            code.append("".join(out))
        return code, docs

    @staticmethod
    def _block_has_no_quote(lines, n):
        """Whether the block comment opening at the start of line n closes, with no `"` inside."""
        depth = 0
        start = lines[n].index("/-")
        for m in range(n, len(lines)):
            line = lines[m]
            i = start if m == n else 0
            while i < len(line):
                two = line[i:i + 2]
                if two == "-/" and depth > 0:
                    depth -= 1
                    i += 2
                    if depth == 0:
                        return True
                elif two == "/-":
                    depth += 1
                    i += 2
                elif line[i] == '"':
                    return False
                else:
                    i += 1
        return False  # never closed

    @staticmethod
    def _strip_line_comment(text, whole_line):
        """`text` with a trailing `--` comment blanked, when it is certainly one."""
        if '"' in text or "-/" in text:
            return text
        at = text.find("--")
        while at != -1:
            before = text[:at]
            if "«" in before:
                return text
            if before.strip(" \t") == "" and whole_line or (at > 0 and text[at - 1] in " \t"):
                return before + " " * (len(text) - at)
            at = text.find("--", at + 1)
        return text

    # -- tokens -----------------------------------------------------------------------------

    def tokens(self, code_line):
        """Command tokens in one line of code: a list of (start, end, token)."""
        found = []
        s = code_line
        i = 0
        while i < len(s):
            c = s[i]
            match = None
            for token in self.by_first.get(c, ()):
                if s.startswith(token, i) and self._is_token(s, i, token):
                    match = token
                    break
            if match:
                found.append((i, i + len(match), match))
                i += len(match)
            else:
                i += 1
        return found

    def _is_token(self, s, i, token):
        if token[0] not in WORD or token[0].isdigit():
            return True  # `#eval`, `@[`: Lean takes the longest token, whatever surrounds it
        end = i + len(token)
        if token[-1] in ID_REST and end < len(s) and s[end] in ID_REST:
            return False  # part of a longer identifier
        a = i
        while a > 0 and s[a - 1] in WORD:
            a -= 1
        before = s[a:i]
        # `xdef` is one identifier, but `0x1Fdef` is a number then `def`, and `≤idef` is the
        # token `≤i` then `def`. After anything else (a space, a bracket, a quote, a dot) the
        # word stands alone, or near enough.
        return before == "" or before[0].isdigit() or before in self.tails

    @staticmethod
    def _top_level_words(text):
        """`text` split at white space outside brackets, or None if the brackets do not match."""
        if '"' in text:
            return None
        words, word, depth = [], "", 0
        for c in text:
            if c in "([{⟨":
                depth += 1
            elif c in ")]}⟩":
                depth -= 1
                if depth < 0:
                    return None
            if c.isspace() and depth == 0:
                if word:
                    words.append(word)
                word = ""
            else:
                word += c
        if depth != 0:
            return None
        return words + ([word] if word else [])

    @classmethod
    def scoped_prefix(cls, text):
        """Whether the text is exactly `open ... in`, `omit ... in` or `include ... in`.

        Such a line changes what is in scope for the one command after it, and nothing else. The
        closing `in` has to stand outside every bracket, or it could belong to a term inside
        one and leave the `open` or `omit` in force for the rest of the file.
        """
        words = cls._top_level_words(text)
        if not words or len(words) < 3 or words[-1] != "in" or "in" in words[1:-1]:
            return False
        head, items = words[0], words[1:-1]
        name = re.compile(r"[^\W\d][\w.']*")
        if head == "open":
            if items[0] == "scoped":
                items = items[1:]
            return bool(items) and all(name.fullmatch(w) for w in items)
        if head == "include":
            return all(name.fullmatch(w) for w in items)
        if head == "omit":
            return all(name.fullmatch(w) or (w[0] == "[" and w[-1] == "]") for w in items)
        return False

    # -- pieces -----------------------------------------------------------------------------

    def analyse(self, text):
        """Per line: its code, the kinds of the pieces its code lies in, and line-level flags."""
        lines = text.split("\n")
        code, docs = self.strip_comments(lines)
        events = []   # (line, column, end line, end column, token, class)
        flags = [set() for _ in lines]
        row_tokens = [[t for t in self.tokens(row) if t[2] not in IGNORED] for row in code]
        n = 0
        while n < len(code):
            row, toks = code[n], row_tokens[n]
            if "/-" in row or "-/" in row:
                flags[n].add("a comment delimiter this check does not follow")
            if toks and toks[0][2] in SCOPED_BY_IN and row[:toks[0][0]].strip(" \t") == "" \
                    and all(t[2] == "scoped" for t in toks[1:]):
                # `open ... in`, possibly over a few lines that hold no other keyword
                last, text = n, row
                while not self.scoped_prefix(text) and last - n < 8 and last + 1 < len(code) \
                        and not row_tokens[last + 1] and "/-" not in code[last + 1] and "-/" not in code[last + 1]:
                    last += 1
                    text += "\n" + code[last]
                if self.scoped_prefix(text):
                    events.append((n, toks[0][0], last, len(code[last]), toks[0][2] + " ... in", "scoped"))
                    n = last + 1
                    continue
            if len(toks) == 1 and toks[0][2] == "set_option" and ROUTINE_OPTION.fullmatch(row):
                events.append((n, toks[0][0], n, len(row), "set_option linter ... in", "scoped"))
                n += 1
                continue
            for start, end, token in toks:
                if token in THEOREM:
                    lead = row[:start].split()
                    cls = "theorem" if all(w in THEOREM_MODIFIERS for w in lead) else "other"
                    name = token if cls == "theorem" else token + " (not at the start of a line)"
                    events.append((n, start, n, end, name, cls))
                elif token in MODIFIERS:
                    events.append((n, start, n, end, token, "modifier"))
                else:
                    events.append((n, start, n, end, token, "other"))
            n += 1
        for n, col, opener in docs:
            if opener == "/--":
                # The comment is blank in `code`; what follows it begins right after.
                events.append((n, col, n, col, "doc comment", "doc"))
            else:
                events.append((n, col, n, col, "module doc comment", "other"))
        events.sort()

        def blank_between(a, b):
            """Whether there is only white space in the code from position a to position b."""
            (ln, col), (ln2, col2) = a, b
            if ln == ln2:
                return code[ln][col:col2].strip(" \t") == ""
            if code[ln][col:].strip(" \t") or code[ln2][:col2].strip(" \t"):
                return False
            return all(code[m].strip(" \t") == "" for m in range(ln + 1, ln2))

        pieces = []    # (line, column, kind), in order
        chain = []     # prefix tokens waiting for the keyword they belong to
        chain_end = None

        def drop_chain():
            # The prefixes were followed by something other than a command keyword.
            for n, col, _last, _end, token, cls in chain:
                if cls == "doc":
                    pieces.append((n, col, "a doc comment with no declaration after it"))
                elif cls == "modifier":
                    flags[n].add(f"`{token}` with no command keyword after it")
                # `open ... in` inside a proof scopes a term or a tactic, and changes nothing.
            chain.clear()

        for event in events:
            n, col, last, end, token, cls = event
            if chain and not blank_between(chain_end, (n, col)):
                drop_chain()
            if cls in ("modifier", "doc", "scoped"):
                chain.append(event)
                chain_end = (last, end)
                continue
            start = (chain[0][0], chain[0][1]) if chain else (n, col)
            chain.clear()
            pieces.append((start[0], start[1], "theorem" if cls == "theorem" else f"`{token}`"))
        drop_chain()
        pieces.sort()

        kinds = []
        current = "the start of the file"
        k = 0
        for n, row in enumerate(code):
            here = set()
            col = 0
            while k < len(pieces) and pieces[k][0] == n:
                if row[col:pieces[k][1]].strip(" \t"):
                    here.add(current)
                col = pieces[k][1]
                current = pieces[k][2]
                k += 1
            if row[col:].strip(" \t"):
                here.add(current)
            kinds.append(frozenset(here))
        return lines, code, kinds, flags


def classify(old, new, scanner=None):
    """Reasons the change from `old` to `new` (bytes) is not a plain proof, as (kind, detail).

    `kind` is "sorry" for an added `sorry`, otherwise "text".
    """
    scanner = scanner or Scanner()
    try:
        old_text, new_text = old.decode("utf-8"), new.decode("utf-8")
    except UnicodeDecodeError:
        return [("text", "the file is not valid UTF-8")]
    for text in (old_text, new_text):
        if re.search(r"[\x00-\x08\x0b-\x1f\x7f\u0085  ]", text):
            return [("text", "the file contains control characters (a carriage return, or worse)")]
    old_lines, old_code, old_kinds, old_flags = scanner.analyse(old_text)
    new_lines, new_code, new_kinds, new_flags = scanner.analyse(new_text)
    reasons = []

    def note(kind, detail):
        if (kind, detail) not in reasons:
            reasons.append((kind, detail))

    matcher = difflib.SequenceMatcher(None, old_lines, new_lines, autojunk=False)
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == "equal":
            for i, j in zip(range(i1, i2), range(j1, j2)):
                if old_code[i] != new_code[j]:
                    note("text", f"line {j + 1}: unchanged text is no longer a comment where it "
                                 "was one, or the reverse")
                elif old_kinds[i] != new_kinds[j]:
                    was = ", ".join(sorted(old_kinds[i])) or "nothing"
                    now = ", ".join(sorted(new_kinds[j])) or "nothing"
                    note("text", f"line {j + 1}: unchanged text moved from {was} to {now}")
            continue
        for i in range(i1, i2):
            if not old_code[i].strip(" \t") or ROUTINE_IMPORT.fullmatch(old_code[i]):
                continue
            for kind in sorted(old_kinds[i] - {"theorem"}):
                note("text", f"removes text from {kind} (old line {i + 1})")
            for flag in sorted(old_flags[i]):
                note("text", f"removes {flag} (old line {i + 1})")
        for j in range(j1, j2):
            line = new_lines[j]
            if re.search(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])", line):
                note("sorry", f"line {j + 1}: adds a `sorry`")
            found = UNFINISHED.search(new_code[j])
            if found and found.group(0) != "sorry":
                note("sorry", f"line {j + 1}: adds `{found.group(0)}`, which leaves a proof unfinished")
            found = DANGEROUS.search(line)
            if found:
                note("text", f"line {j + 1}: `{found.group(0)}`")
            routine = ROUTINE_IMPORT.fullmatch(line) or ROUTINE_OPTION.fullmatch(line)
            found = None if routine else EYES.search(line)
            if found:
                note("text", f"line {j + 1}: matches the triage pattern (`{found.group(0).strip()}`)")
            if "Paper:" in line:
                note("text", f"line {j + 1}: cites the paper, so it may be a statement")
            if not new_code[j].strip(" \t") or ROUTINE_IMPORT.fullmatch(new_code[j]):
                continue
            for kind in sorted(new_kinds[j] - {"theorem"}):
                note("text", f"line {j + 1}: adds text to {kind}")
            for flag in sorted(new_flags[j]):
                note("text", f"line {j + 1}: {flag}")
    return reasons


def declared(lines):
    """The names of the declarations that begin on these lines, private ones apart."""
    names = set()
    for line in lines:
        start = DECLARATION.match(line)
        if start:
            names.add(re.split(r"[\s:({\[]", line[start.end():], maxsplit=1)[0])
    return names - {""}


def classify_change(files, scanner=None):
    """Reasons a pull request is not a plain proof, from [(path, old bytes, new bytes)].

    Each file is judged by `classify`. Across the files, as in scripts/proof_review.sh, a
    declaration that is not `private` and is new outside RiemannMasullo/ForMathlib/ is held
    back: it may be a statement taken from the paper, and those are read before they land.
    """
    scanner = scanner or Scanner()
    reasons, added, removed = [], set(), set()
    for path, old, new in files:
        reasons += [f"{path}: {detail}" for _kind, detail in classify(old, new, scanner)]
        if path.startswith("RiemannMasullo/ForMathlib/"):
            continue
        try:
            old_lines, new_lines = old.decode("utf-8").split("\n"), new.decode("utf-8").split("\n")
        except UnicodeDecodeError:
            continue      # already a reason above
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, old_lines, new_lines, autojunk=False).get_opcodes():
            if tag != "equal":
                removed |= declared(old_lines[i1:i2])
                added |= declared(new_lines[j1:j2])
    if added - removed:
        reasons.append("new declarations that are not private, outside ForMathlib/: " + " ".join(sorted(added - removed)))
    return reasons


def main(argv):
    if len(argv) != 3:
        print(__doc__.split("\n\n")[1], file=sys.stderr)
        return 2
    reasons = classify(Path(argv[1]).read_bytes(), Path(argv[2]).read_bytes())
    for kind, detail in reasons:
        print(f"{kind}: {detail}")
    return 1 if reasons else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
