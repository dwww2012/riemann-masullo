#!/usr/bin/env python3
"""Tests for plain_proof.py: python3 -m unittest discover -s scripts/ci"""
import unittest

import plain_proof

BASE = '''import Mathlib

namespace RiemannMasullo

variable {F : Type*}
  [Field F]

local notation "N[" x "]" =>
  Nat.succ x

/-- Paper: Definition 1, p. 2. A definition. -/
def foo : Nat := 1

/-- Paper: Lemma 1, p. 3. Something. -/
theorem bar (x : Nat) : x + 0 = x := by
  sorry

theorem baz : foo = 1 := by
  sorry

end RiemannMasullo
'''
SORRY = "  sorry\n\ntheorem baz"


class PlainProof(unittest.TestCase):
    scanner = plain_proof.Scanner()

    def reasons(self, new, old=BASE):
        return plain_proof.classify(old.encode(), new.encode(), self.scanner)

    def plain(self, new, old=BASE):
        self.assertEqual(self.reasons(new, old), [])

    def held(self, new, old=BASE, kind=None, needle=None):
        found = self.reasons(new, old)
        self.assertTrue(found, "expected the change to be held back")
        if kind:
            self.assertIn(kind, [k for k, _ in found])
        if needle:
            self.assertTrue(any(needle in d for _, d in found), found)

    # What a proof pull request normally looks like.

    def test_fills_a_proof(self):
        self.plain(BASE.replace(SORRY, "  simp\n\ntheorem baz"))

    def test_adds_helper_lemmas(self):
        self.plain(BASE.replace("/-- Paper: Lemma 1", (
            "/-- The local helper: an open instance of the class structure, for example. -/\n"
            "private theorem helper : (1 : Nat) = 1 := rfl\n\n"
            "open scoped Classical in\n"
            "omit [Field F] in\n"
            "/-- Another one,\nover two lines: a section about the variable. -/\n"
            "lemma helper2 : (2 : Nat) = 2 := by\n"
            "  -- by definition, at the end\n"
            "  rfl -- the instance is local\n\n"
            "/-- Paper: Lemma 1")))

    def test_scoped_prefixes(self):
        for prefix in ("omit hρ [CompactSpace G] [T2Space G] in",
                       "omit hμ hρ [IsTopologicalGroup G] [BorelSpace G]\n  [T2Space E] [ContinuousSMul ℂ E] in",
                       "omit [Fact (1 ≤ p)] [Module ℂ (E →L[ℂ] F)] in", "include hE hF in",
                       "open scoped Pointwise in\nomit [Field F] in", "open Filter Topology in"):
            self.plain(BASE.replace("/-- Paper: Lemma 1", f"{prefix}\nprivate theorem aux : True := trivial\n\n/-- Paper: Lemma 1"))
        for prefix in ("omit [Field F]", "open Filter", "include hF", "omit [Field F] in def evil := 1",
                       "omit [Foo (open Classical in", "omit [Field F]\n  variable [Fact False] in",
                       'omit [Foo "] in', "open Filter in in", "omit [Field F] ) in"):
            self.held(BASE.replace("/-- Paper: Lemma 1", f"{prefix}\nprivate theorem aux : True := trivial\n\n/-- Paper: Lemma 1"))

    def test_open_in_inside_a_proof(self):
        self.plain(BASE.replace(SORRY, "  open Classical in\n  simp\n\ntheorem baz"))

    def test_changing_a_statement_is_not_decided_here(self):
        self.plain(BASE.replace("theorem baz : foo = 1 := by\n  sorry",
                                "theorem baz : True := by\n  trivial"))

    def test_identifiers_that_contain_keywords(self):
        self.plain(BASE.replace(SORRY, "  exact append_def opened x.defn end_of\n\ntheorem baz"))

    # The rules of scripts/proof_review.sh.

    def change(self, new, path="RiemannMasullo/AppA/Sec1.lean", old=BASE):
        return plain_proof.classify_change([(path, old.encode(), new.encode())], self.scanner)

    def test_routine_imports_and_linter_options(self):
        self.plain(BASE.replace("import Mathlib\n", "import Mathlib\nimport Mathlib.Analysis.Normed.Basic\n"))
        self.plain(BASE.replace("import Mathlib\n", "import Mathlib\npublic import RiemannMasullo.AppA.Sec1\n"))
        self.plain(BASE.replace("/-- Paper: Lemma 1", "set_option linter.unusedVariables false in\n/-- Paper: Lemma 1"))
        self.held(BASE.replace("import Mathlib\n", "import Mathlib\nimport Evil.Module\n"), needle="`import`")
        self.held(BASE.replace("import Mathlib\n", "import Mathlib\nimport Mathlib.Lean.Expr.Basic\n"), needle="`Lean`")
        self.held(BASE.replace("/-- Paper: Lemma 1", "set_option linter.unusedVariables false\n/-- Paper: Lemma 1"),
                  needle="`set_option`")
        self.held(BASE.replace("/-- Paper: Lemma 1", "set_option debug.skipKernelTC true in\n/-- Paper: Lemma 1"),
                  needle="`set_option`")
        # an import pushed into the middle of another command
        self.held(BASE.replace("variable {F : Type*}\n", "variable {F : Type*}\nimport Mathlib.Data.Nat.Basic\n"),
                  needle="moved")

    def test_citing_the_paper(self):
        self.held(BASE.replace("/-- Paper: Lemma 1", "/-- Paper: Lemma 0, p. 3. -/\nprivate theorem aux : True := trivial\n\n/-- Paper: Lemma 1"),
                  needle="cites the paper")

    def test_new_public_declarations(self):
        helper = "theorem aux : True := trivial\n\n/-- Paper: Lemma 1"
        new = BASE.replace("/-- Paper: Lemma 1", helper)
        self.plain(new)                                                    # the text of the file alone is fine
        self.assertTrue(any("aux" in r for r in self.change(new)))         # but the name is new and public
        self.assertEqual(self.change(new, path="RiemannMasullo/ForMathlib/Topology/Basic.lean"), [])
        self.assertEqual(self.change(BASE.replace("/-- Paper: Lemma 1", "private " + helper)), [])
        # rewriting the first line of an existing declaration does not make it new
        self.assertEqual(self.change(BASE.replace("theorem baz : foo = 1 := by\n  sorry",
                                                  "theorem baz : foo = 1 := rfl")), [])

    # Leaving a proof unfinished.

    def test_sorry(self):
        self.held(BASE.replace("/-- Paper: Lemma 1", "theorem aux : True := by\n  sorry\n\n/-- Paper: Lemma 1"),
                  kind="sorry")

    def test_admit(self):
        self.held(BASE.replace(SORRY, "  admit\n\ntheorem baz"), kind="sorry")

    # A second command on the line of a proof, where a pattern anchored at the start of the
    # line does not look.

    def test_command_after_a_proof_on_the_same_line(self):
        self.held(BASE.replace(SORRY, "  simp initialize foo : Unit ← pure ()\n\ntheorem baz"),
                  needle="`initialize`")
        self.held(BASE.replace(SORRY, "  simp\n\n/- -/ def evil : Nat := 3\n\ntheorem baz"),
                  needle="`def`")
        self.held(BASE.replace(SORRY, "  simp\n  axiom bad : False\n\ntheorem baz"), needle="`axiom`")
        self.held(BASE.replace(SORRY, "  simp macro_rules | `(tactic| done) => `(tactic| skip)\n\ntheorem baz"),
                  needle="`macro_rules`")

    def test_keyword_glued_to_a_number_or_a_token(self):
        self.held(BASE.replace(SORRY, "  exact Nat.add_zero 0xFinitialize x : Unit ← pure ()\n\ntheorem baz"),
                  needle="`initialize`")
        self.held(BASE.replace(SORRY, "  exact le_refl (0 ≤idef evil := 1)\n\ntheorem baz"), needle="`def`")
        self.held(BASE.replace(SORRY, "  exact (foo)def evil := 1\n\ntheorem baz"), needle="`def`")

    def test_hash_commands_and_attributes(self):
        self.held(BASE.replace(SORRY, "  simp #eval 1\n\ntheorem baz"), needle="`#eval`")
        self.held(BASE.replace("theorem baz", "@[simp]\ntheorem baz"), needle="`@[`")
        self.held(BASE.replace("theorem baz", "set_option maxHeartbeats 400000 in\ntheorem baz"),
                  needle="`set_option`")

    # Commands that leave no declaration behind but change what later statements mean.

    def test_variable(self):
        self.held(BASE.replace("end RiemannMasullo", "variable [Fact False]\n\nend RiemannMasullo"),
                  needle="`variable`")

    def test_line_added_to_an_existing_command(self):
        self.held(BASE.replace("  [Field F]\n", "  [Field F]\n  [Fact False]\n"), needle="`variable`")
        self.held(BASE.replace("  Nat.succ x\n", "  Nat.succ (Nat.succ x)\n"), needle="`notation`")

    def test_open_without_in(self):
        self.held(BASE.replace("theorem baz", "open Complex\n\ntheorem baz"), needle="`open`")
        self.held(BASE.replace("theorem baz", "open Foo in\ndef evil := 1\n\ntheorem baz"), needle="`def`")

    def test_definitions(self):
        self.held(BASE.replace("def foo : Nat := 1", "def foo : Nat := 2"), needle="`def`")
        old = BASE.replace("def foo", "private def foo")
        self.held(old.replace("private def foo : Nat := 1", "private def foo : Nat := 2"), old=old,
                  needle="`def`")
        self.held(BASE.replace("theorem baz", "instance : Inhabited Nat := ⟨0⟩\n\ntheorem baz"),
                  needle="`instance`")

    def test_doc_comment_before_something_that_is_not_a_keyword(self):
        self.held(BASE.replace("theorem baz", "/-- lies -/\nadd_decl_doc foo\n\ntheorem baz"),
                  needle="doc comment")

    # Moving existing text between commands without adding any.

    def test_theorem_inserted_into_a_command(self):
        self.held(BASE.replace("variable {F : Type*}\n", "variable {F : Type*}\ntheorem t : True := trivial\n"),
                  needle="moved")

    def test_text_left_behind_by_a_removed_theorem(self):
        old = BASE.replace("end RiemannMasullo", (
            "variable (n : Nat)\n\nprivate theorem t : True := by\n  trivial /-\n"
            "  [Fact False]\n  -/\n\nend RiemannMasullo"))
        new = old.replace("private theorem t : True := by\n  trivial /-\n", "").replace("  -/\n\nend", "\nend")
        self.held(new, old=old)

    def test_comment_opened_or_closed_around_existing_text(self):
        old = BASE.replace("theorem baz", "/-\nvariable [Fact False]\n-/\n\ntheorem baz")
        self.held(old.replace("/-\nvariable", "/- -/\nvariable").replace("[Fact False]\n-/", "[Fact False]\n"),
                  old=old, needle="comment")
        self.held(old.replace("/-\nvariable", "variable").replace("[Fact False]\n-/\n", "[Fact False]\n"),
                  old=old)

    # Text that only looks like a comment.

    def test_string_that_swallows_a_comment_opener(self):
        self.held(BASE.replace(SORRY, '  exact foo "\n/-- "; def evil := 1 -/\n\ntheorem baz'),
                  needle="`def`")

    def test_dashes_that_are_not_a_comment(self):
        self.held(BASE.replace(SORRY, '  exact f "--" def evil := 1\n\ntheorem baz'), needle="`def`")
        self.held(BASE.replace(SORRY, "  exact f x <-- def evil := 1\n\ntheorem baz"), needle="`def`")

    def test_comment_closed_early(self):
        self.held(BASE.replace(SORRY, "  simp\n/- a /- b -/ -/ def evil := 1 /- c -/\n\ntheorem baz"),
                  needle="`def`")
        self.plain(BASE.replace(SORRY, "  simp\n/- a /- def evil := 1 -/ variable -/\n\ntheorem baz"))

    # Forbidden constructs and odd files.

    def test_dangerous_words(self):
        for text in ("by_elab", "run_tac", "native_decide", "eval% foo", "open Lean in", "IO.println"):
            self.held(BASE.replace(SORRY, f"  exact {text}\n\ntheorem baz"), kind="text")

    def test_control_characters(self):
        self.held(BASE.replace(SORRY, "  simp\r\n\ntheorem baz"), needle="control")

    def test_not_utf8(self):
        self.assertTrue(plain_proof.classify(BASE.encode(), b"\xff\xfe" + BASE.encode(), self.scanner))


class Keywords(unittest.TestCase):
    def test_list(self):
        commands, tails = plain_proof.load_keywords()
        self.assertGreater(len(commands), 200)
        for token in ("theorem", "lemma", "initialize", "variable", "#eval", "@[", "macro_rules"):
            self.assertIn(token, commands)
        self.assertIn("i", tails)


if __name__ == "__main__":
    unittest.main()
