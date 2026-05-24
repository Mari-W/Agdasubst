#!/usr/bin/env python3
"""Tests for agdasubst.py — external (quoted) arguments + unicode identifiers."""
import os
import re
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from agdasubst import (
    Argument,
    Signature,
    TokenType,
    tokenize,
    parse_signature,
    generate_constructors,
    generate_map_clauses,
    generate_variables,
    generate_traversal,
    generate_id_lemma,
    generate_compositionality_lemma,
    generate_agda,
)


def parse(src: str) -> Signature:
    return parse_signature(tokenize(src))


# ============================================================
# Lexer
# ============================================================


class TestLexer(unittest.TestCase):
    def test_string_literal_token(self):
        toks = tokenize('"String"')
        self.assertEqual(toks[0].type, TokenType.STRING_LITERAL)
        self.assertEqual(toks[0].value, '"String"')

    def test_string_with_unicode_and_spaces(self):
        toks = tokenize('"List ℕ"')
        self.assertEqual(toks[0].type, TokenType.STRING_LITERAL)
        self.assertEqual(toks[0].value, '"List ℕ"')

    def test_unicode_id(self):
        toks = tokenize("α→β")
        self.assertEqual(toks[0].type, TokenType.ID)
        self.assertEqual(toks[0].value, "α→β")

    def test_prime_in_id(self):
        toks = tokenize("foo′")
        self.assertEqual(toks[0].type, TokenType.ID)
        self.assertEqual(toks[0].value, "foo′")

    def test_arrow_breaks_id(self):
        # Make sure '->' is still tokenized separately even between IDs
        toks = tokenize("foo -> bar")
        types = [t.type for t in toks if t.type != TokenType.EOF]
        self.assertEqual(
            types, [TokenType.ID, TokenType.ARROW, TokenType.ID]
        )


# ============================================================
# Argument.var_base
# ============================================================


class TestArgumentVarBase(unittest.TestCase):
    def test_non_external_uses_target_type(self):
        a = Argument(binder_types=[], target_type="tm", external=False)
        self.assertEqual(a.var_base, "tm")

    def test_external_simple(self):
        a = Argument(binder_types=[], target_type="String", external=True)
        self.assertEqual(a.var_base, "string")

    def test_external_strips_non_alphanumeric(self):
        a = Argument(binder_types=[], target_type="List ℕ", external=True)
        self.assertEqual(a.var_base, "listℕ")

    def test_external_underscore_kept(self):
        a = Argument(binder_types=[], target_type="My_Type", external=True)
        self.assertEqual(a.var_base, "my_Type")

    def test_external_leading_digit_prefixed(self):
        a = Argument(binder_types=[], target_type="42x", external=True)
        self.assertEqual(a.var_base, "_42x")

    def test_external_empty_falls_back(self):
        a = Argument(binder_types=[], target_type="!!!", external=True)
        self.assertEqual(a.var_base, "ext")


# ============================================================
# Parser
# ============================================================


class TestParser(unittest.TestCase):
    def test_external_argument_parsed(self):
        sig = parse('tm : Type\nconst : "String" -> tm')
        c = sig.constructors[0]
        self.assertEqual(c.name, "const")
        self.assertEqual(len(c.arguments), 1)
        self.assertTrue(c.arguments[0].external)
        self.assertEqual(c.arguments[0].target_type, "String")
        self.assertEqual(c.target_sort, "tm")

    def test_mixed_args(self):
        sig = parse(
            'tm : Type\nty : Type\nfoo : "String" -> tm -> ty -> "ℕ" -> tm'
        )
        c = sig.constructors[0]
        externals = [a.external for a in c.arguments]
        self.assertEqual(externals, [True, False, False, True])
        self.assertEqual(c.arguments[3].target_type, "ℕ")

    def test_unicode_constructor_and_sort_names(self):
        sig = parse("τ : Type\ntm : Type\nα→β : τ -> τ -> tm")
        self.assertEqual([s.name for s in sig.sorts], ["τ", "tm"])
        self.assertEqual(sig.constructors[0].name, "α→β")
        self.assertEqual(sig.constructors[0].target_sort, "tm")

    def test_external_in_binder_rejected(self):
        with self.assertRaises(SyntaxError) as cm:
            parse('tm : Type\nbad : ("String" -> tm) -> tm')
        self.assertIn("External", str(cm.exception))

    def test_external_as_return_rejected(self):
        with self.assertRaises(SyntaxError) as cm:
            parse('tm : Type\nbad : tm -> "String"')
        self.assertIn("cannot return an external", str(cm.exception))


# ============================================================
# Generators (external args)
# ============================================================


class TestGenerateConstructors(unittest.TestCase):
    def test_external_no_scope_wrapping(self):
        sig = parse('tm : Type\nconst : "String" -> tm')
        out = generate_constructors(sig)
        self.assertIn("const : String → S ⊢ tm", out)
        self.assertNotIn("S ⊢ String", out)

    def test_unicode_constructor(self):
        sig = parse("τ : Type\ntm : Type\nα→β : τ -> τ -> tm")
        out = generate_constructors(sig)
        self.assertIn("α→β : S ⊢ τ → S ⊢ τ → S ⊢ tm", out)


class TestGenerateMapClauses(unittest.TestCase):
    def test_external_passes_through(self):
        sig = parse('tm : Type\nconst : "String" -> tm')
        out = generate_map_clauses(sig, "⋯ᴿ", "ρ", "↑ᴿ*", "")
        self.assertIn("(const string0) ⋯ᴿ ρ = const string0", out)
        # external arg is NOT substituted
        self.assertNotIn("(string0 ⋯ᴿ", out)

    def test_mixed_arg_substitution(self):
        sig = parse('tm : Type\nfoo : "String" -> tm -> tm')
        out = generate_map_clauses(sig, "⋯ˢ", "σ", "↑ˢ*", "")
        self.assertIn(
            "(foo string0 tm0) ⋯ˢ σ = foo string0 (tm0 ⋯ˢ σ)", out
        )


class TestGenerateVariables(unittest.TestCase):
    def test_external_no_seq_prefix(self):
        sig = parse('tm : Type\nconst : "String" -> tm')
        out = generate_variables(sig)
        self.assertIn("string0 : String", out)
        for line in out.splitlines():
            if "string0" in line:
                self.assertNotIn("S ⊢", line)

    def test_collision_between_sort_and_external_raises(self):
        with self.assertRaises(SyntaxError) as cm:
            sig = parse(
                'foo : Type\ntm : Type\na : foo -> tm\nb : "Foo" -> tm'
            )
            generate_variables(sig)
        self.assertIn("conflicting", str(cm.exception))

    def test_two_constructors_share_external_var(self):
        sig = parse(
            'tm : Type\nfoo : "String" -> tm\nbar : "String" -> tm -> tm'
        )
        out = generate_variables(sig)
        self.assertEqual(out.count("string0 : String"), 1)


class TestGenerateTraversal(unittest.TestCase):
    def test_external_traversal_is_refl_s(self):
        sig = parse('tm : Type\nconst : "String" -> tm')
        out = generate_traversal(sig, "inst", "⋯ˢ", "σ", "↑ˢ*")
        self.assertIn("inst-const", out)
        self.assertIn("(const string0) ⋯ˢ σ", out)
        self.assertIn("≡ const string0", out)

    def test_external_traversal_is_refl_r(self):
        sig = parse('tm : Type\nconst : "String" -> tm')
        out = generate_traversal(sig, "instᴿ", "⋯ᴿ", "ρ", "↑ᴿ*")
        self.assertIn("instᴿ-const", out)
        self.assertIn("(const string0) ⋯ᴿ ρ", out)


class TestGenerateProofLemmas(unittest.TestCase):
    def test_id_lemma_uses_refl_for_external(self):
        sig = parse('tm : Type\nconst : "String" -> tm')
        out = generate_id_lemma(sig, "right-idˢ", "⋯ˢ_", "lift-idˢ*")
        self.assertIn("right-idˢ (const string0) = cong1 const refl", out)

    def test_id_lemma_mixes_refl_and_recursive(self):
        sig = parse('tm : Type\nfoo : "String" -> tm -> tm')
        out = generate_id_lemma(sig, "right-idˢ", "⋯ˢ_", "lift-idˢ*")
        self.assertIn(
            "right-idˢ (foo string0 tm0) = cong2 foo refl (right-idˢ tm0)",
            out,
        )

    def test_compositionality_refl_for_external(self):
        sig = parse('tm : Type\nconst : "String" -> tm')
        out = generate_compositionality_lemma(
            sig, "", "compositionalityᴿᴿ", "⋯ᴿ_", "lift-dist-comp*ᴿᴿ"
        )
        self.assertIn(
            "compositionalityᴿᴿ  (const string0) = cong1 const refl",
            out,
        )

    def test_pair_with_two_externals(self):
        sig = parse(
            'tm : Type\npair : "String" -> "ℕ" -> tm -> tm -> tm'
        )
        out = generate_id_lemma(sig, "right-idˢ", "⋯ˢ_", "lift-idˢ*")
        self.assertIn(
            "right-idˢ (pair string0 ℕ0 tm0 tm1) "
            "= cong4 pair refl refl (right-idˢ tm0) (right-idˢ tm1)",
            out,
        )


# ============================================================
# End-to-end
# ============================================================


class TestGenerateAgdaIntegration(unittest.TestCase):
    def test_full_pipeline(self):
        src = (
            "ty : Type\n"
            "tm : Type\n"
            "arr : ty -> ty -> ty\n"
            "lam : ty -> (tm -> tm) -> tm\n"
            'const : "String" -> tm\n'
            'pair : "String" -> "ℕ" -> tm -> tm -> tm\n'
            "α→β : tm -> tm -> tm\n"
        )
        agda = generate_agda(parse(src), "test_mod")
        norm = re.sub(r" +", " ", agda)

        # Constructor declarations
        self.assertIn("const : String → S ⊢ tm", norm)
        self.assertIn("pair : String → ℕ → S ⊢ tm → S ⊢ tm → S ⊢ tm", norm)
        self.assertIn("α→β : S ⊢ tm → S ⊢ tm → S ⊢ tm", norm)
        # Variable block
        self.assertIn("string0 : String", norm)
        self.assertIn("ℕ0 : ℕ", norm)
        # Renaming passes externals through
        self.assertIn("(const string0) ⋯ᴿ ρ = const string0", norm)
        # Substitution passes externals through
        self.assertIn("(const string0) ⋯ˢ σ = const string0", norm)
        # Proofs use refl for external positions
        self.assertIn("right-idˢ (const string0) = cong1 const refl", norm)
        # Both renaming and substitution traversal lemmas exist
        self.assertIn("inst-const", norm)
        self.assertIn("instᴿ-const", norm)


# ============================================================
# Regression
# ============================================================


class TestRegressionExistingSignatures(unittest.TestCase):
    """Existing signature files must still regenerate identical to checked-in
    .agda outputs, modulo line 1 (OPTIONS pragma — a pre-existing mismatch in
    the repo) and line 2 (module name)."""

    def test_all_existing_signatures_unchanged(self):
        sig_dir = os.path.join(HERE, "signatures")
        out_dir = os.path.join(HERE, "agda")
        for fn in sorted(os.listdir(sig_dir)):
            if not fn.endswith(".sig"):
                continue
            base = os.path.splitext(fn)[0]
            agda_path = os.path.join(out_dir, base + ".agda")
            if not os.path.exists(agda_path):
                continue
            if base == "sysf_ext":  # has manual imports added
                continue
            with open(os.path.join(sig_dir, fn)) as f:
                sig_src = f.read()
            regen = generate_agda(
                parse_signature(tokenize(sig_src)), base
            )
            with open(agda_path) as f:
                existing = f.read()
            # Strip lines 1+2 (pragma + module name) before comparing.
            self.assertEqual(
                "\n".join(regen.splitlines()[2:]),
                "\n".join(existing.splitlines()[2:]),
                f"Regenerated {base}.agda differs from checked-in copy",
            )


if __name__ == "__main__":
    unittest.main()
