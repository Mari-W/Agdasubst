#!/usr/bin/env python3
import re
import sys
import os
import argparse
from dataclasses import dataclass, field
from enum import Enum, auto

# ==========================================
# 1. AST
# ==========================================


@dataclass
class SortDecl:
    name: str


@dataclass
class Argument:
    binder_types: list[str]
    target_type: str

    @property
    def is_binder(self) -> bool:
        return len(self.binder_types) > 0

    def __repr__(self) -> str:
        if self.is_binder:
            binders = " -> ".join(self.binder_types)
            return f"({binders} -> {self.target_type})"
        return self.target_type


@dataclass
class ConstructorDecl:
    name: str
    arguments: list[Argument]
    target_sort: str


@dataclass
class Signature:
    sorts: list[SortDecl] = field(default_factory=lambda: [])
    constructors: list[ConstructorDecl] = field(default_factory=lambda: [])

    def get_sort_names(self) -> list[str]:
        return [s.name for s in self.sorts]


# ==========================================
# 2. Lexer
# ==========================================


class TokenType(Enum):
    ID = auto()
    ARROW = auto()  # ->
    COLON = auto()  # :
    LPAREN = auto()  # (
    RPAREN = auto()  # )
    TYPE_KW = auto()  # Type
    EOF = auto()


@dataclass
class Token:
    type: TokenType
    value: str
    line: int
    column: int


TOKEN_SPEC: list[tuple[TokenType | None, str]] = [
    (None, r"begin[^\n]*"),
    (None, r"end[^\n]*"),
    (TokenType.ARROW, r"->"),
    (TokenType.LPAREN, r"\("),
    (TokenType.RPAREN, r"\)"),
    (TokenType.COLON, r":"),
    (TokenType.TYPE_KW, r"\bType\b"),
    (TokenType.ID, r"[a-zA-Z_][a-zA-Z0-9_]*"),
    (None, r"\s+"),
    (None, r"--[^\n]*"),
]

TOKEN_REGEX: list[tuple[TokenType | None, re.Pattern[str]]] = [
    (tt, re.compile(p)) for tt, p in TOKEN_SPEC
]


def tokenize(source: str) -> list[Token]:
    tokens: list[Token] = []
    pos = 0
    line_num = 1
    line_start = 0

    while pos < len(source):
        match_found = False
        for token_type, regex in TOKEN_REGEX:
            match = regex.match(source, pos)
            if match:
                match_found = True
                text = match.group(0)

                if token_type:
                    column = match.start() - line_start + 1
                    tokens.append(Token(token_type, text, line_num, column))

                newlines = text.count("\n")
                if newlines > 0:
                    line_num += newlines
                    line_start = match.end() - text.rfind("\n") - 1

                pos = match.end()
                break

        if not match_found:
            raise SyntaxError(f"Illegal character '{source[pos]}' at line {line_num}")

    tokens.append(Token(TokenType.EOF, "", line_num, 0))
    return tokens


# ==========================================
# 3. Parser
# ==========================================


def peek(tokens: list[Token], pos: int, offset: int = 0) -> Token:
    if pos + offset >= len(tokens):
        return tokens[-1]
    return tokens[pos + offset]


def consume(
    tokens: list[Token], pos: int, expected_type: TokenType | None = None
) -> tuple[Token, int]:
    current = peek(tokens, pos)
    if expected_type and current.type != expected_type:
        raise SyntaxError(
            f"Expected {expected_type}, but found {current.type} ('{current.value}') "
            f"at line {current.line}:{current.column}"
        )
    return current, pos + 1


def parse_signature(tokens: list[Token]) -> Signature:
    sig = Signature()
    pos = 0

    while peek(tokens, pos).type != TokenType.EOF:
        id_token, pos = consume(tokens, pos, TokenType.ID)
        _, pos = consume(tokens, pos, TokenType.COLON)

        if peek(tokens, pos).type == TokenType.TYPE_KW:
            _, pos = consume(tokens, pos, TokenType.TYPE_KW)
            sig.sorts.append(SortDecl(name=id_token.value))
        else:
            if peek(tokens, pos).type == TokenType.EOF:
                raise SyntaxError(f"Unexpected EOF after {id_token.value} :")

            parts, pos = parse_type_chain(tokens, pos)
            if not parts:
                raise SyntaxError(
                    f"Constructor {id_token.value} has no type signature."
                )

            target_sort = parts[-1].target_type
            if parts[-1].is_binder:
                raise SyntaxError(
                    f"Constructor {id_token.value} cannot return a function/binder. Found: {parts[-1]}"
                )

            arguments = parts[:-1]
            sig.constructors.append(
                ConstructorDecl(
                    name=id_token.value, arguments=arguments, target_sort=target_sort
                )
            )

    return sig


def parse_type_chain(tokens: list[Token], pos: int) -> tuple[list[Argument], int]:
    args: list[Argument] = []
    arg, pos = parse_argument(tokens, pos)
    args.append(arg)

    while peek(tokens, pos).type == TokenType.ARROW:
        _, pos = consume(tokens, pos, TokenType.ARROW)
        next_arg, pos = parse_argument(tokens, pos)
        args.append(next_arg)

    return args, pos


def parse_argument(tokens: list[Token], pos: int) -> tuple[Argument, int]:
    if peek(tokens, pos).type == TokenType.LPAREN:
        _, pos = consume(tokens, pos, TokenType.LPAREN)
        inner_chain, pos = parse_type_chain(tokens, pos)
        _, pos = consume(tokens, pos, TokenType.RPAREN)

        if not inner_chain:
            raise SyntaxError("Empty parentheses in type signature.")

        target = inner_chain[-1].target_type
        binder_types: list[str] = []
        for arg in inner_chain[:-1]:
            binder_types.append(arg.target_type)

        return Argument(binder_types=binder_types, target_type=target), pos

    elif peek(tokens, pos).type == TokenType.ID:
        token, pos = consume(tokens, pos, TokenType.ID)
        return Argument(binder_types=[], target_type=token.value), pos
    else:
        raise SyntaxError(
            f"Unexpected token in type signature: {peek(tokens, pos).value} at line {peek(tokens, pos).line}"
        )


# ==========================================
# 4. Agda Code Generation
# ==========================================


def get_max_arity(sig: Signature) -> int:
    if not sig.constructors:
        return 0
    return max([len(c.arguments) for c in sig.constructors])


def generate_congs(max_arity: int) -> str:
    limit = max(2, max_arity)
    lines: list[str] = []

    for n in range(1, limit + 1):
        name = f"cong{n}"
        sets = " ".join([f"A{i}" for i in range(1, n + 2)])
        arrows = " → ".join([f"A{i}" for i in range(1, n + 2)])
        implicits = " ".join([f"a{i}" for i in range(1, 2 * n + 1)])
        eqs = " → ".join([f"a{2 * i - 1} ≡ a{2 * i}" for i in range(1, n + 1)])
        lhs_args = " ".join([f"a{2 * i - 1}" for i in range(1, n + 1)])
        rhs_args = " ".join([f"a{2 * i}" for i in range(1, n + 1)])

        sig = f"{name} : ∀ {{{sets} : Set}} (f : {arrows}) {{{implicits}}} →\n  {eqs} → f {lhs_args} ≡ f {rhs_args}"
        refls = " ".join(["refl"] * n)
        defn = f"{name} f {refls} = refl"

        lines.append(sig)
        lines.append(defn)
        lines.append("")

    return "\n".join(lines)


def generate_sorts(sig: Signature) -> str:
    sort_names = [s.name for s in sig.sorts]
    sorts_str = " ".join(sort_names)
    return f"data Sort : Set where \n  {sorts_str} : Sort"


def generate_constructors(sig: Signature) -> str:
    constructors_code: list[str] = []
    max_name_len = 0
    if sig.constructors:
        max_name_len = max([len(c.name) for c in sig.constructors])

    for c in sig.constructors:
        arg_strs: list[str] = []
        for arg in c.arguments:
            if arg.is_binder:
                reversed_binders = reversed(arg.binder_types)
                context_ext = " ∷ ".join(reversed_binders)
                arg_strs.append(f"({context_ext} ∷ S) ⊢ {arg.target_type}")
            else:
                arg_strs.append(f"S ⊢ {arg.target_type}")
        res_str = f"S ⊢ {c.target_sort}"
        full_type = " → ".join(arg_strs + [res_str])
        padding = " " * (max_name_len - len(c.name))
        constructors_code.append(f"  {c.name}{padding} : {full_type}")

    return "\n".join(constructors_code)


def generate_map_clauses(
    sig: Signature, op_symbol: str, map_var: str, lift_op: str, indent: str = ""
) -> str:
    clauses: list[str] = []
    data: list[tuple[str, str]] = []
    max_lhs_len = 0

    for c in sig.constructors:
        arg_vars: list[str] = []
        rhs_args: list[str] = []
        counts: dict[str, int] = {}

        for arg in c.arguments:
            base_name = arg.target_type
            idx = counts.get(base_name, 0)
            counts[base_name] = idx + 1
            var_name: str = f"{base_name}{idx}"

            arg_vars.append(var_name)

            if arg.is_binder:
                rhs_args.append(f"({var_name} {op_symbol} ({map_var} {lift_op} _))")
            else:
                rhs_args.append(f"({var_name} {op_symbol} {map_var})")

        args_pattern = " ".join(arg_vars)
        args_rhs = " ".join(rhs_args)
        lhs = f"({c.name} {args_pattern})" if args_pattern else f"{c.name}"
        rhs = f"{c.name} {args_rhs}" if args_rhs else f"{c.name}"
        data.append((lhs, rhs))
        max_lhs_len = max(max_lhs_len, len(lhs))

    for lhs, rhs in data:
        padding = " " * (max_lhs_len - len(lhs))
        clauses.append(f"{indent}{lhs}{padding} {op_symbol} {map_var} = {rhs}")

    return "\n".join(clauses)


def generate_variables(sig: Signature) -> str:
    used_vars: set[str] = set()
    used_vars_sorts: dict[str, str] = {}

    for c in sig.constructors:
        counts: dict[str, int] = {}
        for arg in c.arguments:
            base_name = arg.target_type
            idx = counts.get(base_name, 0)
            counts[base_name] = idx + 1
            var_name = f"{base_name}{idx}"
            used_vars.add(var_name)
            used_vars_sorts[var_name] = arg.target_type

    vars_by_sort: dict[str, list[str]] = {}
    for v in sorted(list(used_vars)):
        s = used_vars_sorts[v]
        if s not in vars_by_sort:
            vars_by_sort[s] = []
        vars_by_sort[s].append(v)

    variable_block_lines = ["variable"]
    for s, vs in vars_by_sort.items():
        v_str = " ".join(vs)
        variable_block_lines.append(f"  {v_str} : S ⊢ {s}")

    return "\n".join(variable_block_lines)


def generate_traversal(sig: Signature) -> str:
    traversal_clauses: list[str] = []
    trav_data: list[dict[str, str]] = []

    max_name_len = 0
    max_lhs_eq_len = 0

    for c in sig.constructors:
        arg_vars: list[str] = []
        rhs_args: list[str] = []
        counts: dict[str, int] = {}
        for arg in c.arguments:
            base_name = arg.target_type
            idx = counts.get(base_name, 0)
            counts[base_name] = idx + 1
            var_name = f"{base_name}{idx}"
            arg_vars.append(var_name)

            if arg.is_binder:
                binders = " ∷ ".join(reversed(arg.binder_types))
                explicit_list = f"({binders} ∷ [])"
                rhs_args.append(f"({var_name} ⋯ˢ (σ ↑ˢ* {explicit_list}))")
            else:
                rhs_args.append(f"({var_name} ⋯ˢ σ)")

        args_pattern = " ".join(arg_vars)
        args_rhs = " ".join(rhs_args)

        name = f"traversal-{c.name}"
        lhs_term = f"({c.name} {args_pattern})" if args_pattern else f"{c.name}"
        rhs_term = f"{c.name} {args_rhs}" if args_rhs else f"{c.name}"
        lhs_eq = f"{lhs_term} ⋯ˢ σ"

        trav_data.append({"name": name, "lhs_eq": lhs_eq, "rhs_term": rhs_term})

        max_name_len = max(max_name_len, len(name))
        max_lhs_eq_len = max(max_lhs_eq_len, len(lhs_eq))

    for item in trav_data:
        name = item["name"]
        lhs_eq = item["lhs_eq"]
        rhs = item["rhs_term"]

        pad_name = " " * (max_name_len - len(name))
        pad_lhs = " " * (max_lhs_eq_len - len(lhs_eq))

        clause1 = f"  {name}{pad_name} : {lhs_eq}{pad_lhs} ≡ {rhs}"
        clause2 = f"  {name}{pad_name} = refl"

        traversal_clauses.append(clause1)
        traversal_clauses.append(clause2)

    return "\n".join(traversal_clauses)


def generate_id_lemma(
    sig: Signature, lemma_name: str, op_symbol: str, lift_lemma: str
) -> str:
    clauses: list[str] = []
    max_len = 0
    data: list[tuple[str, str]] = []

    for c in sig.constructors:
        arg_vars: list[str] = []
        proofs: list[str] = []
        counts: dict[str, int] = {}

        for arg in c.arguments:
            base_name = arg.target_type
            idx = counts.get(base_name, 0)
            counts[base_name] = idx + 1
            var_name = f"{base_name}{idx}"
            arg_vars.append(var_name)

            if arg.is_binder:
                binders = " ∷ ".join(reversed(arg.binder_types))
                explicit_list = f"({binders} ∷ [])"
                proof = f"(trans (cong1 ({var_name} {op_symbol}) ({lift_lemma} {explicit_list})) ({lemma_name} {var_name}))"
                proofs.append(proof)
            else:
                proofs.append(f"({lemma_name} {var_name})")

        args_pattern = " ".join(arg_vars)
        lhs = (
            f"{lemma_name} ({c.name} {args_pattern})"
            if args_pattern
            else f"{lemma_name} {c.name}"
        )

        arity = len(c.arguments)
        if arity == 0:
            rhs = "refl"
        else:
            rhs = f"cong{arity} {c.name} " + " ".join(proofs)

        data.append((lhs, rhs))
        max_len = max(max_len, len(lhs))

    for lhs, rhs in data:
        padding = " " * (max_len - len(lhs))
        clauses.append(f"  {lhs}{padding} = {rhs}")

    return "\n".join(clauses)


def generate_compositionality_lemma(
    sig: Signature, lemma_name: str, map_op: str, comp_lemma: str
) -> str:
    clauses: list[str] = []
    max_len = 0
    data: list[tuple[str, str]] = []

    for c in sig.constructors:
        arg_vars: list[str] = []
        proofs: list[str] = []
        counts: dict[str, int] = {}

        for arg in c.arguments:
            base_name = arg.target_type
            idx = counts.get(base_name, 0)
            counts[base_name] = idx + 1
            var_name = f"{base_name}{idx}"
            arg_vars.append(var_name)

            if arg.is_binder:
                binders = " ∷ ".join(reversed(arg.binder_types))
                explicit_list = f"({binders} ∷ [])"
                proof = f"(trans ({lemma_name} {var_name}) (cong1 ({var_name} {map_op}) ({comp_lemma} {explicit_list})))"
                proofs.append(proof)
            else:
                proofs.append(f"({lemma_name} {var_name})")

        args_pattern = " ".join(arg_vars)
        lhs = (
            f"{lemma_name} ({c.name} {args_pattern})"
            if args_pattern
            else f"{lemma_name} {c.name}"
        )

        arity = len(c.arguments)
        if arity == 0:
            rhs = "refl"
        else:
            rhs = f"cong{arity} {c.name} " + " ".join(proofs)

        data.append((lhs, rhs))
        max_len = max(max_len, len(lhs))

    for lhs, rhs in data:
        padding = " " * (max_len - len(lhs))
        clauses.append(f"  {lhs}{padding} = {rhs}")

    return "\n".join(clauses)


def generate_rewrite_block(sig: Signature) -> str:
    traversal_names = ["traversal-var"]
    for c in sig.constructors:
        traversal_names.append(f"traversal-{c.name}")

    traversals_str = " ".join(traversal_names)

    return f"""
{{-# REWRITE
  lift-id def-∙-zero def-∙-suc def-↑ˢ def-⨟
  associativity distributivityˢ distributivityᴿ interact
  comp-idᵣ comp-idₗ η-id η-lawˢ η-lawᴿ
  {traversals_str}
  right-id
  compositionalityᴿˢ compositionalityᴿᴿ
  compositionalityˢᴿ compositionalityˢˢ
  coincidence coincidence-fold
#-}}
"""


def render_template(
    module_name: str,
    congs: str,
    sorts: str,
    constructors: str,
    renaming: str,
    variables: str,
    substitution: str,
    traversal: str,
    right_ids: str,
    right_id: str,
    compositionality_rr: str,
    compositionality_rs: str,
    compositionality_sr: str,
    compositionality_ss: str,
    rewrite_block: str,
) -> str:
    part1 = (
        """{-# OPTIONS --rewriting --local-confluence-check --double-check #-}
module """
        + module_name
        + """ where
open import Agda.Builtin.Equality.Rewrite public

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

"""
    )

    part2 = """
open import Data.List using (List; []; _∷_; _++_)

ext : {A : Set} {B : A → Set} {C : A → Set} → {f g : (a : A) → B a → C a} →
  (∀ {a} x → f a x ≡ g a x) → f ≡ g
ext f = fun-ext λ _ → fun-ext λ x → f x

data Mode : Set where 
  V T : Mode

private variable
  m  : Mode

"""

    part3 = """

Scope = List Sort

private variable 
  s s′ : Sort 
  S S₁ S₂ S₃ S₄ : List Sort

data _⊢[_]_ : Scope → Mode → Sort → Set 

_⊢_ = _⊢[ T ]_
_∋_ = _⊢[ V ]_

data _⊢[_]_ where 
  zero : (s ∷ S) ∋ s
  suc  : S ∋ s → (s′ ∷ S) ∋ s
  var  : S ∋ s → S ⊢ s 

"""

    part4 = """

variable
  x x′     : S ∋ s
  t t′     : S ⊢ s
  x/t x/t′ : S ⊢[ m ] s

--! Ren {
_→ᴿ_ : Scope → Scope → Set
S₁ →ᴿ S₂ = ∀ s → S₁ ∋ s → S₂ ∋ s 

--! [
variable
  ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂
--! ]
idᴿ : S →ᴿ S
idᴿ _ x = x

wk : ∀ s → S →ᴿ (s ∷ S)
wk _ _ = suc

_∘_ : S₁ →ᴿ S₂ → S₂ →ᴿ S₃ → S₁ →ᴿ S₃
(ρ₁ ∘ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

_↑ᴿ_ : (S₁ →ᴿ S₂) → ∀ s → 
  ((s ∷ S₁) →ᴿ (s ∷ S₂))
(ρ ↑ᴿ _) _ zero    = zero
(ρ ↑ᴿ _) _ (suc x) = suc (ρ _ x)

_↑ᴿ*_ : (S₁ →ᴿ S₂) → ∀ S → ((S ++ S₁) →ᴿ (S ++ S₂))
ρ ↑ᴿ* []      = ρ
ρ ↑ᴿ* (s ∷ S) = (ρ ↑ᴿ* S) ↑ᴿ s

_⋯ᴿ_ : S₁ ⊢[ m ] s → S₁ →ᴿ S₂ → 
  S₂ ⊢ s 
_⋯ᴿ_ {m = V} x   ρ  = var (ρ _ x)
(var x)         ⋯ᴿ ρ = var (ρ _ x)

"""

    part5 = """

_→ˢ_ : Scope → Scope → Set
S₁ →ˢ S₂ = ∀ s → S₁ ∋ s → S₂ ⊢ s 

variable
  σ σ₁ σ₂ σ₃ : S₁ →ˢ S₂  

⟨_⟩ : S₁ →ᴿ S₂ → S₁ →ˢ S₂ 
⟨ ρ ⟩ _ x = var (ρ _ x)
{-# INLINE ⟨_⟩ #-}

wkˢ : ∀ s → S →ˢ (s ∷ S)
wkˢ _ = ⟨ wk _ ⟩
{-# INLINE wkˢ #-}

idˢ : S →ˢ S
idˢ _ = var
{-# INLINE idˢ #-}

opaque  
  _∙_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂    
  _∙_  t σ _ zero = t
  (t ∙ σ) _ (suc x) = σ _ x 

  _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
  σ ↑ˢ s =  (var zero) ∙ λ s₁ x → (σ _ x) ⋯ᴿ wk _

_↑ˢ*_ : (S₁ →ˢ S₂) → ∀ S → ((S ++ S₁) →ˢ (S ++ S₂))
σ ↑ˢ* [] = σ
σ ↑ˢ* (s ∷ S) = (σ ↑ˢ* S) ↑ˢ s

opaque
  unfolding  _∙_ _↑ˢ_ 
  _⋯ˢ_ : S₁ ⊢[ m ] s → S₁ →ˢ S₂ → S₂ ⊢ s
  _⋯ˢ_ {m = V} x σ = σ _ x
  (var x) ⋯ˢ σ = σ _ x

"""

    part6 = """

  _⨟_ : S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
  (σ₁ ⨟ σ₂) _ x = (σ₁ _ x) ⋯ˢ σ₂

  lift-id            : idᴿ {S = S} ↑ᴿ s ≡ idᴿ 
  def-∙-zero           : zero ⋯ˢ (t ∙ σ)   ≡ t                             
  def-∙-suc            : suc x ⋯ˢ (t ∙ σ)  ≡ x ⋯ˢ σ 
  def-↑ˢ               : σ ↑ˢ s ≡ (var zero) ∙ (σ ⨟ wkˢ _)
  def-⨟ : (x ⋯ˢ (σ₁ ⨟ σ₂)) ≡ ((x ⋯ˢ σ₁) ⋯ˢ σ₂)

  associativity           : (σ₁ ⨟ σ₂) ⨟ σ₃                      ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)                     
  distributivityˢ         : (t ∙ σ₁) ⨟ σ₂                       ≡ ((t ⋯ˢ σ₂) ∙ (σ₁ ⨟ σ₂)) 
  distributivityᴿ         : (t ∙ σ₁) ⨟ ⟨ ρ₂ ⟩                   ≡ ((t ⋯ᴿ ρ₂) ∙ (σ₁ ⨟ ⟨ ρ₂ ⟩)) 
  interact                : wkˢ s ⨟ (t ∙ σ)                     ≡ σ                                        
  comp-idᵣ                : σ ⨟ idˢ                             ≡ σ                                               
  comp-idₗ                : idˢ ⨟ σ                             ≡ σ                                               
  η-id                    : (var (zero {s = s} {S = S})) ∙ (wkˢ _)  ≡ idˢ
  η-lawˢ                  : (zero ⋯ˢ σ) ∙ (wkˢ _ ⨟ σ)           ≡ σ
  η-lawᴿ                  : (zero ⋯ᴿ ρ) ∙ ((wkˢ _ ⨟ ⟨ ρ ⟩))     ≡ ⟨ ρ ⟩

  right-id                : ∀ (t : S ⊢ s) → t ⋯ᴿ idᴿ                   ≡ t   
  compositionalityᴿᴿ      : ∀ (t : S ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂   ≡ t ⋯ᴿ (ρ₁ ∘ ρ₂)     
  compositionalityᴿˢ      : ∀ (t : S ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ t ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂)                                    
  compositionalityˢᴿ      : ∀ (t : S ⊢ s) → (t ⋯ˢ σ₁) ⋯ᴿ ρ₂   ≡ t ⋯ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)                         
  compositionalityˢˢ      : ∀ (t : S ⊢ s) → (t ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ t ⋯ˢ (σ₁ ⨟ σ₂)


  traversal-var           : (var x)         ⋯ˢ σ  ≡ x ⋯ˢ σ
  traversal-var = refl

"""

    part7 = """

  coincidence              : {x/t : S ⊢[ m ] s} → x/t ⋯ˢ ⟨ ρ ⟩ ≡ x/t ⋯ᴿ ρ
  coincidence-fold         : x/t ⋯ˢ (⟨ ρ ↑ᴿ s ⟩ ⨟ ((x/t′ ⋯ᴿ ρ) ∙ idˢ))  ≡ x/t ⋯ˢ ((x/t′ ⋯ᴿ ρ) ∙ ⟨ ρ ⟩)


  lift-id = ext λ { zero → refl; (suc x) → refl }

  def-∙-zero = refl
  def-∙-suc  = refl
  def-↑ˢ     = cong1 ((var zero) ∙_) (sym (ext λ x → coincidence))
  def-⨟      = refl

  lift-idˢ* : ∀ S → (idˢ {S = S₁} ↑ˢ* S) ≡ idˢ 
  lift-idˢ* []    = refl
  lift-idˢ* {S₁} (_ ∷ S) rewrite lift-idˢ* {S₁} S = η-lawᴿ

  right-idˢ               : ∀ (t : S ⊢ s) → t ⋯ˢ idˢ                   ≡ t 
  right-idˢ (var x)        = refl

"""

    part8 = """

  associativity {σ₁ = σ₁} = ext λ x → compositionalityˢˢ (σ₁ _ x) 
  distributivityˢ = ext λ { zero → refl; (suc x) → refl }
  distributivityᴿ = ext λ { zero → coincidence; (suc x) → refl }
  interact        = refl
  comp-idᵣ        = ext λ x → (right-idˢ _)
  comp-idₗ        = refl
  η-id            = ext λ { zero → refl; (suc x) → refl }
  η-lawˢ          = ext λ { zero → refl; (suc x) → refl }
  η-lawᴿ          = ext λ { zero → refl; (suc x) → refl }

  lift-id* : ∀ S → (idᴿ {S = S₁} ↑ᴿ* S) ≡ idᴿ
  lift-id* []    = refl
  lift-id* {S₁}  (_ ∷ S) rewrite lift-id* {S₁} S = lift-id

  right-id (var x)        = refl

"""

    part9 = """
  lift-dist-compᴿᴿ : ((ρ₁ ↑ᴿ s) ∘ (ρ₂ ↑ᴿ s)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ s)
  lift-dist-compᴿᴿ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿᴿ : ∀ S → ((ρ₁ ↑ᴿ* S) ∘ (ρ₂ ↑ᴿ* S)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ* S)
  lift-dist-comp*ᴿᴿ []      = refl 
  lift-dist-comp*ᴿᴿ (_ ∷ S) = trans lift-dist-compᴿᴿ (cong1 (_↑ᴿ _) (lift-dist-comp*ᴿᴿ S))

  compositionalityᴿᴿ (var x)  = refl
"""

    part10 = """
  lift-dist-compᴿˢ : (⟨ ρ₁ ↑ᴿ s ⟩ ⨟ (σ₂ ↑ˢ s)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿˢ : ∀ S → (⟨ (ρ₁ ↑ᴿ* S) ⟩ ⨟ (σ₂ ↑ˢ* S)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ᴿˢ []      = refl 
  lift-dist-comp*ᴿˢ (_ ∷ S) = trans lift-dist-compᴿˢ (cong1 (_↑ˢ _) (lift-dist-comp*ᴿˢ S))

  compositionalityᴿˢ (var x)  = refl
"""

    part11 = """
  lift-dist-compˢᴿ : ((σ₁ ↑ˢ s) ⨟ ⟨ ρ₂ ↑ᴿ s ⟩) ≡ ((σ₁ ⨟ ⟨ ρ₂ ⟩) ↑ˢ s)
  lift-dist-compˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    (t ⋯ᴿ (wk _)) ⋯ˢ ⟨ ρ₂ ↑ᴿ _ ⟩ ≡⟨ coincidence ⟩ 
    (t ⋯ᴿ (wk _)) ⋯ᴿ (ρ₂ ↑ᴿ _)   ≡⟨ compositionalityᴿᴿ t ⟩ 
    t ⋯ᴿ (wk _ ∘ (ρ₂ ↑ᴿ _))    ≡⟨ sym (compositionalityᴿᴿ t) ⟩ 
    (t ⋯ᴿ ρ₂) ⋯ᴿ wk _          ≡⟨ cong1 (_⋯ᴿ (wk _)) (sym coincidence) ⟩ 
    (t ⋯ˢ ⟨ ρ₂ ⟩) ⋯ᴿ wk _      ∎ }

  lift-dist-comp*ˢᴿ : ∀ S → ((σ₁ ↑ˢ* S) ⨟ ⟨ ρ₂ ↑ᴿ* S ⟩) ≡ ((σ₁ ⨟ ⟨ ρ₂ ⟩) ↑ˢ* S )
  lift-dist-comp*ˢᴿ []      = refl 
  lift-dist-comp*ˢᴿ (_ ∷ S) =  trans lift-dist-compˢᴿ (cong1 (_↑ˢ _) (lift-dist-comp*ˢᴿ S))
 
  compositionalityˢᴿ (var x)  = sym coincidence
"""

    part12 = """
  lift-dist-compˢˢ : ((σ₁ ↑ˢ s) ⨟ (σ₂ ↑ˢ s)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ s)
  lift-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    begin
    (t ⋯ᴿ (wk _)) ⋯ˢ (σ₂ ↑ˢ _)    ≡⟨ compositionalityᴿˢ t ⟩ 
    t ⋯ˢ (⟨ (wk _) ⟩ ⨟ (σ₂ ↑ˢ _)) ≡⟨ cong1 (t ⋯ˢ_) (ext λ y → sym coincidence) ⟩   
    t ⋯ˢ (σ₂ ⨟ ⟨ (wk _) ⟩)        ≡⟨ sym (compositionalityˢᴿ t) ⟩ 
    (t ⋯ˢ σ₂) ⋯ᴿ (wk _)           ∎ }
  
  lift-dist-comp*ˢˢ : ∀ S →  ((σ₁ ↑ˢ* S) ⨟ (σ₂ ↑ˢ* S)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ˢˢ []      = refl 
  lift-dist-comp*ˢˢ (_ ∷ S) =  trans lift-dist-compˢˢ (cong1 (_↑ˢ _) (lift-dist-comp*ˢˢ S))

  compositionalityˢˢ (var x)  = refl
"""

    part13 = """
  coincidence {m = V} = refl
  coincidence {m = T} {ρ = ρ} {x/t = x/t} = 
    x/t ⋯ˢ (⟨ ρ ⟩ ⨟ idˢ) ≡⟨ sym (compositionalityᴿˢ x/t) ⟩ 
    (x/t ⋯ᴿ ρ) ⋯ˢ idˢ    ≡⟨ right-idˢ _ ⟩ 
    x/t ⋯ᴿ ρ             ∎

  coincidence-fold {x/t = x/t} {ρ = ρ} {x/t′ = x/t′} = 
    (x/t ⋯ˢ (⟨ ρ ↑ᴿ _ ⟩ ⨟ ((x/t′ ⋯ᴿ ρ) ∙ idˢ))) ≡⟨ cong1 (x/t ⋯ˢ_) (ext λ { zero → refl; (suc x) → refl }) ⟩ 
    (x/t ⋯ˢ ((x/t′ ⋯ᴿ ρ) ∙ ⟨ ρ ⟩))              ∎
"""

    return "".join(
        [
            part1,
            congs,
            part2,
            sorts,
            part3,
            constructors,
            part4,
            renaming,
            "\n\n",
            variables,
            part5,
            substitution,
            part6,
            traversal,
            part7,
            right_ids,
            part8,
            right_id,
            part9,
            compositionality_rr,
            part10,
            compositionality_rs,
            part11,
            compositionality_sr,
            part12,
            compositionality_ss,
            part13,
            rewrite_block,
        ]
    )


def generate_agda(sig: Signature, module_name: str) -> str:
    max_arity = get_max_arity(sig)

    return render_template(
        module_name=module_name,
        congs=generate_congs(max_arity),
        sorts=generate_sorts(sig),
        constructors=generate_constructors(sig),
        renaming=generate_map_clauses(sig, "⋯ᴿ", "ρ", "↑ᴿ*", ""),
        variables=generate_variables(sig),
        substitution=generate_map_clauses(sig, "⋯ˢ", "σ", "↑ˢ*", "  "),
        traversal=generate_traversal(sig),
        right_ids=generate_id_lemma(sig, "right-idˢ", "⋯ˢ_", "lift-idˢ*"),
        right_id=generate_id_lemma(sig, "right-id", "⋯ᴿ_", "lift-id*"),
        compositionality_rr=generate_compositionality_lemma(
            sig, "compositionalityᴿᴿ", "⋯ᴿ_", "lift-dist-comp*ᴿᴿ"
        ),
        compositionality_rs=generate_compositionality_lemma(
            sig, "compositionalityᴿˢ", "⋯ˢ_", "lift-dist-comp*ᴿˢ"
        ),
        compositionality_sr=generate_compositionality_lemma(
            sig, "compositionalityˢᴿ", "⋯ˢ_", "lift-dist-comp*ˢᴿ"
        ),
        compositionality_ss=generate_compositionality_lemma(
            sig, "compositionalityˢˢ", "⋯ˢ_", "lift-dist-comp*ˢˢ"
        ),
        rewrite_block=generate_rewrite_block(sig),
    )


# ==========================================
# 5. CLI
# ==========================================


def main():
    parser = argparse.ArgumentParser(
        description="Generate Agda boilerplate from a signature file."
    )
    parser.add_argument("files", nargs="+", help="Usage: [input.sig] output.agda")

    args = parser.parse_args()

    input_source = None
    output_path = None

    if len(args.files) == 1:
        output_path = args.files[0]
        if sys.stdin.isatty():
            print("Reading from stdin... (Press Ctrl+D to finish)", file=sys.stderr)
        input_source = sys.stdin.read()
    elif len(args.files) == 2:
        input_path = args.files[0]
        output_path = args.files[1]
        try:
            with open(input_path, "r") as f:
                input_source = f.read()
        except FileNotFoundError:
            print(f"Error: Input file '{input_path}' not found.", file=sys.stderr)
            sys.exit(1)
    else:
        parser.print_help()
        sys.exit(1)

    if not input_source or not input_source.strip():
        print("Error: Empty input.", file=sys.stderr)
        sys.exit(1)

    try:
        tokens = tokenize(input_source)
        signature = parse_signature(tokens)

        filename = os.path.basename(output_path)
        module_name = os.path.splitext(filename)[0]

        agda_code = generate_agda(signature, module_name)

        with open(output_path, "w") as f:
            f.write(agda_code)

        print(f"Successfully generated Agda code to '{output_path}'.")

    except SyntaxError as e:
        print(f"Syntax Error: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"An unexpected error occurred: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
