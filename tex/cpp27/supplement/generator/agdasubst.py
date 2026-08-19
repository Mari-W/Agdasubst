#!/usr/bin/env python3
# Disclaimer: We used GenAI in the process of writing this script.
import argparse
import os
import re
import sys
from collections.abc import Callable
from dataclasses import dataclass, field
from enum import Enum, auto

# ==========================================
# 1. AST
# ==========================================


# The per-argument proof an induction splices in: `f(argument, var_name)`.
ArgProof = Callable[["Argument", str], str]


@dataclass
class SortDecl:
    name: str
    # EXTENSION: a sort may be INDEXED BY DATA -- `pat : ℕ -> ℕ -> Type`
    # declares `pat : ℕ → ℕ → Sort`.  Uses then carry index expressions,
    # `pat 0 n`.  This is Sigma/FsubPatterns.agda's pattern sort.
    index_types: list[str] = field(default_factory=list[str])

    @property
    def arity(self) -> int:
        return len(self.index_types)


@dataclass
class Argument:
    binder_types: list[str]
    target_type: str
    external: bool = False
    # EXTENSION: `#n` -- a ℕ-valued INDEX argument, emitted as `(n : ℕ)`.
    # It is a real dependent argument: later argument types may mention it.
    index: bool = False
    # EXTENSION: `(b ^ n -> t)` -- a binder of VARIABLE ARITY.  The scope of
    # the body is extended by n copies of sort b, i.e. `ext* b n S`, and the
    # traversal pushes the map under all n at once with `↑ᴿ*[ b ] n`.
    iter_sort: str | None = None
    iter_arity: str | None = None
    # for an APPLIED sort (`pat 0 n`) the head, used to name variables
    sort_head: str | None = None

    def __post_init__(self) -> None:
        # A variable-arity binder is `(b ^ n -> t)`: it always has BOTH a
        # binder sort and an arity.  Half of one is a parser bug, and it
        # would otherwise surface much later as a `None` in emitted Agda.
        if (self.iter_sort is None) != (self.iter_arity is None):
            raise ValueError(
                "a variable-arity binder needs both a sort and an arity, got "
                f"iter_sort={self.iter_sort!r} iter_arity={self.iter_arity!r}")

    @property
    def is_iterated(self) -> bool:
        return self.iter_sort is not None

    @property
    def iterated(self) -> tuple[str, str]:
        """The (binder sort, arity) of a variable-arity binder.

        Use this rather than the two optional fields wherever the value is
        needed as a string: it is the one place the invariant is turned
        back into a non-optional pair."""
        if self.iter_sort is None or self.iter_arity is None:
            raise ValueError(f"not a variable-arity binder: {self!r}")
        return self.iter_sort, self.iter_arity

    @property
    def is_binder(self) -> bool:
        return len(self.binder_types) > 0

    @property
    def var_base(self) -> str:
        if self.index:
            return self.target_type
        if self.sort_head is not None:
            return self.sort_head
        if not self.external:
            return self.target_type
        sanitized = "".join(ch for ch in self.target_type if ch.isalnum() or ch == "_")
        if not sanitized:
            return "ext"
        if sanitized[0].isdigit():
            sanitized = "_" + sanitized
        return sanitized[0].lower() + sanitized[1:]

    def __repr__(self) -> str:
        if self.index:
            return f"#{self.target_type}"
        if self.is_iterated:
            return f"({self.iter_sort} ^ {self.iter_arity} -> {self.target_type})"
        if self.is_binder:
            binders = " -> ".join(self.binder_types)
            return f"({binders} -> {self.target_type})"
        if self.external:
            return f'"{self.target_type}"'
        return self.target_type


@dataclass
class ConstructorDecl:
    name: str
    arguments: list[Argument]
    target_sort: str


@dataclass
class Signature:
    sorts: list[SortDecl] = field(default_factory=list[SortDecl])
    constructors: list[ConstructorDecl] = field(default_factory=list[ConstructorDecl])

    def get_sort_names(self) -> list[str]:
        return [s.name for s in self.sorts]


# ==========================================
# 2. Lexer
# ==========================================


class TokenType(Enum):
    ID = auto()
    ARROW = auto()  # ->
    COLON = auto()  # :
    CARET = auto()  # ^  (variable-arity binder)
    NUMBER = auto()  # a literal index, e.g. the 0 in `pat 0 n`
    LPAREN = auto()  # (
    RPAREN = auto()  # )
    TYPE_KW = auto()  # Type
    STRING_LITERAL = auto()  # "..."
    EOF = auto()


@dataclass
class Token:
    type: TokenType
    value: str
    line: int
    column: int


TOKEN_SPEC: list[tuple[TokenType | None, str]] = [
    # EXTENSION: a BACKTICK-QUOTED identifier.  Agda names may contain
    # characters the bare `.sg` identifier syntax reserves -- ':' and '-'
    # above all -- so `∀[<:_]_` names the F<: universal quantifier and
    # `_+_`-style names become writable.  The backticks are stripped.
    (TokenType.ID, r"`[^`\n]+`"),
    (None, r"begin[^\n]*"),
    (None, r"end[^\n]*"),
    (TokenType.ARROW, r"->"),
    (TokenType.CARET, r"\^"),
    (TokenType.NUMBER, r"\d+"),
    (TokenType.LPAREN, r"\("),
    (TokenType.RPAREN, r"\)"),
    (TokenType.COLON, r":"),
    (TokenType.TYPE_KW, r"\bType\b"),
    (TokenType.STRING_LITERAL, r'"[^"\n]*"'),
    (TokenType.ID, r"[^\s():\"\-\d][^\s():\"\-]*"),
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
                    value = text
                    if (token_type is TokenType.ID and len(value) >= 2
                            and value[0] == "`" and value[-1] == "`"):
                        value = value[1:-1]
                    tokens.append(Token(token_type, value, line_num, column))

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


# The arity of each INDEXED sort, filled in by parse_signature as the
# declarations are read, and consulted by parse_argument so that `pat 0 n`
# is read as one applied sort rather than three separate arguments.
# Parser state, module-level so that `parse_argument` can see how many
# index expressions an APPLIED sort consumes (`pat 0 n` takes two).
# `parse_signature` clears it before every parse and is the only writer, so
# a signature can never see another signature's arities.  Not reentrant:
# one parse at a time.
sort_arity: dict[str, int] = {}


def parse_index(tokens: list[Token], pos: int) -> str:
    """One index expression: a literal, a variable, or a parenthesised
    application such as `(suc n)`."""
    t = peek(tokens, pos)
    if t.type in (TokenType.NUMBER, TokenType.ID):
        return t.value
    if t.type == TokenType.LPAREN:
        parts: list[str] = []
        pos += 1
        while peek(tokens, pos).type in (TokenType.ID, TokenType.NUMBER):
            parts.append(peek(tokens, pos).value)
            pos += 1
        if peek(tokens, pos).type != TokenType.RPAREN:
            raise SyntaxError(f"malformed index expression at line {t.line}")
        return "(" + " ".join(parts) + ")"
    raise SyntaxError(f"expected an index expression at line {t.line}, found {t.value!r}")


def skip_index(tokens: list[Token], pos: int) -> int:
    t = peek(tokens, pos)
    if t.type in (TokenType.NUMBER, TokenType.ID):
        return pos + 1
    pos += 1
    while peek(tokens, pos).type in (TokenType.ID, TokenType.NUMBER):
        pos += 1
    return pos + 1          # past the ')'


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
    sort_arity.clear()
    pos = 0

    while peek(tokens, pos).type != TokenType.EOF:
        id_token, pos = consume(tokens, pos, TokenType.ID)
        _, pos = consume(tokens, pos, TokenType.COLON)

        # A declaration whose chain ends in `Type` is a SORT declaration;
        # anything before the `Type` is the sort's index telescope.
        look = pos
        idx_types: list[str] = []
        while peek(tokens, look).type == TokenType.ID:
            idx_types.append(peek(tokens, look).value)
            look += 1
            if peek(tokens, look).type != TokenType.ARROW:
                break
            look += 1
        if peek(tokens, look).type == TokenType.TYPE_KW:
            pos = look + 1
            sig.sorts.append(SortDecl(name=id_token.value, index_types=idx_types))
            sort_arity[id_token.value] = len(idx_types)
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
            if parts[-1].external:
                raise SyntaxError(
                    f"Constructor {id_token.value} cannot return an external (quoted) type."
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
        lparen = peek(tokens, pos)
        _, pos = consume(tokens, pos, TokenType.LPAREN)
        inner_chain, pos = parse_type_chain(tokens, pos)
        _, pos = consume(tokens, pos, TokenType.RPAREN)

        if not inner_chain:
            raise SyntaxError("Empty parentheses in type signature.")

        if any(a.external for a in inner_chain):
            raise SyntaxError(
                f"External (quoted) types are not allowed inside binders at line {lparen.line}:{lparen.column}"
            )

        target = inner_chain[-1].target_type
        if inner_chain[-1].is_iterated:
            raise SyntaxError(
                f"a binder cannot RETURN a variable-arity position at line "
                f"{lparen.line}:{lparen.column}")
        iterated = [a for a in inner_chain[:-1] if a.is_iterated]
        if iterated:
            if len(inner_chain) != 2:
                raise SyntaxError(
                    f"a variable-arity binder `(b ^ n -> t)` must bind exactly "
                    f"that one position at line {lparen.line}:{lparen.column}")
            return Argument(binder_types=[], target_type=target,
                            iter_sort=iterated[0].iter_sort,
                            iter_arity=iterated[0].iter_arity), pos
        binder_types: list[str] = []
        for arg in inner_chain[:-1]:
            binder_types.append(arg.target_type)

        return Argument(binder_types=binder_types, target_type=target), pos

    elif peek(tokens, pos).type == TokenType.ID:
        token, pos = consume(tokens, pos, TokenType.ID)
        # EXTENSION: an INDEXED sort consumes exactly its declared number of
        # index expressions -- `pat 0 n`, `rpat n₂ n₃`, `pat n (suc n)`.
        arity = sort_arity.get(token.value, 0)
        if arity:
            idx: list[str] = []
            for _ in range(arity):
                idx.append(parse_index(tokens, pos))
                pos = skip_index(tokens, pos)
            return Argument(binder_types=[],
                            target_type=f"{token.value} {' '.join(idx)}",
                            sort_head=token.value), pos
        # EXTENSION: `#n` is a ℕ-valued index argument.
        if token.value.startswith("#"):
            name = token.value[1:]
            if not name:
                raise SyntaxError(f"empty index name at line {token.line}")
            return Argument(binder_types=[], target_type=name, index=True), pos
        # EXTENSION: `b ^ n` is a variable-arity binder position.
        if peek(tokens, pos).type == TokenType.CARET:
            _, pos = consume(tokens, pos, TokenType.CARET)
            arity_tok, pos = consume(tokens, pos, TokenType.ID)
            return Argument(binder_types=[], target_type=token.value,
                            iter_sort=token.value,
                            iter_arity=arity_tok.value), pos
        return Argument(binder_types=[], target_type=token.value), pos
    elif peek(tokens, pos).type == TokenType.STRING_LITERAL:
        token, pos = consume(tokens, pos, TokenType.STRING_LITERAL)
        inner = token.value[1:-1]
        return Argument(binder_types=[], target_type=inner, external=True), pos
    else:
        raise SyntaxError(
            f"Unexpected token in type signature: {peek(tokens, pos).value} at line {peek(tokens, pos).line}"
        )


# ── BEGIN TEMPLATE CHUNKS ──

# AUTO-EXTRACTED from Reference/Fsub.agda by extract_template.py.
# DO NOT EDIT BY HAND.  See that script for the line ranges.

MAPS_REN_A = r'''-- ─── maps ───────────────────────────────────────────────────────────

_→[_]_ : Scope → Mode → Scope → Set
S₁ →[ m ] S₂ = ∀ s → S₁ ∋ s → S₂ ⊢[ m ] s

_→ᴿ_ : Scope → Scope → Set
S₁ →ᴿ S₂ = S₁ →[ V ] S₂

_→ˢ_ : Scope → Scope → Set
S₁ →ˢ S₂ = S₁ →[ T ] S₂

variable
  ξ ξ′ ξ₁ ξ₂ ξ₃ : S₁ →ᴿ S₂
  σ σ₁ σ₂ σ₃ τ : S₁ →ˢ S₂

-- ─── the renaming world ─────────────────────────────────────────────

opaque
  idᴿ : S →ᴿ S
  idᴿ _ x = x

  wkᴿ : ∀ s′ → S →ᴿ (s′ ∷ S)
  wkᴿ _ _ x = suc x

  _∙ᴿ_ : S₂ ∋ s → S₁ →ᴿ S₂ → (s ∷ S₁) →ᴿ S₂
  (x ∙ᴿ ξ) _ zero    = x
  (_ ∙ᴿ ξ) _ (suc x) = ξ _ x

opaque
  unfolding wkᴿ

  _↑ᴿ_ : S₁ →ᴿ S₂ → ∀ s → (s ∷ S₁) →ᴿ (s ∷ S₂)
  (ξ ↑ᴿ _) _ zero    = zero
  (ξ ↑ᴿ _) _ (suc x) = suc (ξ _ x)'''

MAPS_REN_B = r'''  _[_]ᴿ : S₁ ⊢[ m ] s → S₁ →ᴿ S₂ → S₂ ⊢[ m ] s
  _[_]ᴿ {m = V} x ξ    = ξ _ x'''

COMP_SUB_A = r'''  _⨟ᴿ_ : S₁ →ᴿ S₂ → S₂ →ᴿ S₃ → S₁ →ᴿ S₃
  (ξ₁ ⨟ᴿ ξ₂) _ x = (ξ₁ _ x) [ ξ₂ ]ᴿ

-- ─── the substitution world ─────────────────────────────────────────

opaque
  ⟨_⟩ : S₁ →ᴿ S₂ → S₁ →ˢ S₂
  ⟨ ξ ⟩ _ x = «VAR» (x [ ξ ]ᴿ)

idˢ : S →ˢ S
idˢ = ⟨ idᴿ ⟩

wkˢ : ∀ s′ → S →ˢ (s′ ∷ S)
wkˢ s′ = ⟨ wkᴿ s′ ⟩

opaque
  _∙ˢ_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂
  (t ∙ˢ σ) _ zero    = t
  (t ∙ˢ σ) _ (suc x) = σ _ x'''

COMP_SUB_B = r'''  _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
  (σ ↑ˢ _) _ zero    = «VAR» zero
  (σ ↑ˢ _) _ (suc x) = (σ _ x) [ wkᴿ _ ]ᴿ'''

COMP_SUB_C = r'''  _[_]ˢ : S₁ ⊢[ m ] s → S₁ →ˢ S₂ → S₂ ⊢ s'''

COMP_SUB_D = r'''  _[_]ˢ {m = V} x σ    = σ _ x'''

SEQ_DECLS_A = r'''  _⨟_ : S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
  (σ₁ ⨟ σ₂) _ x = (σ₁ _ x) [ σ₂ ]ˢ

'''

SEQ_DECLS_B = r'''-- ─── the two-world rewrite system ───────────────────────────────────

opaque
  unfolding idᴿ wkᴿ _∙ᴿ_ _↑ᴿ_ _[_]ᴿ _⨟ᴿ_ ⟨_⟩ _∙ˢ_ _[_]ˢ _↑ˢ_ _⨟_

  -- ══ Iᴿ. applied rules, renaming world ═════════════════════════════
  def-wkᴿ       : x [ wkᴿ s′ ]ᴿ ≡ suc x
  def-∙ᴿ-zero   : zero [ (x ∙ᴿ ξ) ]ᴿ ≡ x
  def-∙ᴿ-suc    : (suc {s′ = s′} x′) [ (x ∙ᴿ ξ) ]ᴿ ≡ x′ [ ξ ]ᴿ
  def-↑ᴿ-zero   : zero [ (ξ ↑ᴿ s) ]ᴿ ≡ zero
  def-↑ᴿ-suc    : (suc x) [ (ξ ↑ᴿ s) ]ᴿ ≡ suc (x [ ξ ]ᴿ)

  -- ══ IIᴿ. traversal rules, renaming world ═════════════════════════'''

ALG_R = r'''
  -- ══ IIIᴿ. map algebra, renaming world ════════════════════════════
  assocᴿ      : (ξ₁ ⨟ᴿ ξ₂) ⨟ᴿ ξ₃ ≡ ξ₁ ⨟ᴿ (ξ₂ ⨟ᴿ ξ₃)
  comp-idₗᴿ   : idᴿ ⨟ᴿ ξ ≡ ξ
  comp-idᵣᴿ   : ξ ⨟ᴿ idᴿ ≡ ξ
  distᴿ       : (x ∙ᴿ ξ₁) ⨟ᴿ ξ₂ ≡ (x [ ξ₂ ]ᴿ) ∙ᴿ (ξ₁ ⨟ᴿ ξ₂)
  interactᴿ   : wkᴿ s ⨟ᴿ (x ∙ᴿ ξ) ≡ ξ

  -- ══ IVᴿ. lifting rules, renaming world ═══════════════════════════
  lift-idᴿ     : (idᴿ {S} ↑ᴿ s) ≡ idᴿ
  lift-dist-compᴿᴿ : ((ξ₁ ↑ᴿ s) ⨟ᴿ (ξ₂ ↑ᴿ s)) ≡ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s)
  lift-wkᴿ     : wkᴿ s ⨟ᴿ (ξ ↑ᴿ s) ≡ ξ ⨟ᴿ wkᴿ s
  lift-consᴿ   : (ξ ↑ᴿ s) ⨟ᴿ (x ∙ᴿ ξ′) ≡ x ∙ᴿ (ξ ⨟ᴿ ξ′)

  -- ══ Vᴿ. monad laws, renaming world ═══════════════════════════════
  right-idᴿ : ∀ (x/t : S ⊢[ m ] s) → x/t [ idᴿ ]ᴿ ≡ x/t
  compositionalityᴿᴿ-var  : ∀ (x : S₁ ∋ s) {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
    x [ (ξ₁ ⨟ᴿ ξ₂) ]ᴿ ≡ (x [ ξ₁ ]ᴿ) [ ξ₂ ]ᴿ
  compositionalityᴿᴿ   : ∀ (t : S₁ ⊢ s) {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
    (t [ ξ₁ ]ᴿ) [ ξ₂ ]ᴿ ≡ t [ (ξ₁ ⨟ᴿ ξ₂) ]ᴿ

  -- ══ VIᴿ. completion companions, renaming world ═══════════════════
  lift-dist-compᴿᴿ-var  : (x [ (ξ₁ ↑ᴿ s) ]ᴿ) [ (ξ₂ ↑ᴿ s) ]ᴿ ≡ x [ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s) ]ᴿ
  interactᴿ-⨟ᴿ    : wkᴿ s ⨟ᴿ ((x ∙ᴿ ξ) ⨟ᴿ ξ′) ≡ ξ ⨟ᴿ ξ′
  lift-wkᴿ-⨟ᴿ     : wkᴿ s ⨟ᴿ ((ξ ↑ᴿ s) ⨟ᴿ ξ′) ≡ ξ ⨟ᴿ (wkᴿ s ⨟ᴿ ξ′)
  lift-dist-compᴿᴿ-⨟ᴿ : (ξ₁ ↑ᴿ s) ⨟ᴿ ((ξ₂ ↑ᴿ s) ⨟ᴿ ξ′) ≡ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s) ⨟ᴿ ξ′

  -- ══ Iˢ. applied rules, substitution world ════════════════════════
  coincidence-var : x [ ⟨ ξ ⟩ ]ˢ ≡ «VAR» (x [ ξ ]ᴿ)
  def-∙ˢ-zero  : zero [ (t ∙ˢ σ) ]ˢ ≡ t
  def-∙ˢ-suc   : (suc {s′ = s′} x) [ (t ∙ˢ σ) ]ˢ ≡ x [ σ ]ˢ
  def-↑ˢ-zero  : zero [ (σ ↑ˢ s) ]ˢ ≡ «VAR» zero
  def-↑ˢ-suc   : (suc x) [ (σ ↑ˢ s) ]ˢ ≡ x [ (σ ⨟ ⟨ wkᴿ s ⟩) ]ˢ

  -- ══ IIˢ. traversal rules, substitution world ═════════════════════'''

COMPANION_S = r'''
  -- ══ VIˢ. completion companions, substitution world ══════════════
  compositionalityᴿˢ-⨟-var      : x [ (⟨ ξ ⟩ ⨟ σ) ]ˢ ≡ (x [ ξ ]ᴿ) [ σ ]ˢ
  def-↑ˢ-zero-⨟  : zero [ ((σ ↑ˢ s) ⨟ τ) ]ˢ ≡ zero [ τ ]ˢ
  def-↑ˢ-suc-⨟   : (suc x) [ ((σ ↑ˢ s) ⨟ τ) ]ˢ ≡ x [ (σ ⨟ (⟨ wkᴿ s ⟩ ⨟ τ)) ]ˢ
  lift-wk-⨟     : ⟨ wkᴿ s ⟩ ⨟ ((σ ↑ˢ s) ⨟ τ) ≡ σ ⨟ (⟨ wkᴿ s ⟩ ⨟ τ)
  lift-dist-compˢˢ-⨟ : (σ₁ ↑ˢ s) ⨟ ((σ₂ ↑ˢ s) ⨟ τ) ≡ ((σ₁ ⨟ σ₂) ↑ˢ s) ⨟ τ

  -- ══ IIIˢ/IVˢ. map algebra and lifting, substitution world ════════
  interact    : ⟨ wkᴿ s ⟩ ⨟ (t ∙ˢ σ) ≡ σ
  comp-idₗ    : ⟨ idᴿ {S₁} ⟩ ⨟ σ ≡ σ
  comp-idᵣ    : σ ⨟ ⟨ idᴿ ⟩ ≡ σ
  lift-wk     : ⟨ wkᴿ s ⟩ ⨟ (σ ↑ˢ s) ≡ σ ⨟ ⟨ wkᴿ s ⟩
  assoc       : (σ₁ ⨟ σ₂) ⨟ σ₃ ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)
  dist        : (t ∙ˢ σ₁) ⨟ σ₂ ≡ (t [ σ₂ ]ˢ) ∙ˢ (σ₁ ⨟ σ₂)
  lift-cons   : (σ ↑ˢ s) ⨟ (t ∙ˢ τ) ≡ t ∙ˢ (σ ⨟ τ)
  lift-dist-compˢˢ : ((σ₁ ↑ˢ s) ⨟ (σ₂ ↑ˢ s)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ s)

  -- ══ Vˢ. monad laws, substitution world ═══════════════════════════
  compositionalityˢˢ : ∀ (x/t : S₁ ⊢[ m ] s) {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃} →
    (x/t [ σ₁ ]ˢ) [ σ₂ ]ˢ ≡ x/t [ (σ₁ ⨟ σ₂) ]ˢ

  -- ══ the two mixed compositionality laws ══════════════════════════
  compositionalityᴿˢ : ∀ (t : S₁ ⊢ s) {ξ₁ : S₁ →ᴿ S₂} {σ₂ : S₂ →ˢ S₃} →
    (t [ ξ₁ ]ᴿ) [ σ₂ ]ˢ ≡ t [ (⟨ ξ₁ ⟩ ⨟ σ₂) ]ˢ
  compositionalityˢᴿ : ∀ (x/t : S₁ ⊢[ m ] s) {σ₁ : S₁ →ˢ S₂} {ξ₂ : S₂ →ᴿ S₃} →
    (x/t [ σ₁ ]ˢ) [ ξ₂ ]ᴿ ≡ x/t [ (σ₁ ⨟ ⟨ ξ₂ ⟩) ]ˢ

  lift-dist-compᴿˢ-⨟ : ∀ {S₄} {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} {τ : (s ∷ S₃) →ˢ S₄} →
    ⟨ ξ ↑ᴿ s ⟩ ⨟ ((σ ↑ˢ s) ⨟ τ) ≡ ((⟨ ξ ⟩ ⨟ σ) ↑ˢ s) ⨟ τ
  lift-dist-compˢᴿ-⨟ : ∀ {S₄} {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} {τ : (s ∷ S₃) →ˢ S₄} →
    (σ ↑ˢ s) ⨟ (⟨ ξ ↑ᴿ s ⟩ ⨟ τ) ≡ ((σ ⨟ ⟨ ξ ⟩) ↑ˢ s) ⨟ τ
  lift-dist-compᴿˢ-var  : (x [ (ξ ↑ᴿ s) ]ᴿ) [ (σ ↑ˢ s) ]ˢ ≡ x [ ((⟨ ξ ⟩ ⨟ σ) ↑ˢ s) ]ˢ
  lift-dist-compᴿˢ-⨟-var : ∀ {S₄} {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} {τ : (s ∷ S₃) →ˢ S₄} →
    (x [ (ξ ↑ᴿ s) ]ᴿ) [ ((σ ↑ˢ s) ⨟ τ) ]ˢ ≡ x [ (((⟨ ξ ⟩ ⨟ σ) ↑ˢ s) ⨟ τ) ]ˢ

  ⟨⟩-lift-cons : ⟨ ξ ↑ᴿ s ⟩ ⨟ (t ∙ˢ σ) ≡ t ∙ˢ (⟨ ξ ⟩ ⨟ σ)
  ⟨⟩-lift-cons-var : (x [ (ξ ↑ᴿ s) ]ᴿ) [ (t ∙ˢ σ) ]ˢ ≡ x [ (t ∙ˢ (⟨ ξ ⟩ ⨟ σ)) ]ˢ

  ⟨⟩-comp-⨟-lift-wkᴿ  : ∀ {S₄} {ξ : S₁ →ᴿ S₂} {τ : (s ∷ S₂) →ˢ S₄} →
    ⟨ wkᴿ s ⟩ ⨟ (⟨ ξ ↑ᴿ s ⟩ ⨟ τ) ≡ ⟨ ξ ⟩ ⨟ (⟨ wkᴿ s ⟩ ⨟ τ)
  ⟨⟩-comp-⨟-interactᴿ  : ∀ {ξ : S₁ →ᴿ S₂} {x : S₂ ∋ s} {τ : S₂ →ˢ S₃} →
    ⟨ wkᴿ s ⟩ ⨟ (⟨ x ∙ᴿ ξ ⟩ ⨟ τ) ≡ ⟨ ξ ⟩ ⨟ τ
  ⟨⟩-comp-⨟-lift-dist-compᴿᴿ : ∀ {S₄} {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} {τ : (s ∷ S₃) →ˢ S₄} →
    ⟨ ξ₁ ↑ᴿ s ⟩ ⨟ (⟨ ξ₂ ↑ᴿ s ⟩ ⨟ τ) ≡ ⟨ (ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s ⟩ ⨟ τ
  ⟨⟩-split-tail : ∀ {S₄} {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} {ξ′ : (s ∷ S₃) →ᴿ S₄} →
    (σ ↑ˢ s) ⨟ ⟨ (ξ ↑ᴿ s) ⨟ᴿ ξ′ ⟩ ≡ ((σ ⨟ ⟨ ξ ⟩) ↑ˢ s) ⨟ ⟨ ξ′ ⟩

  -- ══ the collapse family ══════════════════════════════════════════
  coincidence  : ∀ (t : S ⊢ s) (ξ : S →ᴿ S₂) → t [ ⟨ ξ ⟩ ]ˢ ≡ t [ ξ ]ᴿ
  ⟨⟩-comp      : ⟨ ξ₁ ⟩ ⨟ ⟨ ξ₂ ⟩ ≡ ⟨ ξ₁ ⨟ᴿ ξ₂ ⟩
  ⟨⟩-split-⨟   : ⟨ ξ₁ ⨟ᴿ ξ₂ ⟩ ⨟ σ ≡ ⟨ ξ₁ ⟩ ⨟ (⟨ ξ₂ ⟩ ⨟ σ)
  ⟨⟩-lift      : (⟨ ξ ⟩ ↑ˢ s) ≡ ⟨ ξ ↑ᴿ s ⟩

  -- ══ SUBSUMED: σ⇑'s LiftId is a lemma, not a rule ════════════════
  -- ⟨⟩-lift already sends its LHS to ⟨ idᴿ ↑ᴿ s ⟩, where lift-idᴿ
  -- finishes under the coercion.  A base rule subsumed by its own
  -- coercion image is redundant; it still holds by refl for user code.
  lift-id     : (⟨ idᴿ {S} ⟩ ↑ˢ s) ≡ ⟨ idᴿ ⟩

  -- ══ η: lemmas only ═══════════════════════════════════════════════
  η-idᴿ  : (zero {s = s} {S = S}) ∙ᴿ (wkᴿ s) ≡ idᴿ
  η-lawᴿ : (zero [ ξ ]ᴿ) ∙ᴿ (wkᴿ s ⨟ᴿ ξ) ≡ ξ
  η-id   : («VAR» zero) ∙ˢ (wkˢ s) ≡ idˢ {S = s ∷ S}
  η-law  : (zero [ σ ]ˢ) ∙ˢ (wkˢ s ⨟ σ) ≡ σ
  def-↑ᴿ : ξ ↑ᴿ s ≡ zero ∙ᴿ (ξ ⨟ᴿ wkᴿ s)
  def-↑ˢ  : σ ↑ˢ s ≡ («VAR» zero) ∙ˢ (σ ⨟ wkˢ s)
'''

IR_PROOFS = r'''  -- ── proofs ────────────────────────────────────────────────────────

  def-wkᴿ     = refl
  def-∙ᴿ-zero = refl
  def-∙ᴿ-suc  = refl
  def-↑ᴿ-zero = refl
  def-↑ᴿ-suc  = refl
'''

ALG_R_PROOF = r'''
  assocᴿ {ξ₁ = ξ₁} {ξ₂ = ξ₂} {ξ₃ = ξ₃} = ext λ x → sym (compositionalityᴿᴿ-var (ξ₁ _ x) {ξ₁ = ξ₂} {ξ₂ = ξ₃})
  comp-idₗᴿ = refl
  comp-idᵣᴿ = ext λ x → right-idᴿ _
  distᴿ     = ext λ { zero → refl ; (suc x) → refl }
  interactᴿ = refl

  lift-idᴿ     = ext λ { zero → refl ; (suc x) → refl }
  lift-dist-compᴿᴿ = ext λ { zero → refl ; (suc x) → refl }
  lift-wkᴿ     = refl
  lift-consᴿ   = ext λ { zero → refl ; (suc x) → refl }
'''

CRR_VAR = r'''
  compositionalityᴿᴿ-var x           = refl'''

PROOF_MID = r'''
  lift-dist-compᴿᴿ-var {x = zero}  = refl
  lift-dist-compᴿᴿ-var {x = suc x} = refl
  interactᴿ-⨟ᴿ    = refl
  lift-wkᴿ-⨟ᴿ {s = s} {ξ = ξ} {ξ′ = ξ′} =
    trans (sym (assocᴿ {ξ₁ = wkᴿ s} {ξ₂ = ξ ↑ᴿ s} {ξ₃ = ξ′}))
          (trans (cong (_⨟ᴿ ξ′) (lift-wkᴿ {s = s} {ξ = ξ}))
                 (assocᴿ {ξ₁ = ξ} {ξ₂ = wkᴿ s} {ξ₃ = ξ′}))
  lift-dist-compᴿᴿ-⨟ᴿ {ξ₁ = ξ₁} {s = s} {ξ₂ = ξ₂} {ξ′ = ξ′} =
    trans (sym (assocᴿ {ξ₁ = ξ₁ ↑ᴿ s} {ξ₂ = ξ₂ ↑ᴿ s} {ξ₃ = ξ′}))
          (cong (_⨟ᴿ ξ′) (lift-dist-compᴿᴿ {ξ₁ = ξ₁} {s = s} {ξ₂ = ξ₂}))

  coincidence-var = refl
  def-∙ˢ-zero  = refl
  def-∙ˢ-suc   = refl
  def-↑ˢ-zero  = refl
  def-↑ˢ-suc {x = x} {σ = σ} {s = s} = sym (coincidence (σ _ x) (wkᴿ s))
  compositionalityᴿˢ-⨟-var     = refl
  def-↑ˢ-zero-⨟ = refl
  def-↑ˢ-suc-⨟ {x = x} {σ = σ} {s = s} {τ = τ} =
    trans (compositionalityᴿˢ (σ _ x)) (cong ((σ _ x) [_]ˢ) (ext λ y → refl))
  interact  = refl
  comp-idₗ  = refl
  comp-idᵣ {σ = σ} = ext λ y → trans (coincidence (σ _ y) idᴿ) (right-idᴿ (σ _ y))
  lift-wk {s = s} {σ = σ} = ext λ y → sym (coincidence (σ _ y) (wkᴿ s))
  lift-id   = ext λ { zero → refl ; (suc x) → refl }
  lift-wk-⨟ {s = s} {σ = σ} {τ = τ} =
    trans (sym (assoc {σ₁ = ⟨ wkᴿ s ⟩} {σ₂ = σ ↑ˢ s} {σ₃ = τ}))
          (trans (cong (_⨟ τ) (lift-wk {s = s} {σ = σ}))
                 (assoc {σ₁ = σ} {σ₂ = ⟨ wkᴿ s ⟩} {σ₃ = τ}))
  lift-dist-compˢˢ-⨟ {σ₁ = σ₁} {s = s} {σ₂ = σ₂} {τ = τ} =
    trans (sym (assoc {σ₁ = σ₁ ↑ˢ s} {σ₂ = σ₂ ↑ˢ s} {σ₃ = τ}))
          (cong (_⨟ τ) (lift-dist-compˢˢ {σ₁ = σ₁} {s = s} {σ₂ = σ₂}))
'''

LDC_RS = r'''
  lift-dist-compᴿˢ : ∀ {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} →
    (⟨ ξ ↑ᴿ s ⟩ ⨟ (σ ↑ˢ s)) ≡ ((⟨ ξ ⟩ ⨟ σ) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl ; (suc x) → refl }
'''

LDC_SR = r'''
  lift-dist-compˢᴿ : ∀ {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} →
    ((σ ↑ˢ s) ⨟ ⟨ ξ ↑ᴿ s ⟩) ≡ ((σ ⨟ ⟨ ξ ⟩) ↑ˢ s)
  lift-dist-compˢᴿ {s = s} {σ = σ} {ξ = ξ} = ext λ where
    zero    → refl
    (suc x) → let t = σ _ x in
      trans (coincidence (t [ wkᴿ s ]ᴿ) (ξ ↑ᴿ s))
      (trans (compositionalityᴿᴿ t {ξ₁ = wkᴿ s} {ξ₂ = ξ ↑ᴿ s})
      (trans (cong (t [_]ᴿ) (lift-wkᴿ {s = s} {ξ = ξ}))
      (trans (sym (compositionalityᴿᴿ t {ξ₁ = ξ} {ξ₂ = wkᴿ s}))
             (cong (_[ wkᴿ s ]ᴿ) (sym (coincidence t ξ))))))
'''

LDC_SS = r'''
  lift-dist-compˢˢ {σ₁ = σ₁} {s = s} {σ₂ = σ₂} = ext λ where
    zero    → refl
    (suc x) → let t = σ₁ _ x in
      trans (compositionalityᴿˢ t)
      (trans (cong (t [_]ˢ) (ext λ y → sym (coincidence (σ₂ _ y) (wkᴿ s))))
             (sym (compositionalityˢᴿ t)))
'''

ASSOC_DIST = r'''
  assoc {σ₁ = σ₁} {σ₂ = σ₂} {σ₃ = σ₃} = ext λ x → compositionalityˢˢ (σ₁ _ x) {σ₁ = σ₂} {σ₂ = σ₃}
  dist            = ext λ { zero → refl ; (suc x) → refl }
  lift-cons {σ = σ} {t = t} {τ = τ} = ext λ where
    zero    → refl
    (suc x) → trans (compositionalityᴿˢ (σ _ x)) (cong ((σ _ x) [_]ˢ) (ext λ y → refl))
'''

TAIL_PROOF = r'''
  lift-dist-compᴿˢ-⨟ {s = s} {ξ = ξ} {σ = σ} {τ = τ} =
    trans (sym (assoc {σ₁ = ⟨ ξ ↑ᴿ s ⟩} {σ₂ = σ ↑ˢ s} {σ₃ = τ}))
          (cong (_⨟ τ) (lift-dist-compᴿˢ {s = s} {ξ = ξ} {σ = σ}))
  lift-dist-compˢᴿ-⨟ {s = s} {σ = σ} {ξ = ξ} {τ = τ} =
    trans (sym (assoc {σ₁ = σ ↑ˢ s} {σ₂ = ⟨ ξ ↑ᴿ s ⟩} {σ₃ = τ}))
          (cong (_⨟ τ) (lift-dist-compˢᴿ {s = s} {σ = σ} {ξ = ξ}))
  lift-dist-compᴿˢ-var {x = zero}  = refl
  lift-dist-compᴿˢ-var {x = suc x} = refl
  lift-dist-compᴿˢ-⨟-var {x = zero}  = refl
  lift-dist-compᴿˢ-⨟-var {x = suc x} = refl
  ⟨⟩-comp-⨟-lift-wkᴿ    = ext λ x → refl
  ⟨⟩-comp-⨟-interactᴿ    = ext λ x → refl
  ⟨⟩-comp-⨟-lift-dist-compᴿᴿ  = ext λ { zero → refl ; (suc x) → refl }
  ⟨⟩-split-tail {s = s} {σ = σ} {ξ = ξ} {ξ′ = ξ′} = ext λ where
    zero    → refl
    (suc x) → let t = σ _ x in begin
        (t [ wkᴿ s ]ᴿ) [ ⟨ (ξ ↑ᴿ s) ⨟ᴿ ξ′ ⟩ ]ˢ
      ≡⟨ coincidence (t [ wkᴿ s ]ᴿ) ((ξ ↑ᴿ s) ⨟ᴿ ξ′) ⟩
        (t [ wkᴿ s ]ᴿ) [ ((ξ ↑ᴿ s) ⨟ᴿ ξ′) ]ᴿ
      ≡⟨ compositionalityᴿᴿ t {ξ₁ = wkᴿ s} {ξ₂ = (ξ ↑ᴿ s) ⨟ᴿ ξ′} ⟩
        t [ (wkᴿ s ⨟ᴿ ((ξ ↑ᴿ s) ⨟ᴿ ξ′)) ]ᴿ
      ≡⟨ cong (t [_]ᴿ) (lift-wkᴿ-⨟ᴿ {s = s} {ξ = ξ} {ξ′ = ξ′}) ⟩
        t [ (ξ ⨟ᴿ (wkᴿ s ⨟ᴿ ξ′)) ]ᴿ
      ≡⟨ sym (compositionalityᴿᴿ t {ξ₁ = ξ} {ξ₂ = wkᴿ s ⨟ᴿ ξ′}) ⟩
        (t [ ξ ]ᴿ) [ (wkᴿ s ⨟ᴿ ξ′) ]ᴿ
      ≡⟨ cong (_[ (wkᴿ s ⨟ᴿ ξ′) ]ᴿ) (sym (coincidence t ξ)) ⟩
        (t [ ⟨ ξ ⟩ ]ˢ) [ (wkᴿ s ⨟ᴿ ξ′) ]ᴿ
      ≡⟨ sym (compositionalityᴿᴿ (t [ ⟨ ξ ⟩ ]ˢ) {ξ₁ = wkᴿ s} {ξ₂ = ξ′}) ⟩
        ((t [ ⟨ ξ ⟩ ]ˢ) [ wkᴿ s ]ᴿ) [ ξ′ ]ᴿ
      ≡⟨ sym (coincidence ((t [ ⟨ ξ ⟩ ]ˢ) [ wkᴿ s ]ᴿ) ξ′) ⟩
        ((t [ ⟨ ξ ⟩ ]ˢ) [ wkᴿ s ]ᴿ) [ ⟨ ξ′ ⟩ ]ˢ
      ∎
  ⟨⟩-lift-cons  = ext λ { zero → refl ; (suc x) → refl }
  ⟨⟩-lift-cons-var {x = zero}  = refl
  ⟨⟩-lift-cons-var {x = suc x} = refl
  ⟨⟩-comp    = ext λ x → refl
  ⟨⟩-split-⨟ = ext λ x → refl
  ⟨⟩-lift    = ext λ { zero → refl ; (suc x) → refl }

  η-idᴿ  = ext λ { zero → refl ; (suc x) → refl }
  η-lawᴿ = ext λ { zero → refl ; (suc x) → refl }
  η-id   = ext λ { zero → refl ; (suc x) → refl }
  η-law  = ext λ { zero → refl ; (suc x) → refl }
  def-↑ᴿ = ext λ { zero → refl ; (suc x) → refl }
  def-↑ˢ {σ = σ} {s = s} = ext λ { zero → refl ; (suc x) → sym (coincidence (σ _ x) (wkᴿ s)) }
'''

EPILOGUE = r'''-- ─── the derived operations ─────────────────────────────────────────
-- Neither is primitive and neither has rules of its own: weakening is a
-- renaming, single substitution is a cons onto the identity.  The
-- rewrite system computes through both without knowing they exist.

weaken : S ⊢ s → (s′ ∷ S) ⊢ s
weaken t = t [ wkᴿ _ ]ᴿ

_[_]₀ : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s
t [ t′ ]₀ = t [ (t′ ∙ˢ idˢ) ]ˢ'''

# ── END TEMPLATE CHUNKS ──

# ── BEGIN LIFT-STAR ──

# AUTO-EXTRACTED from Reference/FsubPatterns.agda by extract_lift_star.py.
# DO NOT EDIT BY HAND.

STAR_EXT = r'''
-- ─── iterated lifting: a binder of VARIABLE ARITY ───────────────────
--
-- `ext* b n S` extends a scope by n copies of ONE sort.  DERIVED and
-- TRANSPARENT: it computes on n, so the rewrite system needs rules only
-- for the case where n is abstract.
--
-- Generalized from gen/Reference/FsubPatterns.agda, which fixes b := expr.

ext* : Sort → ℕ → Scope → Scope
ext* b zero    S = S
ext* b (suc n) S = b ∷ ext* b n S
'''

STAR_LIFT_R = r'''
-- The n-fold renaming lift.  Derived and transparent, and defined
-- BETWEEN the _↑ᴿ_ block and the _[_]ᴿ block, because the traversal of a
-- variable-arity binder uses it.

_↑ᴿ*[_]_ : S₁ →ᴿ S₂ → ∀ b n → (ext* b n S₁) →ᴿ (ext* b n S₂)
ξ ↑ᴿ*[ b ] zero    = ξ
ξ ↑ᴿ*[ b ] (suc n) = (ξ ↑ᴿ*[ b ] n) ↑ᴿ b
'''

STAR_LIFT_S = r'''
-- The n-fold substitution lift, likewise between _↑ˢ_ and _[_]ˢ.

_↑ˢ*[_]_ : S₁ →ˢ S₂ → ∀ b n → (ext* b n S₁) →ˢ (ext* b n S₂)
σ ↑ˢ*[ b ] zero    = σ
σ ↑ˢ*[ b ] (suc n) = (σ ↑ˢ*[ b ] n) ↑ˢ b
'''

STAR_DECLS = r'''
  -- ITERATED lifting.  Unlike records, patterns FORCE these to be
  -- REWRITE RULES: without lift*-idᴿ the pair (right-idᴿ, instᴿ-let) is
  -- not joinable, because `e₂ [ idᴿ ↑ᴿ*[ b ] n ]ᴿ` is stuck for abstract n.
  lift*-idᴿ         : ∀ b n → (idᴿ {S} ↑ᴿ*[ b ] n) ≡ idᴿ
  lift*-dist-compᴿᴿ : ∀ b n → ((ξ₁ ↑ᴿ*[ b ] n) ⨟ᴿ (ξ₂ ↑ᴿ*[ b ] n)) ≡ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ*[ b ] n)
  lift*-dist-compᴿˢ : ∀ b n {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} →
    (⟨ ξ ↑ᴿ*[ b ] n ⟩ ⨟ (σ ↑ˢ*[ b ] n)) ≡ ((⟨ ξ ⟩ ⨟ σ) ↑ˢ*[ b ] n)
  lift*-dist-compˢᴿ : ∀ b n {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} →
    ((σ ↑ˢ*[ b ] n) ⨟ ⟨ ξ ↑ᴿ*[ b ] n ⟩) ≡ ((σ ⨟ ⟨ ξ ⟩) ↑ˢ*[ b ] n)
  lift*-dist-compˢˢ : ∀ b n → ((σ₁ ↑ˢ*[ b ] n) ⨟ (σ₂ ↑ˢ*[ b ] n)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ*[ b ] n)
  ⟨⟩-lift*          : ∀ b n → (⟨ ξ ⟩ ↑ˢ*[ b ] n) ≡ ⟨ ξ ↑ᴿ*[ b ] n ⟩

  -- THE ITERATED COMPLETION COMPANIONS.  One for each `-var` / `-⨟ᴿ` /
  -- `-⨟` companion of the single-lifting layer; each closes exactly the
  -- pair that its single-lifting counterpart closes, one level up.
  lift*-dist-compᴿᴿ-var : ∀ {S₁ S₂ S₃} (b : Sort) (n : ℕ) {s} {x : (ext* b n S₁) ∋ s}
    {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
    (x [ (ξ₁ ↑ᴿ*[ b ] n) ]ᴿ) [ (ξ₂ ↑ᴿ*[ b ] n) ]ᴿ ≡ x [ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ*[ b ] n) ]ᴿ
  lift*-dist-compᴿᴿ-⨟ᴿ : ∀ {S₁ S₂ S₃ S₄} (b : Sort) (n : ℕ) {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃}
    {ξ′ : (ext* b n S₃) →ᴿ S₄} →
    (ξ₁ ↑ᴿ*[ b ] n) ⨟ᴿ ((ξ₂ ↑ᴿ*[ b ] n) ⨟ᴿ ξ′) ≡ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ*[ b ] n) ⨟ᴿ ξ′
  lift*-dist-compˢˢ-⨟ : ∀ {S₁ S₂ S₃} (b : Sort) (n : ℕ) {S₄} {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃}
    {τ : (ext* b n S₃) →ˢ S₄} →
    (σ₁ ↑ˢ*[ b ] n) ⨟ ((σ₂ ↑ˢ*[ b ] n) ⨟ τ) ≡ ((σ₁ ⨟ σ₂) ↑ˢ*[ b ] n) ⨟ τ
  lift*-dist-compᴿˢ-⨟ : ∀ {S₁ S₂ S₃} (b : Sort) (n : ℕ) {S₄} {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃}
    {τ : (ext* b n S₃) →ˢ S₄} →
    ⟨ ξ ↑ᴿ*[ b ] n ⟩ ⨟ ((σ ↑ˢ*[ b ] n) ⨟ τ) ≡ ((⟨ ξ ⟩ ⨟ σ) ↑ˢ*[ b ] n) ⨟ τ
  lift*-dist-compˢᴿ-⨟ : ∀ {S₁ S₂ S₃} (b : Sort) (n : ℕ) {S₄} {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃}
    {τ : (ext* b n S₃) →ˢ S₄} →
    (σ ↑ˢ*[ b ] n) ⨟ (⟨ ξ ↑ᴿ*[ b ] n ⟩ ⨟ τ) ≡ ((σ ⨟ ⟨ ξ ⟩) ↑ˢ*[ b ] n) ⨟ τ
  lift*-dist-compᴿˢ-var : ∀ {S₁ S₂ S₃} (b : Sort) (n : ℕ) {s} {x : (ext* b n S₁) ∋ s}
    {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} →
    (x [ (ξ ↑ᴿ*[ b ] n) ]ᴿ) [ (σ ↑ˢ*[ b ] n) ]ˢ ≡ x [ ((⟨ ξ ⟩ ⨟ σ) ↑ˢ*[ b ] n) ]ˢ
  ⟨⟩-comp-⨟-lift*-dist-compᴿᴿ : ∀ {S₁ S₂ S₃} (b : Sort) (n : ℕ) {S₄} {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃}
    {τ : (ext* b n S₃) →ˢ S₄} →
    ⟨ ξ₁ ↑ᴿ*[ b ] n ⟩ ⨟ (⟨ ξ₂ ↑ᴿ*[ b ] n ⟩ ⨟ τ) ≡ ⟨ (ξ₁ ⨟ᴿ ξ₂) ↑ᴿ*[ b ] n ⟩ ⨟ τ
  lift*-dist-compᴿˢ-⨟-var : ∀ {S₁ S₂ S₃} (b : Sort) (n : ℕ) {S₄} {s} {x : (ext* b n S₁) ∋ s}
    {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} {τ : (ext* b n S₃) →ˢ S₄} →
    (x [ (ξ ↑ᴿ*[ b ] n) ]ᴿ) [ ((σ ↑ˢ*[ b ] n) ⨟ τ) ]ˢ ≡ x [ (((⟨ ξ ⟩ ⨟ σ) ↑ˢ*[ b ] n) ⨟ τ) ]ˢ
  ⟨⟩-split*-tail : ∀ {S₁ S₂ S₃} (b : Sort) (n : ℕ) {S₄} {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃}
    {ξ′ : (ext* b n S₃) →ᴿ S₄} →
    (σ ↑ˢ*[ b ] n) ⨟ ⟨ (ξ ↑ᴿ*[ b ] n) ⨟ᴿ ξ′ ⟩ ≡ ((σ ⨟ ⟨ ξ ⟩) ↑ˢ*[ b ] n) ⨟ ⟨ ξ′ ⟩'''

STAR_PROOFS = r'''  lift*-idᴿ b zero    = refl
  lift*-idᴿ b (suc n) = trans (cong (_↑ᴿ b) (lift*-idᴿ b n)) lift-idᴿ
  lift*-dist-compᴿᴿ b zero = refl
  lift*-dist-compᴿᴿ {ξ₁ = ξ₁} {ξ₂ = ξ₂} b (suc n) =
    trans (lift-dist-compᴿᴿ {ξ₁ = ξ₁ ↑ᴿ*[ b ] n} {s = b} {ξ₂ = ξ₂ ↑ᴿ*[ b ] n})
          (cong (_↑ᴿ b) (lift*-dist-compᴿᴿ b n))
  lift*-dist-compᴿˢ b zero = refl
  lift*-dist-compᴿˢ b (suc n) {ξ = ξ} {σ = σ} =
    trans (lift-dist-compᴿˢ {s = b} {ξ = ξ ↑ᴿ*[ b ] n} {σ = σ ↑ˢ*[ b ] n})
          (cong (_↑ˢ b) (lift*-dist-compᴿˢ b n))
  lift*-dist-compˢᴿ b zero = refl
  lift*-dist-compˢᴿ b (suc n) {σ = σ} {ξ = ξ} =
    trans (lift-dist-compˢᴿ {s = b} {σ = σ ↑ˢ*[ b ] n} {ξ = ξ ↑ᴿ*[ b ] n})
          (cong (_↑ˢ b) (lift*-dist-compˢᴿ b n))
  lift*-dist-compˢˢ b zero = refl
  lift*-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂} b (suc n) =
    trans (lift-dist-compˢˢ {σ₁ = σ₁ ↑ˢ*[ b ] n} {s = b} {σ₂ = σ₂ ↑ˢ*[ b ] n})
          (cong (_↑ˢ b) (lift*-dist-compˢˢ b n))
  ⟨⟩-lift* b zero    = refl
  ⟨⟩-lift* {ξ = ξ} b (suc n) =
    trans (cong (_↑ˢ b) (⟨⟩-lift* b n)) (⟨⟩-lift {ξ = ξ ↑ᴿ*[ b ] n} {s = b})

  lift*-dist-compᴿᴿ-var b zero = refl
  lift*-dist-compᴿᴿ-var b (suc n) {x = x} {ξ₁ = ξ₁} {ξ₂ = ξ₂} =
    trans (lift-dist-compᴿᴿ-var {x = x} {ξ₁ = ξ₁ ↑ᴿ*[ b ] n} {ξ₂ = ξ₂ ↑ᴿ*[ b ] n})
          (cong (λ z → x [ (z ↑ᴿ b) ]ᴿ) (lift*-dist-compᴿᴿ b n))
  lift*-dist-compᴿᴿ-⨟ᴿ b zero {ξ₁ = ξ₁} {ξ₂ = ξ₂} {ξ′ = ξ′} =
    sym (assocᴿ {ξ₁ = ξ₁} {ξ₂ = ξ₂} {ξ₃ = ξ′})
  lift*-dist-compᴿᴿ-⨟ᴿ b (suc n) {ξ₁ = ξ₁} {ξ₂ = ξ₂} {ξ′ = ξ′} =
    trans (lift-dist-compᴿᴿ-⨟ᴿ {ξ₁ = ξ₁ ↑ᴿ*[ b ] n} {ξ₂ = ξ₂ ↑ᴿ*[ b ] n} {ξ′ = ξ′})
          (cong (λ z → (z ↑ᴿ b) ⨟ᴿ ξ′) (lift*-dist-compᴿᴿ b n))
  lift*-dist-compˢˢ-⨟ b zero {σ₁ = σ₁} {σ₂ = σ₂} {τ = τ} =
    sym (assoc {σ₁ = σ₁} {σ₂ = σ₂} {σ₃ = τ})
  lift*-dist-compˢˢ-⨟ b (suc n) {σ₁ = σ₁} {σ₂ = σ₂} {τ = τ} =
    trans (lift-dist-compˢˢ-⨟ {σ₁ = σ₁ ↑ˢ*[ b ] n} {σ₂ = σ₂ ↑ˢ*[ b ] n} {τ = τ})
          (cong (λ z → (z ↑ˢ b) ⨟ τ) (lift*-dist-compˢˢ b n))
  lift*-dist-compᴿˢ-⨟ b zero {ξ = ξ} {σ = σ} {τ = τ} =
    sym (assoc {σ₁ = ⟨ ξ ⟩} {σ₂ = σ} {σ₃ = τ})
  lift*-dist-compᴿˢ-⨟ b (suc n) {ξ = ξ} {σ = σ} {τ = τ} =
    trans (lift-dist-compᴿˢ-⨟ {s = b} {ξ = ξ ↑ᴿ*[ b ] n} {σ = σ ↑ˢ*[ b ] n} {τ = τ})
          (cong (λ z → (z ↑ˢ b) ⨟ τ) (lift*-dist-compᴿˢ b n))
  lift*-dist-compˢᴿ-⨟ b zero {σ = σ} {ξ = ξ} {τ = τ} =
    sym (assoc {σ₁ = σ} {σ₂ = ⟨ ξ ⟩} {σ₃ = τ})
  lift*-dist-compˢᴿ-⨟ b (suc n) {σ = σ} {ξ = ξ} {τ = τ} =
    trans (lift-dist-compˢᴿ-⨟ {s = b} {σ = σ ↑ˢ*[ b ] n} {ξ = ξ ↑ᴿ*[ b ] n} {τ = τ})
          (cong (λ z → (z ↑ˢ b) ⨟ τ) (lift*-dist-compˢᴿ b n))
  lift*-dist-compᴿˢ-var b zero {x = x} {ξ = ξ} {σ = σ} = sym (compositionalityᴿˢ-⨟-var {x = x} {ξ = ξ} {σ = σ})
  lift*-dist-compᴿˢ-var b (suc n) {x = x} {ξ = ξ} {σ = σ} =
    trans (lift-dist-compᴿˢ-var {x = x} {ξ = ξ ↑ᴿ*[ b ] n} {σ = σ ↑ˢ*[ b ] n})
          (cong (λ z → x [ (z ↑ˢ b) ]ˢ) (lift*-dist-compᴿˢ b n))
  ⟨⟩-comp-⨟-lift*-dist-compᴿᴿ b zero {ξ₁ = ξ₁} {ξ₂ = ξ₂} {τ = τ} =
    sym (⟨⟩-split-⨟ {ξ₁ = ξ₁} {ξ₂ = ξ₂} {σ = τ})
  ⟨⟩-comp-⨟-lift*-dist-compᴿᴿ b (suc n) {ξ₁ = ξ₁} {ξ₂ = ξ₂} {τ = τ} =
    trans (⟨⟩-comp-⨟-lift-dist-compᴿᴿ {ξ₁ = ξ₁ ↑ᴿ*[ b ] n} {ξ₂ = ξ₂ ↑ᴿ*[ b ] n} {τ = τ})
          (cong (λ z → ⟨ z ↑ᴿ b ⟩ ⨟ τ) (lift*-dist-compᴿᴿ b n))

  lift*-dist-compᴿˢ-⨟-var b zero {x = x} {ξ = ξ} {σ = σ} {τ = τ} =
    trans (sym (compositionalityᴿˢ-⨟-var {x = x} {ξ = ξ} {σ = σ ⨟ τ}))
          (cong (x [_]ˢ) (sym (assoc {σ₁ = ⟨ ξ ⟩} {σ₂ = σ} {σ₃ = τ})))
  lift*-dist-compᴿˢ-⨟-var b (suc n) {x = x} {ξ = ξ} {σ = σ} {τ = τ} =
    trans (lift-dist-compᴿˢ-⨟-var {x = x} {ξ = ξ ↑ᴿ*[ b ] n} {σ = σ ↑ˢ*[ b ] n} {τ = τ})
          (cong (λ z → x [ ((z ↑ˢ b) ⨟ τ) ]ˢ) (lift*-dist-compᴿˢ b n))
  ⟨⟩-split*-tail b zero {σ = σ} {ξ = ξ} {ξ′ = ξ′} =
    sym (trans (assoc {σ₁ = σ} {σ₂ = ⟨ ξ ⟩} {σ₃ = ⟨ ξ′ ⟩})
               (cong (σ ⨟_) (⟨⟩-comp {ξ₁ = ξ} {ξ₂ = ξ′})))
  ⟨⟩-split*-tail b (suc n) {σ = σ} {ξ = ξ} {ξ′ = ξ′} =
    trans (⟨⟩-split-tail {σ = σ ↑ˢ*[ b ] n} {ξ = ξ ↑ᴿ*[ b ] n} {ξ′ = ξ′})
          (cong (λ z → (z ↑ˢ b) ⨟ ⟨ ξ′ ⟩) (lift*-dist-compˢᴿ b n))'''

STAR_RULES = ['lift*-idᴿ', 'lift*-dist-compᴿᴿ', 'lift*-dist-compᴿˢ', 'lift*-dist-compˢᴿ', 'lift*-dist-compˢˢ', '⟨⟩-lift*', 'lift*-dist-compᴿᴿ-var', 'lift*-dist-compᴿᴿ-⨟ᴿ', 'lift*-dist-compˢˢ-⨟', 'lift*-dist-compᴿˢ-⨟', 'lift*-dist-compˢᴿ-⨟', 'lift*-dist-compᴿˢ-var', '⟨⟩-comp-⨟-lift*-dist-compᴿᴿ', 'lift*-dist-compᴿˢ-⨟-var', '⟨⟩-split*-tail']

# ── END LIFT-STAR ──

# ==========================================
# 4. Agda code generation
# ==========================================
#
# The emitted module carries the CURATED (locally confluent) rule set of
# the hand-written reference core, gen/Reference/Fsub.agda.  Everything
# that is syntax-independent is the verbatim text of that file (the chunk
# constants above, produced by `extract_template.py`); the emitter below
# supplies only the syntax-dependent parts:
#
#   * data Sort, the constructor declarations, the variable block
#   * the `_[_]ᴿ` / `_[_]ˢ` clauses
#   * the `instᴿ-*` / `inst-*` rules and their `refl` proofs
#   * the constructor cases of right-idᴿ, compositionality{ᴿᴿ,ᴿˢ,ˢᴿ,ˢˢ}
#     and coincidence
#   * the {-# REWRITE #-} block
#
# EXTENSION over the hand-written core: a binder may bind SEVERAL variables
# (`lam : ty -> (vl -> tm -> tm) -> vl`).  The hand core only ever lifts a
# map once; here a k-ary binder lifts k times, `((ξ ↑ᴿ b₁) ↑ᴿ b₂)`, and the
# five structural inductions chain their lifting lemma k times.  No new
# REWRITE rule is needed — iterated lifting is iterated use of the same
# single-lift rules.


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

        s = (f"{name} : ∀ {{{sets} : Set}} (f : {arrows}) {{{implicits}}} →\n"
             f"  {eqs} → f {lhs_args} ≡ f {rhs_args}")
        refls = " ".join(["refl"] * n)
        defn = f"{name} f {refls} = refl"

        lines.append(s)
        lines.append(defn)
        lines.append("")

    return "\n".join(lines)


def generate_sorts(sig: Signature) -> str:
    plain = [d.name for d in sig.sorts if d.arity == 0]
    lines = ["data Sort : Set where"]
    if plain:
        lines.append(f"  {' '.join(plain)} : Sort")
    for d in sig.sorts:
        if d.arity:
            lines.append(f"  {d.name} : {' → '.join(d.index_types)} → Sort")
    return "\n".join(lines)


IDX_RESERVED = {"suc", "zero"}


def all_nat_vars(sig: Signature) -> list[str]:
    out = list(index_vars(sig))
    for c in sig.constructors:
        for a in c.arguments:
            if a.index and a.target_type not in out:
                out.append(a.target_type)
            if a.is_iterated and a.iterated[1] not in out:
                out.append(a.iterated[1])
    return out


def index_vars(sig: Signature) -> list[str]:
    """Every identifier that occurs in an index position and is not a
    literal or a ℕ constructor.  These become generalizable ℕ variables."""
    out: list[str] = []

    def scan(applied: str) -> None:
        for tok in applied.replace("(", " ").replace(")", " ").split()[1:]:
            if tok in IDX_RESERVED or tok.isdigit() or tok in out:
                continue
            out.append(tok)

    for c in sig.constructors:
        for a in c.arguments:
            if a.sort_head is not None:
                scan(a.target_type)
        if " " in c.target_sort:
            scan(c.target_sort)
    return out


def generate_constructors(sig: Signature, var_name: str = "var") -> str:
    out: list[str] = []
    max_name_len = max([len(c.name) for c in sig.constructors] + [len(var_name), 4])

    def decl(name: str, ty: str) -> str:
        return f"  {name}{' ' * (max_name_len - len(name))} : {ty}"

    out.append(decl("zero", "(s ∷ S) ∋ s"))
    out.append(decl("suc", "S ∋ s → (s′ ∷ S) ∋ s"))
    out.append(decl(var_name, "S ∋ s → S ⊢ s"))

    for c in sig.constructors:
        arg_strs: list[str] = []
        for arg in c.arguments:
            if arg.index:
                arg_strs.append(f"({arg.target_type} : ℕ)")
            elif arg.is_iterated:
                arg_strs.append(
                    f"(ext* {arg.iter_sort} {arg.iter_arity} S) ⊢ {arg.target_type}")
            elif arg.is_binder:
                context_ext = " ∷ ".join(reversed(arg.binder_types))
                arg_strs.append(f"({context_ext} ∷ S) ⊢ {arg.target_type}")
            elif arg.external:
                arg_strs.append(arg.target_type)
            else:
                arg_strs.append(f"S ⊢ {arg.target_type}")
        full_type = " → ".join(arg_strs + [f"S ⊢ {c.target_sort}"])
        padding = " " * (max_name_len - len(c.name))
        out.append(f"  {c.name}{padding} : {full_type}")

    return "\n".join(out)


def arg_names(c: ConstructorDecl) -> list[str]:
    names: list[str] = []
    counts: dict[str, int] = {}
    for arg in c.arguments:
        if arg.index:                       # `#n` is referred to by its own name
            names.append(arg.target_type)
            continue
        base = arg.var_base
        idx = counts.get(base, 0)
        counts[base] = idx + 1
        names.append(f"{base}{idx}")
    return names


def ctor_index_vars(c: ConstructorDecl) -> list[str]:
    """Index variables this constructor mentions, anywhere."""
    out: list[str] = []

    def scan(applied: str) -> None:
        for tok in applied.replace("(", " ").replace(")", " ").split()[1:]:
            if tok not in IDX_RESERVED and not tok.isdigit() and tok not in out:
                out.append(tok)

    for a in c.arguments:
        if a.sort_head is not None:
            scan(a.target_type)
        if a.is_iterated and a.iterated[1] not in out:
            out.append(a.iterated[1])
    if " " in c.target_sort:
        scan(c.target_sort)
    return out


def target_only_index_vars(c: ConstructorDecl) -> list[str]:
    """Index variables that occur ONLY in the conclusion.  Nothing in the
    arguments determines them, so a rewrite rule must pin them explicitly --
    this is `nilP {S = S} {n = n}` in ../Sigma/FsubPatterns.agda."""
    in_args: set[str] = set()
    for a in c.arguments:
        if a.sort_head is not None:
            in_args.update(t for t in a.target_type.replace("(", " ").replace(")", " ").split()[1:])
        if a.is_iterated:
            in_args.add(a.iterated[1])
        if a.index:
            in_args.add(a.target_type)
    out: list[str] = []
    if " " in c.target_sort:
        for tok in c.target_sort.replace("(", " ").replace(")", " ").split()[1:]:
            if (tok not in IDX_RESERVED and not tok.isdigit()
                    and tok not in in_args and tok not in out):
                out.append(tok)
    return out


def mentions_index(c: ConstructorDecl) -> bool:
    return bool(ctor_index_vars(c))


def iter_pins(c: ConstructorDecl) -> str:
    """Pins the induction clauses need: the arity of a variable-arity binder
    is mentioned by the proof body, so it must be bound by the pattern.  If
    the arity is an explicit `#n` argument it is already bound and must NOT
    be pinned -- it is not an implicit argument at all."""
    explicit = {a.target_type for a in c.arguments if a.index}
    return "".join(f" {{{a.iter_arity} = {a.iter_arity}}}"
                   for a in c.arguments
                   if a.is_iterated and a.iter_arity not in explicit)


def arg_agda_type(arg: Argument) -> str:
    """The Agda type of a constructor argument, in scope `S`."""
    if arg.index:
        return "ℕ"
    if arg.external:
        return arg.target_type
    if arg.is_iterated:
        return f"(ext* {arg.iter_sort} {arg.iter_arity} S) ⊢ {arg.target_type}"
    if arg.is_binder:
        return f"({' ∷ '.join(reversed(arg.binder_types))} ∷ S) ⊢ {arg.target_type}"
    return f"S ⊢ {arg.target_type}"


def needs_dep_cong(c: ConstructorDecl) -> bool:
    """A constructor carrying a ℕ index is a DEPENDENT function -- a later
    argument's type mentions the index -- so the non-dependent `congN`
    helpers do not apply to it.  It gets its own congruence instead, with
    the index (and any external parameter) held FIXED on both sides.  This
    is what ../Sigma/FsubPatterns.agda writes by hand as `cong-let`."""
    return any(a.index for a in c.arguments) or mentions_index(c)


def generate_dep_congs(sig: Signature) -> str:
    out: list[str] = []
    for c in sig.constructors:
        if not needs_dep_cong(c):
            continue
        names = arg_names(c)
        fixed = [(a, v) for a, v in zip(c.arguments, names, strict=True) if a.index or a.external]
        vary = [(a, v) for a, v in zip(c.arguments, names, strict=True) if not (a.index or a.external)]
        if not vary:
            continue
        binds = " ".join(f"{{{v} {v}′ : {arg_agda_type(a)}}}" for a, v in vary)
        prem = " → ".join(f"{v} ≡ {v}′" for _, v in vary)
        lhs = " ".join(names)
        rhs = " ".join(v if (a.index or a.external) else v + "′"
                       for a, v in zip(c.arguments, names, strict=True))
        fixed_binds = "".join(f" {{{v} : {arg_agda_type(a)}}}" for a, v in fixed)
        # An index variable that occurs ONLY in the conclusion is determined by
        # nothing in the premises, so pin it on both sides or it stays a meta.
        pins = "".join(f" {{{v} = {v}}}" for v in target_only_index_vars(c))
        head = f"{c.name}{pins}"
        out.append(f"cong-{c.name} :{fixed_binds} {binds} →")
        out.append(f"  {prem} → {head} {lhs} ≡ {head} {rhs}")
        out.append(f"cong-{c.name} {' '.join(['refl'] * len(vary))} = refl")
        out.append("")
    return "\n".join(out)


def generate_variables(sig: Signature) -> str:
    used_vars: set[str] = set()
    used_vars_type: dict[str, str] = {}
    used_vars_external: dict[str, bool] = {}

    index_names: list[str] = []      # now declared in the EARLY variable block
    for c in sig.constructors:
        for arg, var_name in zip(c.arguments, arg_names(c), strict=True):
            if arg.index:
                continue          # declared in the EARLY variable block
            if arg.sort_head is not None:
                continue          # bound explicitly per rule, not generalized
            if var_name in used_vars and (
                used_vars_type[var_name] != arg.target_type
                or used_vars_external[var_name] != arg.external
            ):
                raise SyntaxError(
                    f"Variable name '{var_name}' would be declared with conflicting "
                    f"types: '{used_vars_type[var_name]}' and '{arg.target_type}'. "
                    f"Rename one of the external types or sorts."
                )
            used_vars.add(var_name)
            used_vars_type[var_name] = arg.target_type
            used_vars_external[var_name] = arg.external

    vars_by_type: dict[tuple[str, bool], list[str]] = {}
    for v in sorted(used_vars):
        key = (used_vars_type[v], used_vars_external[v])
        vars_by_type.setdefault(key, []).append(v)

    if not vars_by_type and not index_names:
        return ""

    lines = ["variable"]
    if index_names:
        lines.append(f"  {' '.join(index_names)} : ℕ")
    for (t, external), vs in vars_by_type.items():
        v_str = " ".join(vs)
        lines.append(f"  {v_str} : {t}" if external else f"  {v_str} : S ⊢ {t}")

    return "\n".join(lines)


# ── lifting: a k-ary binder lifts the map k times ────────────────────


def lifted(map_var: str, binders: list[str], lift_op: str) -> str:
    """`ξ`, `(ξ ↑ᴿ b₁)`, `((ξ ↑ᴿ b₁) ↑ᴿ b₂)`, … — the map under a binder.

    The constructor's scope extension is `(bₖ ∷ … ∷ b₁ ∷ S)` (the binder
    list reversed), so b₁ is lifted first."""
    e = map_var
    for b in binders:
        e = f"({e} {lift_op} {b})"
    return e


def chain(binders: list[str], base: str, step_fun: str, base_first: bool) -> str:
    """Iterate a single-lift lemma over a k-ary binder.

    base_first = True  : Pₖ = trans (cong step Pₖ₋₁) base   (lemma applies OUTSIDE)
    base_first = False : Pₖ = trans base (cong step Pₖ₋₁)   (lemma applies at the top)
    """
    p = base
    for b in binders[1:]:
        if base_first:
            p = f"(trans (cong ({step_fun} {b}) {p}) {base})"
        else:
            p = f"(trans {base} (cong ({step_fun} {b}) {p}))"
    return p


# ── the syntax-dependent blocks ──────────────────────────────────────


def unparen(t: str) -> str:
    """Drop one fully-enclosing paren pair: inside `[ … ]ᴿ` it is redundant."""
    if not (t.startswith("(") and t.endswith(")")):
        return t
    depth = 0
    for i, c in enumerate(t):
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return t[1:-1] if i == len(t) - 1 else t
    return t


def generate_map_clauses(sig: Signature, op: str, map_var: str, lift_op: str) -> str:
    """`op` is the WORLD SUFFIX (ᴿ / ˢ): the traversal is the mixfix `_[_]ᴿ`."""
    data: list[tuple[str, str]] = []
    for c in sig.constructors:
        names = arg_names(c)
        # In a DEFINING CLAUSE a generalizable variable is not in scope, so an
        # arity that comes from an indexed sort is written `_` and inferred.
        # An arity introduced by an explicit `#n` argument is bound by the
        # pattern and is written by name.
        bound = {a.target_type for a in c.arguments if a.index}
        rhs_args: list[str] = []
        for arg, v in zip(c.arguments, names, strict=True):
            if arg.external or arg.index:
                rhs_args.append(v)
            elif arg.is_iterated:
                ar = arg.iter_arity if arg.iter_arity in bound else "_"
                rhs_args.append(f"({v} [ {map_var} {lift_op}*[ {arg.iter_sort} ] "
                                f"{ar} ]{op})")
            elif arg.is_binder:
                rhs_args.append(f"({v} [ {unparen(lifted(map_var, arg.binder_types, lift_op))} ]{op})")
            else:
                rhs_args.append(f"({v} [ {map_var} ]{op})")
        pat = " ".join(names)
        lhs = f"({c.name} {pat})" if pat else f"{c.name}"
        rhs = f"{c.name} {' '.join(rhs_args)}" if rhs_args else f"{c.name}"
        data.append((lhs, rhs))

    width = max([len(l) for l, _ in data], default=0)
    return "\n".join(
        f"  {l}{' ' * (width - len(l))} [ {map_var} ]{op} = {r}" for l, r in data
    )


def generate_inst_decls(sig: Signature, prefix: str, op: str, map_var: str,
                        lift_op: str) -> str:
    data: list[tuple[str, str, str]] = []
    for c in sig.constructors:
        names = arg_names(c)
        rhs_args: list[str] = []
        for arg, v in zip(c.arguments, names, strict=True):
            if arg.external or arg.index:
                rhs_args.append(v)
            elif arg.is_iterated:
                rhs_args.append(f"({v} [ {map_var} {lift_op}*[ {arg.iter_sort} ] "
                                f"{arg.iter_arity} ]{op})")
            elif arg.is_binder:
                rhs_args.append(f"({v} [ {unparen(lifted(map_var, arg.binder_types, lift_op))} ]{op})")
            else:
                rhs_args.append(f"({v} [ {map_var} ]{op})")
        pat = " ".join(names)
        pins = "".join(f" {{{v} = {v}}}" for v in target_only_index_vars(c))
        head = f"{c.name}{pins}" if pins else c.name
        if pat:
            lhs = f"({head} {pat}) [ {map_var} ]{op}"
        else:
            lhs = f"{head} {{S = S}} [ {map_var} ]{op}" if not pins else \
                  f"{head[:len(c.name)]} {{S = S}}{pins} [ {map_var} ]{op}"
        rhs = f"{c.name} {' '.join(rhs_args)}" if rhs_args else f"{c.name}"
        # An index-carrying constructor gets an EXPLICIT telescope, because the
        # global `variable` block cannot express the index linkage between its
        # arguments (consP : pat n₁ n₂ → rpat n₂ n₃ → rpat n₁ n₃).
        tele = ""
        if mentions_index(c):
            binds = " ".join(f"{{{v} : {arg_agda_type(a)}}}"
                             for a, v in zip(c.arguments, names, strict=True)
                             if not (a.index or a.external))
            if binds:
                tele = f"∀ {binds} → "
        data.append((f"{prefix}-{c.name}", tele + lhs, rhs))

    nw = max([len(n) for n, _, _ in data], default=0)
    lw = max([len(l) for _, l, _ in data], default=0)
    return "\n".join(
        f"  {n}{' ' * (nw - len(n))} : {l}{' ' * (lw - len(l))} ≡ {r}"
        for n, l, r in data
    )


def generate_refl_proofs(sig: Signature, prefix: str) -> str:
    names = [f"{prefix}-{c.name}" for c in sig.constructors]
    nw = max([len(n) for n in names], default=0)
    return "\n".join(f"  {n}{' ' * (nw - len(n))} = refl" for n in names)


def generate_induction(sig: Signature, lemma: str,
                       arg_proof: ArgProof) -> str:
    """One structural induction: one clause per constructor, `congN` of the
    per-argument proofs supplied by `arg_proof(arg, var_name)`."""
    data: list[tuple[str, str]] = []
    for c in sig.constructors:
        names = arg_names(c)
        pat = " ".join(names)
        head = c.name + iter_pins(c)
        lhs = f"{lemma} ({head} {pat})" if pat else f"{lemma} {c.name}"
        if needs_dep_cong(c):
            proofs = [arg_proof(a, v) for a, v in zip(c.arguments, names, strict=True)
                      if not (a.index or a.external)]
            rhs = f"cong-{c.name} " + " ".join(proofs) if proofs else "refl"
        else:
            proofs = [arg_proof(arg, v) for arg, v in zip(c.arguments, names, strict=True)]
            rhs = "refl" if not proofs else f"cong{len(proofs)} {c.name} " + " ".join(proofs)
        data.append((lhs, rhs))
    width = max([len(l) for l, _ in data], default=0)
    return "\n".join(f"  {l}{' ' * (width - len(l))} = {r}" for l, r in data)


def right_idR_arg(arg: Argument, v: str) -> str:
    if arg.external or arg.index:
        return "refl"
    if arg.is_iterated:
        return (f"(trans (cong ({v} [_]ᴿ) (lift*-idᴿ {arg.iter_sort} {arg.iter_arity})) "
                f"(right-idᴿ {v}))")
    if arg.is_binder:
        p = chain(arg.binder_types, "lift-idᴿ", "_↑ᴿ", base_first=True)
        return f"(trans (cong ({v} [_]ᴿ) {p}) (right-idᴿ {v}))"
    return f"(right-idᴿ {v})"


def comp_arg(lemma: str, op: str, base: str, lift_op: str) -> ArgProof:
    def go(arg: Argument, v: str) -> str:
        if arg.external or arg.index:
            return "refl"
        if arg.is_iterated:
            star = base.replace("lift-", "lift*-", 1)
            return (f"(trans ({lemma} {v}) (cong ({v} {op}) "
                    f"({star} {arg.iter_sort} {arg.iter_arity})))")
        if arg.is_binder:
            p = chain(arg.binder_types, base, f"_{lift_op}", base_first=False)
            return f"(trans ({lemma} {v}) (cong ({v} {op}) {p}))"
        return f"({lemma} {v})"
    return go


def coincidence_arg(arg: Argument, v: str) -> str:
    if arg.external or arg.index:
        return "refl"
    if arg.is_iterated:
        b, n = arg.iter_sort, arg.iter_arity
        return (f"(trans (cong ({v} [_]ˢ) (⟨⟩-lift* {{ξ = ξ}} {b} {n})) "
                f"(coincidence {v} (ξ ↑ᴿ*[ {b} ] {n})))")
    if arg.is_binder:
        p = chain(arg.binder_types, "⟨⟩-lift", "_↑ˢ", base_first=True)
        if len(arg.binder_types) == 1:
            p = "(⟨⟩-lift {ξ = ξ})"
        return (f"(trans (cong ({v} [_]ˢ) {p}) "
                f"(coincidence {v} {lifted('ξ', arg.binder_types, '↑ᴿ')}))")
    return f"(coincidence {v} ξ)"


def generate_coincidence(sig: Signature) -> str:
    data: list[tuple[str, str]] = []
    for c in sig.constructors:
        names = arg_names(c)
        pat = " ".join(names)
        head = c.name + iter_pins(c)
        lhs = f"coincidence ({head} {pat}) ξ" if pat else f"coincidence {c.name} ξ"
        if needs_dep_cong(c):
            proofs = [coincidence_arg(a, v) for a, v in zip(c.arguments, names, strict=True)
                      if not (a.index or a.external)]
            rhs = f"cong-{c.name} " + " ".join(proofs) if proofs else "refl"
        else:
            proofs = [coincidence_arg(arg, v) for arg, v in zip(c.arguments, names, strict=True)]
            rhs = "refl" if not proofs else f"cong{len(proofs)} {c.name} " + " ".join(proofs)
        data.append((lhs, rhs))
    width = max([len(l) for l, _ in data], default=0)
    return "\n".join(f"  {l}{' ' * (width - len(l))} = {r}" for l, r in data)


def generate_rewrite_block(sig: Signature, register_star: bool = True) -> str:
    def wrap(names: list[str]) -> str:
        out: list[str] = []
        line = "  "
        for n in names:
            if len(line) + len(n) > 76 and line.strip():
                out.append(line.rstrip())
                line = "  "
            line += n + " "
        if line.strip():
            out.append(line.rstrip())
        return "\n".join(out)

    instR = wrap(["instᴿ-var"] + [f"instᴿ-{c.name}" for c in sig.constructors])
    instS = wrap(["inst-var"] + [f"inst-{c.name}" for c in sig.constructors])
    # With register_star = False the 15 iterated-lifting laws are still DECLARED
    # AND PROVED but not registered as rewrite rules.  That is the "zero new
    # rewrite rules" position; it does not reach local confluence for a
    # signature with a variable-arity binder, and test_agdasubst.py pins it.
    star = wrap(STAR_RULES) if register_star else ""

    n_inst = 2 * (len(sig.constructors) + 1)   # instᴿ-*/inst-*, plus the two var rules
    n_star = len(STAR_RULES)
    return f"""-- ═══ THE COMPLETED TWO-WORLD SYSTEM ════════════════════════════════
--
-- The curated, locally confluent rule set of gen/Reference/Fsub.agda:
-- {60 + n_star + n_inst} rules -- 60 signature-independent, {n_star} for the
-- iterated (variable-arity) lifting, {n_inst} traversal rules (one instᴿ-*
-- and one inst-* per constructor, plus the variable case).

{{-# REWRITE
  def-wkᴿ def-∙ᴿ-zero def-∙ᴿ-suc def-↑ᴿ-zero def-↑ᴿ-suc
{instR}
  assocᴿ comp-idₗᴿ comp-idᵣᴿ interactᴿ
  lift-idᴿ lift-dist-compᴿᴿ lift-wkᴿ
  right-idᴿ compositionalityᴿᴿ-var compositionalityᴿᴿ
  lift-dist-compᴿᴿ-var interactᴿ-⨟ᴿ lift-wkᴿ-⨟ᴿ lift-dist-compᴿᴿ-⨟ᴿ
  coincidence-var def-∙ˢ-zero def-∙ˢ-suc def-↑ˢ-zero def-↑ˢ-suc
  compositionalityᴿˢ-⨟-var def-↑ˢ-zero-⨟ def-↑ˢ-suc-⨟
{instS}
  assoc dist interact comp-idₗ comp-idᵣ
  lift-wk lift-cons lift-dist-compˢˢ lift-wk-⨟ lift-dist-compˢˢ-⨟
  compositionalityˢˢ compositionalityᴿˢ compositionalityˢᴿ
  lift-dist-compᴿˢ lift-dist-compˢᴿ lift-dist-compᴿˢ-⨟ lift-dist-compˢᴿ-⨟
  lift-dist-compᴿˢ-var lift-dist-compᴿˢ-⨟-var ⟨⟩-lift-cons-var
  coincidence ⟨⟩-comp ⟨⟩-split-⨟ ⟨⟩-lift ⟨⟩-lift-cons
  ⟨⟩-comp-⨟-lift-wkᴿ ⟨⟩-comp-⨟-interactᴿ ⟨⟩-comp-⨟-lift-dist-compᴿᴿ ⟨⟩-split-tail
{star}
#-}}
"""


# ── the fixed frame ──────────────────────────────────────────────────

HEADER = r"""{-# OPTIONS «OPTIONS» #-}

-- Generated by gen/agdasubst.py.  DO NOT EDIT.
--
-- The multi-sorted, mode-merged σ-calculus with FIRST-CLASS RENAMINGS,
-- installed as a locally confluent Agda REWRITE system.  Every part that
-- does not mention the signature is the verbatim text of the verified
-- hand-written reference core, gen/Reference/Fsub.agda.

module «MODULE» where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; module ≡-Reasoning)
open ≡-Reasoning
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate
  fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

ext : {A : Set} {B : A → Set} {C : A → Set} → {f g : (a : A) → B a → C a} →
  (∀ {a} x → f a x ≡ g a x) → f ≡ g
ext f = fun-ext λ _ → fun-ext λ x → f x

"""

SYNTAX_HEAD = r"""
Scope = List Sort

variable
  s s₁ s₂ s′ : Sort
  S S₁ S₂ S₃ : Scope«IDX_VARS»

«STAR_EXT»
data Mode : Set where V T : Mode

variable
  m : Mode

data _⊢[_]_ : Scope → Mode → Sort → Set

_⊢_ = _⊢[ T ]_
_∋_ = _⊢[ V ]_

data _⊢[_]_ where
"""

TERM_VARS = r"""
variable
  t t₁ t₂ t′ : S ⊢ s
  x x′       : S ∋ s
  x/t x/t′   : S ⊢[ m ] s
"""


def count_rules(agda: str) -> int:
    import re as _re
    m = _re.search(r"\{-# REWRITE(.*?)#-\}", agda, _re.DOTALL)
    return 0 if m is None else len(m.group(1).split())


def render(sig: Signature, module_name: str, preamble: str, options: str,
           epilogue: str = "", var_name: str = "var",
           register_star: bool = True, funext_name: str = "ext") -> str:
    congs = generate_congs(get_max_arity(sig))
    parts: list[str] = []
    add = parts.append

    add(HEADER.replace("«OPTIONS»", options).replace("«MODULE»", module_name))
    add(congs)
    if preamble:
        add("\n" + preamble + "\n")
    add("\n-- ─── syntax ─────────────────────────────────────────────────────────\n\n")
    add(generate_sorts(sig))
    nats = all_nat_vars(sig)
    add(SYNTAX_HEAD
        .replace("«IDX_VARS»", f"\n  {' '.join(nats)} : ℕ" if nats else "")
        .replace("«STAR_EXT»", STAR_EXT))
    add(generate_constructors(sig, var_name))
    add("\n")
    add(TERM_VARS)
    v = generate_variables(sig)
    if v:
        add("\n" + v + "\n")
    dc = generate_dep_congs(sig)
    if dc:
        add("\n-- congruences for the constructors that carry a ℕ INDEX: those are\n"
            "-- dependent functions, so the non-dependent congN helpers do not apply.\n"
            + dc)

    add("\n" + MAPS_REN_A + "\n")
    add(STAR_LIFT_R)
    # GLUE: the traversal gets its own opaque block so that the n-fold lift
    # above can sit between it and _↑ᴿ_.  Same layout as ../Sigma/FsubPatterns.agda.
    add("\nopaque\n  unfolding wkᴿ _↑ᴿ_\n\n")
    add(MAPS_REN_B + "\n")
    add("  («VAR» x) [ ξ ]ᴿ = «VAR» (x [ ξ ]ᴿ)\n")
    add(generate_map_clauses(sig, "ᴿ", "ξ", "↑ᴿ") + "\n")

    add("\n" + COMP_SUB_A + "\n")
    add("opaque\n  unfolding _∙ˢ_\n")
    add(COMP_SUB_B + "\n")
    add(STAR_LIFT_S)
    add("\nopaque\n  unfolding _∙ˢ_ _↑ˢ_\n")
    add(COMP_SUB_C + "\n")
    add(COMP_SUB_D + "\n")
    add("  («VAR» x) [ σ ]ˢ = σ _ x\n")
    add(generate_map_clauses(sig, "ˢ", "σ", "↑ˢ") + "\n")

    add("\n" + SEQ_DECLS_A + "\n")
    add(SEQ_DECLS_B + "\n")
    add("  instᴿ-var : («VAR» x) [ ξ ]ᴿ ≡ «VAR» (x [ ξ ]ᴿ)\n")
    add(generate_inst_decls(sig, "instᴿ", "ᴿ", "ξ", "↑ᴿ") + "\n")

    add(ALG_R + "\n")
    add("  inst-var : («VAR» x) [ σ ]ˢ ≡ x [ σ ]ˢ\n")
    add(generate_inst_decls(sig, "inst", "ˢ", "σ", "↑ˢ") + "\n")

    add(COMPANION_S + "\n")
    add(STAR_DECLS + "\n")
    add(IR_PROOFS + "\n")
    add("  instᴿ-var = refl\n")
    add(generate_refl_proofs(sig, "instᴿ") + "\n")

    add(ALG_R_PROOF + "\n")
    add("  right-idᴿ {m = V} x = refl\n")
    add("  right-idᴿ («VAR» x)   = refl\n")
    add(generate_induction(sig, "right-idᴿ", right_idR_arg) + "\n")

    add(CRR_VAR + "\n")
    add("  compositionalityᴿᴿ («VAR» x) {ξ₁ = ξ₁} {ξ₂ = ξ₂} = "
        "cong «VAR» (sym (compositionalityᴿᴿ-var x {ξ₁ = ξ₁} {ξ₂ = ξ₂}))\n")
    add(generate_induction(sig, "compositionalityᴿᴿ",
                           comp_arg("compositionalityᴿᴿ", "[_]ᴿ",
                                    "lift-dist-compᴿᴿ", "↑ᴿ")) + "\n")

    add(PROOF_MID + "\n")
    add("  inst-var = refl\n")
    add(generate_refl_proofs(sig, "inst") + "\n")

    add(LDC_RS + "\n")
    add("  compositionalityᴿˢ («VAR» x) = refl\n")
    add(generate_induction(sig, "compositionalityᴿˢ",
                           comp_arg("compositionalityᴿˢ", "[_]ˢ",
                                    "lift-dist-compᴿˢ", "↑ˢ")) + "\n")

    add(LDC_SR + "\n")
    add("  compositionalityˢᴿ {m = V} x {σ₁ = σ₁} {ξ₂ = ξ₂} = sym (coincidence (σ₁ _ x) ξ₂)\n")
    add("  compositionalityˢᴿ («VAR» x) {σ₁ = σ₁} {ξ₂ = ξ₂} = sym (coincidence (σ₁ _ x) ξ₂)\n")
    add(generate_induction(sig, "compositionalityˢᴿ",
                           comp_arg("compositionalityˢᴿ", "[_]ˢ",
                                    "lift-dist-compˢᴿ", "↑ˢ")) + "\n")

    add(LDC_SS + "\n")
    add("  compositionalityˢˢ {m = V} x = refl\n")
    add("  compositionalityˢˢ («VAR» x)   = refl\n")
    add(generate_induction(sig, "compositionalityˢˢ",
                           comp_arg("compositionalityˢˢ", "[_]ˢ",
                                    "lift-dist-compˢˢ", "↑ˢ")) + "\n")

    add(ASSOC_DIST + "\n")
    add("  coincidence («VAR» x) ξ = refl\n")
    add(generate_coincidence(sig) + "\n")

    add(TAIL_PROOF + "\n")
    add(STAR_PROOFS + "\n\n")
    add(generate_rewrite_block(sig, register_star))
    add("\n" + EPILOGUE + "\n")

    body = "".join(parts).replace("«VAR»", var_name)
    if funext_name != "ext":
        # `ext` as a whole word, but never `ext*` and never inside a longer name
        body = re.sub(r"\bext(?![*\w])", funext_name, body)
    if epilogue:
        body += "\n" + epilogue + "\n"
    return body


# ==========================================
# 4b. Preamble directives
# ==========================================
#
# A line of a `.sg` file that begins with `%` is copied VERBATIM into the
# generated module, just after the standard imports and before the `Sort`
# datatype.  This is what makes quoted external argument types
# (`c : "Label" -> ty -> ty`) usable end to end -- the preamble is where
# the import or definition of `Label` goes -- and it is also where fixity
# declarations go, since they must precede the constructor they govern.


def split_directives(
    source: str,
) -> tuple[str, str, str, str, str | None, str]:
    """Split a `.sg` source into its directives and its body.

    Returns (preamble, epilogue, var-constructor, funext helper, module
    name or None, body).

    `%  <text>`   preamble line, copied verbatim before `data Sort`.
    `%%module M`  the name of the emitted module.  Needed when the module
                  is QUALIFIED and so does not match the output file's
                  basename: `Sigma/Fsub.agda` holds `module Sigma.Fsub`.
                  Defaults to the basename of the output file.
    `%%funext N`  EXTENSION: the name of the function-extensionality helper
                  (default `ext`; rename it when the signature needs `ext`).
    `%%var NAME`  EXTENSION: the name of the variable constructor
                  (default `var`; `Sigma/Fsub.agda` calls it `` `_ ``).
    `%%epilogue`  EXTENSION: everything after this line is copied verbatim
                  after the REWRITE block.  This is where a signature puts
                  the Agda text that DEPENDS on its own syntax and belongs
                  to the core module -- the F<: context machinery
                  (`↑ˢᵗ_`, `Ctx`, `_∷ₜ_`, `wk-telescope`, `_∋_∶_`) and the
                  generalizable variables the metatheory expects.
    """
    pre: list[str] = []
    epi: list[str] = []
    body: list[str] = []
    var_name = "var"
    funext_name = "ext"
    module_name = None
    in_epilogue = False

    for line in source.splitlines():
        if in_epilogue:
            epi.append(line)
        elif line.startswith("%%"):
            directive = line[2:].strip()
            if directive == "epilogue":
                in_epilogue = True
            elif directive.startswith("var "):
                var_name = directive[4:].strip()
            elif directive.startswith("module "):
                module_name = directive[7:].strip()
            elif directive.startswith("funext "):
                # EXTENSION: rename the function-extensionality helper.  The
                # default `ext` collides with Sigma/FsubPatterns.agda's scope
                # extension `ext : ℕ → Scope → Scope`, which is why that file
                # calls the helper `ext-f`.
                funext_name = directive[7:].strip()
            else:
                raise SyntaxError(f"unknown %% directive: {line!r}")
        elif line.startswith("%"):
            pre.append(line[2:] if line[1:2] == " " else line[1:])
        else:
            body.append(line)

    return ("\n".join(pre), "\n".join(epi), var_name, funext_name,
            module_name, "\n".join(body))


# ==========================================
# 5. CLI
# ==========================================


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate the σ-calculus boilerplate from a signature file.",
        epilog="agdasubst.py input.sg output.agda   |   agdasubst.py output.agda "
               "(signature on stdin)")
    parser.add_argument("files", nargs="+", metavar="FILE",
                        help="[input.sg] output.agda")
    args = parser.parse_args()

    input_source = None
    output_path = None

    if len(args.files) == 1:
        output_path = args.files[0]
        if sys.stdin.isatty():
            print("Reading from stdin... (Press Ctrl+D to finish)", file=sys.stderr)
        if hasattr(sys.stdin, "reconfigure"):        # signatures are UTF-8
            sys.stdin.reconfigure(encoding="utf-8") # pyright: ignore[reportUnknownMemberType, reportAttributeAccessIssue]
        input_source = sys.stdin.read()
    elif len(args.files) == 2:
        input_path = args.files[0]
        output_path = args.files[1]
        try:
            with open(input_path, encoding="utf-8") as f:
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
        (preamble, epilogue, var_name, funext_name, module_name,
         body) = split_directives(input_source)
        tokens = tokenize(body)
        signature = parse_signature(tokens)

        if module_name is None:
            module_name = os.path.splitext(os.path.basename(output_path))[0]

        agda_code = render(signature, module_name, preamble,
                           "--rewriting --local-confluence-check",
                           epilogue=epilogue, var_name=var_name,
                           funext_name=funext_name)

        try:
            with open(output_path, "w", encoding="utf-8") as f:
                f.write(agda_code)
        except OSError as e:
            print(f"Error: cannot write '{output_path}': {e}", file=sys.stderr)
            sys.exit(1)

        print(f"Successfully generated Agda code to '{output_path}' "
              f"({count_rules(agda_code)} rewrite rules, "
              f"{len(agda_code.splitlines())} lines).")

    except SyntaxError as e:
        print(f"Syntax Error: {e}", file=sys.stderr)
        sys.exit(1)
    except ValueError as e:
        # a signature that parses but violates an invariant of the AST
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
