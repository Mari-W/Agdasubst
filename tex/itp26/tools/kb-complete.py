#!/usr/bin/env python3
"""Knuth-Bendix-style completion driver for an Agda --rewriting theory.

Reads Agda's [RewriteNonConfluent] reports, turns each unjoined critical pair
into a candidate lemma (statement = the two reducts, proof found by a small
tactic ladder), registers the ones that typecheck, and iterates.
"""
import re, os, subprocess, sys, json

D = "/home/weidner/proglang/research/agda/Agdasubst/tex/itp26"
MOD = "systemfKB"
PATH = os.path.join(D, MOD + ".agda")

# ── anchors in the source where generated material is spliced ───────────────
DECL_ANCHOR = "  coincidence-↑ : ∀ {S₁ S₂ s s₁} (t : (s ∷ S₁) ⊢ s₁) {ρ : S₁ →ᴿ S₂} → t ⋯ˢ (⟨ ρ ⟩ ↑ˢ s) ≡ t ⋯ᴿ (ρ ↑ᴿ s)"
PRF_ANCHOR  = "  coincidence-↑ t {ρ = ρ} = trans (cong (t ⋯ˢ_) (sym (⟨⟩-↑ {ρ = ρ}))) (coincidence t)"

def load_base():
    src = open(os.path.join(D, "systemfLift.agda")).read()
    src = src.replace("{-# OPTIONS --rewriting #-}", "{-# OPTIONS --rewriting --local-confluence-check #-}", 1)
    src = src.replace("module systemfLift where", f"module {MOD} where", 1)
    return src

BASE = load_base()
i = BASE.index("{-# REWRITE"); j = BASE.index("#-}", i)
BASE_RULES = BASE[i+len("{-# REWRITE"):j].split()

def render(lemmas, rules):
    s = BASE
    decls = "".join("\n" + l["decl"] for l in lemmas)
    prfs  = "".join("\n" + l["proof"] for l in lemmas)
    s = s.replace(DECL_ANCHOR, DECL_ANCHOR + decls, 1)
    s = s.replace(PRF_ANCHOR,  PRF_ANCHOR + prfs, 1)
    a = s.index("{-# REWRITE"); b = s.index("#-}", a)
    return s[:a] + "{-# REWRITE " + " ".join(rules) + "\n#-}" + s[b+3:]

def agda(src):
    open(PATH, "w").write(src)
    r = subprocess.run(["agda", PATH], capture_output=True, text=True, cwd=D, timeout=3600)
    out = "\n".join(l for l in (r.stdout + r.stderr).splitlines()
                    if not l.strip().startswith("Checking "))
    pairs, other = [], []
    for b in out.split("\n\n"):
        if not b.strip(): continue
        if "RewriteNonConfluent" in b:
            m = re.search(r"reduces to both\s+(.*?)\s+and\s+(.*?)\s+which are not equal", b, re.S)
            r2 = re.search(r"rewrite rule\s+(\S+)\s+with\s+(\S+)", b, re.S)
            if m: pairs.append({"A": " ".join(m.group(1).split()),
                                "B": " ".join(m.group(2).split()),
                                "rules": (r2.group(1), r2.group(2)) if r2 else ("?","?")})
        elif "error" in b:
            other.append(b)
    return pairs, other, out

# ── turning printed terms back into source ─────────────────────────────────
ETA = re.compile(r"\(λ\s+(\S+)\s+(\S+)\s+→\s+(\S+)\s+\1\s+\2\)")
def clean(t):
    prev = None
    while prev != t:
        prev = t
        t = ETA.sub(r"\3", t)
    return " ".join(t.split())

# names the file's `variable` block can generalise
KNOWN = set("s s₁ s₂ s′ S S₁ S₂ S₃ S₄ m e e₁ e₂ e′ k k′ x x′ t t₁ t₂ t′ "
            "ρ ρ₁ ρ₂ ρ₃ σ σ₁ σ₂ σ₃".split())
SYNTAX = set("≡ ∙ˢ ∙ᴿ ⨟ ∘ ⋯ˢ ⋯ᴿ ↑ˢ ↑ᴿ ⟨ ⟩ ` zero suc idˢ idᴿ wkˢ wkᴿ λx Λα ∀[α∶ ] · • ⇒ * ( ) → ∷ [ ] expr type kind".split())
CONSTR = ("λx", "Λα", "∀[α∶", "suc", "zero", "`", "*")
POOLS = {"x": ["x", "x′"], "ρ": ["ρ", "ρ₁", "ρ₂", "ρ₃"], "σ": ["σ", "σ₁", "σ₂", "σ₃"],
         "t": ["t", "t₁", "t₂", "t′"], "e": ["e", "e₁", "e₂", "e′"], "k": ["k", "k′"],
         "s": ["s", "s₁", "s₂", "s′"], "S": ["S", "S₁", "S₂", "S₃", "S₄"]}

def kind_of(tok):
    base = tok.split(".")[-1] if "." in tok else tok
    c = base[0]
    if c in POOLS: return c
    if c in "yzw": return "x"
    return None

def normalise(A, B):
    """rename printer-invented names (x₁, ρ.S₁, x.s …) to names the variable block knows"""
    toks = [t for t in tokens(A) + tokens(B) if t not in SYNTAX]
    used = {t for t in toks if t in KNOWN}
    ren = {}
    for t in toks:
        if t in KNOWN or t in ren: continue
        k = kind_of(t)
        if k is None: return None, None
        free = [n for n in POOLS[k] if n not in used and n not in ren.values()]
        if not free: return None, None
        ren[t] = free[0]; used.add(free[0])
    def apply(s):
        for a, b in sorted(ren.items(), key=lambda kv: -len(kv[0])):
            s = re.sub(r"(?<![\w₀-₉′.])" + re.escape(a) + r"(?![\w₀-₉′])", b, s)
        return s
    return apply(A), apply(B)

def tokens(t):
    return re.findall(r"[^\s()]+", t)

def usable(t):
    """reject terms mentioning metavariable projections (σ₂.S₁) or unknown names"""
    for tok in tokens(t):
        if "." in tok: return False
        if tok in SYNTAX or tok in KNOWN: continue
        if re.fullmatch(r"[A-Za-z][\w₀-₉′]*", tok) and tok not in KNOWN: return False
    return True

def size(t): return len(tokens(t))

LADDER = [
    "{name} = refl",
    "{name} = ext λ {{ zero → refl ; (suc x) → refl }}",
    "{name} = ext λ x → refl",
    "{name} {{x = zero}} = refl\n{name} {{x = suc x}} = refl",
]

def head_ok(t):
    t = t.strip()
    while t.startswith("("):
        depth, k = 0, 0
        for k, ch in enumerate(t):
            depth += (ch == "(") - (ch == ")")
            if depth == 0: break
        inner = t[1:k]
        if k == len(t) - 1: t = inner.strip()
        else: break
    return not any(t.startswith(c + " ") or t == c for c in CONSTR)

def make_lemma(idx, A, B):
    A, B = clean(A), clean(B)
    A, B = normalise(A, B)
    if A is None or A == B: return None
    if not (usable(A) and usable(B)): return None
    lhs, rhs = (A, B) if size(A) >= size(B) else (B, A)
    if not head_ok(lhs):
        lhs, rhs = rhs, lhs
        if not head_ok(lhs) or size(lhs) < size(rhs): return None
    name = f"kb{idx}"
    return {"name": name, "lhs": lhs, "rhs": rhs, "tactic": 0,
            "decl": f"  {name} : {lhs} ≡ {rhs}",
            "proof": ("  " + LADDER[0].format(name=name))}

def set_tactic(l, k):
    l["tactic"] = k
    body = LADDER[k].format(name=l["name"])
    l["proof"] = "\n".join("  " + ln for ln in body.split("\n"))
    return l

def offending(err_blocks, src, lemmas):
    """which lemma does this error belong to?"""
    names = {l["name"] for l in lemmas}
    for b in err_blocks:
        for n in sorted(names, key=len, reverse=True):
            if re.search(r"(?<![\w])" + re.escape(n) + r"(?![\w])", b): return n
        m = re.search(re.escape(MOD) + r"\.agda:(\d+)", b)
        if m:
            line = int(m.group(1)); lines = src.split("\n")
            for k in range(line-1, -1, -1):
                mm = re.match(r"\s*(kb\d+)", lines[k])
                if mm and mm.group(1) in names: return mm.group(1)
    return None

def validate(lemmas, rules, log):
    """advance tactics / drop lemmas until the file typechecks (rules NOT yet added)"""
    cur = list(lemmas)
    for _ in range(6 * len(cur) + 12):
        src = render(cur, rules)
        pairs, other, out = agda(src)
        if not other: return cur
        bad = offending(other, src, cur)
        if bad is None:
            log(f"    unattributable error, dropping all new: {' '.join(other[0][:150].split())}")
            return [l for l in cur if not l["name"].startswith("kb") or l in lemmas[:0]]
        l = next(x for x in cur if x["name"] == bad)
        if l["tactic"] + 1 < len(LADDER):
            set_tactic(l, l["tactic"] + 1)
            log(f"    {bad}: tactic -> {l['tactic']}")
        else:
            cur = [x for x in cur if x["name"] != bad]
            log(f"    {bad}: unprovable by ladder, dropped")
    return cur

def run(max_rounds=12, max_lemmas=60):
    log_f = open("kb.log", "a")
    def log(m):
        print(m, flush=True); log_f.write(m + "\n"); log_f.flush()
    lemmas, rules = [], list(BASE_RULES)
    idx = 0
    history = []
    for rnd in range(1, max_rounds + 1):
        pairs, other, _ = agda(render(lemmas, rules))
        log(f"round {rnd}: {len(pairs)} open pairs, {len(other)} errors, {len(lemmas)} lemmas")
        if other:
            log("  ERRORS: " + " ".join(other[0][:300].split())); break
        if not pairs:
            log("  *** CONFLUENT ***"); break
        history.append(len(pairs))
        if len(history) >= 4 and len(set(history[-4:])) == 1:
            log("  no progress for 4 rounds, stopping"); break
        if len(lemmas) > max_lemmas:
            log("  lemma budget exhausted, stopping"); break
        new, skipped = [], 0
        for p in pairs:
            idx += 1
            l = make_lemma(idx, p["A"], p["B"])
            if l is None: skipped += 1; continue
            if any(x["lhs"] == l["lhs"] and x["rhs"] == l["rhs"] for x in lemmas + new): continue
            new.append(l)
        log(f"  {len(new)} candidates ({skipped} unprintable)")
        if not new:
            log("  nothing addable, stopping"); break
        keep = validate(lemmas + new, rules, log)
        added = [l for l in keep if l not in lemmas]
        log(f"  {len(added)} lemmas proven: {' '.join(l['name'] for l in added)}")
        if not added:
            log("  no provable candidates, stopping"); break
        lemmas = keep
        rules = rules + [l["name"] for l in added]
    json.dump({"lemmas": lemmas, "rules": rules}, open("kb_state.json", "w"), ensure_ascii=False, indent=1)
    return lemmas, rules

if __name__ == "__main__":
    run()
