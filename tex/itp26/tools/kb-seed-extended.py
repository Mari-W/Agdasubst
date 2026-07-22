"""Second seeding pass: the three σ-side extended rules."""
import re, os, sys
import kb
P = os.path.join(kb.D, "systemfLift.agda")

SEEDS = [
 ("lifts-comp-ext",
  "∀ {S₁ S₂ S₃ S₄ s} {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃} {σ₃ : (s ∷ S₃) →ˢ S₄} → "
  "(σ₁ ↑ˢ s) ⨟ ((σ₂ ↑ˢ s) ⨟ σ₃) ≡ ((σ₁ ⨟ σ₂) ↑ˢ s) ⨟ σ₃",
  ["{σ₃ = σ₃} = cong (_⨟ σ₃) ↑ˢ-⨟", "= cong (_⨟ _) ↑ˢ-⨟", "= ext λ x → refl"]),
 ("lifts-cons-ext",
  "∀ {S₁ S₂ S₃ S₄ s} {σ₁ : S₁ →ˢ S₂} {t : S₃ ⊢ s} {σ₂ : S₂ →ˢ S₃} {σ₃ : S₃ →ˢ S₄} → "
  "(σ₁ ↑ˢ s) ⨟ ((t ∙ˢ σ₂) ⨟ σ₃) ≡ (t ∙ˢ (σ₁ ⨟ σ₂)) ⨟ σ₃",
  ["{σ₃ = σ₃} = cong (_⨟ σ₃) ↑ˢ-cons", "= cong (_⨟ _) ↑ˢ-cons", "= ext λ x → refl"]),
 ("wklifts-ext",
  "∀ {S₁ S₂ S₃ s} {σ : S₁ →ˢ S₂} {σ₃ : (s ∷ S₂) →ˢ S₃} → "
  "wkˢ s ⨟ ((σ ↑ˢ s) ⨟ σ₃) ≡ (σ ⨟ wkˢ s) ⨟ σ₃",
  ["{σ₃ = σ₃} = cong (_⨟ σ₃) wk-↑ˢ", "= cong (_⨟ _) wk-↑ˢ", "= ext λ x → refl"]),
]

def offending(errs, src, ls):
    names = [l["name"] for l in ls]
    for b in errs:
        for n in sorted(names, key=len, reverse=True):
            if n in b: return n
        m = re.search(re.escape(kb.MOD) + r"\.agda:(\d+)", b)
        if m:
            lines = src.split("\n")
            for k in range(int(m.group(1)) - 1, -1, -1):
                st = lines[k].strip().split(" ")[0] if lines[k].strip() else ""
                if st in names: return st
    return None

def run():
    ls = [{"name": n, "decl": f"  {n} : {sig}", "lad": lad, "t": 0,
           "proof": f"  {n} {lad[0]}"} for n, sig, lad in SEEDS]
    for _ in range(6 * len(ls) + 12):
        src = kb.render(ls, kb.BASE_RULES)
        pairs, other, out = kb.agda(src)
        if not other:
            print("proven:", " ".join(l["name"] for l in ls), "| open pairs:", len(pairs), flush=True)
            return ls
        bad = offending(other, src, ls)
        if bad is None:
            print("unattributable:", " ".join(other[0][:250].split()), flush=True)
            return ls
        l = next(x for x in ls if x["name"] == bad)
        if l["t"] + 1 < len(l["lad"]):
            l["t"] += 1
            l["proof"] = f"  {bad} {l['lad'][l['t']]}"
            print(f"  {bad} -> tactic {l['t']}", flush=True)
        else:
            print(f"  {bad}: UNPROVABLE, dropping", flush=True)
            ls = [x for x in ls if x["name"] != bad]
    return ls

if __name__ == "__main__":
    ls = run()
    if not ls: sys.exit(0)
    src = open(P).read()
    src = src.replace(kb.DECL_ANCHOR, kb.DECL_ANCHOR + "".join("\n" + l["decl"] for l in ls), 1)
    src = src.replace(kb.PRF_ANCHOR, kb.PRF_ANCHOR + "".join("\n" + l["proof"] for l in ls), 1)
    i = src.index("{-# REWRITE"); j = src.index("#-}", i)
    src = src[:j] + " ".join(l["name"] for l in ls) + "\n" + src[j:]
    open(P, "w").write(src)
    print("written")
