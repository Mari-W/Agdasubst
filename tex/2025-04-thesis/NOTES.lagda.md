# structure

1.  introduction
    - proving lemmas about substitution is repetitive
    - the problem with 8 assoc lemmas or 4 fusion lemmas / proving everything twice
    - instriniscally scoped syntax is sweet spot between unscoped and intrinsically typed
2.  preliminaries
    - the sigma calculus
    - agda and rewriting
    - kits by mc bride
3.  related Work
    - autosubst 2
    - abstraction for multisorted substitution 
    - universe of syntaxes with binding
4.  agdasubst 
    - the laws 
    - extension system
    - an guided example using 
      - derive
      - generics
    - limitations
      - assoc lemma
      - postulates we dont get away
5.  intrinsic typing 
    - it does help to rewrite the sigma calculus in the higher levels of the hierarchies for 
      proving lemmas in the lower levels.
    - intrinsically scoped is hard to generalize to intrinsically typed 
      (because of hierarchy and arbitrary telescopes in scopes).
6. conclusion