# QF_BV prototype support

The SAT/SMT chapter code remains in the separate `sat-smt` worktree. This fork
contains the compiler and functional standard-library support used to translate
that code without rewriting its Rust implementation for the proofs.

Function items have no stored lifetime-bearing payload. Their quantified call
lifetimes do not outlive an enclosing storage borrow. Internal signature and
ADT constraints are still checked; the three higher-ranked implied-bound
negative regressions remain rejected. `function_item_lifetimes.rs` translates
and its generated Lean fixture compiles. Function-pointer backward translation
and existing function effect restrictions remain unchanged.

`StringPatterns` models `starts_with` and `strip_prefix` with UTF-8 byte prefixes
for character and string patterns. Direct native Searcher construction is outside
this interface. `StringParse` models unsigned decimal parsing, the optional plus
sign, invalid/empty input, and machine-word overflow. Its decimal-value, overflow
and totality theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The generic Zip trait uses the existing functional short-circuiting `next` model
and ordinary fold default, including callback effects. The SAT bridge core now
translates and compiles against this trait record.

These are functional standard-library models. Correspondence to native unsafe
iterator or allocator bodies is not proved here. Full chapter 28b/28c translation
and their composed correctness proofs are still in progress; Unicode character
iteration is also an outstanding model boundary.
