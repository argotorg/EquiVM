# Precompile-style bytecode proofs

This tree contains bytecode verification examples whose public specification is a pure Lean
function rather than a Sol⁻ contract. Each example may supply an acceptance predicate, output
function, and exact gas term through the generic interface in `Reasoning/Bytecode.lean`.

Contract-to-Solm equivalence layers, when they exist for the same implementation, remain in their
ordinary sibling example directories.
