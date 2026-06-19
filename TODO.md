# Solm Semantics
- [X] Constructor calls
  + currently we don't have
- [X] Arithmetic overflow handling
  + Option 1: wrap-around arithmetic and explicit overflow checks in the spec
  + Option 2: parameterize with the checked arith semantics of the language
  + [CURRENT] Option 3: unbounded arith, explicit inRange checks, and truncation to bounded arith when storing to storage
- [ ] Add low level call in Solm 
- [ ] Study locals (esp. arrays, mappings and structs) and how to model them in Solm
- [ ] Dynamic data (arrays and strings)
 
- [ ] Out of gas
  + currently we treat OOG as equivalent to any spec
  + nonterminting EVM programs are currently equivalent to any spec [OK]

- When writing spec, the reads/writes of mappings (and likely arrays too) should happen in the 
  order they appear in the bytecode. Otherwise, we may need ta add keccak axioms.

- Optimizations on vs off