# Act Semantics
- [ ] Constructor calls
  + currently we don't have
  + state equivalence.
    In the EVM there is no concept of calldata for the initcode
    In solidity a constructor compiles to a bytecode object, but in the deployed code
    any creation call appends the arguments to the end

- [ ] fallback functions

- [ ] support for storage layout that depends on storage contents
    e.g. solidity's representation for string and byte[]

- [ ] Arithmetic overflow handling
  + Option 1: wrap-around arithmetic and explicit overflow checks in the spec
  + Option 2: parameterize with the checked arith semantics of the language

unckecked {

uint128 x 
uint128 y 
uint128 z
 
z := x + y

}


explicitly checked:

uint128 x 
uint128 y 
uint128 z
 

z := assert_in_range(128, x + y)


- [ ] Substate equality in equivalence?
 
- [ ] Out of gas
  + currently we treat OOG as equivalent to any spec
  + nonterminting EVM programs are currently equivalent to any spec







# Related Work

- Multilanguage Semantics
  + https://dl.acm.org/doi/10.1145/1498926.1498930
  + https://www.ccs.neu.edu/home/amal/papers/voc.pdf
  
- 
