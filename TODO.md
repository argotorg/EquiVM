# Act Semantics
- [ ] Constructor calls
  + currently we don't have

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