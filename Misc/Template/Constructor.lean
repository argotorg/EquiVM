import Benchmarks.Xxx.Common

/-!
# Xxx constructor correctness (TEMPLATE)

Creation-code equivalence: the constructor's EVM trace (arg decode, stores, runtime-code
return) against the Solm constructor body.  For non-trivial constructors split the trace into
`ConstructorTrace*` files (args / stores / return) and the Solm side into `ConstructorSource`,
then assemble here through the account-map-equivalence chain — see
`Benchmarks/Dss/Pot/Constructor.lean` and `Examples/Ballot`'s creation proof.

Shape of the capstone piece:

```
theorem xxxConstructorCorrect :
    constructorEquivalence config xxxCreationBytecode contract xxxBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args deployedInitcode
    hdeploy hcode hcalldata hperm hAccounts
  -- 1. shape of the deployment payload (initcode ++ ABI-encoded args)
  -- 2. by_cases on weiValue: nonzero ⇒ the callvalue guard reverts on both sides
  -- 3. success: run the creation trace, build the stored account map store-by-store,
  --    and match the Solm constructor evaluation
  sorry
```
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Xxx

-- TODO: xxxCtorDeployment_shape, xxxInitcodeSuccess, per-store account maps,
--       theorem xxxConstructorCorrect (see docstring).

end Benchmarks.Xxx
