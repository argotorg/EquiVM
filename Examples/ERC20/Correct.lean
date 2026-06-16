import Examples.ERC20.Bytecode
import Examples.ERC20.Spec
import Reasoning.Theory

/-!
# ERC20 — correctness statement

This file records the ERC20 runtime-equivalence target.  Unlike `Truth`, `Pow`, and `Caller`, this
example does not yet include the full per-branch symbolic EVM trace proof for the six-function
dispatcher and the storage-mutating transfer paths.
-/

open Solm Ethereum Ethereum.EVM Reasoning.Theory

namespace ERC20

/-- The deployed runtime bytecode refines the Solm specification, for every initial state. -/
axiom erc20Correct :
    runtimeEquivalence!?! erc20Config erc20Bytecode erc20Contract

end ERC20
