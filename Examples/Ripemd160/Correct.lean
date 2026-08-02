import Examples.Ripemd160.Bytecode
import Solm.Equiv

/-!
# Ripemd160Deployed runtime-equivalence target

The contract has no selector-based entries: runtime calls enter the raw fallback. This file states
the equivalence goal only. Constructor equivalence and the runtime proof are intentionally out of
scope.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Ripemd160

def runtimeEquivalenceTarget : Prop :=
  runtimeEquivalence config ripemd160RuntimeBytecode contract

end Ripemd160
