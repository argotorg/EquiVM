import Ethereum.Semantics

/-!
# Identity replacement bytecode

The implementation is the seven-byte EVM program documented by
`evmification/src/identity/Identity.sol` at commit
`c0aabf32aa4682925836044948a204da8cd62e9f`:

`CALLDATASIZE PUSH0 PUSH0 CALLDATACOPY CALLDATASIZE PUSH0 RETURN`

It is also the assembly body of `IdentityDeployed.sol`, without compiler metadata.
-/

namespace Identity

def runtimeBytecode : ByteArray :=
  ⟨#[0x36, 0x5f, 0x5f, 0x37, 0x36, 0x5f, 0xf3]⟩

@[simp] theorem runtimeBytecode_size : runtimeBytecode.size = 7 := by
  native_decide

end Identity
