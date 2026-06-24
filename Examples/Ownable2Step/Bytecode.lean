import Examples.Ownable2Step.Spec
import Solm.Dispatch
import Reasoning.JumpDest

open Solm Ethereum Ethereum.EVM

/-! ## `Ownable2Step`'s deployed runtime bytecode — **optimizer ON**

Produced by `solc --optimize --evm-version shanghai --bin-runtime Examples/Ownable2Step/Ownable2Step.sol`
(solc 0.8.35, Shanghai ⇒ PUSH0).  591 bytes.  **Linear** selector dispatcher (5 arms from pc 30,
exactly the ERC20 shape).

Function selectors:
`renounceOwnership() = 0x715018a6`, `acceptOwnership() = 0x79ba5097`, `owner() = 0x8da5cb5b`,
`pendingOwner() = 0xe30c3978`, `transferOwnership(address) = 0xf2fde38b`.
-/

def ownableBytecode : ByteArray :=
  ⟨#[96, 128, 96, 64, 82, 52, 128, 21, 97, 0, 15, 87, 95, 95, 253, 91, 80, 96, 4, 54, 16, 97, 0,
    85, 87, 95, 53, 96, 224, 28, 128, 99, 113, 80, 24, 166, 20, 97, 0, 89, 87, 128, 99, 121, 186,
    80, 151, 20, 97, 0, 99, 87, 128, 99, 141, 165, 203, 91, 20, 97, 0, 107, 87, 128, 99, 227, 12,
    57, 120, 20, 97, 0, 147, 87, 128, 99, 242, 253, 227, 139, 20, 97, 0, 164, 87, 91, 95, 95, 253,
    91, 97, 0, 97, 97, 0, 183, 86, 91, 0, 91, 97, 0, 97, 97, 1, 30, 86, 91, 95, 84, 96, 1, 96, 1,
    96, 160, 27, 3, 22, 91, 96, 64, 81, 96, 1, 96, 1, 96, 160, 27, 3, 144, 145, 22, 129, 82, 96,
    32, 1, 96, 64, 81, 128, 145, 3, 144, 243, 91, 96, 1, 84, 96, 1, 96, 1, 96, 160, 27, 3, 22, 97,
    0, 119, 86, 91, 97, 0, 97, 97, 0, 178, 54, 96, 4, 97, 1, 236, 86, 91, 97, 1, 133, 86, 91, 95,
    84, 96, 1, 96, 1, 96, 160, 27, 3, 22, 51, 20, 97, 1, 1, 87, 96, 64, 81, 98, 70, 27, 205, 96,
    229, 27, 129, 82, 96, 32, 96, 4, 130, 1, 82, 96, 9, 96, 36, 130, 1, 82, 104, 39, 39, 170, 47,
    167, 171, 167, 34, 169, 96, 185, 27, 96, 68, 130, 1, 82, 96, 100, 1, 91, 96, 64, 81, 128, 145,
    3, 144, 253, 91, 96, 1, 128, 84, 96, 1, 96, 1, 96, 160, 27, 3, 25, 144, 129, 22, 144, 145, 85,
    95, 128, 84, 144, 145, 22, 144, 85, 86, 91, 96, 1, 84, 96, 1, 96, 1, 96, 160, 27, 3, 22, 51,
    20, 97, 1, 102, 87, 96, 64, 81, 98, 70, 27, 205, 96, 229, 27, 129, 82, 96, 32, 96, 4, 130, 1,
    82, 96, 11, 96, 36, 130, 1, 82, 106, 78, 79, 84, 95, 80, 69, 78, 68, 73, 78, 71, 96, 168, 27,
    96, 68, 130, 1, 82, 96, 100, 1, 97, 0, 248, 86, 91, 96, 1, 128, 84, 96, 1, 96, 1, 96, 160, 27,
    3, 25, 144, 129, 22, 144, 145, 85, 95, 128, 84, 144, 145, 22, 51, 23, 144, 85, 86, 91, 95, 84,
    96, 1, 96, 1, 96, 160, 27, 3, 22, 51, 20, 97, 1, 202, 87, 96, 64, 81, 98, 70, 27, 205, 96,
    229, 27, 129, 82, 96, 32, 96, 4, 130, 1, 82, 96, 9, 96, 36, 130, 1, 82, 104, 39, 39, 170, 47,
    167, 171, 167, 34, 169, 96, 185, 27, 96, 68, 130, 1, 82, 96, 100, 1, 97, 0, 248, 86, 91, 96,
    1, 128, 84, 96, 1, 96, 1, 96, 160, 27, 3, 25, 22, 96, 1, 96, 1, 96, 160, 27, 3, 146, 144, 146,
    22, 145, 144, 145, 23, 144, 85, 86, 91, 95, 96, 32, 130, 132, 3, 18, 21, 97, 1, 252, 87, 95,
    95, 253, 91, 129, 53, 96, 1, 96, 1, 96, 160, 27, 3, 129, 22, 129, 20, 97, 2, 18, 87, 95, 95,
    253, 91, 147, 146, 80, 80, 80, 86, 254, 162, 100, 105, 112, 102, 115, 88, 34, 18, 32, 42, 218,
    102, 137, 112, 212, 6, 190, 14, 46, 253, 117, 52, 211, 35, 209, 114, 99, 193, 245, 246, 85,
    45, 221, 169, 55, 109, 130, 241, 76, 96, 12, 100, 115, 111, 108, 99, 67, 0, 8, 35, 0, 51]⟩

/-- `keccak("owner()")[0:4] = 0x8da5cb5b`. -/
axiom ownableOwnerSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr Ownable2Step.ownerTransition))).extract 0 4
      = ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩

/-- `keccak("pendingOwner()")[0:4] = 0xe30c3978`. -/
axiom ownablePendingOwnerSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr Ownable2Step.pendingOwnerTransition))).extract 0 4
      = ⟨#[0xe3, 0x0c, 0x39, 0x78]⟩

/-- `keccak("transferOwnership(address)")[0:4] = 0xf2fde38b`. -/
axiom ownableTransferOwnershipSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr Ownable2Step.transferOwnershipTransition))).extract 0 4
      = ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩

/-- `keccak("acceptOwnership()")[0:4] = 0x79ba5097`. -/
axiom ownableAcceptOwnershipSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr Ownable2Step.acceptOwnershipTransition))).extract 0 4
      = ⟨#[0x79, 0xba, 0x50, 0x97]⟩

/-- `keccak("renounceOwnership()")[0:4] = 0x715018a6`. -/
axiom ownableRenounceOwnershipSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr Ownable2Step.renounceOwnershipTransition))).extract 0 4
      = ⟨#[0x71, 0x50, 0x18, 0xa6]⟩

/-- The `JUMPDEST` set of `ownableBytecode` (confirmed from the bytecode disassembly). -/
@[valid_jumps] theorem ownableValidJumps :
    Ethereum.EVM.D_J ownableBytecode 0
      = #[⟨15⟩, ⟨85⟩, ⟨89⟩, ⟨97⟩, ⟨99⟩, ⟨107⟩, ⟨119⟩, ⟨147⟩, ⟨164⟩, ⟨178⟩, ⟨183⟩, ⟨248⟩, ⟨257⟩,
          ⟨286⟩, ⟨358⟩, ⟨389⟩, ⟨458⟩, ⟨492⟩, ⟨508⟩, ⟨530⟩]
  := by native_decide
