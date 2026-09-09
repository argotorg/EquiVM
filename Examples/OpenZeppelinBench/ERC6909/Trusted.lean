import Examples.OpenZeppelinBench.ERC6909.Bytecode
import Solm.Semantics

/-!
# ERC6909 benchmark trusted selector facts

`selectorOf` goes through the opaque `ffi.KEC`, so as in the completed examples we record the
four-byte Solidity selector facts as trusted bytecode/ABI facts.  The jump-destination fact remains
in `Bytecode.lean` and is proved by `decide +native` from the byte array.
-/

namespace OpenZeppelinBench.ERC6909

/-- `keccak("balanceOf(address,uint256)")[0:4] = 0x00fdd58e`. -/
axiom erc6909BalanceOfSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr balanceOfTransition))).extract 0 4
      = ⟨#[0x00, 0xfd, 0xd5, 0x8e]⟩

/-- `keccak("supportsInterface(bytes4)")[0:4] = 0x01ffc9a7`. -/
axiom erc6909SupportsInterfaceSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr supportsInterfaceTransition))).extract 0 4
      = ⟨#[0x01, 0xff, 0xc9, 0xa7]⟩

/-- `keccak("transfer(address,uint256,uint256)")[0:4] = 0x095bcdb6`. -/
axiom erc6909TransferSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr transferTransition))).extract 0 4
      = ⟨#[0x09, 0x5b, 0xcd, 0xb6]⟩

/-- `keccak("approve(address,uint256,uint256)")[0:4] = 0x426a8493`. -/
axiom erc6909ApproveSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr approveTransition))).extract 0 4
      = ⟨#[0x42, 0x6a, 0x84, 0x93]⟩

/-- `keccak("setOperator(address,bool)")[0:4] = 0x558a7297`. -/
axiom erc6909SetOperatorSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr setOperatorTransition))).extract 0 4
      = ⟨#[0x55, 0x8a, 0x72, 0x97]⟩

/-- `keccak("allowance(address,address,uint256)")[0:4] = 0x598af9e7`. -/
axiom erc6909AllowanceSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr allowanceTransition))).extract 0 4
      = ⟨#[0x59, 0x8a, 0xf9, 0xe7]⟩

/-- `keccak("isOperator(address,address)")[0:4] = 0xb6363cf2`. -/
axiom erc6909IsOperatorSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr isOperatorTransition))).extract 0 4
      = ⟨#[0xb6, 0x36, 0x3c, 0xf2]⟩

/-- `keccak("transferFrom(address,address,uint256,uint256)")[0:4] = 0xfe99049a`. -/
axiom erc6909TransferFromSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr transferFromTransition))).extract 0 4
      = ⟨#[0xfe, 0x99, 0x04, 0x9a]⟩

end OpenZeppelinBench.ERC6909
