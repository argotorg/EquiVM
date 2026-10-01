import Examples.OpenZeppelinBench.ERC6909.Bytecode
import Solm.Semantics

/-!
# ERC6909 benchmark selector facts

The jump-destination fact lives in `Bytecode.lean` and is computed from the byte array.
-/

open Solm Ethereum Ethereum.EVM

namespace OpenZeppelinBench.ERC6909

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- `keccak("balanceOf(address,uint256)")[0:4] = 0x00fdd58e`. -/
theorem erc6909BalanceOfSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr balanceOfTransition))).extract 0 4
      = ⟨#[0x00, 0xfd, 0xd5, 0x8e]⟩ := by
  have hsig : Solm.transitionSigStr balanceOfTransition = "balanceOf(address,uint256)" := by
    simp [Solm.transitionSigStr, ABI.printSignature, transitionSignature, balanceOfTransition, addr, uint256, uint256Int, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, show Nat.repr 256 = "256" by decide +kernel]
    decide +kernel
  rw [hsig]
  decide +kernel

/-- `keccak("supportsInterface(bytes4)")[0:4] = 0x01ffc9a7`. -/
theorem erc6909SupportsInterfaceSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr supportsInterfaceTransition))).extract 0 4
      = ⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ := by
  have hsig : Solm.transitionSigStr supportsInterfaceTransition = "supportsInterface(bytes4)" := by
    simp [Solm.transitionSigStr, ABI.printSignature, transitionSignature, supportsInterfaceTransition, bytes4, ABI.abiToSigStr, ABI.elemToSigStr]
    decide +kernel
  rw [hsig]
  decide +kernel

/-- `keccak("transfer(address,uint256,uint256)")[0:4] = 0x095bcdb6`. -/
theorem erc6909TransferSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr transferTransition))).extract 0 4
      = ⟨#[0x09, 0x5b, 0xcd, 0xb6]⟩ := by
  have hsig : Solm.transitionSigStr transferTransition = "transfer(address,uint256,uint256)" := by
    simp [Solm.transitionSigStr, ABI.printSignature, transitionSignature, transferTransition, addr, uint256, uint256Int, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, show Nat.repr 256 = "256" by decide +kernel]
    decide +kernel
  rw [hsig]
  decide +kernel

/-- `keccak("approve(address,uint256,uint256)")[0:4] = 0x426a8493`. -/
theorem erc6909ApproveSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr approveTransition))).extract 0 4
      = ⟨#[0x42, 0x6a, 0x84, 0x93]⟩ := by
  have hsig : Solm.transitionSigStr approveTransition = "approve(address,uint256,uint256)" := by
    simp [Solm.transitionSigStr, ABI.printSignature, transitionSignature, approveTransition, addr, uint256, uint256Int, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, show Nat.repr 256 = "256" by decide +kernel]
    decide +kernel
  rw [hsig]
  decide +kernel

/-- `keccak("setOperator(address,bool)")[0:4] = 0x558a7297`. -/
theorem erc6909SetOperatorSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr setOperatorTransition))).extract 0 4
      = ⟨#[0x55, 0x8a, 0x72, 0x97]⟩ := by
  have hsig : Solm.transitionSigStr setOperatorTransition = "setOperator(address,bool)" := by
    simp [Solm.transitionSigStr, ABI.printSignature, transitionSignature, setOperatorTransition, addr, boolTy, ABI.abiToSigStr, ABI.elemToSigStr]
    decide +kernel
  rw [hsig]
  decide +kernel

/-- `keccak("allowance(address,address,uint256)")[0:4] = 0x598af9e7`. -/
theorem erc6909AllowanceSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr allowanceTransition))).extract 0 4
      = ⟨#[0x59, 0x8a, 0xf9, 0xe7]⟩ := by
  have hsig : Solm.transitionSigStr allowanceTransition = "allowance(address,address,uint256)" := by
    simp [Solm.transitionSigStr, ABI.printSignature, transitionSignature, allowanceTransition, addr, uint256, uint256Int, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, show Nat.repr 256 = "256" by decide +kernel]
    decide +kernel
  rw [hsig]
  decide +kernel

/-- `keccak("isOperator(address,address)")[0:4] = 0xb6363cf2`. -/
theorem erc6909IsOperatorSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr isOperatorTransition))).extract 0 4
      = ⟨#[0xb6, 0x36, 0x3c, 0xf2]⟩ := by
  have hsig : Solm.transitionSigStr isOperatorTransition = "isOperator(address,address)" := by
    simp [Solm.transitionSigStr, ABI.printSignature, transitionSignature, isOperatorTransition, addr, ABI.abiToSigStr, ABI.elemToSigStr]
    decide +kernel
  rw [hsig]
  decide +kernel

/-- `keccak("transferFrom(address,address,uint256,uint256)")[0:4] = 0xfe99049a`. -/
theorem erc6909TransferFromSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr transferFromTransition))).extract 0 4
      = ⟨#[0xfe, 0x99, 0x04, 0x9a]⟩ := by
  have hsig : Solm.transitionSigStr transferFromTransition = "transferFrom(address,address,uint256,uint256)" := by
    simp [Solm.transitionSigStr, ABI.printSignature, transitionSignature, transferFromTransition, addr, uint256, uint256Int, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, show Nat.repr 256 = "256" by decide +kernel]
    decide +kernel
  rw [hsig]
  decide +kernel

end OpenZeppelinBench.ERC6909
