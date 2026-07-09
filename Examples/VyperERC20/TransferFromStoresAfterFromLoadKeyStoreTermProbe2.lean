import Examples.VyperERC20.TransferFromStoresAfterFromLoadKeyReady

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

section

variable {cA gh bl σ σ₀ A I : _} {g : Sat256}

#check
  fun (rd499 : RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨499⟩
      [⟨32⟩, transferFromFromWord I, ⟨0⟩, transferFromSelectorWord]
      (transferFromAllowanceScratchMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferFromAllowanceSlotI I)
        (transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I)) 0 0) =>
    rd499.mstore 0
      (transferFromFromBalanceKeyMemI σ I)
      (UInt256.ofNat 5)
      (by native_decide) mem_cost rfl (by decide) (by evm_ov)

end

end VyperERC20
