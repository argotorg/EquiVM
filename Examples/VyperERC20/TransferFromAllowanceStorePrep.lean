import Examples.VyperERC20.TransferFromAllowanceStoreInnerHashStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAllowanceStoreInnerSlot {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨475⟩
      [transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromSelectorWord]
      (transferFromAllowanceInnerScratchMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨479⟩
      [transferFromAllowanceInnerSlotWord (transferFromFromWord I) (transferFromToWord I),
        transferFromAllowanceDebitWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromSelectorWord]
      (transferFromAllowanceInnerScratchMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k, C, rd475⟩ := hreach
  have rd477 := evm_run rd475 with [push1 ⟨64⟩, push0]
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (ffi.KEC ((transferFromAllowanceInnerScratchMem
              (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
              (transferFromCurrentAllowanceRaw σ I)).readWithPadding 0 64))) =
        transferFromAllowanceInnerSlotWord (transferFromFromWord I) (transferFromToWord I) := by
    unfold transferFromAllowanceInnerSlotWord
    rw [transferFromAllowanceInnerScratchMem_read0_64,
      transferFromAllowanceInnerHashMem_read0_64]
  have rd479 := rd477.keccak256 0
    (transferFromAllowanceInnerSlotWord (transferFromFromWord I) (transferFromToWord I))
    (UInt256.ofNat 5)
    (by native_decide) mem_cost hslot (by decide) (by evm_ov)
  exact ⟨_, _, rd479⟩


end VyperERC20
