import Examples.VyperERC20.TransferFromStoresTo

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

noncomputable def transferFromLogActualMemI (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (transferFromValueWord I)).write 0 (transferFromAfterToLoadMemI σ I) 160 32

noncomputable def transferFromReturnActualMemI (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (transferFromLogActualMemI σ I) 160 32

theorem transferFromLogActualMemI_size (σ : AccountMap) (I : ExecutionEnv) :
    (transferFromLogActualMemI σ I).size = 192 := by
  have hbase :
      (transferFromAfterToLoadMemI σ I).size = 160 := by
    simpa [transferFromAfterToLoadMemI, transferFromAfterFromLoadMemI, transferFromAllowanceScratchMemI] using
      transferFromAfterToLoadMem_size
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I)
  unfold transferFromLogActualMemI
  have hw :=
    write_end_size_from (UInt256.toByteArray (transferFromValueWord I))
      (transferFromAfterToLoadMemI σ I) 0 32
      (by decide)
      (by rw [toByteArray_size])
  rw [hbase] at hw
  simpa using hw

theorem transferFromReturnActualMemI_read160 (σ : AccountMap) (I : ExecutionEnv) :
    (transferFromReturnActualMemI σ I).readWithPadding 160 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold transferFromReturnActualMemI
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [transferFromLogActualMemI_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem erc20X_transferFromAfterLogTopics {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨563⟩
      [transferFromSelectorWord]
      (transferFromAfterToLoadMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterToI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨602⟩
      [transferEventTopic, transferFromFromWord I, transferFromToWord I, transferFromSelectorWord]
      (transferFromAfterToLoadMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterToI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨k, C, rd563⟩ := hreach
  have hafterSize :
      (transferFromAfterToLoadMemI σ I).size = 160 := by
    simpa [transferFromAfterToLoadMemI, transferFromAfterFromLoadMemI, transferFromAllowanceScratchMemI] using
      transferFromAfterToLoadMem_size
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I)
  have hread96 :
      (transferFromAfterToLoadMemI σ I).readWithPadding 96 32 =
        UInt256.toByteArray (transferFromToWord I) := by
    simpa [transferFromAfterToLoadMemI, transferFromAfterFromLoadMemI, transferFromAllowanceScratchMemI] using
      transferFromAfterToLoadMem_read96
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I)
  have hread64 :
      (transferFromAfterToLoadMemI σ I).readWithPadding 64 32 =
        UInt256.toByteArray (transferFromFromWord I) := by
    simpa [transferFromAfterToLoadMemI, transferFromAfterFromLoadMemI, transferFromAllowanceScratchMemI] using
      transferFromAfterToLoadMem_read64
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I)
  have rdAfterTopic := (evm_run rd563 with [
    push1 ⟨96⟩,
    raw mload 0 (transferFromToWord I) (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := transferFromAfterToLoadMemI σ I)
          (aw := UInt256.ofNat 5) (off := ⟨96⟩) (v := transferFromToWord I)
          (by rw [hafterSize]; decide)
          (by decide)
          hread96)
      (by decide) (by evm_ov),
    push1 ⟨64⟩,
    raw mload 0 (transferFromFromWord I) (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := transferFromAfterToLoadMemI σ I)
          (aw := UInt256.ofNat 5) (off := ⟨64⟩) (v := transferFromFromWord I)
          (by rw [hafterSize]; decide)
          (by decide)
          hread64)
      (by decide) (by evm_ov)]).pushConst transferEventTopic (width := 32) (op := .PUSH32)
      (by decide) (by vyper_erc20_transferFrom_decode) (by evm_ov)
  exact ⟨_, _, rdAfterTopic⟩

theorem erc20X_transferFromBeforeLog {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨602⟩
      [transferEventTopic, transferFromFromWord I, transferFromToWord I, transferFromSelectorWord]
      (transferFromAfterToLoadMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterToI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨612⟩
      [⟨160⟩, ⟨32⟩, transferEventTopic, transferFromFromWord I, transferFromToWord I,
        transferFromSelectorWord]
      (transferFromLogActualMemI σ I)
      (UInt256.ofNat 6) ByteArray.empty
      (cA, transferFromAccountMapAfterToI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨k, C, rdAfterTopic⟩ := hreach
  have rdBeforeLog := evm_run rdAfterTopic with [
    push1 ⟨68⟩, calldataload,
    push1 ⟨160⟩,
    raw mstore 3
      (transferFromLogActualMemI σ I)
      (UInt256.ofNat 6)
      (by vyper_erc20_transferFrom_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨160⟩]
  have hpc612 :
      (⟨602⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 =
        (⟨612⟩ : UInt256) := by
    native_decide
  exact ⟨_, _, by simpa [hpc612] using rdBeforeLog⟩

theorem erc20X_transferFromAfterLog {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨612⟩
      [⟨160⟩, ⟨32⟩, transferEventTopic, transferFromFromWord I, transferFromToWord I,
        transferFromSelectorWord]
      (transferFromLogActualMemI σ I)
      (UInt256.ofNat 6) ByteArray.empty
      (cA, transferFromAccountMapAfterToI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨613⟩
      [transferFromSelectorWord]
      (transferFromLogActualMemI σ I)
      (UInt256.ofNat 6) ByteArray.empty
      (cA, transferFromAccountMapAfterToI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨k, C, rd612⟩ := hreach
  exact ⟨_, _, rd612.log3 0 (UInt256.ofNat 6)
    (by vyper_erc20_transferFrom_decode) hperm mem_cost (by decide) (by evm_ov)⟩

theorem erc20X_transferFromReturnFromAfterLog {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨613⟩
      [transferFromSelectorWord]
      (transferFromLogActualMemI σ I)
      (UInt256.ofNat 6) ByteArray.empty
      (cA, transferFromAccountMapAfterToI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C) :
    RDret vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, transferFromAccountMapAfterToI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨k, C, rd613⟩ := hreach
  have rdBeforeReturn := evm_run rd613 with [
    push1 ⟨1⟩, push1 ⟨160⟩,
    raw mstore 0
      (transferFromReturnActualMemI σ I)
      (UInt256.ofNat 6)
      (by vyper_erc20_transferFrom_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨160⟩]
  exact rdBeforeReturn.ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256))
    (by vyper_erc20_transferFrom_decode) mem_cost
    (transferFromReturnActualMemI_read160 σ I)
    (by evm_ov)

end VyperERC20
