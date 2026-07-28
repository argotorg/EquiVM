import Examples.VyperERC20.TransferFromStoresAfterFromStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAfterToLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨528⟩
      [transferFromSelectorWord]
      (transferFromAfterFromLoadMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterBalanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨543⟩
      [transferFromToBalanceRawAfterBalance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
          (transferFromBalanceDebitWord
            (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I),
        transferFromToSlot I, transferFromSelectorWord]
      (transferFromAfterToLoadMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterBalanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)) k C := by
  obtain ⟨k, C, rd528⟩ := hreach
  let evm0 := initState cA gh bl σ σ₀ g A I
  have hread0_64 :
      (transferFromAfterToLoadMemI σ I).readWithPadding 0 64 =
        UInt256.toByteArray (⟨0⟩ : UInt256) ++ UInt256.toByteArray (transferFromToWord I) := by
    simpa [transferFromAfterToLoadMemI, transferFromAfterFromLoadMemI, transferFromAllowanceScratchMemI] using
      transferFromAfterToLoadMem_read0_64
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I)
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC ((transferFromAfterToLoadMemI σ I).readWithPadding 0 64))) =
        transferFromToSlot I := by
    rw [hread0_64]
    unfold transferFromToSlot erc20BalanceOfSlot vyperMappingSlot
    rw [keyValueToWord_address_of_canonical _ hcanonTo]
    exact keccakSlot_eq _
  have htoLoadRaw :
      transferFromToBalanceRawAfterBalance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
          (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm0 I) I) =
        transferFromToBalanceWord evm0 I := by
    simpa [evm0] using
      (transferFromToBalanceRawAfterBalance_initState (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
  have hafterSize :
      (transferFromAfterFromLoadMemI σ I).size = 160 := by
    simpa [transferFromAfterFromLoadMemI, transferFromAllowanceScratchMemI] using
      transferFromAfterFromLoadMem_size
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I)
  have hread96 :
      (transferFromAfterFromLoadMemI σ I).readWithPadding 96 32 =
        UInt256.toByteArray (transferFromToWord I) := by
    simpa [transferFromAfterFromLoadMemI, transferFromAllowanceScratchMemI] using
      transferFromAfterFromLoadMem_read96
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I)
  have rd541 := evm_run rd528 with [
    push0, push1 ⟨96⟩,
    raw mload 0 (transferFromToWord I) (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := transferFromAfterFromLoadMemI σ I)
          (aw := UInt256.ofNat 5) (off := ⟨96⟩) (v := transferFromToWord I)
          (by rw [hafterSize]; decide)
          (by decide)
          hread96)
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    raw mstore 0
      (wordAt32Mem (transferFromToWord I) (transferFromAfterFromLoadMemI σ I))
      (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost rfl (by decide) (by evm_ov),
    push0,
    raw mstore 0
      (transferFromAfterToLoadMemI σ I)
      (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (transferFromToSlot I)
      (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost hslot (by decide) (by evm_ov),
    dup1]
  obtain ⟨k1, C1, rdAfterLoad⟩ := rd541.sload
    (by vyper_erc20_transferFrom_decode) (by evm_ov)
  have hpc543 :
      (⟨528⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        (⟨543⟩ : UInt256) := by
    native_decide
  exact ⟨_, _, by
    simpa [evm0, htoLoadRaw, hpc543, transferFromAfterToLoadMemI,
      transferFromToBalanceRawAfterBalance] using rdAfterLoad⟩

theorem erc20X_transferFromBeforeToStore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hfit : transferFromNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨543⟩
      [transferFromToBalanceRawAfterBalance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
          (transferFromBalanceDebitWord
            (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I),
        transferFromToSlot I, transferFromSelectorWord]
      (transferFromAfterToLoadMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterBalanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨561⟩
      [transferFromToSlot I,
        transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromToSlot I, transferFromSelectorWord]
      (transferFromAfterToLoadMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterBalanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)) k C := by
  obtain ⟨k, C, rdAfterLoad⟩ := hreach
  let evm0 := initState cA gh bl σ σ₀ g A I
  have htoLoadRaw :
      transferFromToBalanceRawAfterBalance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
          (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm0 I) I) =
        transferFromToBalanceWord evm0 I := by
    simpa [evm0] using
      (transferFromToBalanceRawAfterBalance_initState (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
  have hnewRaw :
      transferFromToBalanceRawAfterBalance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
          (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm0 I) I) +
          transferFromValueWord I =
        transferFromNewToWord evm0 I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt (by
      rw [htoLoadRaw]
      simpa [evm0, transferFromNewToNat] using hfit)]
    rw [transferFromNewToWord_toNat evm0 I hfit, transferFromNewToNat, htoLoadRaw]
  have hcreditGuardRaw :
      UInt256.lt
          (transferFromToBalanceRawAfterBalance σ I
            (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
            (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm0 I) I) +
            transferFromValueWord I)
          (transferFromToBalanceRawAfterBalance σ I
            (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
            (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm0 I) I)) = ⟨0⟩ := by
    exact ult_zero (by
      rw [uadd_toNat, Nat.mod_eq_of_lt (by
        rw [htoLoadRaw]
        simpa [evm0, transferFromNewToNat] using hfit), htoLoadRaw]
      rw [transferFromNewToNat] at hfit
      exact Nat.le_add_right _ _)
  have rdBeforeStore := evm_run rdAfterLoad with [
    push1 ⟨68⟩, calldataload,
    dup1, dup3, add, dup3, dup2, lt, push2 ⟨801⟩,
    jumpiNT (by simpa [transferFromValueWord] using hcreditGuardRaw),
    swap1, pop, swap1, pop, dup2]
  have hnewRaw' :
      transferFromToBalanceRawAfterBalance σ I
          (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
          (transferFromBalanceDebitWord (transferFromAfterAllowanceState evm0 I) I) +
          uInt256OfByteArray (I.calldata.readBytes (⟨68⟩ : UInt256).toNat 32) =
        transferFromNewToWord evm0 I := by
    simpa [transferFromValueWord] using hnewRaw
  have hpc561 :
      (⟨543⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ =
        (⟨561⟩ : UInt256) := by
    native_decide
  exact ⟨_, _, by simpa [evm0, hnewRaw', hpc561] using rdBeforeStore⟩

theorem erc20X_transferFromAfterToStore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨561⟩
      [transferFromToSlot I,
        transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I,
        transferFromToSlot I, transferFromSelectorWord]
      (transferFromAfterToLoadMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterBalanceI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨563⟩
      [transferFromSelectorWord]
      (transferFromAfterToLoadMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromAccountMapAfterToI σ I
        (transferFromAllowanceDebitI cA gh bl σ σ₀ A I g)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState cA gh bl σ σ₀ g A I) I) I)
        (transferFromNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨k, C, rd561⟩ := hreach
  obtain ⟨k1, C1, rdAfterStore⟩ := rd561.sstore hperm
    (by vyper_erc20_transferFrom_decode) (by evm_ov)
  exact ⟨_, _, evm_run rdAfterStore with [pop]⟩

end VyperERC20
