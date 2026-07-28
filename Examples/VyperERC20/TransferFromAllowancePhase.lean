import Examples.VyperERC20.TransferFromBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAfterAllowanceSLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨331⟩
      [transferFromSelectorWord] transferFromDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨409⟩
      [transferFromCurrentAllowanceRaw σ I, transferFromSelectorWord]
      (transferFromAllowanceOuterHashMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I))
      (UInt256.ofNat 4) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k, C, rd331⟩ := hreach
  have hslot := transferFromAllowanceOuterKeccakSlot I hcanonFrom
  have hsizeGuard := calldataSizeGuardOk (n := I.calldata.size) (m := 100) hsz100 hsize
  have hcanonFromGuard : UInt256.shiftRight (transferFromFromWord I) ⟨160⟩ = ⟨0⟩ :=
    u256_shiftRight160_zero_of_lt (transferFromFromWord I) hcanonFrom
  have hcanonToGuard : UInt256.shiftRight (transferFromToWord I) ⟨160⟩ = ⟨0⟩ :=
    u256_shiftRight160_zero_of_lt (transferFromToWord I) hcanonTo
  have rd412 := evm_run rd331 with [
    jumpdest,
    raw push4 transferFromSelectorWord (by vyper_erc20_transferFrom_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by native_decide),
    push1 ⟨100⟩, calldatasize, lt, callvalue, lor, push2 ⟨801⟩,
    jumpiNT (by rw [u256_lor_comm, hwv, u256_lor_zero]; exact hsizeGuard),
    push1 ⟨4⟩, calldataload, dup1, push1 ⟨160⟩, shr, push2 ⟨801⟩,
    jumpiNT (by simpa [transferFromFromWord, calldataWord] using hcanonFromGuard),
    push1 ⟨64⟩,
    raw mstore 6 (transferFromFromArgMem (transferFromFromWord I)) (UInt256.ofNat 3)
      (by vyper_erc20_transferFrom_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨36⟩, calldataload, dup1, push1 ⟨160⟩, shr, push2 ⟨801⟩,
    jumpiNT (by simpa [transferFromToWord, calldataWord] using hcanonToGuard),
    push1 ⟨96⟩,
    raw mstore 3
      (transferFromArgsMem (transferFromFromWord I) (transferFromToWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_transferFrom_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨64⟩,
    raw mload 0 (transferFromFromWord I) (UInt256.ofNat 4)
      (by vyper_erc20_transferFrom_decode)
      mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := transferFromArgsMem (transferFromFromWord I) (transferFromToWord I))
          (aw := UInt256.ofNat 4) (off := ⟨64⟩) (v := transferFromFromWord I)
          (by rw [transferFromArgsMem_size]; decide)
          (by decide)
          (transferFromArgsMem_read64 (transferFromFromWord I) (transferFromToWord I)))
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    raw mstore 0
      (transferFromAllowanceInnerKeyMem (transferFromFromWord I) (transferFromToWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_transferFrom_decode) mem_cost rfl (by decide) (by evm_ov),
    push0,
    raw mstore 0
      (transferFromAllowanceInnerHashMem (transferFromFromWord I) (transferFromToWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_transferFrom_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0
      (transferFromAllowanceInnerSlotWord (transferFromFromWord I) (transferFromToWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_transferFrom_decode) mem_cost rfl (by decide) (by evm_ov),
    dup1, caller, push1 ⟨32⟩,
    raw mstore 0
      (transferFromAllowanceOuterKeyMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_transferFrom_decode) mem_cost rfl (by decide) (by evm_ov),
    push0,
    raw mstore 0
      (transferFromAllowanceOuterHashMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_transferFrom_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (transferFromAllowanceSlotI I)
      (UInt256.ofNat 4)
      (by vyper_erc20_transferFrom_decode) mem_cost hslot (by decide) (by evm_ov),
    swap1, pop]
  obtain ⟨k1, C1, rdAfterLoad⟩ := rd412.sload
    (by vyper_erc20_transferFrom_decode) (by evm_ov)
  exact ⟨_, _, by simpa [transferFromCurrentAllowanceRaw] using rdAfterLoad⟩

theorem erc20X_transferFromAfterAllowanceLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (transferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨331⟩
      [transferFromSelectorWord] transferFromDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨412⟩
      [transferFromSelectorWord]
      (transferFromAllowanceMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k, C, rdAfterLoad⟩ := erc20X_transferFromAfterAllowanceSLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hwv hsz100 hsize hcanonFrom hcanonTo hreach
  have rdAfterStore := evm_run rdAfterLoad with [
    push1 ⟨128⟩,
    raw mstore 3
      (transferFromAllowanceMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost rfl (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa [transferFromCurrentAllowanceRaw] using rdAfterStore⟩

theorem erc20X_transferFromAfterAllowanceGuard {cA gh bl σ σ₀ A I} {g : Sat256}
    (hallowance : (transferFromValueWord I).toNat ≤
      (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨412⟩
      [transferFromSelectorWord]
      (transferFromAllowanceMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨423⟩
      [transferFromSelectorWord]
      (transferFromAllowanceMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k, C, rd412⟩ := hreach
  let evm0 := initState cA gh bl σ σ₀ g A I
  have hallowanceGuard :
      UInt256.lt (transferFromCurrentAllowanceWord evm0 I) (transferFromValueWord I) = ⟨0⟩ := by
    exact ult_zero (by simpa [evm0] using hallowance)
  have hallowanceGuardRaw :
      UInt256.lt (transferFromCurrentAllowanceRaw σ I) (transferFromValueWord I) = ⟨0⟩ := by
    rw [transferFromCurrentAllowanceRaw_initState (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)]
    exact hallowanceGuard
  have rd423 := evm_run rd412 with [
    push1 ⟨68⟩, calldataload,
    push1 ⟨128⟩,
    raw mload 0 (transferFromCurrentAllowanceRaw σ I) (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := transferFromAllowanceMem
            (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
            (transferFromCurrentAllowanceRaw σ I))
          (aw := UInt256.ofNat 5) (off := ⟨128⟩) (v := transferFromCurrentAllowanceRaw σ I)
          (by rw [transferFromAllowanceMem_size]; decide)
          (by decide)
          (transferFromAllowanceMem_read128
            (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
            (transferFromCurrentAllowanceRaw σ I)))
      (by decide) (by evm_ov),
    lt, push2 ⟨801⟩,
    jumpiNT (by simpa [transferFromValueWord] using hallowanceGuardRaw)]
  exact ⟨_, _, rd423⟩

theorem erc20TransferFromX_insufficientAllowance {cA gh bl σ σ₀ A I} {g : Sat256}
    (hlt : (transferFromCurrentAllowanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromValueWord I).toNat)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨412⟩
      [transferFromSelectorWord]
      (transferFromAllowanceMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd412⟩ := hreach
  let evm0 := initState cA gh bl σ σ₀ g A I
  have hallowanceGuard :
      UInt256.lt (transferFromCurrentAllowanceWord evm0 I) (transferFromValueWord I) = ⟨1⟩ := by
    exact ult_one (by simpa [evm0] using hlt)
  have hallowanceGuardRaw :
      UInt256.lt (transferFromCurrentAllowanceRaw σ I) (transferFromValueWord I) = ⟨1⟩ := by
    rw [transferFromCurrentAllowanceRaw_initState (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)]
    exact hallowanceGuard
  have rd801 := evm_run rd412 with [
    push1 ⟨68⟩, calldataload,
    push1 ⟨128⟩,
    raw mload 0 (transferFromCurrentAllowanceRaw σ I) (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := transferFromAllowanceMem
            (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
            (transferFromCurrentAllowanceRaw σ I))
          (aw := UInt256.ofNat 5) (off := ⟨128⟩) (v := transferFromCurrentAllowanceRaw σ I)
          (by rw [transferFromAllowanceMem_size]; decide)
          (by decide)
          (transferFromAllowanceMem_read128
            (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
            (transferFromCurrentAllowanceRaw σ I)))
      (by decide) (by evm_ov),
    lt, push2 ⟨801⟩,
    jumpiT (by rw [show
        UInt256.lt
          (transferFromCurrentAllowanceRaw σ I)
          (uInt256OfByteArray (I.calldata.readBytes (⟨68⟩ : UInt256).toNat 32)) = ⟨1⟩ by
          simpa [transferFromValueWord] using hallowanceGuardRaw]; decide)
      (by vyper_erc20_transferFrom_decode)]
  exact vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) rd801 rfl (by
      simp only [List.length_cons, List.length_nil]
      omega)


end VyperERC20
