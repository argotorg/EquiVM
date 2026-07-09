import Examples.VyperERC20.TransferFromAllowancePhase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAfterBalanceLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨423⟩
      [transferFromSelectorWord]
      (transferFromAllowanceMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨440⟩
      [transferFromFromBalanceRaw σ I, transferFromValueWord I, transferFromSelectorWord]
      (transferFromFromBalanceHashMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k, C, rd423⟩ := hreach
  have hslot := transferFromFromBalanceKeccakSlot I hcanonFrom
    (transferFromCurrentAllowanceRaw σ I)
  have rdBeforeLoad := evm_run rd423 with [
    push1 ⟨68⟩, calldataload,
    push0, push1 ⟨64⟩,
    raw mload 0 (transferFromFromWord I) (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := transferFromAllowanceMem
            (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
            (transferFromCurrentAllowanceRaw σ I))
          (aw := UInt256.ofNat 5) (off := ⟨64⟩) (v := transferFromFromWord I)
          (by rw [transferFromAllowanceMem_size]; decide)
          (by decide)
          (transferFromAllowanceMem_read64
            (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
            (transferFromCurrentAllowanceRaw σ I)))
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    raw mstore 0
      (transferFromFromBalanceKeyMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost rfl (by decide) (by evm_ov),
    push0,
    raw mstore 0
      (transferFromFromBalanceHashMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (transferFromFromSlot I)
      (UInt256.ofNat 5)
      (by vyper_erc20_transferFrom_decode) mem_cost
      (by
        simpa using hslot)
      (by decide) (by evm_ov)]
  obtain ⟨k1, C1, rdAfterLoad⟩ := rdBeforeLoad.sload
    (by vyper_erc20_transferFrom_decode) (by evm_ov)
  exact ⟨_, _, by simpa [transferFromFromBalanceRaw, transferFromValueWord] using rdAfterLoad⟩

theorem erc20X_transferFromAfterBalanceGuard {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hbalance : (transferFromValueWord I).toNat ≤
      (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨423⟩
      [transferFromSelectorWord]
      (transferFromAllowanceMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨445⟩
      [transferFromSelectorWord]
      (transferFromFromBalanceHashMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k, C, rdAfterLoad⟩ := erc20X_transferFromAfterBalanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcanonFrom hreach
  let evm0 := initState cA gh bl σ σ₀ g A I
  have hbalanceGuard :
      UInt256.lt (transferFromFromBalanceWord evm0 I) (transferFromValueWord I) = ⟨0⟩ := by
    exact ult_zero (by simpa [evm0] using hbalance)
  have hbalanceGuardRaw :
      UInt256.lt (transferFromFromBalanceRaw σ I) (transferFromValueWord I) = ⟨0⟩ := by
    rw [transferFromFromBalanceRaw_initState (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)]
    exact hbalanceGuard
  have rd445 := evm_run rdAfterLoad with [
    lt, push2 ⟨801⟩,
    jumpiNT (by simpa [transferFromValueWord] using hbalanceGuardRaw)]
  exact ⟨_, _, by simpa [transferFromFromBalanceRaw] using rd445⟩

theorem erc20TransferFromX_insufficientBalance {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonFrom : (transferFromFromWord I).toNat < EVM.addressModulus)
    (hlt : (transferFromFromBalanceWord (initState cA gh bl σ σ₀ g A I) I).toNat <
      (transferFromValueWord I).toNat)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨423⟩
      [transferFromSelectorWord]
      (transferFromAllowanceMem
        (transferFromFromWord I) (transferFromToWord I) (approveOwnerWord I)
        (transferFromCurrentAllowanceRaw σ I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  let evm0 := initState cA gh bl σ σ₀ g A I
  have hbalanceGuard :
      UInt256.lt (transferFromFromBalanceWord evm0 I) (transferFromValueWord I) = ⟨1⟩ := by
    exact ult_one (by simpa [evm0] using hlt)
  have hbalanceGuardRaw :
      UInt256.lt (transferFromFromBalanceRaw σ I) (transferFromValueWord I) = ⟨1⟩ := by
    rw [transferFromFromBalanceRaw_initState (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)]
    exact hbalanceGuard
  obtain ⟨k, C, rdAfterLoad⟩ := erc20X_transferFromAfterBalanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcanonFrom hreach
  have rd801 := evm_run rdAfterLoad with [
    lt, push2 ⟨801⟩,
    jumpiT (by
      intro hzero
      have hone : (⟨1⟩ : UInt256) ≠ ⟨0⟩ := by decide
      exact hone (by simpa [hbalanceGuardRaw] using hzero))
      (by vyper_erc20_transferFrom_decode)]
  exact vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) rd801 rfl (by
      simp only [List.length_cons, List.length_nil]
      omega)


end VyperERC20
