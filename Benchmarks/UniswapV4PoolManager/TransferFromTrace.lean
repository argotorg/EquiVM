import Benchmarks.UniswapV4PoolManager.TransferFromSource
import Benchmarks.UniswapV4PoolManager.MappingMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_004
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_005

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000000

def transferFromStack (sender receiver id amount : UInt256) (R : List UInt256) : List UInt256 :=
  receiver :: solcAddrMask :: ⟨633⟩ :: transferEventTopic :: sender :: amount :: id :: R

def operatorSlot (sender caller : UInt256) : UInt256 := mappingSlotWord caller (mappingSlotWord sender ⟨3⟩)

def transferFromOperatorMemory (I : ExecutionEnv) (sender : UInt256) (mem : ByteArray) : ByteArray :=
  nestedMappingMemory sender (accountWord I.source) ⟨3⟩ mem

theorem transferFromOperatorTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {sender receiver : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 12 ≤ 1024) (hmem : mem.size = 96)
    (hc : sender.toNat < EVM.addressModulus) (hne : accountWord I.source ≠ sender)
    (h : RD (deployedRuntime v) I g s0 ⟨453⟩ (receiver :: sender :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨532⟩
      (UInt256.isZero (UInt256.land (solcSlotWordAt (operatorSlot sender (accountWord I.source)) σ I) ⟨255⟩) ::
        transferFromStack sender receiver (calldataWord I.calldata 68) (calldataWord I.calldata 100) R)
      (transferFromOperatorMemory I sender mem) aw' rdata σ k' C' := by
  have heq : UInt256.eq (accountWord I.source) sender = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun h => hne (uInt256_eq_one_eq h))
  have hcond : UInt256.isZero (UInt256.eq (accountWord I.source) (UInt256.land sender solcAddrMask)) ≠ ⟨0⟩ := by
    rw [solcAddrMask_clean hc, heq]; decide
  have hj781 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 781) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have h781 := poolManagerBlocks.poolManager_block_453_taken (by omega) hcond hj781 h
  change RD (deployedRuntime v) I g s0 ⟨781⟩
    (UInt256.isZero (UInt256.eq (accountWord I.source) (UInt256.land sender solcAddrMask)) ::
      receiver :: solcAddrMask :: ⟨633⟩ :: transferEventTopic :: UInt256.land sender solcAddrMask ::
      calldataWord I.calldata 100 :: calldataWord I.calldata 68 :: R) mem aw rdata σ _ _ at h781
  rw [solcAddrMask_clean hc] at h781
  have hj532 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 532) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  obtain ⟨k', C', hnext⟩ := poolManagerBlocks.poolManager_block_781
    (by simp only [List.length_cons]; omega) hj532 h781
  let masked := UInt256.land (accountWord I.source) solcAddrMask
  let nextMem := nestedMappingMemory sender masked ⟨3⟩ mem
  change RD (deployedRuntime v) I g s0 ⟨532⟩
    (UInt256.isZero (UInt256.land (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ nextMem) σ I) ⟨255⟩) ::
      transferFromStack sender receiver (calldataWord I.calldata 68) (calldataWord I.calldata 100) R)
    nextMem _ rdata σ k' C' at hnext
  have hm : masked = accountWord I.source := solcAddrMask_clean (accountWord_canonical _)
  dsimp only [nextMem] at hnext
  rw [hm, nestedMappingMemory_slot _ _ _ hmem] at hnext
  exact ⟨_, k', C', hnext⟩

theorem transferFromSkipAllowanceTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {sender receiver : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 12 ≤ 1024) (hmem : mem.size = 96)
    (hc : sender.toNat < EVM.addressModulus)
    (hskip : ¬(accountWord I.source ≠ sender ∧
      UInt256.land (solcSlotWordAt (operatorSlot sender (accountWord I.source)) σ I) ⟨255⟩ = ⟨0⟩))
    (h : RD (deployedRuntime v) I g s0 ⟨453⟩ (receiver :: sender :: R) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', mem'.size = 96 ∧ memLoad ⟨64⟩ mem' = memLoad ⟨64⟩ mem ∧
      RD (deployedRuntime v) I g s0 ⟨537⟩
        (transferFromStack sender receiver (calldataWord I.calldata 68) (calldataWord I.calldata 100) R)
        mem' aw' rdata σ k' C' := by
  by_cases heq : accountWord I.source = sender
  · have hcond : UInt256.isZero (UInt256.eq (accountWord I.source) (UInt256.land sender solcAddrMask)) = ⟨0⟩ := by
      rw [solcAddrMask_clean hc, heq, uInt256_eq_self]; decide
    have h532 := poolManagerBlocks.poolManager_block_453_fallthrough (by omega) hcond h
    change RD (deployedRuntime v) I g s0 ⟨532⟩
      (UInt256.isZero (UInt256.eq (accountWord I.source) (UInt256.land sender solcAddrMask)) ::
        receiver :: solcAddrMask :: ⟨633⟩ :: transferEventTopic :: UInt256.land sender solcAddrMask ::
        calldataWord I.calldata 100 :: calldataWord I.calldata 68 :: R) mem aw rdata σ _ _ at h532
    rw [solcAddrMask_clean hc] at h532
    have hz : UInt256.isZero (UInt256.eq (accountWord I.source) sender) = ⟨0⟩ := by
      rw [heq, uInt256_eq_self]; decide
    have h537 := poolManagerBlocks.poolManager_block_532_fallthrough
      (R := transferFromStack sender receiver (calldataWord I.calldata 68) (calldataWord I.calldata 100) R)
      (by simp only [transferFromStack, List.length_cons]; omega) hz h532
    exact ⟨mem, _, _, _, hmem, rfl, h537⟩
  · have hop : UInt256.land (solcSlotWordAt (operatorSlot sender (accountWord I.source)) σ I) ⟨255⟩ ≠ ⟨0⟩ :=
      fun hz => hskip ⟨heq, hz⟩
    obtain ⟨aw', k', C', h532⟩ := transferFromOperatorTrace v hstack hmem hc heq h
    have h537 := poolManagerBlocks.poolManager_block_532_fallthrough
      (by simp only [transferFromStack, List.length_cons]; omega) (isZero_eq_zero_of_ne hop) h532
    exact ⟨_, _, _, _, nestedMappingMemory_size _ _ _ hmem,
      nestedMappingMemory_load64 _ _ _ hmem, h537⟩

theorem transferFromNeedAllowanceTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {sender receiver : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 12 ≤ 1024) (hmem : mem.size = 96)
    (hc : sender.toNat < EVM.addressModulus)
    (hneed : accountWord I.source ≠ sender ∧
      UInt256.land (solcSlotWordAt (operatorSlot sender (accountWord I.source)) σ I) ⟨255⟩ = ⟨0⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨453⟩ (receiver :: sender :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨647⟩
      (transferFromStack sender receiver (calldataWord I.calldata 68) (calldataWord I.calldata 100) R)
      (transferFromOperatorMemory I sender mem) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', h532⟩ := transferFromOperatorTrace v hstack hmem hc hneed.1 h
  have hj647 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 647) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have h537 := poolManagerBlocks.poolManager_block_532_taken
    (by simp only [transferFromStack, List.length_cons]; omega) (by rw [hneed.2]; decide) hj647 h532
  exact ⟨_, _, _, h537⟩


def transferFromAllowanceMemory (I : ExecutionEnv) (sender id : UInt256) (mem : ByteArray) : ByteArray :=
  tripleMappingMemory sender (accountWord I.source) id ⟨5⟩ mem

theorem transferFromAllowanceReadTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {sender receiver id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 12 ≤ 1024) (hmem : mem.size = 96)
    (h : RD (deployedRuntime v) I g s0 ⟨647⟩ (transferFromStack sender receiver id amount R)
      mem aw rdata σ k C) :
    let allowed := solcSlotWordAt (allowanceSlot sender (accountWord I.source) id) σ I
    ∃ aw' k' C', RD (deployedRuntime v) I g s0
      (if allowed = maxAllowanceWord then ⟨723⟩ else ⟨730⟩)
      (amount :: allowed :: transferFromStack sender receiver id amount R)
      (transferFromAllowanceMemory I sender id mem) aw' rdata σ k' C' := by
  let allowed := solcSlotWordAt (allowanceSlot sender (accountWord I.source) id) σ I
  let rawMem := tripleMappingMemory sender (UInt256.land (accountWord I.source) solcAddrMask) id ⟨5⟩ mem
  have hm : rawMem = transferFromAllowanceMemory I sender id mem := by
    dsimp only [rawMem, transferFromAllowanceMemory]
    rw [solcAddrMask_clean (accountWord_canonical _)]
  have hs : keccakWord ⟨0⟩ ⟨64⟩ rawMem = allowanceSlot sender (accountWord I.source) id := by
    rw [hm, transferFromAllowanceMemory, tripleMappingMemory_slot _ _ _ _ hmem]; rfl
  have hv : solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ rawMem) σ I = allowed := congrArg (fun slot => solcSlotWordAt slot σ I) hs
  dsimp only
  by_cases hmax : allowed = maxAllowanceWord
  · rw [if_pos hmax]
    have hcond : UInt256.sub (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ rawMem) σ I) maxAllowanceWord = ⟨0⟩ := by
      rw [hv, hmax]; exact u256_sub_eq_zero_iff_eq.mpr rfl
    obtain ⟨k', C', hnext⟩ := poolManagerBlocks.poolManager_block_647_fallthrough (R := R) (by omega) hcond h
    change RD (deployedRuntime v) I g s0 ⟨723⟩
      (amount :: solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ rawMem) σ I :: transferFromStack sender receiver id amount R)
      rawMem _ rdata σ k' C' at hnext
    rw [hv, hm] at hnext
    exact ⟨_, k', C', hnext⟩
  · rw [if_neg hmax]
    have hcond : UInt256.sub (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ rawMem) σ I) maxAllowanceWord ≠ ⟨0⟩ := by
      rw [hv]; exact fun hz => hmax (u256_sub_eq_zero_iff_eq.mp hz)
    have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 730) = true := by
      rw [deployedRuntime_jumps]; jump_dest
    obtain ⟨k', C', hnext⟩ := poolManagerBlocks.poolManager_block_647_taken (R := R) (by omega) hcond hj h
    change RD (deployedRuntime v) I g s0 ⟨730⟩
      (amount :: solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ rawMem) σ I :: transferFromStack sender receiver id amount R)
      rawMem _ rdata σ k' C' at hnext
    rw [hv, hm] at hnext
    exact ⟨_, k', C', hnext⟩

theorem transferFromAllowanceStoreTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {sender receiver id amount value : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 12 ≤ 1024) (hmem : mem.size = 96) (hperm : I.perm = true)
    (h : RD (deployedRuntime v) I g s0 ⟨739⟩ (value :: transferFromStack sender receiver id amount R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨537⟩ (transferFromStack sender receiver id amount R)
      (transferFromAllowanceMemory I sender id mem) aw' rdata
      (sstoreAccountMap I.codeOwner σ (allowanceSlot sender (accountWord I.source) id) value) k' C' := by
  have hj723 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 723) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have hj537 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 537) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  obtain ⟨k', C', h723⟩ := poolManagerBlocks.poolManager_block_739 (R := R) (by omega) hperm hj723 h
  let rawMem := tripleMappingMemory sender (UInt256.land (accountWord I.source) solcAddrMask) id ⟨5⟩ mem
  change RD (deployedRuntime v) I g s0 ⟨723⟩ (amount :: ⟨0⟩ :: transferFromStack sender receiver id amount R)
    rawMem _ rdata (sstoreAccountMap I.codeOwner σ (keccakWord ⟨0⟩ ⟨64⟩ rawMem) value) k' C' at h723
  have h537 := poolManagerBlocks.poolManager_block_723
    (by simp only [transferFromStack, List.length_cons]; omega) hj537 h723
  have hm : rawMem = transferFromAllowanceMemory I sender id mem := by
    dsimp only [rawMem, transferFromAllowanceMemory]
    rw [solcAddrMask_clean (accountWord_canonical _)]
  have hs : keccakWord ⟨0⟩ ⟨64⟩ rawMem = allowanceSlot sender (accountWord I.source) id := by
    rw [hm, transferFromAllowanceMemory, tripleMappingMemory_slot _ _ _ _ hmem]; rfl
  rw [hs, hm] at h537
  exact ⟨_, _, _, h537⟩

open poolManagerBlocks in
theorem transferFromAllowanceStaticTrace {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 739) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata σ k C)
    : RDstatic (immutableLayout.runtime poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨739⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup6 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨740⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨741⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨742⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 5) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨743⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 5), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨745⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨747⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨748⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨750⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨751⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨752⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.caller (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨753⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨754⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨755⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := RD.genMstore r14 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨756⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨757⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := RD.genMstore r16 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨759⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨760⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨762⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := RD.genKeccak256 r19 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨763⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup9 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨764⟩ : UInt256), UInt8.ofNat 136, .DUP9, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨765⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := RD.genMstore r22 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨766⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨767⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := RD.genMstore r24 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨769⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨770⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨772⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := RD.genKeccak256 r27 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨773⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r28 hperm
    (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨774⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64))
    (by evm_ov)


theorem transferFromBalanceLoadTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {sender receiver id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 12 ≤ 1024) (hmem : mem.size = 96)
    (h : RD (deployedRuntime v) I g s0 ⟨537⟩ (transferFromStack sender receiver id amount R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12269⟩
      (solcSlotWordAt (balanceSlot sender id) σ I :: amount :: ⟨570⟩ :: balanceSlot sender id ::
        transferFromStack sender receiver id amount R)
      (nestedMappingMemory sender id ⟨4⟩ mem) aw' rdata σ k' C' := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12269) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  obtain ⟨k', C', hnext⟩ := poolManagerBlocks.poolManager_block_537 (R := R) hstack hj h
  let nextMem := nestedMappingMemory sender id ⟨4⟩ mem
  change RD (deployedRuntime v) I g s0 ⟨12269⟩
    (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ nextMem) σ I :: amount :: ⟨570⟩ ::
      keccakWord ⟨0⟩ ⟨64⟩ nextMem :: transferFromStack sender receiver id amount R)
    nextMem _ rdata σ k' C' at hnext
  rw [nestedMappingMemory_slot _ _ _ hmem] at hnext
  exact ⟨_, k', C', hnext⟩

open poolManagerBlocks in
theorem transferFromBalanceStaticTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {value slot : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 2 ≤ 1024) (hperm : I.perm = false)
    (h : RD (deployedRuntime v) I g s0 ⟨570⟩ (value :: slot :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  have r1 := h.jumpdest
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨570⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨571⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r2 hperm
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨572⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

theorem transferFromBalanceCreditTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {value slot sender receiver id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 12 ≤ 1024) (hmem : mem.size = 96)
    (hc : receiver.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (h : RD (deployedRuntime v) I g s0 ⟨570⟩
      (value :: slot :: transferFromStack sender receiver id amount R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12282⟩
      (solcSlotWordAt (balanceSlot receiver id) (sstoreAccountMap I.codeOwner σ slot value) I ::
        amount :: ⟨607⟩ :: balanceSlot receiver id :: amount :: ⟨633⟩ :: transferEventTopic :: sender :: receiver :: id :: R)
      (nestedMappingMemory receiver id ⟨4⟩ mem) aw' rdata (sstoreAccountMap I.codeOwner σ slot value) k' C' := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12282) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  obtain ⟨k', C', hnext⟩ := poolManagerBlocks.poolManager_block_570 (R := R) (by omega) hperm hj h
  let masked := UInt256.land receiver solcAddrMask
  let nextMem := nestedMappingMemory masked id ⟨4⟩ mem
  change RD (deployedRuntime v) I g s0 ⟨12282⟩
    (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ nextMem) (sstoreAccountMap I.codeOwner σ slot value) I ::
      amount :: ⟨607⟩ :: keccakWord ⟨0⟩ ⟨64⟩ nextMem :: amount :: ⟨633⟩ :: transferEventTopic :: sender :: masked :: id :: R)
    nextMem _ rdata (sstoreAccountMap I.codeOwner σ slot value) k' C' at hnext
  have hm : masked = receiver := solcAddrMask_clean hc
  dsimp only [nextMem] at hnext
  rw [hm, nestedMappingMemory_slot _ _ _ hmem] at hnext
  exact ⟨_, k', C', hnext⟩

theorem transferFromBalanceReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {value slot sender receiver id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 12 ≤ 1024) (hmem : mem.size = 96) (hp : memLoad ⟨64⟩ mem = ⟨160⟩)
    (hperm : I.perm = true)
    (h : RD (deployedRuntime v) I g s0 ⟨607⟩
      (value :: slot :: amount :: ⟨633⟩ :: transferEventTopic :: sender :: receiver :: id :: R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 (sstoreAccountMap I.codeOwner σ slot value) (⟨1⟩ : UInt256).toByteArray := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 633) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  obtain ⟨k', C', hnext⟩ := poolManagerBlocks.poolManager_block_607
    (R := transferEventTopic :: sender :: receiver :: id :: R)
    (by simp only [List.length_cons]; omega) hperm hj h
  have hret := poolManagerBlocks.poolManager_block_633 (R := R) (by omega) hperm hnext
  let eventMem := Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem
    (memLoad ⟨64⟩ mem).toNat (accountWord I.source)) (memLoad ⟨64⟩ mem + ⟨32⟩).toNat amount
  change RDret (deployedRuntime v) g s0 (sstoreAccountMap I.codeOwner σ slot value)
    (((⟨1⟩ : UInt256).toByteArray.write 0 eventMem (memLoad ⟨64⟩ eventMem).toNat 32).readWithPadding
      (memLoad ⟨64⟩ eventMem).toNat 32) at hret
  have hout := eventTwoWordsThenReturn hp (by rw [hmem]) (by decide)
    (by rw [hmem]; native_decide) (by decide) (accountWord I.source) amount (⟨1⟩ : UInt256)
  exact (congrArg (fun out => RDret (deployedRuntime v) g s0 (sstoreAccountMap I.codeOwner σ slot value) out) hout).mp hret

end Benchmarks.UniswapV4PoolManager
