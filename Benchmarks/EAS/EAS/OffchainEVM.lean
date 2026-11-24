import Benchmarks.EAS.EAS.OffchainStorage
import Benchmarks.EAS.EAS.MappingHash
import Benchmarks.EAS.EAS.RuntimeBlocks_027

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def offchainAccounts (σ : AccountMap) (ee : ExecutionEnv) (revoker : AccountAddress) (word time : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ (offchainSlot (keyValueToWord (.address revoker)) word)
    (setLowWord (solcSlotWord σ ee (offchainSlot (keyValueToWord (.address revoker)) word)) time 64)

theorem offchainStore_accounts (evm : EVM.State) (revoker : AccountAddress) (word time : UInt256) :
    (offchainStore evm revoker word time).accountMap = offchainAccounts evm.accountMap evm.executionEnv revoker word time := by
  rw [offchainStore, storageStore_accountMap, storageLoad_eq_solcSlotWord]
  rfl

theorem offchainWord_solc (evm : EVM.State) (revoker : AccountAddress) (word : UInt256) :
    offchainWord evm revoker word = UInt256.land
      (solcSlotWord evm.accountMap evm.executionEnv (offchainSlot (keyValueToWord (.address revoker)) word)) easUint64Mask := by
  rw [offchainWord, storageLoad_eq_solcSlotWord]

theorem offchainAddress_clean (revoker : AccountAddress) :
    UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975)
      (keyValueToWord (.address revoker)) = keyValueToWord (.address revoker) := by
  rw [keyValueToWord_address]
  exact solcAddrMask_clean_left (addressWord_val_canonical revoker)

def offchainMemory (revoker : AccountAddress) (word : UInt256) (mem : ByteArray) : ByteArray :=
  twoWordHashMem word (solcMappingSlot ⟨3⟩ (keyValueToWord (.address revoker)))
    (twoWordHashMem (keyValueToWord (.address revoker)) ⟨3⟩ mem)

theorem easOffchain_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {revoker : AccountAddress} {word time ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 9 ≤ 1024)
    (hz : UInt256.land (solcSlotWord σ ee (offchainSlot (keyValueToWord (.address revoker)) word)) easUint64Mask = ⟨0⟩)
    (hperm : ee.perm = true)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7001⟩
      (keyValueToWord (.address revoker) :: word :: time :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret R
      (twoWordHashMem word (solcMappingSlot ⟨3⟩ (keyValueToWord (.address revoker)))
        (offchainMemory revoker word mem)) aw' rdata (offchainAccounts σ ee revoker word time) k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := easBlocks.eas_block_7001_fallthrough_packed (immWords := wordsOf (immStore v))
    (x0 := keyValueToWord (.address revoker)) (x1 := word) (x2 := time) (R := ret :: R) (mem := mem)
    (by simp only [List.length_cons]; omega)
    (by simpa only [offchainAddress_clean, mappingHash] using hz) rd
  simp only [easBlocks.eas_block_7001_fallthrough_stack, easBlocks.eas_block_7001_fallthrough_memory,
    offchainAddress_clean, mappingHash] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := easBlocks.eas_block_7068_packed (immWords := wordsOf (immStore v))
    hstack hperm hvalid rd1
  simp only [mappingHash, easBlocks.eas_block_7068_stack] at rd2
  refine ⟨aw2, k2, C2, ?_⟩
  unfold offchainAccounts
  rw [setLowWord_eq]
  exact rd2

theorem easOffchain_revert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {revoker : AccountAddress} {word time : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 7 ≤ 1024)
    (hz : UInt256.land (solcSlotWord σ ee (offchainSlot (keyValueToWord (.address revoker)) word)) easUint64Mask ≠ ⟨0⟩)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7001⟩
      (keyValueToWord (.address revoker) :: word :: time :: R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, rd1⟩ := easBlocks.eas_block_7001_taken_packed (immWords := wordsOf (immStore v))
    hstack (by simpa only [offchainAddress_clean, mappingHash] using hz)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  exact easBlocks.eas_block_7172 (immWords := wordsOf (immStore v))
    (by simp only [easBlocks.eas_block_7001_taken_stack, List.length_cons]; omega) rd1

/-- Stop the write routine at SSTORE when the execution is static. -/
theorem easOffchain_store_static {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 9 ≤ 1024) (hperm : ee.perm = false)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7068⟩ (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata σ k C) :
    RDstatic fork (deployedRuntime v) g s0 := by
  let r0 := rd
  have r1 := r0.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7068⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7077⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup4 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7078⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 0) (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7079⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMstore r4 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7081⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7082⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7084⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7085⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 0) (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7087⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7089⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup3 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7090⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup3 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7091⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.and (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7092⟩ : UInt256), UInt8.ofNat 22, .AND, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039439137263839420088320) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7093⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039439137263839420088320), 32), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup3 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7126⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r16⟩ := RD.sload r15 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7127⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.and (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7128⟩ : UInt256), UInt8.ofNat 22, .AND, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.or (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7129⟩ : UInt256), UInt8.ofNat 23, .OR, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.swap1 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7130⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r19 hperm
    (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨7131⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64))
    (by evm_ov)

theorem easOffchain_static {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {revoker : AccountAddress} {word time ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 9 ≤ 1024)
    (hz : UInt256.land (solcSlotWord σ ee (offchainSlot (keyValueToWord (.address revoker)) word)) easUint64Mask = ⟨0⟩)
    (hperm : ee.perm = false)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7001⟩
      (keyValueToWord (.address revoker) :: word :: time :: ret :: R) mem aw rdata σ k C) :
    RDstatic fork (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, rd1⟩ := easBlocks.eas_block_7001_fallthrough_packed (immWords := wordsOf (immStore v))
    (x0 := keyValueToWord (.address revoker)) (x1 := word) (x2 := time) (R := ret :: R) (mem := mem)
    (by simp only [List.length_cons]; omega)
    (by simpa only [offchainAddress_clean, mappingHash] using hz) rd
  exact easOffchain_store_static v hstack hperm rd1

end Benchmarks.EAS.EAS
