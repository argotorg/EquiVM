import Benchmarks.EAS.EAS.TimestampSource
import Benchmarks.EAS.EAS.MappingHash

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def timestampAccounts (σ : AccountMap) (ee : ExecutionEnv) (word time : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ (timestampSlot word)
    (setLowWord (solcSlotWord σ ee (timestampSlot word)) time 64)

theorem timestampStore_accounts (evm : EVM.State) (word time : UInt256) :
    (timestampStore evm word time).accountMap = timestampAccounts evm.accountMap evm.executionEnv word time := by
  rw [timestampStore, storageStore_accountMap, storageLoad_eq_solcSlotWord]
  rfl

theorem timestampWord_solc (evm : EVM.State) (word : UInt256) :
    timestampWord evm word = UInt256.land (solcSlotWord evm.accountMap evm.executionEnv (timestampSlot word)) easUint64Mask := by
  rw [timestampWord, storageLoad_eq_solcSlotWord]

theorem timestampHash (word : UInt256) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      ((UInt256.ofNat 2).toByteArray.write 0 (word.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
        (UInt256.ofNat 32).toNat 32) = timestampSlot word := by
  exact mappingHash word ⟨2⟩ mem

theorem easTimestamp_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {word time ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 8 ≤ 1024)
    (hz : UInt256.land (solcSlotWord σ ee (timestampSlot word)) easUint64Mask = ⟨0⟩)
    (hperm : ee.perm = true)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13315⟩ (word :: time :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret R
      (twoWordHashMem word ⟨2⟩ (twoWordHashMem word ⟨2⟩ mem)) aw' rdata (timestampAccounts σ ee word time) k' C' := by
  have hc : UInt256.land (solcSlotWord σ ee (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      ((UInt256.ofNat 2).toByteArray.write 0 (word.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
        (UInt256.ofNat 32).toNat 32))) easUint64Mask = ⟨0⟩ := by
    rw [timestampHash]
    exact hz
  obtain ⟨aw1, k1, C1, rd1⟩ := easBlocks.eas_block_13315_fallthrough_packed (immWords := wordsOf (immStore v))
    (x0 := word) (x1 := time) (R := ret :: R) (mem := mem)
    (by simp only [List.length_cons]; omega) hc rd
  change RD fork _ _ _ _ ⟨13346⟩ (time :: word :: ret :: R) (twoWordHashMem word ⟨2⟩ mem) _ _ _ _ _ at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := easBlocks.eas_block_13346_packed (immWords := wordsOf (immStore v))
    (x0 := time) (x1 := word) (x2 := ret) (R := R) (mem := twoWordHashMem word ⟨2⟩ mem) hstack hperm hvalid rd1
  simp only [timestampHash, easBlocks.eas_block_13346_stack] at rd2
  have hw : UInt256.lor
      (UInt256.land (solcSlotWord σ ee (timestampSlot word))
        (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039439137263839420088320))
      (UInt256.land time (UInt256.ofNat 18446744073709551615)) =
      setLowWord (solcSlotWord σ ee (timestampSlot word)) time 64 := by
    exact (setLowWord_eq _ _ 64).symm
  refine ⟨aw2, k2, C2, ?_⟩
  unfold timestampAccounts
  rw [← hw]
  exact rd2

theorem easTimestamp_revert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {word time : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 5 ≤ 1024)
    (hz : UInt256.land (solcSlotWord σ ee (timestampSlot word)) easUint64Mask ≠ ⟨0⟩)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13315⟩ (word :: time :: R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have hc : UInt256.land (solcSlotWord σ ee (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      ((UInt256.ofNat 2).toByteArray.write 0 (word.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
        (UInt256.ofNat 32).toNat 32))) easUint64Mask ≠ ⟨0⟩ := by
    rw [timestampHash]
    exact hz
  obtain ⟨aw1, k1, C1, rd1⟩ := easBlocks.eas_block_13315_taken_packed (immWords := wordsOf (immStore v)) hstack hc
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  exact easBlocks.eas_block_13452 (immWords := wordsOf (immStore v))
    (by simp only [easBlocks.eas_block_13315_taken_stack, List.length_cons]; omega) rd1


/-- The provided success summary requires write permission; this variant stops at its first SSTORE. -/
theorem easTimestamp_store_static {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {x0 x1 x2 : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 8 ≤ 1024) (hperm : ee.perm = false)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13346⟩ (x0 :: x1 :: x2 :: R) mem aw rdata σ k C) :
    RDstatic fork (deployedRuntime v) g s0 := by
  let r0 := rd
  have r1 := r0.pushConst (UInt256.ofNat 18446744073709551615) (width := 8) (op := .PUSH8) (by decide) (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13346⟩ : UInt256), UInt8.ofNat 103, .Push .PUSH8, some ((UInt256.ofNat 18446744073709551615), 8), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13355⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup3 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13356⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 0) (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13357⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMstore r4 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13359⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 2) (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13360⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13362⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genMstore r7 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13364⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13365⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 0) (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13367⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genKeccak256 r10 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13369⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup3 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13370⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup3 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13371⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.and (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13372⟩ : UInt256), UInt8.ofNat 22, .AND, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039439137263839420088320) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13373⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039439137263839420088320), 32), easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup3 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13406⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r17⟩ := RD.sload r16 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13407⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.and (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13408⟩ : UInt256), UInt8.ofNat 22, .AND, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.or (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13409⟩ : UInt256), UInt8.ofNat 23, .OR, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.swap1 (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13410⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r20 hperm
    (by immutable_decode(immutableLayout, easBytecode, wordsOf (immStore v), (⟨13411⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, easBlocks.immutableLayout_inBounds, easBlocks.immutableTemplate_size64))
    (by evm_ov)

theorem easTimestamp_static {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {word time ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 8 ≤ 1024)
    (hz : UInt256.land (solcSlotWord σ ee (timestampSlot word)) easUint64Mask = ⟨0⟩)
    (hperm : ee.perm = false)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13315⟩ (word :: time :: ret :: R) mem aw rdata σ k C) :
    RDstatic fork (deployedRuntime v) g s0 := by
  have hc : UInt256.land (solcSlotWord σ ee (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      ((UInt256.ofNat 2).toByteArray.write 0 (word.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
        (UInt256.ofNat 32).toNat 32))) easUint64Mask = ⟨0⟩ := by
    rw [timestampHash]
    exact hz
  obtain ⟨aw1, k1, C1, rd1⟩ := easBlocks.eas_block_13315_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hc rd
  exact easTimestamp_store_static v hstack hperm rd1

end Benchmarks.EAS.EAS
