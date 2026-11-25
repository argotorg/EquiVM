import Benchmarks.Midnight.InitMarketStorage
import Benchmarks.Midnight.MarketHeapAccess
import Benchmarks.Midnight.PositionUpdateMemory
import Benchmarks.Midnight.RuntimeBlocks_081

variable {fork : Ethereum.Fork}

/-! The first market write and the subsequent default-settlement-fee read. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def initMarketDefaultWord (evm : EVM.State) (id : UInt256) (token : AccountAddress) : UInt256 :=
  Stele.EVM.storageLoad (initMarketTick evm id) evm.executionEnv.codeOwner
    (solcMappingSlot ⟨4⟩ (UInt256.ofNat token.val))

def initMarketScratch (mem : ByteArray) (id : UInt256) (token : AccountAddress) : ByteArray :=
  twoWordHashMem (UInt256.ofNat token.val) (UInt256.ofNat 4)
    (twoWordHashMem id (UInt256.ofNat 1) mem)

theorem initMarketTickWord (old : UInt256) :
    UInt256.lor (UInt256.land old (UInt256.lnot
      (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 144))))
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 146)) =
      setUint8Offset18Word old ⟨4⟩ := rfl

theorem midnightInitMarketTick {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr limit root id ret previous count : UInt256}
    {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 9 ≤ 1024) (hm : MarketStored mem ptr arrayPtr limit m)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hperm : evm.executionEnv.perm = true)
    (rd : RD fork midnightBytecode evm.executionEnv g s0 ⟨21130⟩
      (arrayPtr :: previous :: ret :: ptr :: (ptr + UInt256.ofNat 96) :: id :: count :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD fork midnightBytecode evm.executionEnv g s0 ⟨21213⟩
      (initMarketDefaultWord evm id m.loanToken :: (root + UInt256.ofNat 32) :: root ::
        initMarketDefaultWord evm id m.loanToken :: (ptr + UInt256.ofNat 64) ::
        (solcMappingSlot ⟨1⟩ id + ⟨2⟩) :: ptr :: id :: ret :: R)
      (writeWord (initMarketScratch mem id m.loanToken) root.toNat
        (settlementFeeWord (initMarketDefaultWord evm id m.loanToken) 0))
      aw' rdata (initMarketTick evm id).accountMap k' C' := by
  have hlo := hm.lower
  have hsz := hm.words.size
  have hb := hm.words.bound
  change ptr.toNat + 32 * 8 ≤ mem.size at hsz
  change ptr.toNat + 32 * 8 < UInt256.size at hb
  have hmem : 96 ≤ mem.size := by omega
  have hp64 : (ptr + UInt256.ofNat 64).toNat = ptr.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 1) mem) =
      solcMappingSlot ⟨1⟩ id := twoWordHashMem_mapSlot_of_ge64 _ _ (by omega)
  have hloan : memLoad (ptr + UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 1) mem) =
      UInt256.ofNat m.loanToken.val := by
    rw [memLoad_twoWordHashMem _ _ _ (by rw [hp64]; omega) (by rw [hp64]; omega)]
    exact hm.loanToken
  have hclean : UInt256.land solcAddrMask (UInt256.ofNat m.loanToken.val) =
      UInt256.ofNat m.loanToken.val := by
    rw [u256_land_comm]
    exact solcAddrMask_clean (addressWord_val_canonical m.loanToken)
  have hsize1 : (twoWordHashMem id (UInt256.ofNat 1) mem).size = mem.size :=
    twoWordHashMem_size_of_ge_64 _ _ (by omega)
  have hh4 : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem (UInt256.ofNat m.loanToken.val) (UInt256.ofNat 4)
        (twoWordHashMem id (UInt256.ofNat 1) mem)) =
      solcMappingSlot ⟨4⟩ (UInt256.ofNat m.loanToken.val) :=
    twoWordHashMem_mapSlot_of_ge64 _ _ (by rw [hsize1]; omega)
  have hf : memLoad (UInt256.ofNat 64)
      (twoWordHashMem (UInt256.ofNat m.loanToken.val) (UInt256.ofNat 4)
        (twoWordHashMem id (UInt256.ofNat 1) mem)) = root := by
    rw [memLoad_twoWordHashMem _ _ _ (by decide) (by rw [hsize1]; exact hmem),
      memLoad_twoWordHashMem id (UInt256.ofNat 1) (UInt256.ofNat 64) (by decide) hmem, hfree]
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_21130_packed hstack hperm rd
  simp only [midnightBlocks.midnight_block_21130_stack,
    midnightBlocks.midnight_block_21130_memory, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
    hh1, hloan, addressMask_computed, hclean, hh4, hf, initMarketTickWord,
    u256_add_comm (UInt256.ofNat 2)] at rd1
  have hac : sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap
      (solcMappingSlot ⟨1⟩ id + ⟨2⟩) (setUint8Offset18Word (marketFeeWord evm id) ⟨4⟩) =
      (initMarketTick evm id).accountMap := by
    rw [initMarketTick, storageStore_accountMap]
  refine ⟨aw1, k1, C1, ?_⟩
  simpa only [initMarketDefaultWord, initMarketScratch, settlementFeeWord_zero,
    initMarketTick, storageStore_accountMap, marketFeeWord,
    Stele.EVM.storageLoad, State.lookupAccount, storageStore_executionEnv,
    solcSlotWordAt, solcSlotWord, Reasoning.Theory.writeWord] using rd1

theorem midnightInitMarketStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x0 x1 x2 x3 x4 x5 x6 : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hperm : I.perm = false)
    (rd : RD fork midnightBytecode I g s0 ⟨21130⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata σ k C) :
    RDstatic fork midnightBytecode g s0 := by
  have r1 := rd.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.swap4 (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r15 := r14.push0 (by native_decide) (by evm_ov)
  have r16 := RD.genKeccak256 r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r18 := r17.add (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 146) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 144) (by native_decide) (by evm_ov)
  have r24 := r23.shl (by native_decide) (by evm_ov)
  have r25 := r24.not (by native_decide) (by evm_ov)
  have r26 := r25.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r27⟩ := RD.sload r26 (by native_decide) (by evm_ov)
  have r28 := r27.and (by native_decide) (by evm_ov)
  have r29 := r28.or (by native_decide) (by evm_ov)
  have r30 := r29.dup2 (by native_decide) (by evm_ov)
  exact r30.sstoreStatic hperm (by native_decide) (by evm_ov)

end Benchmarks.Midnight
