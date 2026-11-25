import Benchmarks.Midnight.TakeReceiverGuard
import Benchmarks.Midnight.TakeAuthorizationRead

variable {fork : Ethereum.Fork}

/-! The offer maker must authorize the ratifier, with input-copy funding retained. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeRatifierMemory (mem : ByteArray) (offer : OfferData) : ByteArray :=
  twoWordHashMem (UInt256.ofNat offer.ratifier.val)
    (solcMappingSlot ⟨3⟩ (UInt256.ofNat offer.maker.val))
    (twoWordHashMem (UInt256.ofNat offer.maker.val) (UInt256.ofNat 3) mem)

theorem takeRatifierMemory_prefix (mem : ByteArray) (offer : OfferData) (limit : Nat) :
    MemoryPrefix mem (takeRatifierMemory mem offer) limit :=
  (twoWordHashMem_prefix mem _ _ limit).trans (twoWordHashMem_prefix _ _ _ limit)

theorem takeRatifierMemory_size (mem : ByteArray) (offer : OfferData) (hm : 64 ≤ mem.size) :
    (takeRatifierMemory mem offer).size = mem.size := by
  unfold takeRatifierMemory
  rw [twoWordHashMem_size_of_ge_64 _ _ (by rw [twoWordHashMem_size_of_ge_64 _ _ hm]; exact hm),
    twoWordHashMem_size_of_ge_64 _ _ hm]

theorem takeRatifierMemory_load (mem : ByteArray) (offer : OfferData) (off : UInt256)
    (hlo : 64 ≤ off.toNat) (hin : off.toNat + 32 ≤ mem.size) :
    memLoad off (takeRatifierMemory mem offer) = memLoad off mem := by
  have hs : 64 ≤ mem.size := by omega
  unfold takeRatifierMemory
  rw [memLoad_twoWordHashMem _ _ _ hlo
    (by rw [twoWordHashMem_size_of_ge_64 _ _ hs]; exact hin),
    memLoad_twoWordHashMem _ _ _ hlo hin]

set_option maxHeartbeats 800000 in
theorem midnightTakeRatifierAuthorization {credit : Nat} {I : ExecutionEnv}
    {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root : UInt256}
    {k C : Nat} {R : List UInt256} {offer : OfferData}
    (evm : State) (henv : evm.executionEnv = I)
    (hstack : R.length + 5 ≤ 1024) (hmem : 416 ≤ mem.size)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11209⟩ R mem aw rdata evm.accountMap k C) :
    (authorizationWord evm (UInt256.ofNat offer.maker.val) (UInt256.ofNat offer.ratifier.val) = ⟨0⟩ ∧
      RDrev fork midnightBytecode g s0) ∨
    (authorizationWord evm (UInt256.ofNat offer.maker.val) (UInt256.ofNat offer.ratifier.val) ≠ ⟨0⟩ ∧
      ∃ aw' k' C', MemoryFunding credit (takeRatifierMemory mem offer) aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨11276⟩ R
          (takeRatifierMemory mem offer) aw' rdata evm.accountMap k' C') := by
  subst I
  have hmaker : memLoad (UInt256.ofNat 64 + (⟨832⟩ : UInt256)) mem =
      UInt256.ofNat offer.maker.val := by
    rw [u256_add_comm]
    exact ho.words.load_offset ⟨2, by change 2 < 15; decide⟩ rfl
  let first := twoWordHashMem (UInt256.ofNat offer.maker.val) (UInt256.ofNat 3) mem
  have hroot1 : memLoad (UInt256.ofNat 384) first = ⟨832⟩ := by
    dsimp only [first]
    rw [memLoad_twoWordHashMem _ _ (UInt256.ofNat 384) (by decide) hmem, hroot]
  have ho1 := ho.preserve (twoWordHashMem_prefix mem (UInt256.ofNat offer.maker.val)
    (UInt256.ofNat 3) root.toNat)
  have hratifier : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 320) first =
      UInt256.ofNat offer.ratifier.val :=
    ho1.words.load_offset ⟨10, by change 10 < 15; decide⟩ rfl
  have hh1 : keccakWord ⟨0⟩ (UInt256.ofNat 64) first =
      solcMappingSlot ⟨3⟩ (UInt256.ofNat offer.maker.val) :=
    twoWordHashMem_mapSlot_of_ge64 _ _ (by omega)
  have hh2 : keccakWord ⟨0⟩ (UInt256.ofNat 64) (takeRatifierMemory mem offer) =
      authorizationSlot (UInt256.ofNat offer.maker.val) (UInt256.ofNat offer.ratifier.val) :=
    twoWordHashMem_mapSlot_of_ge64 _ _
      (by rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; omega)
  dsimp only [first] at hroot1 hratifier hh1
  dsimp only [takeRatifierMemory] at hh2
  let r0 := rd
  have r1 := r0.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r2 := RD.genMload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := RD.genMload r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.sub (by native_decide) (by evm_ov)
  have r13 := r12.and (by native_decide) (by evm_ov)
  have r14 := r13.push0 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r20 := RD.genMstore r19 (by native_decide) (by evm_ov)
  have r21 := RD.genKeccak256 r20 (by native_decide) (by evm_ov)
  have ha21 := memoryFundingAt (credit := credit) r21 (by memory_fund ha)
  simp only [hroot, hmaker, addressMask_computed, u256_land_comm solcAddrMask,
    solcAddrMask_clean (addressWord_canonical offer.maker),
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at r21 ha21
  rw [hh1] at r21
  have r22 := r21.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r25 := r24.shl (by native_decide) (by evm_ov)
  have r26 := r25.sub (by native_decide) (by evm_ov)
  have r27 := r26.dup1 (by native_decide) (by evm_ov)
  have r28 := r27.push2 (UInt256.ofNat 320) (by native_decide) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 384) (by native_decide) (by evm_ov)
  have r30 := RD.genMload r29 (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := RD.genMload r31 (by native_decide) (by evm_ov)
  have r33 := r32.and (by native_decide) (by evm_ov)
  have r34 := r33.and (by native_decide) (by evm_ov)
  have r35 := r34.push0 (by native_decide) (by evm_ov)
  have r36 := RD.genMstore r35 (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r38 := RD.genMstore r37 (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r41 := r40.push0 (by native_decide) (by evm_ov)
  have r42 := RD.genKeccak256 r41 (by native_decide) (by evm_ov)
  have ha42 := memoryFundingAt (credit := credit) r42 (by memory_fund ha21)
  simp only [hroot1, hratifier, addressMask_computed,
    solcAddrMask_clean (addressWord_canonical offer.ratifier),
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at r42 ha42
  rw [hh2] at r42
  obtain ⟨_, _, hc43, r43⟩ := RD.sloadMono r42 (by native_decide) (by evm_ov)
  have ha43 := ha42.mono hc43
  have r44 := r43.and (by native_decide) (by evm_ov)
  have r45 := r44.iszero (by native_decide) (by evm_ov)
  have r46 := r45.push2 (UInt256.ofNat 14859) (by native_decide) (by evm_ov)
  by_cases hz : authorizationWord evm (UInt256.ofNat offer.maker.val)
      (UInt256.ofNat offer.ratifier.val) = ⟨0⟩
  · have r47 := r46.jumpiT (by native_decide) (by
      change UInt256.isZero (UInt256.land
        (solcSlotWordAt (authorizationSlot (UInt256.ofNat offer.maker.val)
          (UInt256.ofNat offer.ratifier.val)) evm.accountMap evm.executionEnv) ⟨255⟩) ≠ ⟨0⟩
      change UInt256.isZero (authorizationWord evm (UInt256.ofNat offer.maker.val)
        (UInt256.ofNat offer.ratifier.val)) ≠ ⟨0⟩
      rw [hz]; decide) (by jump_dest) (by evm_ov)
    exact Or.inl ⟨hz, midnightBlocks.midnight_block_14859 (by omega) r47⟩
  · have r47 := r46.jumpiNT (by native_decide) (by
      change UInt256.isZero (authorizationWord evm (UInt256.ofNat offer.maker.val)
        (UInt256.ofNat offer.ratifier.val)) = ⟨0⟩
      exact isZero_eq_zero_of_ne hz) (by evm_ov)
    have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 11276)) r47 (by native_decide)
    exact Or.inr ⟨hz, _, _, _, by unfold takeRatifierMemory; memory_fund ha43, rFinal⟩

end Benchmarks.Midnight
