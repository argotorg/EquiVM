import Benchmarks.Midnight.TakeEventLog
import Benchmarks.Midnight.TakeEventPrepare
import Benchmarks.Midnight.AllocationFunding
import Benchmarks.Midnight.AllocationArithmetic

/-! The complete trade event trace, ending at the transient-lock exchange. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeEventTrace {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata ratifierData : ByteArray}
    {aw root encodedPtr encodedDataPtr decrease increase ratifierPtr id seller : UInt256}
    {sellerCallback payer buyerCallback : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hi : increase.toNat < 2^128) (hd : decrease.toNat < 2^128)
    (hroot : root.toNat + 128 < 2^64) (hlo : 576 ≤ root.toNat) (hm : 576 ≤ mem.size)
    (hrat : MemoryByteString mem ratifierPtr ratifierData)
    (hratBelow : ratifierPtr.toNat + 32 + paddedSize ratifierData.size ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (hseller : memLoad (UInt256.ofNat 448) mem = seller)
    (hcanon : seller.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨12838⟩
      ([encodedPtr, encodedDataPtr, decrease, increase, ratifierPtr,
        sellerCallback, payer, buyerCallback] ++ R) mem aw rdata σ k C) :
    ∃ eventMem aw' k' C', MemoryPrefix mem eventMem root.toNat ∧
      MemoryFunding (credit + 3 * ((ratifierData.size + 31) / 32))
        (dynamicLockMemory eventMem root id seller) aw' C' ∧
      RD midnightBytecode I g s0 ⟨13223⟩ ([root, sellerCallback, payer, buyerCallback] ++ R)
        (dynamicLockMemory eventMem root id seller) aw' rdata σ k' C' := by
  have hbound : root.toNat + 480 < UInt256.size := by change _ < 2^256; omega
  have h480 : (root + UInt256.ofNat 480).toNat = root.toNat + 480 :=
    uadd_word_ofNat_toNat _ _ hbound
  simp only [List.cons_append, List.nil_append] at rd
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightTakeEventPrepare
    (R := [sellerCallback, payer, buyerCallback] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by omega) (by omega) ha rd
  simp only [midnightBlocks.midnight_block_12838_fallthrough_stack] at rd1
  obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightTakeEventHead
    (R := [sellerCallback, payer, buyerCallback] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by omega) hfree ha1 rd1
  let group := memLoad (memLoad (UInt256.ofNat 384) mem + UInt256.ofNat 192) mem
  let ratifier := UInt256.land
    (memLoad (memLoad (UInt256.ofNat 384) mem + UInt256.ofNat 320) mem) solcAddrMask
  let buy := UInt256.isZero (UInt256.isZero
    (memLoad (memLoad (UInt256.ofNat 384) mem + UInt256.ofNat 32) mem))
  let hash := keccakWord encodedDataPtr (memLoad encodedPtr mem) mem
  let headMem := takeEventHeadMemory mem root (UInt256.ofNat I.source.val) hash buy group ratifier
  have hp2 : MemoryPrefix mem headMem root.toNat := takeEventHeadMemory_prefix ..
  have hr2 := hrat.preserve hp2 hratBelow
  change MemoryFunding credit headMem aw2 C2 at ha2
  have hlen := hrat.length
  have hpad := nat_le_paddedSize ratifierData.size
  obtain ⟨aw3, k3, C3, ha3, rd3⟩ := midnightMemoryBytesEncoder_funded
    (R := [UInt256.sub increase decrease,
      UInt256.land (memLoad (memLoad (UInt256.ofNat 384) mem + UInt256.ofNat 64) mem) solcAddrMask,
      root, sellerCallback, payer, buyerCallback] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    hlen (by have hb := hrat.bound; omega)
    (by rw [h480]; change _ < 2^256; omega) hr2.header (by jump_dest) ha2 rd2
  let bytesMem := memoryBytesEncodeMemory headMem ratifierPtr.toNat
    (root + UInt256.ofNat 480).toNat ratifierData.size
  have hsrc : ratifierPtr.toNat + 32 + ratifierData.size ≤ headMem.size := by
    have hs := hr2.size
    omega
  have hp3 : MemoryPrefix headMem bytesMem root.toNat :=
    memoryBytesEncodeMemory_prefix _ _ _ _ _ hsrc (by rw [h480]; omega)
  have hfree3 : memLoad (UInt256.ofNat 64) bytesMem = root := by
    rw [memoryBytesEncodeMemory_load_before _ _ _ _ (UInt256.ofNat 64) hsrc
      (by change 96 ≤ headMem.size; have hh := hp2.size; omega)
      (by rw [h480]; change 96 ≤ root.toNat + 480; omega)]
    exact (takeEventHeadMemory_load mem root _ _ _ _ _ (UInt256.ofNat 64)
      (by change 96 ≤ mem.size; omega) (by change 96 ≤ root.toNat; omega)).trans hfree
  obtain ⟨aw4, k4, C4, ha4, rd4⟩ := midnightTakeEventTail
    (R := [sellerCallback, payer, buyerCallback] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by omega) (by omega) (by
      change 160 ≤ bytesMem.size
      have h2 := hp2.size; have h3 := hp3.size; omega) ha3 rd3
  let tailMem := takeEventTailMemory bytesMem I root (UInt256.sub increase decrease)
  have hp4 : MemoryPrefix bytesMem tailMem root.toNat :=
    takeEventTailMemory_prefix _ _ _ _ (by omega)
  have hp14 := (hp2.trans hp3).trans hp4
  have hfree4 : memLoad (UInt256.ofNat 64) tailMem = root :=
    (takeEventTailMemory_load bytesMem I root _ (UInt256.ofNat 64) (by omega)
      (by change 96 ≤ bytesMem.size; have hh := (hp2.trans hp3).size; omega)
      (by change 96 ≤ root.toNat; omega)).trans hfree3
  have hid4 : memLoad (UInt256.ofNat 512) tailMem = id :=
    (hp14.load _ (by decide) (by change 544 ≤ root.toNat; omega)
      (by change 544 ≤ mem.size; omega)).trans hid
  have hs4 : memLoad (UInt256.ofNat 448) tailMem = seller :=
    (hp14.load _ (by decide) (by change 480 ≤ root.toNat; omega)
      (by change 480 ≤ mem.size; omega)).trans hseller
  obtain ⟨aw5, k5, C5, ha5, rd5⟩ := midnightTakeEventLog (R := buyerCallback :: R)
    (by simp only [List.length_cons]; omega) hbound hlo
    (by change 576 ≤ tailMem.size; have hh := hp14.size; omega)
    hfree4 hid4 hs4 hcanon hperm ha4 rd4
  let eventMem := takeEventLogMemory tailMem root
    (UInt256.land (memLoad (UInt256.ofNat 128) bytesMem) solcAddrMask) payer
  have hp5 : MemoryPrefix tailMem eventMem root.toNat := takeEventLogMemory_prefix _ _ _ _ hbound
  obtain ⟨aw6, k6, C6, ha6, rd6⟩ := midnightAllocate_funded
    (R := [root, sellerCallback, payer, buyerCallback] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (allocationCheck_bounded (ptr := root) (size := UInt256.ofNat 128)
      (by decide) hroot) (by jump_dest) ha5 rd5
  have hend : allocationEnd root (UInt256.ofNat 128) = root + UInt256.ofNat 128 := by
    unfold allocationEnd
    congr 1
  rw [hend] at ha6 rd6
  exact ⟨eventMem, aw6, k6, C6, hp14.trans hp5, ha6, rd6⟩

end Benchmarks.Midnight
