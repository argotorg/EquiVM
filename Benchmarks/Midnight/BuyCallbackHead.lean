import Benchmarks.Midnight.BuyCallbackLayout
import Benchmarks.Midnight.RuntimeBlocks_051

/-! The buyer callback selector and the handoff to the market encoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightBuyCallbackHead {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root market id callback ptr outputSize ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 15 ≤ 1024)
    (hb : root.toNat + 68 < UInt256.size) (hlo : 544 ≤ root.toNat) (hm : 544 ≤ mem.size)
    (hmarket : memLoad (memLoad (UInt256.ofNat 384) mem) mem = market)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨13805⟩
      ([callback, ptr, outputSize, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (buyCallbackHeaderMemory mem root.toNat id) aw' C' ∧
      RD midnightBytecode I g s0 ⟨19181⟩
        ([market, root + UInt256.ofNat 228, ⟨13868⟩, ptr, ret, root, solcAddrMask,
          ⟨0⟩, root, callback, root, outputSize, root] ++ R)
        (buyCallbackHeaderMemory mem root.toNat id) aw' rdata σ k' C' := by
  have hsel : UInt256.shiftLeft (UInt256.ofNat 470529357) (UInt256.ofNat 224) =
      UInt256.ofNat (470529357 * 2^224) := by decide +kernel
  have hid' : memLoad (UInt256.ofNat 512)
      ((UInt256.ofNat (470529357 * 2^224)).toByteArray.write 0 mem root.toNat 32) = id := by
    change memLoad (UInt256.ofNat 512)
      (writeWord mem root.toNat (UInt256.ofNat (470529357 * 2^224))) = id
    rw [memLoad_writeWord_preserved _ _ (UInt256.ofNat 512) _ hm (Or.inl hlo), hid]
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_13805 hstack (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_13805_stack,
    midnightBlocks.midnight_block_13805_memory, hmarket, hfree, hsel,
    hid', addressMask_computed] at rd1
  have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
  simp only [uadd_word_ofNat_toNat root 4 (by omega),
    uadd_word_ofNat_toNat root 36 (by omega)] at rd1 ha1
  exact ⟨_, _, _, ha1, rd1⟩

end Benchmarks.Midnight
