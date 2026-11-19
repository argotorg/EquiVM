import Benchmarks.Midnight.MulticallMemory
import Benchmarks.Midnight.MemoryFunding
import Benchmarks.Midnight.RuntimeBlocks_017

/-! The calldata copy and DELEGATECALL arguments for one multicall iteration. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMulticallPrepare {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw root dp dl : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hmem : 832 ≤ mem.size) (hlower : 832 ≤ root.toNat)
    (hroot : root.toNat < 2^64) (hdl : dl.toNat < 2^64)
    (hd : dl.toNat = 0 ∨ dp.toNat + dl.toNat ≤ I.calldata.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨3662⟩ (dl :: dp :: R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C',
      MemoryFunding (credit + 67 + 3 * ((dl.toNat + 31) / 32))
        (copyZeroMemory I.calldata mem dp.toNat root.toNat dl.toNat) aw' C' ∧
      RD midnightBytecode I g s0 ⟨3692⟩
        (gasArg :: UInt256.ofNat I.codeOwner.val :: root :: dl :: ⟨0⟩ :: ⟨0⟩ :: R)
        (copyZeroMemory I.calldata mem dp.toNat root.toNat dl.toNat) aw' rdata σ k' C' := by
  have hn : (root + dl).toNat = root.toNat + dl.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
  have hz1 : memLoad (UInt256.ofNat 800)
      (I.calldata.write dp.toNat mem root.toNat dl.toNat) = ⟨0⟩ := by
    rw [copySparse_load_before_or_empty I.calldata mem dp.toNat root.toNat dl.toNat
      (UInt256.ofNat 800) hd hmem hlower, hz]
  have hz2 : memLoad (UInt256.ofNat 800)
      (copyZeroMemory I.calldata mem dp.toNat root.toNat dl.toNat) = ⟨0⟩ := by
    rw [copyZeroMemory_load_before_or_empty I.calldata mem dp.toNat root.toNat dl.toNat
      (UInt256.ofNat 800) hd hmem hlower, hz]
  have rd1 := midnightBlocks.midnight_block_3662 hstack rd
  simp only [midnightBlocks.midnight_block_3662_stack,
    midnightBlocks.midnight_block_3662_memory, hfree, hz1, word_add_sub_left] at rd1
  have ha1 := memoryFundingAt (credit := credit + 67 + 3 * ((dl.toNat + 31) / 32))
    rd1 (by memory_fund ha)
  simp only [hn] at rd1 ha1
  change MemoryFunding _ (copyZeroMemory I.calldata mem dp.toNat root.toNat dl.toNat) _ _ at ha1
  change RD _ _ _ _ _
    (_ :: UInt256.ofNat I.codeOwner.val :: root :: dl ::
      memLoad (UInt256.ofNat 800) (copyZeroMemory I.calldata mem dp.toNat root.toNat dl.toNat) ::
      memLoad (UInt256.ofNat 800) (copyZeroMemory I.calldata mem dp.toNat root.toNat dl.toNat) :: R)
    (copyZeroMemory I.calldata mem dp.toNat root.toNat dl.toNat) _ _ _ _ _ at rd1
  rw [hz2] at rd1
  exact ⟨_, _, _, _, ha1, rd1⟩

end Benchmarks.Midnight
