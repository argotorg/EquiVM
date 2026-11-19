import Benchmarks.Midnight.MarketCalldataPrepare
import Benchmarks.Midnight.MarketCalldataArrayHeader
import Benchmarks.Midnight.MarketCalldataArrayDecode
import Benchmarks.Midnight.MemoryDecodeBounds

/-! Complete runtime decoding of a market from ordinary-sized calldata. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMarketCalldataDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr head ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 25 ≤ 1024)
    (hsize : I.calldata.size < 2^255) (hhead : head.toNat < 2^127)
    (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨18574⟩
      (head :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C) :
    ((∀ m, decodeMarketData I.calldata head.toNat = some m →
        ¬ ptr.toNat + 288 + 160 * m.collaterals.length < 2^64) ∧ RDrev midnightBytecode g s0) ∨
    (∃ m, decodeMarketData I.calldata head.toNat = some m ∧
      ptr.toNat + 288 + 160 * m.collaterals.length < 2^64 ∧
      ∃ mem' root aw' k' C',
        root.toNat = ptr.toNat + 288 + 160 * m.collaterals.length ∧
        MarketStored mem' ptr (ptr + UInt256.ofNat 256) root m ∧
        memLoad (UInt256.ofNat 64) mem' = root ∧
        RD midnightBytecode I g s0 ret (ptr :: R) mem' aw' rdata σ k' C') := by
  have hcd : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hcheck := signedDecodeCheck (finish := UInt256.ofNat I.calldata.size) (start := head)
    (need := 256) (by rw [hcd]; exact hsize) (by omega) (by decide)
  rw [hcd] at hcheck
  by_cases hheadfit : head.toNat + 256 ≤ I.calldata.size
  · rw [decide_eq_false (by omega)] at hcheck
    have rd1 := midnightBlocks.midnight_block_18574_fallthrough (by omega) hcheck rd
    rcases midnightMarketCalldataPrepare (by omega) (by change _ < 2^256; omega)
        hptr hfree rd1 with
      ⟨hcap, hr⟩ | ⟨hnone, hr⟩ | ⟨hfit, hm, hl, hoff, aw2, k2, C2, rd2⟩
    · exact Or.inl ⟨fun _ _ ↦ by omega, hr⟩
    · exact Or.inl ⟨(fun m hm ↦ by rw [hnone] at hm; cases hm), hr⟩
    · let allocMem := writeWord mem 64 (ptr + UInt256.ofNat 256)
      let firstMem := marketFirstMemory allocMem ptr I.calldata head.toNat
      have hf2 : memLoad (UInt256.ofNat 64) firstMem = ptr + UInt256.ofNat 256 :=
        marketFirstMemory_free (memLoad_writeWord mem (UInt256.ofNat 64) _)
          (by dsimp only [allocMem]; rw [writeWord_sparse_size]; omega) hlo
      have hm2 : MemoryWords firstMem ptr.toNat (marketFirstWords I.calldata head.toNat) :=
        MemoryWords.of_writeWordArray allocMem ptr.toNat (marketFirstWords I.calldata head.toNat)
          (by change ptr.toNat + 32 * 3 < 2^256; omega) (by simp [marketFirstWords])
      rcases midnightMarketCalldataArrayHeader (by simp only [List.length_cons]; omega)
          hsize hhead hoff rd2 with
        ⟨hnone, hr⟩ | ⟨harrayhead, hn, k3, C3, rd3⟩
      · exact Or.inl ⟨(fun m hm ↦ by rw [hnone] at hm; cases hm), hr⟩
      · have hh : (head + calldataWord I.calldata (head.toNat + 96)).toNat =
            head.toNat + (calldataWord I.calldata (head.toNat + 96)).toNat := by
          rw [uadd_toNat, Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
        exact midnightMarketCalldataArrayDecode hstack hsize hhead hheadfit hlo hfit hm2 hf2
          hm hl hoff harrayhead rfl hn hh hvalid rd3
  · left
    refine ⟨?_, ?_⟩
    · intro m hm
      have hb := (decodeMarketData_success hm).1
      omega
    · rw [decide_eq_true (by omega)] at hcheck
      have rd1 := midnightBlocks.midnight_block_18574_taken (by omega)
        (by rw [hcheck]; decide) (by jump_dest) rd
      exact midnightBlocks.midnight_block_6350 (by
        simp only [midnightBlocks.midnight_block_18574_taken_stack, List.length_cons]; omega) rd1

end Benchmarks.Midnight
