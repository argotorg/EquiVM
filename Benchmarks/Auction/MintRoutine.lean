import Benchmarks.Auction.MintCall
import Benchmarks.Auction.MintReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

noncomputable def mintFinalMem (mem out : ByteArray) (ptr : UInt256) : ByteArray :=
  returnReserveMem (mintCallMem mem out ptr) ptr out.size

def mintFinalWords (aw ptr : UInt256) : UInt256 :=
  expandedWords (mintCallWords aw ptr) ptr ⟨32⟩

theorem mintRoutine {I g s0 ret R mem aw ptr rdata cA σ k C evm}
    (h : RD auctionBytecode I g s0 ⟨3000⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 2 ^ 139 ≤ 2 ^ 200)
    (hov : R.length + 13 ≤ 1024) :
    ∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray),
      callViaEVM evm (AccountAddress.ofUInt256 (nounsWord σ I)) 0
        mintSelector (z, evm', out) ∧
      SourceState s0 I cA' σ' evm' ∧ out.size < 2 ^ 138 ∧
      ((z = true ∧ 32 ≤ out.size ∧
          (∃ k' C', RD auctionBytecode I g s0 ⟨3172⟩ (calldataWord out 0 :: ret :: R)
            (mintFinalMem mem out ptr) (mintFinalWords aw ptr) out (cA', σ') k' C') ∧
          MemoryCursor (mintFinalMem mem out ptr) (mintFinalWords aw ptr)
            (returnReservePtr ptr out.size) ∧
          MemoryPrefix mem (mintFinalMem mem out ptr) ptr.toNat ∧
          ptr.toNat ≤ (returnReservePtr ptr out.size).toNat ∧
          (returnReservePtr ptr out.size).toNat ≤ ptr.toNat + 2 ^ 139 ∧
          aw.toNat ≤ (mintFinalWords aw ptr).toNat) ∨
        (z = true ∧ out.size < 32 ∧ RDrev auctionBytecode g s0) ∨
        (z = false ∧
          (∃ k' C', RD auctionBytecode I g s0 ⟨3116⟩ (ret :: R)
            (mintCallMem mem out ptr) (mintCallWords aw ptr) out (cA', σ') k' C') ∧
          HeapMemory (mintCallMem mem out ptr) (mintCallWords aw ptr) ptr ∧
          MemoryPrefix mem (mintCallMem mem out ptr) ptr.toNat ∧
          aw.toNat ≤ (mintCallWords aw ptr).toNat)) := by
  have hb32 : ptr.toNat + 32 ≤ 2 ^ 200 := by omega
  obtain ⟨evm', cA', σ', z, out, _, _, hc, hs', rd3071, ho⟩ :=
    mintCall h hs hperm hm hb32 hov
  refine ⟨evm', cA', σ', z, out, hc, hs', ho, ?_⟩
  have hou : out.size < UInt256.size := by change out.size < 2 ^ 256; omega
  have hh := mintCall_heap hm out hb32 hou
  have hp := mintCall_prefix hm out hou
  have hg := mintCallWords_mono hm.active hb32
  cases z with
  | false => exact Or.inr (Or.inr ⟨rfl, mintAfterFailure rd3071 (by omega), hh, hp, hg⟩)
  | true =>
    by_cases hl : 32 ≤ out.size
    · have hsz := mintCallMem_size hm out hou
      have hsbuf : (selectorMem mem ptr mintWord).size = max mem.size (ptr.toNat + 32) :=
        writeWord_size _ _ _ (by have hu := lt_usize 32 (by decide); have hgap := hm.gap; omega)
      have hread : (mintCallMem mem out ptr).readWithPadding ptr.toNat 32 =
          (calldataWord out 0).toByteArray :=
        callOutput32_read_word _ out ptr hou hl (by omega)
      have hcover : ptr.toNat < (mintCallWords aw ptr).toNat * 32 :=
        callActiveWords_cover32 (activeWords_expand32 hm.active hb32)
          (show ptr.toNat + (⟨4⟩ : UInt256).toNat ≤ 2 ^ 200 by
            change ptr.toNat + 4 ≤ _; omega) hb32
      have hrd := mintReturnOk rd3071 hh.cursor hl (by omega) (by omega) hcover hread (by omega)
      have hb' : ptr.toNat + out.size + 31 ≤ 2 ^ 200 := by omega
      have hcursor := (returnReserve_cursor hh.cursor out.size hb').expand32 ptr hb32
      have hptr := returnReservePtr_toNat hb'
      have hg' := expandedWords_mono (off := ptr) (size := ⟨32⟩) hh.active hb32
      exact Or.inl ⟨rfl, hl, hrd, hcursor, hp.trans (returnReserve_prefix hh.cursor out.size),
        by omega, by omega, le_trans hg hg'⟩
    · exact Or.inr (Or.inl ⟨rfl, by omega, mintReturnShort rd3071 hh.cursor (by omega) (by omega)⟩)

end Auction
