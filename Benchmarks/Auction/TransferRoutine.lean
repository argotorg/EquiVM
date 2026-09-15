import Benchmarks.Auction.TransferCall
import Benchmarks.Auction.TransferReturn
import Benchmarks.Auction.ReturnABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

noncomputable def transferFinalMem (mem out : ByteArray) (ptr recipient amount : UInt256) :
  ByteArray :=
  returnReserveMem (transferCallMem mem out ptr recipient amount) ptr out.size

def transferFinalWords (aw ptr : UInt256) : UInt256 :=
  expandedWords (transferCallWords aw ptr) ptr ⟨32⟩

/-- WETH's raw transfer call, its required success bit, and its strict ABI bool decoder. -/
theorem transferRoutine {I g s0 amount recipient ret oldTarget R mem aw ptr rdata cA σ k C evm}
    (h : RD auctionBytecode I g s0 ⟨3449⟩
      (amount :: ⟨0xd0e30db0⟩ :: oldTarget :: amount :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 2 ^ 139 ≤ 2 ^ 200)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 18 ≤ 1024) :
    ∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray),
      callViaEVM evm (AccountAddress.ofUInt256 (wethWord σ I)) 0
        (transferData recipient amount) (z, evm', out) ∧
      SourceState s0 I cA' σ' evm' ∧ out.size < 2 ^ 138 ∧
      ((z = true ∧ BoolReturnValid out ∧
          (∃ k' C', RD auctionBytecode I g s0 ret R
            (transferFinalMem mem out ptr recipient amount) (transferFinalWords aw ptr)
            out (cA', σ') k' C') ∧
          MemoryCursor (transferFinalMem mem out ptr recipient amount) (transferFinalWords aw ptr)
            (returnReservePtr ptr out.size) ∧
          MemoryPrefix mem (transferFinalMem mem out ptr recipient amount) ptr.toNat ∧
          ptr.toNat ≤ (returnReservePtr ptr out.size).toNat ∧
          (returnReservePtr ptr out.size).toNat ≤ ptr.toNat + 2 ^ 139) ∨
        ((z = false ∨ ¬ BoolReturnValid out) ∧ RDrev auctionBytecode g s0)) := by
  have hb68 : ptr.toNat + 68 ≤ 2 ^ 200 := by omega
  obtain ⟨evm', cA', σ', z, out, _, _, hc, hs', rd3518, ho⟩ :=
    transferCall h hs hperm hm hb68 hov
  refine ⟨evm', cA', σ', z, out, hc, hs', ho, ?_⟩
  cases z with
  | false =>
    exact Or.inr ⟨Or.inl rfl, transferAfterFailure rd3518 (by omega)⟩
  | true =>
    obtain ⟨_, _, rd3537⟩ := transferAfterSuccess rd3518 (by omega)
    have hou : out.size < UInt256.size := by change out.size < 2 ^ 256; omega
    have hohi : out.size < 2 ^ 255 := by omega
    have hcall := transferCall_heap hm recipient amount out hb68 hou
    by_cases hlen : 32 ≤ out.size
    · have hsbuf :=
        (callMem2_sizes hm transferWord (UInt256.land recipient solcAddrMask) amount).2.2
      have hinbuf : ptr.toNat + 32 ≤
          (callMem2 mem ptr transferWord (UInt256.land recipient solcAddrMask) amount).size := by
        omega
      have hcopysz := callOutput32_size
        (callMem2 mem ptr transferWord (UInt256.land recipient solcAddrMask) amount) out ptr hou
          hinbuf
      have hin : ptr.toNat + 32 ≤ (transferCallMem mem out ptr recipient amount).size := by
        unfold transferCallMem
        rw [hcopysz]
        exact hinbuf
      have hread : (transferCallMem mem out ptr recipient amount).readWithPadding ptr.toNat 32 =
          (calldataWord out 0).toByteArray :=
        callOutput32_read_word _ out ptr hou hlen (by omega)
      have hmem := callMem2_heap hm transferWord (UInt256.land recipient solcAddrMask) amount hb68
      have hcover : ptr.toNat < (transferCallWords aw ptr).toNat * 32 :=
        callActiveWords_cover32 hmem.active hb68 (by omega)
      by_cases hcanon : calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩
      · have hrd := transferReturnOk rd3537 hcall.cursor hlen hohi hin hcover hread hcanon hret
          (by omega)
        have hb' : ptr.toNat + out.size + 31 ≤ 2 ^ 200 := by omega
        have hcursor := (returnReserve_cursor hcall.cursor out.size hb').expand32 ptr (by omega)
        have hprefix := (transferCall_prefix hm recipient amount out hou).trans
          (returnReserve_prefix hcall.cursor out.size)
        have hp := returnReservePtr_toNat hb'
        exact Or.inl ⟨rfl, ⟨hlen, hcanon⟩, hrd, hcursor, hprefix, by omega, by omega⟩
      · exact Or.inr ⟨Or.inr (fun hv => hcanon hv.2),
          transferReturnNoncanonical rd3537 hcall.cursor hlen hohi hin hcover hread hcanon (by
            omega)⟩
    · exact Or.inr ⟨Or.inr (fun hv => hlen hv.1),
        transferReturnShort rd3537 hcall.cursor (by omega) (by omega)⟩

end Auction
