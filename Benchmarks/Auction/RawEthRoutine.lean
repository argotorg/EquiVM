import Benchmarks.Auction.RawEthPrefix
import Benchmarks.Auction.RawEthReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def rawEthPtr (ptr : UInt256) (out : ByteArray) : UInt256 :=
  rawReturnPtr (nextEmptyPtr ptr) out

def rawEthMem (mem out : ByteArray) (ptr : UInt256) : ByteArray :=
  rawReturnMem (emptyEncodedMem mem ptr) out (nextEmptyPtr ptr)

def rawEthWords (aw ptr : UInt256) (out : ByteArray) : UInt256 :=
  rawReturnWords (emptyEncodedWords aw ptr) (nextEmptyPtr ptr) out

/-- The 30,000-gas ETH call at 4768, including allocation and all return-data branches. -/
theorem rawEthRoutine {I g s0 amount recipient ret R mem aw ptr rdata σ k C evm}
    (h : RD auctionBytecode I g s0 ⟨4768⟩ (amount :: recipient :: ret :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 2 ^ 139 ≤ 2 ^ 200)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 20 ≤ 1024) :
    ∃ (evm' : EVM.State) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 (UInt256.land recipient solcAddrMask))
        (Int.ofNat amount.toNat) ByteArray.empty (z, evm', out) ∧
      SourceState s0 I σ' evm' ∧
      RD auctionBytecode I g s0 ret ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (rawEthMem mem out ptr) (rawEthWords aw ptr out) out σ' k' C' ∧
      HeapMemory (rawEthMem mem out ptr) (rawEthWords aw ptr out) (rawEthPtr ptr out) ∧
      MemoryPrefix mem (rawEthMem mem out ptr) ptr.toNat ∧
      out.size < 2 ^ 138 ∧ ptr.toNat ≤ (rawEthPtr ptr out).toNat ∧
      (rawEthPtr ptr out).toNat ≤ ptr.toNat + 2 ^ 139 := by
  have h64 : ptr.toNat + 64 ≤ 2 ^ 200 := by omega
  obtain ⟨evm', σ', z, out, _, _, hc, hs', rd4833, ho⟩ :=
    rawEthCall h hs hperm hm h64 hov
  have hp := nextEmptyPtr_toNat h64
  have he := emptyEncoded_heap hm h64
  have hb' : (nextEmptyPtr ptr).toNat + out.size + 63 ≤ 2 ^ 200 := by omega
  obtain ⟨_, _, rdret⟩ := rawEthAfter rd4833 he hb' hret (by omega)
  have hheap := rawReturn_heap he out hb'
  have hprefix := (emptyEncoded_prefix hm h64).trans
    ((rawReturn_prefix he out).mono (by omega))
  have hptr := rawReturnPtr_bounds hb'
  refine ⟨evm', σ', z, out, _, _, hc, hs', rdret, hheap, hprefix, ho, ?_, ?_⟩
  · change ptr.toNat ≤ (rawReturnPtr (nextEmptyPtr ptr) out).toNat
    omega
  · change (rawReturnPtr (nextEmptyPtr ptr) out).toNat ≤ ptr.toNat + 2 ^ 139
    omega

end Auction
