import Solm.Benchmarks.Auction.EmptyBytes
import Solm.Benchmarks.Auction.CallBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem rawEthPrefix {I g s0 amount recipient ret R mem aw ptr rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨4768⟩ (amount :: recipient :: ret :: R)
      mem aw rdata acc k C)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 64 ≤ 2 ^ 200)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨4827⟩
      (⟨30000⟩ :: UInt256.land recipient solcAddrMask :: amount :: nextEmptyPtr ptr :: ⟨0⟩ ::
        nextEmptyPtr ptr :: ⟨0⟩ :: nextEmptyPtr ptr :: amount :: ⟨30000⟩ ::
        UInt256.land recipient solcAddrMask :: ⟨0⟩ :: ⟨0⟩ :: amount :: recipient :: ret :: R)
      (emptyEncodedMem mem ptr) (emptyEncodedWords aw ptr) rdata acc k' C' := by
  have rd4773 := evm_run h with [jumpdest, push1 ⟨64⟩, dup1,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hm.load64, expandedWords64_eq hm.active] at rd4773
  have rd4777 := evm_run rd4773 with [push0, dup1, dup3,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  have rd4784 := evm_run rd4777 with [push1 ⟨32⟩, dup3, add, swap1, swap3,
    raw mstoreSymbolic (by native_decide) (by evm_ov)]
  rw [expandedWords64_eq (activeWords_expand32 hm.active (by omega))] at rd4784
  change RD _ _ _ _ ⟨4784⟩ (ptr :: ⟨0⟩ :: amount :: recipient :: ret :: R)
    (emptyHeaderMem mem ptr) (emptyHeaderWords aw ptr) _ _ _ _ at rd4784
  have rd4806 := evm_run rd4784 with [dup2, swap1, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, dup6, and, swap1, push2 ⟨30000⟩, swap1, dup6,
    swap1, push1 ⟨64⟩, raw mloadSymbolic (by native_decide) (by evm_ov)]
  have hh := emptyHeader_heap hm hb
  rw [hh.load64, expandedWords64_eq hh.active] at rd4806
  have hmask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  rw [hmask] at rd4806
  have rd6093 := evm_run rd4806 with [push2 ⟨4815⟩, swap2, swap1,
    push2 ⟨6093⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd4815⟩ := encodeEmptyBytes rd6093 (emptyHeader_zero hm hb)
    (by jump_dest) (by evm_ov)
  change RD _ _ _ _ ⟨4815⟩
    (nextEmptyPtr ptr :: amount :: ⟨30000⟩ :: UInt256.land recipient solcAddrMask ::
      ⟨0⟩ :: ⟨0⟩ :: amount :: recipient :: ret :: R)
    (emptyEncodedMem mem ptr) (emptyEncodedWords aw ptr) _ _ _ _ at rd4815
  have he := emptyEncoded_heap hm hb
  have rd4820 := evm_run rd4815 with [jumpdest, push0, push1 ⟨64⟩,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [he.load64, expandedWords64_eq he.active] at rd4820
  have rd4827 := evm_run rd4820 with [dup1, dup4, sub, dup2, dup6, dup9, dup9]
  rw [u256_sub_self] at rd4827
  exact ⟨_, _, rd4827⟩

theorem callOutputMem_zero (mem out : ByteArray) (off : UInt256) :
    callOutputMem mem out off ⟨0⟩ = mem := by
  unfold callOutputMem
  have hmin : min (⟨0⟩ : UInt256) (UInt256.ofNat out.size) = ⟨0⟩ := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      change (0 : Nat) ≤ _
      omega
    simp [min, hle]
  rw [hmin]
  exact byteArray_write_len_zero _ _ _ _

theorem callActiveWords_zero (aw inOff outOff : UInt256) :
    callActiveWords aw inOff ⟨0⟩ outOff ⟨0⟩ = aw := by
  exact u256_ofNat_toNat aw

theorem rawEthCall {I g s0 amount recipient ret R mem aw ptr rdata cA σ k C evm}
    (h : RD auctionBytecode I g s0 ⟨4768⟩ (amount :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 64 ≤ 2 ^ 200)
    (hov : R.length + 20 ≤ 1024) :
    ∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 (UInt256.land recipient solcAddrMask))
        (Int.ofNat amount.toNat) ByteArray.empty (z, evm', out) ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ⟨4833⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨0⟩ :: ⟨0⟩ :: amount :: recipient :: ret :: R)
        (emptyEncodedMem mem ptr) (emptyEncodedWords aw ptr) out (cA', σ') k' C' ∧
      out.size < 2 ^ 138 := by
  obtain ⟨_, _, rd4827⟩ := rawEthPrefix h hm hb hov
  obtain ⟨evm', cA', σ', z, out, _, _, hc, hs', rd4828, ho⟩ :=
    callBridge rd4827 hs hperm (by native_decide) (byteArray_readWithPadding_zero _ _)
      (by decide) (by evm_ov)
  rw [callOutputMem_zero, callActiveWords_zero] at rd4828
  have rd4833 := evm_run rd4828 with [swap4, pop, pop, pop, pop]
  exact ⟨evm', cA', σ', z, out, _, _, hc, hs', rd4833, ho⟩

end Auction
