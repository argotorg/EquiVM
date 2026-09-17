import Benchmarks.Auction.BurnPrefix
import Benchmarks.Auction.RawEthPrefix
import Benchmarks.Auction.RevertData
import Benchmarks.Auction.BytesMemory
import Benchmarks.Auction.ABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

noncomputable def burnData (nounId : UInt256) : ByteArray := burnSelector ++ nounId.toByteArray

theorem burnData_size (nounId : UInt256) : (burnData nounId).size = 36 := by
  simp only [burnData, ByteArray.size_append, toByteArray_size]
  rfl

theorem burnData_encode (nounId : UInt256) :
    auctionConfig.externalABI.encode? "burn" [.int (Int.ofNat nounId.toNat)] =
      some (burnData nounId) := by
  have he : encodeABIValue? uint256 (.int (Int.ofNat nounId.toNat)) =
      some (EVM.Word.toBytesBE nounId) :=
    scalarValueEncoding (by native_decide) rfl (uint256ReturnEncoding nounId)
  change encodeCallWithSelector? burnSelector [uint256] _ = _
  simp only [encodeCallWithSelector?, encodeABIValues?,
    show abiTupleHeadSize? [uint256] = some 32 from by native_decide,
    encodeABIValuesFrom?, he, show isDynamicABIType uint256 = false from rfl,
    bind, Option.bind, if_false, Bool.false_eq_true, List.nil_append, List.append_nil,
    word_toBytesBE_toByteArray_eq_toByteArray, burnData]

def burnCallWords (aw ptr : UInt256) : UInt256 := expandedWords (callWords1 aw ptr) ptr ⟨36⟩

theorem burnCall_heap {mem aw ptr} (hm : HeapMemory mem aw ptr) (nounId : UInt256)
    (hb : ptr.toNat + 36 ≤ 2 ^ 200) :
    HeapMemory (callMem1 mem ptr burnWord nounId) (burnCallWords aw ptr) ptr := by
  have hh := callMem1_heap hm burnWord nounId hb
  exact ⟨hh.size, hh.free, hh.lower, hh.gap, activeWords_expand hh.active hb⟩

theorem burnCall {I g s0 snap nounId ret R mem aw ptr rdata cA σ k C evm}
    (h : RD auctionBytecode I g s0 ⟨4435⟩ (snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 36 ≤ 2 ^ 200)
    (hn : loadedWord mem aw snap = nounId) (ha : expandedWords aw snap ⟨32⟩ = aw)
    (hyes : extCodeSizeWord σ (nounsWord σ I) ≠ ⟨0⟩) (hov : R.length + 16 ≤ 1024) :
    ∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 (nounsWord σ I)) 0 (burnData nounId) (z, evm', out) ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ⟨4513⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (ptr + ⟨36⟩) :: ⟨0x42966c68⟩ ::
          nounsWord σ I :: snap :: ret :: R)
        (callMem1 mem ptr burnWord nounId) (burnCallWords aw ptr) out (cA', σ') k' C' ∧
      out.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd4512⟩ := burnCallPrefix h hm hb hn ha hyes hov
  have hcd : (callMem1 mem ptr burnWord nounId).readWithPadding ptr.toNat 36 = burnData nounId := by
    rw [callMem1_read hm, burnWord_prefix]
    rfl
  obtain ⟨evm', cA', σ', z, out, _, _, hc, hs', rd4513, ho⟩ :=
    callBridge rd4512 hs hperm (by native_decide) hcd (by rw [burnData_size]; decide) (by evm_ov)
  rw [callOutputMem_zero] at rd4513
  exact ⟨evm', cA', σ', z, out, _, _, hc, hs', rd4513, ho⟩

theorem burnAfterSuccess {I g s0 snap ret R mem aw ptr out acc k C target}
    (h : RD auctionBytecode I g s0 ⟨4513⟩
      (⟨1⟩ :: (ptr + ⟨36⟩) :: ⟨0x42966c68⟩ :: target :: snap :: ret :: R)
      mem aw out acc k C) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨4647⟩ (snap :: ret :: R) mem aw out acc k' C' := by
  exact ⟨_, _, evm_run h with [iszero, dup1, iszero, push2 ⟨4527⟩,
    jumpiT (by decide) (by jump_dest), jumpdest, pop, pop, pop, pop,
    push2 ⟨4647⟩, jump (by jump_dest)]⟩

set_option synthInstance.maxSize 1024 in
theorem burnAfterFailure {I g s0 snap ret R mem aw ptr out acc k C target}
    (h : RD auctionBytecode I g s0 ⟨4513⟩
      (⟨0⟩ :: (ptr + ⟨36⟩) :: ⟨0x42966c68⟩ :: target :: snap :: ret :: R)
      mem aw out acc k C) (hov : R.length + 10 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have rd4520 := evm_run h with [iszero, dup1, iszero, push2 ⟨4527⟩, jumpiNT (by decide)]
  exact rd4520.revertData (by unfold revertDataWf; native_decide) (by evm_ov)

end Auction
