import Solm.Benchmarks.Auction.NounTransferPrefix
import Solm.Benchmarks.Auction.BurnCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

noncomputable def nounTransferData (I : ExecutionEnv) (bidder nounId : UInt256) : ByteArray :=
  transferFromSelector ++ (contractAddressWord I).toByteArray ++
    (UInt256.land bidder solcAddrMask).toByteArray ++ nounId.toByteArray

theorem nounTransferData_size (I : ExecutionEnv) (bidder nounId : UInt256) :
    (nounTransferData I bidder nounId).size = 100 := by
  simp only [nounTransferData, ByteArray.size_append, toByteArray_size]
  rfl

theorem nounTransferData_encode (I : ExecutionEnv) (bidder nounId : UInt256) :
    auctionConfig.externalABI.encode? "transferFrom"
      [.address I.codeOwner, .address (AccountAddress.ofNat (UInt256.land bidder
        solcAddrMask).toNat),
        .int (Int.ofNat nounId.toNat)] = some (nounTransferData I bidder nounId) := by
  have hself : encodeABIValue? addr (.address I.codeOwner) =
      some (EVM.Word.toBytesBE (contractAddressWord I)) := by
    simp only [addr, encodeABIValue?, encodeABIWord?, bind, Option.bind]
    rfl
  have ha : encodeABIValue? addr
      (.address (AccountAddress.ofNat (UInt256.land bidder solcAddrMask).toNat)) =
      some (EVM.Word.toBytesBE (UInt256.land bidder solcAddrMask)) :=
    scalarValueEncoding (by native_decide) rfl (solcAddressReturnEncoding (addrTy := addr) rfl
      bidder)
  have hu : encodeABIValue? uint256 (.int (Int.ofNat nounId.toNat)) =
      some (EVM.Word.toBytesBE nounId) :=
    scalarValueEncoding (by native_decide) rfl (uint256ReturnEncoding nounId)
  change encodeCallWithSelector? transferFromSelector [addr, addr, uint256] _ = _
  simp only [encodeCallWithSelector?, encodeABIValues?,
    show abiTupleHeadSize? [addr, addr, uint256] = some 96 from by native_decide,
    encodeABIValuesFrom?, hself, ha, hu, show isDynamicABIType addr = false from rfl,
    show isDynamicABIType uint256 = false from rfl, bind, Option.bind, if_false,
    Bool.false_eq_true, List.nil_append, List.append_nil, list_toByteArray_append,
    word_toBytesBE_toByteArray_eq_toByteArray, nounTransferData, ByteArray.append_assoc]

def nounTransferCallWords (aw ptr : UInt256) : UInt256 :=
  expandedWords (callWords3 aw ptr) ptr ⟨100⟩

theorem nounTransferCall_heap {mem aw ptr} (hm : HeapMemory mem aw ptr)
    (I : ExecutionEnv) (bidder nounId : UInt256) (hb : ptr.toNat + 100 ≤ 2 ^ 200) :
    HeapMemory
      (callMem3 mem ptr transferFromWord (contractAddressWord I) (UInt256.land bidder solcAddrMask)
        nounId) (nounTransferCallWords aw ptr) ptr := by
  have hh := callMem3_heap hm transferFromWord (contractAddressWord I)
    (UInt256.land bidder solcAddrMask) nounId hb
  exact ⟨hh.size, hh.free, hh.lower, hh.gap, activeWords_expand hh.active hb⟩

theorem nounTransferCall {I g s0 snap nounId bidder ret R mem aw ptr rdata cA σ k C evm}
    (h : RD auctionBytecode I g s0 ⟨4536⟩ (snap :: ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 100 ≤ 2 ^ 200)
    (hn : loadedWord mem aw snap = nounId) (ha : expandedWords aw snap ⟨32⟩ = aw)
    (hbid : loadedWord mem aw (snap + ⟨128⟩) = bidder)
    (hab : expandedWords aw (snap + ⟨128⟩) ⟨32⟩ = aw)
    (hyes : extCodeSizeWord σ (nounsWord σ I) ≠ ⟨0⟩) (hov : R.length + 17 ≤ 1024) :
    ∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 (nounsWord σ I)) 0
        (nounTransferData I bidder nounId) (z, evm', out) ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ⟨4628⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (ptr + ⟨100⟩) :: ⟨0x23b872dd⟩ ::
          nounsWord σ I :: snap :: ret :: R)
        (callMem3 mem ptr transferFromWord (contractAddressWord I) (UInt256.land bidder
          solcAddrMask)
          nounId) (nounTransferCallWords aw ptr) out (cA', σ') k' C' ∧ out.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd4627⟩ := nounTransferCallPrefix h hm hb hn ha hbid hab hyes hov
  have hcd :
      (callMem3 mem ptr transferFromWord (contractAddressWord I) (UInt256.land bidder solcAddrMask)
        nounId).readWithPadding ptr.toNat 100 = nounTransferData I bidder nounId := by
    rw [callMem3_read hm, transferFromWord_prefix]
    rfl
  obtain ⟨evm', cA', σ', z, out, _, _, hc, hs', rd4628, ho⟩ :=
    callBridge rd4627 hs hperm (by native_decide) hcd
      (by rw [nounTransferData_size]; decide) (by evm_ov)
  rw [callOutputMem_zero] at rd4628
  exact ⟨evm', cA', σ', z, out, _, _, hc, hs', rd4628, ho⟩

theorem nounTransferAfterSuccess {I g s0 snap ret R mem aw ptr out acc k C target}
    (h : RD auctionBytecode I g s0 ⟨4628⟩
      (⟨1⟩ :: (ptr + ⟨100⟩) :: ⟨0x23b872dd⟩ :: target :: snap :: ret :: R)
      mem aw out acc k C) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨4647⟩ (snap :: ret :: R) mem aw out acc k' C' := by
  exact ⟨_, _, evm_run h with [iszero, dup1, iszero, push2 ⟨4642⟩,
    jumpiT (by decide) (by jump_dest), jumpdest, pop, pop, pop, pop]⟩

set_option synthInstance.maxSize 1024 in
theorem nounTransferAfterFailure {I g s0 snap ret R mem aw ptr out acc k C target}
    (h : RD auctionBytecode I g s0 ⟨4628⟩
      (⟨0⟩ :: (ptr + ⟨100⟩) :: ⟨0x23b872dd⟩ :: target :: snap :: ret :: R)
      mem aw out acc k C) (hov : R.length + 10 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have rd4635 := evm_run h with [iszero, dup1, iszero, push2 ⟨4642⟩, jumpiNT (by decide)]
  exact rd4635.revertData (by unfold revertDataWf; native_decide) (by evm_ov)

end Auction
