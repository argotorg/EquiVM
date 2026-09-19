import Solm.Benchmarks.Auction.TransferPrefix
import Solm.Benchmarks.Auction.CallOutput
import Solm.Benchmarks.Auction.RevertData
import Solm.Benchmarks.Auction.ABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

noncomputable def transferData (recipient amount : UInt256) : ByteArray :=
  transferSelector ++ (UInt256.land recipient solcAddrMask).toByteArray ++ amount.toByteArray

theorem transferData_size (recipient amount : UInt256) :
    (transferData recipient amount).size = 68 := by
  simp only [transferData, ByteArray.size_append, toByteArray_size]
  rfl

theorem transferData_encode (recipient amount : UInt256) :
    auctionConfig.externalABI.encode? "transfer"
      [.address (AccountAddress.ofNat (UInt256.land recipient solcAddrMask).toNat),
        .int (Int.ofNat amount.toNat)] = some (transferData recipient amount) := by
  have ha : encodeABIValue? addr
      (.address (AccountAddress.ofNat (UInt256.land recipient solcAddrMask).toNat)) =
      some (EVM.Word.toBytesBE (UInt256.land recipient solcAddrMask)) :=
    scalarValueEncoding (by native_decide) rfl (solcAddressReturnEncoding (addrTy := addr) rfl
      recipient)
  have hu : encodeABIValue? uint256 (.int (Int.ofNat amount.toNat)) =
      some (EVM.Word.toBytesBE amount) :=
    scalarValueEncoding (by native_decide) rfl (uint256ReturnEncoding amount)
  change encodeCallWithSelector? transferSelector [addr, uint256] _ = _
  simp only [encodeCallWithSelector?, encodeABIValues?,
    show abiTupleHeadSize? [addr, uint256] = some 64 from by native_decide,
    encodeABIValuesFrom?, ha, hu, show isDynamicABIType addr = false from rfl,
    show isDynamicABIType uint256 = false from rfl, bind, Option.bind, if_false,
    Bool.false_eq_true, List.nil_append, List.append_nil, list_toByteArray_append,
    word_toBytesBE_toByteArray_eq_toByteArray, transferData, ByteArray.append_assoc]

noncomputable def transferCallMem (mem out : ByteArray) (ptr recipient amount : UInt256) :
  ByteArray :=
  callOutputMem (callMem2 mem ptr transferWord (UInt256.land recipient solcAddrMask) amount)
    out ptr ⟨32⟩

def transferCallWords (aw ptr : UInt256) : UInt256 :=
  callActiveWords (callWords2 aw ptr) ptr ⟨68⟩ ptr ⟨32⟩

theorem transferCall {I g s0 amount recipient ret oldTarget R mem aw ptr rdata cA σ k C evm}
    (h : RD auctionBytecode I g s0 ⟨3449⟩
      (amount :: ⟨0xd0e30db0⟩ :: oldTarget :: amount :: recipient :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 68 ≤ 2 ^ 200)
    (hov : R.length + 18 ≤ 1024) :
    ∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 (wethWord σ I)) 0
        (transferData recipient amount) (z, evm', out) ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ⟨3518⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (ptr + ⟨68⟩) :: ⟨0xa9059cbb⟩ ::
          wethWord σ I :: amount :: recipient :: ret :: R)
        (transferCallMem mem out ptr recipient amount) (transferCallWords aw ptr)
        out (cA', σ') k' C' ∧ out.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd3517⟩ := transferPrefix h hm hb hov
  have hcd :
      (callMem2 mem ptr transferWord (UInt256.land recipient solcAddrMask) amount).readWithPadding
        ptr.toNat 68 = transferData recipient amount := by
    rw [callMem2_read hm, transferWord_prefix]
    rfl
  exact callBridge rd3517 hs hperm (by native_decide) hcd
    (by rw [transferData_size]; decide) (by evm_ov)

theorem transferCall_heap {mem aw ptr} (hm : HeapMemory mem aw ptr) (recipient amount : UInt256)
    (out : ByteArray) (hb : ptr.toNat + 68 ≤ 2 ^ 200) (ho : out.size < UInt256.size) :
    HeapMemory (transferCallMem mem out ptr recipient amount) (transferCallWords aw ptr) ptr := by
  have hh := callMem2_heap hm transferWord (UInt256.land recipient solcAddrMask) amount hb
  have hsz := (callMem2_sizes hm transferWord (UInt256.land recipient solcAddrMask) amount).2.2
  have hc := callOutput32_heap hh out ho (by omega)
  exact ⟨hc.size, hc.free, hc.lower, hc.gap,
    callActiveWords_active hh.active hb (by change ptr.toNat + 32 ≤ 2 ^ 200; omega)⟩

theorem transferCall_prefix {mem aw ptr} (hm : HeapMemory mem aw ptr) (recipient amount : UInt256)
    (out : ByteArray) (ho : out.size < UInt256.size) :
    MemoryPrefix mem (transferCallMem mem out ptr recipient amount) ptr.toNat := by
  have hsz := (callMem2_sizes hm transferWord (UInt256.land recipient solcAddrMask) amount).2.2
  exact (callMem2_prefix hm transferWord (UInt256.land recipient solcAddrMask) amount).trans
    (callOutput32_prefix _ out ptr ho (by omega))

theorem transferAfterSuccess {I g s0 amount recipient ret R mem aw ptr out acc k C target}
    (h : RD auctionBytecode I g s0 ⟨3518⟩
      (⟨1⟩ :: (ptr + ⟨68⟩) :: ⟨0xa9059cbb⟩ :: target :: amount :: recipient :: ret :: R)
      mem aw out acc k C)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨3537⟩ (amount :: recipient :: ret :: R)
      mem aw out acc k' C' := by
  exact ⟨_, _, evm_run h with [iszero, dup1, iszero, push2 ⟨3532⟩,
    jumpiT (by decide) (by jump_dest), jumpdest, pop, pop, pop, pop]⟩

set_option synthInstance.maxSize 1024 in
theorem transferAfterFailure {I g s0 amount recipient ret R mem aw ptr out acc k C target}
    (h : RD auctionBytecode I g s0 ⟨3518⟩
      (⟨0⟩ :: (ptr + ⟨68⟩) :: ⟨0xa9059cbb⟩ :: target :: amount :: recipient :: ret :: R)
      mem aw out acc k C)
    (hov : R.length + 11 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have rd3525 := evm_run h with [iszero, dup1, iszero, push2 ⟨3532⟩, jumpiNT (by decide)]
  exact rd3525.revertData (by unfold revertDataWf; native_decide) (by evm_ov)

end Auction
