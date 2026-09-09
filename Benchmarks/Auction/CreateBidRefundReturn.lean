import Benchmarks.Auction.CreateBidAfterRefund

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

def auctionRefundReturnedFree (o : ByteArray) : UInt256 :=
  ⟨352⟩ + UInt256.land (UInt256.ofNat o.size + ⟨63⟩) (UInt256.lnot ⟨31⟩)

def auctionRefundReturnedMem (mem o : ByteArray) : ByteArray :=
  o.write 0 ((UInt256.ofNat o.size).toByteArray.write 0
    ((auctionRefundReturnedFree o).toByteArray.write 0 mem 64 32) 352 32) 384 o.size

def auctionRefundReturnedAw (o : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M 12 384 o.size)

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidRefundNonemptyToFallbackExact {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner marker amount success : UInt256} {mem o : ByteArray} {k C : ℕ}
    (hfree : auctionLoadWord mem (UInt256.ofNat 12) ⟨64⟩ = ⟨352⟩)
    (hosz : o.size < UInt256.size)
    (hne : o.size ≠ 0)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4828⟩
      [success, ⟨352⟩, amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner,
        ⟨3347⟩, amount, owner, ⟨1715⟩, marker, ⟨128⟩, auctionCreateBidArgWord I,
        ⟨413⟩, auctionSelWord I]
      mem (UInt256.ofNat 12) o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      [success, amount, owner, ⟨1715⟩, marker, ⟨128⟩, auctionCreateBidArgWord I,
        ⟨413⟩, auctionSelWord I]
      (auctionRefundReturnedMem mem o) (auctionRefundReturnedAw o) o acc k' C'  := by
  let oszWord := UInt256.ofNat o.size
  let freePtr : UInt256 := ⟨352⟩
  let awFree : UInt256 := UInt256.ofNat 12
  let rounded := UInt256.land (oszWord + ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let newFree := freePtr + rounded
  let memFree := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStoreFree : UInt256 := UInt256.ofNat 12
  let memLen := (UInt256.toByteArray oszWord).write 0 memFree freePtr.toNat 32
  let awLen : UInt256 := UInt256.ofNat 12
  let dataPtr : UInt256 := ⟨384⟩
  let memCopy := o.write 0 memLen dataPtr.toNat oszWord.toNat
  let awCopy : UInt256 := UInt256.ofNat (MachineState.M awLen.toNat dataPtr.toNat oszWord.toNat)
  have hoszWord_ne : oszWord ≠ ⟨0⟩ := by
    intro hzero
    have hnat := congrArg UInt256.toNat hzero
    have hsizeZero : o.size = 0 := by
      simpa [oszWord, UInt256.toNat_ofNat_of_lt hosz] using hnat
    exact hne hsizeZero
  have heqZero : UInt256.eq oszWord ⟨0⟩ = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hoszWord_ne (uInt256_eq_one_eq heq)
  have rd4838 := evm_run rd with [
    swap4, pop, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd4844 := evm_run rd4838 with [
    push2 ⟨4874⟩,
    jumpiNT (by simpa [oszWord] using heqZero)]
  have rd4862 := evm_run rd4844 with [
    push1 ⟨64⟩,
    raw mload (Cₘ awFree - Cₘ (UInt256.ofNat 12)) freePtr awFree (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by native_decide))
      hfree (by native_decide) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore (Cₘ awStoreFree - Cₘ awFree) memFree awStoreFree (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by native_decide))
      (by rfl) (by native_decide) (by evm_ov),
    returndatasize, dup3,
    raw mstore (Cₘ awLen - Cₘ awStoreFree) memLen awLen (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by native_decide))
      (by rfl) (by native_decide) (by evm_ov),
    returndatasize, push0, push1 ⟨32⟩, dup5, add]
  have rd4863 := RD.returndatacopy (Cₘ awCopy - Cₘ awLen) memCopy awCopy rd4862
    (by native_decide)
    (by
      change 0 + oszWord.toNat ≤ o.size
      rw [show oszWord.toNat = o.size by
        simpa [oszWord] using UInt256.toNat_ofNat_of_lt hosz]
      omega)
    (fun _ haws hstks => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, dataPtr, awCopy,
        oszWord, freePtr]
      rfl)
    (by rfl) (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4879 := evm_run rd4863 with [push2 ⟨4879⟩, jump (by jump_dest)]
  have rd3347 := evm_run rd4879 with [
    jumpdest, pop, swap1, swap3, pop, pop, pop,
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa only [memCopy, memLen, memFree, newFree, freePtr, rounded, oszWord, dataPtr,
      awCopy, awLen, UInt256.toNat_ofNat_of_lt hosz, auctionRefundReturnedMem,
      auctionRefundReturnedAw, auctionRefundReturnedFree] using rd3347⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidRefundNonemptyReturnExact {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner marker amount : UInt256} {mem o : ByteArray} {k C : ℕ}
    (hfree : auctionLoadWord mem (UInt256.ofNat 12) ⟨64⟩ = ⟨352⟩)
    (hosz : o.size < UInt256.size)
    (hne : o.size ≠ 0)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4828⟩
      [⟨1⟩, ⟨352⟩, amount, ⟨30000⟩, owner, ⟨0⟩, ⟨0⟩, amount, owner,
        ⟨3347⟩, amount, owner, ⟨1715⟩, marker, ⟨128⟩, auctionCreateBidArgWord I,
        ⟨413⟩, auctionSelWord I]
      mem (UInt256.ofNat 12) o acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1715⟩
      [marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      (auctionRefundReturnedMem mem o) (auctionRefundReturnedAw o) o acc k' C'  := by
  obtain ⟨_, _, h3347⟩ := auctionCreateBidRefundNonemptyToFallbackExact hfree hosz hne rd
  have h3570 := evm_run h3347 with [
    jumpdest, push2 ⟨3570⟩, jumpiT (by native_decide) (by jump_dest)]
  exact ⟨_, _, evm_run h3570 with [jumpdest, pop, pop, jump (by jump_dest)]⟩

theorem auctionRefundReturnedMem_size {mem o : ByteArray}
    (hmem : mem.size = 384) (hne : o.size ≠ 0) :
    (auctionRefundReturnedMem mem o).size = 384 + o.size := by
  have hfree := toByteArray_write32_size_of_le mem (auctionRefundReturnedFree o) 64
    384 384 hmem (by omega) (by native_decide)
  have hlen := toByteArray_write32_size_of_le _ (UInt256.ofNat o.size) 352 384 384
    hfree (by omega) (by native_decide)
  have hcopy := write_end_size_from o
    ((UInt256.ofNat o.size).toByteArray.write 0
      ((auctionRefundReturnedFree o).toByteArray.write 0 mem 64 32) 352 32)
    0 o.size hne (by omega)
  rw [hlen] at hcopy
  exact hcopy

theorem auctionRefundReturnedMem_read224 {mem o : ByteArray}
    (hmem : mem.size = 384) (hne : o.size ≠ 0) :
    (auctionRefundReturnedMem mem o).readWithPadding 224 32 = mem.readWithPadding 224 32 := by
  have hfree := toByteArray_write32_size_of_le mem (auctionRefundReturnedFree o) 64
    384 384 hmem (by omega) (by native_decide)
  have hlen := toByteArray_write32_size_of_le _ (UInt256.ofNat o.size) 352 384 384
    hfree (by omega) (by native_decide)
  unfold auctionRefundReturnedMem
  rw [write_read_below_gen_extend o _ 384 o.size 224 hne (by omega) (by omega)
    (by native_decide)]
  rw [write32_read_below _ _ 352 224 (by rw [toByteArray_size]) (by omega)
    (by native_decide)]
  exact write32_read_above _ mem 64 224 (by rw [toByteArray_size]) (by omega)
    (by native_decide) (by omega)

theorem auctionRefundReturnedAw_bounds {o : ByteArray} (hsize : o.size < 2 ^ 138) :
    12 ≤ (auctionRefundReturnedAw o).toNat ∧
      (auctionRefundReturnedAw o).toNat < 2 ^ 251 := by
  have hbound : 12 ≤ MachineState.M 12 384 o.size ∧
      MachineState.M 12 384 o.size < 2 ^ 251 := by
    unfold MachineState.M
    split <;> omega
  unfold auctionRefundReturnedAw
  rw [UInt256.toNat_ofNat_of_lt (Nat.lt_trans hbound.2 (by native_decide))]
  exact hbound

theorem auctionRefundReturnedMem_load224 {mem o : ByteArray} {finish : UInt256}
    (hmem : mem.size = 384) (hread : mem.readWithPadding 224 32 = finish.toByteArray)
    (hne : o.size ≠ 0) (hsize : o.size < 2 ^ 138) :
    auctionLoadWord (auctionRefundReturnedMem mem o) (auctionRefundReturnedAw o) ⟨224⟩ =
      finish := by
  apply mloadWordValue_of_readWithPadding
  · rw [auctionRefundReturnedMem_size hmem hne]
    change 224 < 384 + o.size
    omega
  · have hb := auctionRefundReturnedAw_bounds hsize
    intro hle
    have hm : (auctionRefundReturnedAw o * ⟨32⟩).toNat =
        (auctionRefundReturnedAw o).toNat * 32 := by
      change (UInt256.mul (auctionRefundReturnedAw o) ⟨32⟩).toNat = _
      rw [u256_mul_toNat]
      exact Nat.mod_eq_of_lt (by change _ * 32 < UInt256.size; unfold UInt256.size; omega)
    have hh : (auctionRefundReturnedAw o * ⟨32⟩).toNat ≤ 224 := hle
    rw [hm] at hh
    omega
  · exact (auctionRefundReturnedMem_read224 hmem hne).trans hread

end Auction
