import Benchmarks.Auction.SettleAuctionCallSetup
import Benchmarks.Auction.DynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferETHReturnNonempty
    {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner amount aw success ret : UInt256} {R : List UInt256} {mem o : ByteArray} {k C : ℕ}
    (hR : R.length ≤ 970)
    (hosz : o.size < UInt256.size)
    (hne : o.size ≠ 0)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4828⟩
      (success :: ⟨352⟩ :: amount :: ⟨30000⟩ :: owner :: ⟨0⟩ :: ⟨0⟩ :: amount :: owner ::
        ⟨3347⟩ :: amount :: owner :: ret :: R)
      mem aw o acc k C) :
    let oszWord := UInt256.ofNat o.size
    let freePtr :=
      if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
    let awFree : UInt256 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
    let rounded := UInt256.land (oszWord + ⟨63⟩) (UInt256.lnot ⟨31⟩)
    let newFree := freePtr + rounded
    let memFree := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
    let awStoreFree : UInt256 :=
      UInt256.ofNat (MachineState.M awFree.toNat (⟨64⟩ : UInt256).toNat 32)
    let memLen := (UInt256.toByteArray oszWord).write 0 memFree freePtr.toNat 32
    let awLen : UInt256 := UInt256.ofNat (MachineState.M awStoreFree.toNat freePtr.toNat 32)
    let dataPtr := freePtr + ⟨32⟩
    let memCopy := o.write 0 memLen dataPtr.toNat oszWord.toNat
    let awCopy : UInt256 := UInt256.ofNat (MachineState.M awLen.toNat dataPtr.toNat oszWord.toNat)
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      (success :: amount :: owner :: ret :: R)
      memCopy awCopy o acc k' C' := by
  let oszWord := UInt256.ofNat o.size
  let freePtr :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let awFree : UInt256 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let rounded := UInt256.land (oszWord + ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let newFree := freePtr + rounded
  let memFree := (UInt256.toByteArray newFree).write 0 mem (⟨64⟩ : UInt256).toNat 32
  let awStoreFree : UInt256 :=
    UInt256.ofNat (MachineState.M awFree.toNat (⟨64⟩ : UInt256).toNat 32)
  let memLen := (UInt256.toByteArray oszWord).write 0 memFree freePtr.toNat 32
  let awLen : UInt256 := UInt256.ofNat (MachineState.M awStoreFree.toNat freePtr.toNat 32)
  let dataPtr := freePtr + ⟨32⟩
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
    raw mload (Cₘ awFree - Cₘ aw) freePtr awFree (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore (Cₘ awStoreFree - Cₘ awFree) memFree awStoreFree (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    returndatasize, dup3,
    raw mstore (Cₘ awLen - Cₘ awStoreFree) memLen awLen (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
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
        oszWord])
    (by rfl) (by rfl)
    (by evm_ov)
  have rd4879 := evm_run rd4863 with [push2 ⟨4879⟩, jump (by jump_dest)]
  exact ⟨_, _, evm_run rd4879 with [
    jumpdest, pop, swap1, swap3, pop, pop, pop,
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]⟩

def auctionETHReturnedState (mem : ByteArray) (aw : UInt256) (out : ByteArray) :
    ByteArray × UInt256 :=
  if out.size = 0 then (mem, aw) else
    let size := UInt256.ofNat out.size
    let free := auctionLoadWord mem aw ⟨64⟩
    let awLoad := auctionGrowWords aw ⟨64⟩ 32
    let rounded := UInt256.land (size + ⟨63⟩) (UInt256.lnot ⟨31⟩)
    let memFree := auctionStoreWord mem ⟨64⟩ (free + rounded)
    let awFree := auctionGrowWords awLoad ⟨64⟩ 32
    let memLen := auctionStoreWord memFree free size
    let awLen := auctionGrowWords awFree free 32
    let ptr := free + ⟨32⟩
    (out.write 0 memLen ptr.toNat size.toNat, auctionGrowWords awLen ptr size.toNat)

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferETHReturn {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner amount aw success ret : UInt256} {R : List UInt256}
    {mem out : ByteArray} {k C : Nat}
    (hR : R.length ≤ 970) (hsize : out.size < UInt256.size)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4828⟩
      (success :: ⟨352⟩ :: amount :: ⟨30000⟩ :: owner :: ⟨0⟩ :: ⟨0⟩ :: amount :: owner ::
        ⟨3347⟩ :: amount :: owner :: ret :: R) mem aw out acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      (success :: amount :: owner :: ret :: R) (auctionETHReturnedState mem aw out).1
      (auctionETHReturnedState mem aw out).2 out acc k' C' := by
  by_cases hz : out.size = 0
  · have rd4838 := evm_run rd with [
      swap4, pop, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
    have rd4874 := evm_run rd4838 with [
      push2 ⟨4874⟩, jumpiT (by rw [hz]; native_decide) (by jump_dest)]
    have rd4886 := evm_run rd4874 with [
      jumpdest, push1 ⟨96⟩, swap2, pop, jumpdest, pop, swap1, swap3, pop, pop, pop]
    have hr := evm_run rd4886 with [jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
    exact ⟨_, _, by simpa only [auctionETHReturnedState, hz, if_pos rfl] using hr⟩
  · simpa only [auctionETHReturnedState, if_neg hz, auctionStoreWord, auctionGrowWords,
      auctionLoadWord] using auctionSafeTransferETHReturnNonempty hR hsize hz rd

theorem auctionSafeTransferETHSuccessReturn {cA gh bl σ σ₀ A I}
    {g : Sat256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owner amount aw ret : UInt256} {R : List UInt256}
    {mem out : ByteArray} {k C : Nat}
    (hR : R.length ≤ 970) (hret : (D_J auctionBytecode 0).contains ret = true)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      (⟨1⟩ :: amount :: owner :: ret :: R) mem aw out acc k C) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ret R mem aw out acc k' C' := by
  have rd3570 := evm_run rd with [jumpdest, push2 ⟨3570⟩,
    jumpiT (by native_decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd3570 with [jumpdest, pop, pop, jump hret]⟩

end Auction
