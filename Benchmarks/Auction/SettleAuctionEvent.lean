import Benchmarks.Auction.SettleAuctionCallSetup
import Benchmarks.Auction.DynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

/-- Memory and active-word count after the settlement event. -/
def auctionSettleEventState (ptr : UInt256) (mem : ByteArray) (aw : UInt256) :
    ByteArray × UInt256 :=
  let awNoun := auctionGrowWords aw ptr 32
  let bidderPtr := ptr + ⟨128⟩
  let bidder := auctionLoadWord mem awNoun bidderPtr
  let awBidder := auctionGrowWords awNoun bidderPtr 32
  let amountPtr := ptr + ⟨32⟩
  let amount := auctionLoadWord mem awBidder amountPtr
  let awAmount := auctionGrowWords awBidder amountPtr 32
  let free := auctionLoadWord mem awAmount ⟨64⟩
  let awFree := auctionGrowWords awAmount ⟨64⟩ 32
  let winner := UInt256.land bidder
    (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
  let memWinner := auctionStoreWord mem free winner
  let awWinner := auctionGrowWords awFree free 32
  let amountDataPtr := free + ⟨32⟩
  let memAmount := auctionStoreWord memWinner amountDataPtr amount
  let awData := auctionGrowWords awWinner amountDataPtr 32
  let logPtr := auctionLoadWord memAmount awData ⟨64⟩
  let awLogPtr := auctionGrowWords awData ⟨64⟩ 32
  let logSize := UInt256.sub (free + ⟨64⟩) logPtr
  (memAmount, auctionGrowWords awLogPtr logPtr logSize.toNat)

-- General stack tail: both public settlement paths use this event routine.
set_option maxHeartbeats 1000000 in
theorem auctionSettleAuctionEventToRetExact {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {ptr ret aw : UInt256} {mem o : ByteArray} {k C : Nat} {R : List UInt256}
    (hR : R.length ≤ 990) (hperm : I.perm = true)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (rd : RD auctionBytecode I g s0 ⟨4688⟩ (ptr :: ret :: R) mem aw o acc k C) :
    ∃ k' C', RD auctionBytecode I g s0 ret R
      (auctionSettleEventState ptr mem aw).1 (auctionSettleEventState ptr mem aw).2
      o acc k' C' := by
  let noun :=
    if ptr.toNat ≥ mem.size ∨ ptr ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding ptr.toNat 32))
  let aw4690 : UInt256 := UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)
  let bidderPtr := ptr + ⟨128⟩
  let bidder :=
    if bidderPtr.toNat ≥ mem.size ∨ bidderPtr ≥ aw4690 * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding bidderPtr.toNat 32))
  let aw4695 : UInt256 := UInt256.ofNat (MachineState.M aw4690.toNat bidderPtr.toNat 32)
  let amountPtr := ptr + ⟨32⟩
  let amount :=
    if amountPtr.toNat ≥ mem.size ∨ amountPtr ≥ aw4695 * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding amountPtr.toNat 32))
  let aw4701 : UInt256 := UInt256.ofNat (MachineState.M aw4695.toNat amountPtr.toNat 32)
  let eventDataPtr :=
    if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw4701 * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let aw4705 : UInt256 :=
    UInt256.ofNat (MachineState.M aw4701.toNat (⟨64⟩ : UInt256).toNat 32)
  let winner :=
    UInt256.land bidder
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
  let mem4718 := (UInt256.toByteArray winner).write 0 mem eventDataPtr.toNat 32
  let aw4718 : UInt256 :=
    UInt256.ofNat (MachineState.M aw4705.toNat eventDataPtr.toNat 32)
  let amountDataPtr := eventDataPtr + ⟨32⟩
  let mem4722 := (UInt256.toByteArray amount).write 0 mem4718 amountDataPtr.toNat 32
  let aw4722 : UInt256 :=
    UInt256.ofNat (MachineState.M aw4718.toNat amountDataPtr.toNat 32)
  have rd4722 := evm_run rd with [
    jumpdest, dup1,
    raw mload (Cₘ aw4690 - Cₘ aw) noun aw4690 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨128⟩, dup3, add,
    raw mload (Cₘ aw4695 - Cₘ aw4690) bidder aw4695 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, dup1, dup5, add,
    raw mload (Cₘ aw4701 - Cₘ aw4695) amount aw4701 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨64⟩, dup1,
    raw mload (Cₘ aw4705 - Cₘ aw4701) eventDataPtr aw4705 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap5, and, dup5,
    raw mstore (Cₘ aw4718 - Cₘ aw4705) mem4718 aw4718 (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    swap2, dup4, add,
    raw mstore (Cₘ aw4722 - Cₘ aw4718) mem4722 aw4722 (by native_decide)
      (fun _ haws hstks => mstoreCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov)]
  have rd4756 := rd4722.pushConst auctionAuctionSettledTopic
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  let logDataPtr :=
    if (⟨64⟩ : UInt256).toNat ≥ mem4722.size ∨ (⟨64⟩ : UInt256) ≥ aw4722 * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat
      (fromByteArrayBigEndian (mem4722.readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let aw4760 : UInt256 :=
    UInt256.ofNat (MachineState.M aw4722.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd4765Pre := evm_run rd4756 with [
    swap2, add, push1 ⟨64⟩,
    raw mload (Cₘ aw4760 - Cₘ aw4722) logDataPtr aw4760 (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
      (by rfl) (by rfl) (by evm_ov),
    dup1, swap2, sub, swap1]
  let logSize := (eventDataPtr + (⟨64⟩ : UInt256)).sub logDataPtr
  let aw4765 : UInt256 :=
    UInt256.ofNat (MachineState.M aw4760.toNat logDataPtr.toNat logSize.toNat)
  have rd4766 := Auction.RD.log2 (Cₘ aw4765 - Cₘ aw4760) aw4765 rd4765Pre
    (by native_decide) hperm
    (fun _ haws hstks => auctionLog2Cost_of_stack haws hstks (by rfl))
    (by rfl) (by evm_ov)
  exact ⟨_, _, evm_run rd4766 with [pop, jump hret]⟩

end Auction
