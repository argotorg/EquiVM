import Benchmarks.Auction.CreateAuctionArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def auctionMintDecodedMemory (free : UInt256) (mem out : ByteArray) : ByteArray :=
  auctionStoreWord mem ⟨64⟩
    (UInt256.add free (UInt256.land (UInt256.lnot ⟨31⟩)
      (UInt256.add (UInt256.ofNat out.size) ⟨31⟩)))

theorem auctionCreateAuctionMintReturnToDecode {s0 : State} {I : ExecutionEnv} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g s0 ⟨3078⟩ R mem aw out acc k C)
    (hov : R.length + 5 ≤ 1024) :
    let free := auctionLoadWord mem aw ⟨64⟩
    let awLoad := auctionGrowWords aw ⟨64⟩ 32
    let awStore := auctionGrowWords awLoad ⟨64⟩ 32
    ∃ k' C', RD auctionBytecode I g s0 ⟨5820⟩
      (free :: UInt256.add free (UInt256.ofNat out.size) :: ⟨3108⟩ :: R)
      (auctionMintDecodedMemory free mem out) awStore out acc k' C' := by
  intro free awLoad awStore
  exact ⟨_, _, evm_run rd with [
    push1 ⟨64⟩, dup1,
    raw mload (Cₘ awLoad - Cₘ aw) free awLoad (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks rfl)
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨31⟩, returndatasize, swap1, dup2, add, push1 ⟨31⟩, not, and, dup3, add,
    swap1, swap3,
    raw mstore (Cₘ awStore - Cₘ awLoad) (auctionMintDecodedMemory free mem out) awStore
      (by native_decide) (fun _ haws hstks => mstoreCost_of_stack haws hstks rfl)
      (by rfl) (by rfl) (by evm_ov),
    push2 ⟨3108⟩, swap2, dup2, add, swap1, push2 ⟨5820⟩, jump (by jump_dest)]⟩

theorem auctionMintDecodeLengthCheck (free : UInt256) {len : Nat} (hlen : len < UInt256.size) :
    UInt256.sub (UInt256.add free (UInt256.ofNat len)) free = UInt256.ofNat len := by
  simpa only [u256_ofNat_toNat] using
    usub_uadd_lit_cancel_mod (show free.toNat < UInt256.size from free.val.isLt) hlen

theorem auctionCreateAuctionMintDecodeOk {s0 : State} {I : ExecutionEnv} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {free aw retWord : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g s0 ⟨5820⟩
      (free :: UInt256.add free (UInt256.ofNat out.size) :: ⟨3108⟩ :: R) mem aw out acc k C)
    (ho32 : 32 ≤ out.size) (ho : out.size < 2 ^ 255)
    (hword : auctionLoadWord mem aw free = retWord) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨3108⟩ (retWord :: R)
      mem (auctionGrowWords aw free 32) out acc k' C' := by
  have hlen : out.size < UInt256.size := lt_size_of_lt_sign ho
  have hcheck : UInt256.slt (UInt256.sub (UInt256.add free (UInt256.ofNat out.size)) free)
      ⟨32⟩ = ⟨0⟩ := by
    rw [auctionMintDecodeLengthCheck free hlen]
    exact slt_ofNat_lit_zero (by decide) ho32 ho
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨5836⟩,
    jumpiT (by rw [hcheck]; decide) (by jump_dest), jumpdest, pop,
    raw mload (Cₘ (auctionGrowWords aw free 32) - Cₘ aw)
      retWord (auctionGrowWords aw free 32) (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks rfl)
      hword (by rfl) (by evm_ov),
    swap2, swap1, pop, jump (by jump_dest)]⟩

theorem auctionCreateAuctionMintDecodeRevert {s0 : State} {I : ExecutionEnv} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {free aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g s0 ⟨5820⟩
      (free :: UInt256.add free (UInt256.ofNat out.size) :: ⟨3108⟩ :: R) mem aw out acc k C)
    (hbad : UInt256.slt (UInt256.sub (UInt256.add free (UInt256.ofNat out.size)) free)
      ⟨32⟩ = ⟨1⟩) (hov : R.length + 8 ≤ 1024) : RDrev auctionBytecode g s0 := by
  have rd5832 := evm_run rd with [jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt]
  rw [hbad] at rd5832
  have rd5835 := evm_run rd5832 with [iszero, push2 ⟨5836⟩, jumpiNT (by decide), push0, dup1]
  exact auctionRevertDynamic rd5835 (by native_decide) (by evm_ov)

end Auction
