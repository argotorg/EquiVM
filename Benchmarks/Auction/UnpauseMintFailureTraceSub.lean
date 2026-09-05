import Benchmarks.Auction.UnpauseMintFailureTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionMintFailureSub_decode :
    decode auctionBytecode auctionMintFailureAfterPushSelectorPc = some (.SUB, .none) := by
  decide

theorem auctionMintFailurePush3162_decode :
    decode auctionBytecode auctionMintFailureAfterSubPc =
      some (.Push .PUSH2, some (⟨3162⟩, 2)) := by
  decide

theorem auctionMintFailureJumpi_decode :
    decode auctionBytecode (⟨3134⟩ : UInt256) = some (.JUMPI, .none) := by
  decide

theorem auctionMintFailureJumpdest3162_decode :
    decode auctionBytecode (⟨3162⟩ : UInt256) = some (.JUMPDEST, .none) := by
  decide

theorem auctionMintFailurePop3163_decode :
    decode auctionBytecode (⟨3163⟩ : UInt256) = some (.POP, .none) := by
  decide

theorem auctionMintFailureJumpdest3164_decode :
    decode auctionBytecode (⟨3164⟩ : UInt256) = some (.JUMPDEST, .none) := by
  decide

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_mintCallFailureSelectorPushedToBubble {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {memSel o : ByteArray} {k C : ℕ} {sel : UInt256} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I)
      auctionMintFailureAfterPushSelectorPc
      (⟨0x08c379a0⟩ :: sel :: sel :: R) memSel (UInt256.ofNat 5) o acc k C)
    (hsub : UInt256.sub sel ⟨0x08c379a0⟩ ≠ ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3165⟩
      R memSel (UInt256.ofNat 5) o acc k' C' := by
  have hselNe : (⟨0x08c379a0⟩ : UInt256) ≠ sel := by
    intro hEq
    apply hsub
    rw [← hEq]
    exact u256_sub_self (⟨0x08c379a0⟩ : UInt256)
  have hsubRev : UInt256.sub (⟨0x08c379a0⟩ : UInt256) sel ≠ ⟨0⟩ :=
    u256_sub_ne_zero_of_ne hselNe
  have rd3165 := evm_run rd with [
    sub, push2 ⟨3162⟩, jumpiT hsubRev (by jump_dest), jumpdest, pop, jumpdest]
  exact ⟨_, _, rd3165⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_mintCallFailureSelectorSwitchRevert {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {memSel o : ByteArray} {k C : ℕ} {sel : UInt256} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I)
      auctionMintFailureSwitchPc
      (sel :: R) memSel (UInt256.ofNat 5) o acc k C)
    (hosz : o.size < UInt256.size)
    (hsub : UInt256.sub sel ⟨0x08c379a0⟩ ≠ ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) :
    RDrev auctionBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  obtain ⟨_, _, rd3124⟩ :=
    auctionCreateAuction_mintCallFailureSelectorSwitchDup rd hov
  obtain ⟨_, _, rd3129⟩ :=
    auctionCreateAuction_mintCallFailureSelectorSwitchPush rd3124 hov
  obtain ⟨_, _, rd3165⟩ :=
    auctionCreateAuction_mintCallFailureSelectorPushedToBubble rd3129 hsub hov
  exact auctionCreateAuction_mintCallFailureBubbleRevertTail
    (mem := memSel) (aw := UInt256.ofNat 5) rd3165 hosz hov

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_mintCallFailureSelectorRevert {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 preSel sel : UInt256} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3067⟩
      (⟨0⟩ :: d0 :: d1 :: d2 :: R) mem (UInt256.ofNat 5) o acc k C)
    (hlen : 4 ≤ o.size) (hosz : o.size < UInt256.size)
    (hword :
      (if (⟨0⟩ : UInt256).toNat ≥ (o.write 0 mem 0 4).size ∨
          (⟨0⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((o.write 0 mem 0 4).readWithPadding
            (⟨0⟩ : UInt256).toNat 32))) = preSel)
    (hshr : UInt256.shiftRight preSel ⟨224⟩ = sel)
    (hsub : UInt256.sub sel ⟨0x08c379a0⟩ ≠ ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) :
    RDrev auctionBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  obtain ⟨_, _, rd3123⟩ :=
    auctionCreateAuction_mintCallFailureSelectorToSwitch rd hlen hosz hword hshr hov
  exact auctionCreateAuction_mintCallFailureSelectorSwitchRevert rd3123 hosz hsub hov

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_mintCallFailureErrorStringShortRevert {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 preSel : UInt256} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3067⟩
      (⟨0⟩ :: d0 :: d1 :: d2 :: R) mem (UInt256.ofNat 5) o acc k C)
    (hlen : 4 ≤ o.size) (hshort : o.size < 68) (hosz : o.size < UInt256.size)
    (hword :
      (if (⟨0⟩ : UInt256).toNat ≥ (o.write 0 mem 0 4).size ∨
          (⟨0⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((o.write 0 mem 0 4).readWithPadding
            (⟨0⟩ : UInt256).toNat 32))) = preSel)
    (hshr : UInt256.shiftRight preSel ⟨224⟩ = (⟨0x08c379a0⟩ : UInt256))
    (hov : R.length + 8 ≤ 1024) :
    RDrev auctionBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  obtain ⟨_, _, rd3123⟩ :=
    auctionCreateAuction_mintCallFailureSelectorToSwitch rd hlen hosz hword hshr hov
  have rd3134₀ := evm_run rd3123 with [dup1, push4 ⟨0x08c379a0⟩, sub]
  have rd3134 := rd3134₀
  rw [show UInt256.sub (⟨0x08c379a0⟩ : UInt256) ⟨0x08c379a0⟩ = ⟨0⟩ by decide]
    at rd3134
  have rd5925 := evm_run rd3134 with [push2 ⟨3162⟩, jumpiNT (by decide), pop,
    push2 ⟨3143⟩, push2 ⟨5925⟩, jump (by jump_dest), jumpdest]
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨68⟩ : UInt256) = ⟨1⟩ := by
    apply ult_one
    change (UInt256.ofNat o.size).toNat < 68
    rw [UInt256.toNat_ofNat_of_lt hosz]
    omega
  have rd5931₀ := evm_run rd5925 with [push0, push1 ⟨68⟩, returndatasize, lt]
  have rd5931 := rd5931₀
  rw [hlt] at rd5931
  have rd5932₀ := evm_run rd5931 with [iszero]
  have rd5932 := rd5932₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd5932
  have rd3143 := evm_run rd5932 with [push2 ⟨5938⟩, jumpiNT (by decide), swap1,
    jump (by jump_dest), jumpdest]
  have rd3164 := evm_run rd3143 with [dup1, push2 ⟨3154⟩, jumpiNT (by decide), pop,
    push2 ⟨3164⟩, jump (by jump_dest), jumpdest]
  exact auctionCreateAuction_mintCallFailureBubbleRevertTail
    (mem := o.write 0 mem 0 4) (aw := UInt256.ofNat 5) rd3164 hosz hov

end Auction
