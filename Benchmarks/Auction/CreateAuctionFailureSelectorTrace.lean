import Benchmarks.Auction.UnpauseMintTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionMintFailureSelectorToSwitchDynamic {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {d0 d1 d2 preSel sel : UInt256} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3067⟩
      (⟨0⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hcopyAw : auctionGrowWords aw ⟨0⟩ 4 = aw)
    (hloadAw : auctionGrowWords aw ⟨0⟩ 32 = aw)
    (hlen : 4 ≤ o.size) (hosz : o.size < UInt256.size)
    (hword :
      (if (⟨0⟩ : UInt256).toNat ≥ (o.write 0 mem 0 4).size ∨
          (⟨0⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((o.write 0 mem 0 4).readWithPadding
            (⟨0⟩ : UInt256).toNat 32))) = preSel)
    (hshr : UInt256.shiftRight preSel ⟨224⟩ = sel)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I)
      ⟨3124⟩ (sel :: R) (o.write 0 mem 0 4) aw o acc k' C' := by
  have rd3111 := evm_run rd with [
    swap3, pop, pop, pop, dup1, iszero, push2 ⟨3111⟩,
    jumpiT (by decide) (by jump_dest), jumpdest]
  have rd5843 := evm_run rd3111 with [
    push2 ⟨3172⟩, jumpiNT (by decide), push2 ⟨3123⟩, push2 ⟨5843⟩,
    jump (by jump_dest), jumpdest]
  have hgt : UInt256.gt (UInt256.ofNat o.size) (⟨3⟩ : UInt256) = ⟨1⟩ := by
    apply ugt_one
    change 3 < (UInt256.ofNat o.size).toNat
    rw [UInt256.toNat_ofNat_of_lt hosz]
    omega
  have rd5849₀ := evm_run rd5843 with [push0, push1 ⟨3⟩, returndatasize, gt]
  have rd5849 := rd5849₀
  rw [hgt] at rd5849
  have rd5850₀ := evm_run rd5849 with [iszero]
  have rd5850 := rd5850₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd5850
  have rd5854 := evm_run rd5850 with [push2 ⟨5865⟩, jumpiNT (by decide),
    push1 ⟨4⟩, push0, dup1]
  let memSel := o.write 0 mem 0 4
  have rd5859 := RD.returndatacopy 0 memSel aw rd5854 (by native_decide)
    (by
      change 0 + (⟨4⟩ : UInt256).toNat ≤ o.size
      simpa using hlen)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      change Cₘ (auctionGrowWords aw ⟨0⟩ 4) - Cₘ aw = 0
      rw [hcopyAw, Nat.sub_self])
    (by rfl) (by exact hcopyAw)
    (by simp only [List.length_cons]; omega)
  have rd5864₀ := evm_run rd5859 with [pop, push0,
    raw mload 0 preSel aw (by native_decide)
      (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by
        change Cₘ (auctionGrowWords aw ⟨0⟩ 32) - Cₘ aw = 0
        rw [hloadAw]; exact Nat.sub_self _))
      (by simpa only [memSel] using hword) hloadAw (by evm_ov),
    push1 ⟨224⟩, shr]
  have rd5864 := rd5864₀
  rw [hshr] at rd5864
  have rd3123 := evm_run rd5864 with [jumpdest, swap1, jump (by jump_dest), jumpdest]
  exact ⟨_, _, by simpa [memSel] using rd3123⟩

theorem auctionMintFailureSwitchToDecoder {s0 : State} {I : ExecutionEnv} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw : UInt256} {R : List UInt256} {k C : Nat}
    (rd : RD auctionBytecode I g s0 ⟨3124⟩ (⟨0x08c379a0⟩ :: R) mem aw out acc k C)
    (hR : R.length + 4 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨5926⟩ (⟨3143⟩ :: R) mem aw out acc k' C' := by
  have rd3131 := evm_run rd with [dup1, push4 ⟨0x08c379a0⟩, sub]
  rw [show UInt256.sub (⟨0x08c379a0⟩ : UInt256) ⟨0x08c379a0⟩ = ⟨0⟩ by decide] at rd3131
  exact ⟨_, _, evm_run rd3131 with [push2 ⟨3162⟩, jumpiNT (by decide), pop,
    push2 ⟨3143⟩, push2 ⟨5925⟩, jump (by jump_dest), jumpdest]⟩

theorem auctionMintFailureDecoderShortToReturn {s0 : State} {I : ExecutionEnv} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw : UInt256} {R : List UInt256} {k C : Nat}
    (rd : RD auctionBytecode I g s0 ⟨5926⟩ (⟨3143⟩ :: R) mem aw out acc k C)
    (hshort : out.size < 68) (hosz : out.size < UInt256.size) (hR : R.length + 4 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨3143⟩ (⟨0⟩ :: R) mem aw out acc k' C' := by
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨68⟩ : UInt256) = ⟨1⟩ := by
    apply ult_one
    change (UInt256.ofNat out.size).toNat < 68
    rwa [UInt256.toNat_ofNat_of_lt hosz]
  have rd5931 := evm_run rd with [push0, push1 ⟨68⟩, returndatasize, lt]
  rw [hlt] at rd5931
  exact ⟨_, _, evm_run rd5931 with [iszero, push2 ⟨5938⟩, jumpiNT (by decide), swap1,
    jump (by jump_dest)]⟩

end Auction
