import Benchmarks.Auction.UnpauseMintTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

abbrev auctionMintFailureSwitchPc : UInt256 := ⟨3124⟩

abbrev auctionMintFailureAfterDupPc : UInt256 := ⟨3125⟩

abbrev auctionMintFailureAfterPushSelectorPc : UInt256 := ⟨3130⟩

abbrev auctionMintFailureAfterSubPc : UInt256 := ⟨3131⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_mintCallFailureBubbleRevertTail {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3165⟩
      R mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 8 ≤ 1024) :
    RDrev auctionBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  have rd3166 := RD.returndatasize rd (by decide) (by omega)
  have rd3167 := RD.push0 rd3166 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd3168 := RD.dup1 rd3167 (by decide)
    (by simp only [List.length_cons]; omega)
  let len := UInt256.ofNat o.size
  let memout := o.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd3169 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd3168 (by decide)
    (by
      change 0 + len.toNat ≤ o.size
      dsimp [len]
      rw [UInt256.toNat_ofNat_of_lt hosz]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, len, awout])
    (by rfl) (by rfl)
    (by omega)
  have rd3170 := RD.returndatasize rd3169 (by decide) (by omega)
  have rd3171 := RD.push0 rd3170 (by decide)
    (by simp only [List.length_cons]; omega)
  exact RD.rev (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd3171 (by decide)
    (fun s haws hstks => by
      simpa [awout, len, haws] using memExpRevertZeroOff s hstks)
    (by omega)

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_mintCallFailureSelectorToSwitch {cA gh bl σInit σ₀ A I}
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
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I)
      auctionMintFailureSwitchPc (sel :: R) (o.write 0 mem 0 4) (UInt256.ofNat 5) o acc k' C' := by
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
  have rd5859 := RD.returndatacopy 0 memSel (UInt256.ofNat 5) rd5854 (by decide)
    (by
      change 0 + (⟨4⟩ : UInt256).toNat ≤ o.size
      simpa using hlen)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      decide)
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd5864₀ := evm_run rd5859 with [pop, push0,
    raw mload 0 preSel (UInt256.ofNat 5) (by decide) mem_cost
      (by simpa [memSel] using hword) (by decide) (by evm_ov),
    push1 ⟨224⟩, shr]
  have rd5864 := rd5864₀
  rw [hshr] at rd5864
  have rd3123 := evm_run rd5864 with [jumpdest, swap1, jump (by jump_dest), jumpdest]
  exact ⟨_, _, by simpa [memSel] using rd3123⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_mintCallFailureSelectorSwitchDup {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {memSel o : ByteArray} {k C : ℕ} {sel : UInt256} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I)
      auctionMintFailureSwitchPc
      (sel :: R) memSel (UInt256.ofNat 5) o acc k C)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I)
      auctionMintFailureAfterDupPc (sel :: sel :: R) memSel (UInt256.ofNat 5) o acc k' C' := by
  have rd3124 := RD.dup1 rd (by decide) (by omega)
  exact ⟨_, _, by
    simpa [auctionMintFailureSwitchPc, auctionMintFailureAfterDupPc] using rd3124⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_mintCallFailureSelectorSwitchPush {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {memSel o : ByteArray} {k C : ℕ} {sel : UInt256} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I)
      auctionMintFailureAfterDupPc (sel :: sel :: R) memSel (UInt256.ofNat 5) o acc k C)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I)
      auctionMintFailureAfterPushSelectorPc
      (⟨0x08c379a0⟩ :: sel :: sel :: R) memSel (UInt256.ofNat 5) o acc k' C' := by
  have rd3129 := RD.push4 rd ⟨0x08c379a0⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [auctionMintFailureAfterDupPc, auctionMintFailureAfterPushSelectorPc] using rd3129⟩

end Auction
