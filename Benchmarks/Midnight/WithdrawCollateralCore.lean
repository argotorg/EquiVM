import Benchmarks.Midnight.WithdrawBeforeHealth
import Benchmarks.Midnight.WithdrawAfterHealth

/-! Collateral withdrawal after the market touch, through its final return. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem withdrawCollateralCore {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw market array heap root budgetRoot user index assets extra : UInt256}
    {receiver : AccountAddress} {credit k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I evm.accountMap evm)
    (hf : SupplyTouchSourceFrame frame m user index assets)
    (hreceiver : frame.locals.get? "receiver" = some (.address receiver))
    (hcanon : user.toNat < EVM.addressModulus) (hstack : R.length + 32 ≤ 1024)
    (hmem : 832 ≤ mem.size) (hm : MarketStored mem market array heap m)
    (hroot : root.toNat + 4096 < 2^64) (hlower : 832 ≤ root.toNat)
    (hheap : heap.toNat ≤ root.toNat)
    (halign : root.toNat % 32 = 0 ∨ budgetRoot.toNat + 160 ≤ 2^62)
    (hbound : root.toNat + 4096 ≤ budgetRoot.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hzero800 : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (hcredit : 4 * ((budgetRoot.toNat + safeTransferCallAllocation false + 31) / 32) ≤
      credit + 999921)
    (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨4472⟩
      ([m.id, user, UInt256.ofNat 4643, user, index, UInt256.ofNat receiver.val, assets,
        market, extra] ++ R) mem aw rdata evm.accountMap k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock config frame evm (withdrawCollateralTransition.body.drop 5) .reverted) ∨
    (RDstatic midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock config frame evm (withdrawCollateralTransition.body.drop 5) .staticViolation) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (withdrawCollateralTransition.body.drop 5) (.ok frame' evm') ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap ByteArray.empty := by
  rcases withdrawBeforeHealth hs hf hreceiver hcanon (by omega) hmem hzero800 hm hb rd with
    ⟨hr, hs⟩ | ⟨hr, hs⟩ |
      ⟨hi, hperm, frame1, evm1, aw1, k1, C1, hs1, hf1, hb1, hprefix, rd1⟩
  · exact Or.inr (Or.inl ⟨hr, hs⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hr, hs⟩))
  · have hp := positionReadMemory_prefix mem m.id user root.toNat
    have hm1 := hm.preserve (hp.mono hheap)
    have hfree1 : memLoad (UInt256.ofNat 64) (positionReadMemory mem m.id user) = root := by
      rw [positionReadMemory, memLoad_twoWordHashMem _ _ (UInt256.ofNat 64) (by decide)
          (by rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; change 96 ≤ mem.size; omega),
        memLoad_twoWordHashMem _ _ (UInt256.ofNat 64) (by decide)
          (by change 96 ≤ mem.size; omega), hfree]
    have hz1 : memLoad (UInt256.ofNat 96) (positionReadMemory mem m.id user) = ⟨0⟩ := by
      rw [hp.load (UInt256.ofNat 96) (by decide)
        (by change 128 ≤ root.toNat; omega) (by change 128 ≤ mem.size; omega), hzero]
    have hz800 : memLoad (UInt256.ofNat 800) (positionReadMemory mem m.id user) = ⟨0⟩ := by
      rw [hp.load (UInt256.ofNat 800) (by decide) hlower hmem, hzero800]
    simp only [List.cons_append, List.nil_append] at rd1
    rcases withdrawAfterHealth hs1 hf1 hcanon hperm
        (by simp only [List.length_cons]; omega) (hmem.trans hp.size) hroot hlower hheap
        halign hbound hfree1 hz1 hz800 hm1 hb1 hcredit hgas hfork rd1 with
      hoog | ⟨hr, ht⟩ | ⟨frame', evm', ht, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨hr, hprefix _ ht⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨frame', evm', hprefix _ ht, hr⟩))

end Benchmarks.Midnight
