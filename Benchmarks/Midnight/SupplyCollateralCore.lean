import Benchmarks.Midnight.SupplyReadSource
import Benchmarks.Midnight.SupplyCollateralRead
import Benchmarks.Midnight.SupplyCollateralIf

/-! The supply body after market initialization. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem supplyBudgetBefore32 {root aw : UInt256} {credit C : Nat} {mem : ByteArray}
    (hn : (root + UInt256.ofNat 32).toNat = root.toNat + 32)
    (hb : TransferBudget (root + UInt256.ofNat 32) credit mem aw C) :
    TransferBudget root credit mem aw C := by
  rcases hb with hs | ⟨ha, hf⟩
  · exact Or.inl (by rw [hn] at hs; omega)
  · exact Or.inr ⟨by rw [hn] at ha; omega, hf⟩

theorem supplyCollateralCore {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw market array limit root index user assets extra : UInt256}
    {credit k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I evm.accountMap evm)
    (hf : SupplyTouchSourceFrame frame m user index assets)
    (hcanon : user.toNat < EVM.addressModulus)
    (hstack : R.length + 28 ≤ 1024) (hmem : 128 ≤ mem.size)
    (hm : MarketStored mem market array limit m)
    (hroot : root.toNat + 32 < 2^64) (hlower : 128 ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : TransferBudget (root + UInt256.ofNat 32) credit mem aw C)
    (hcredit : 4 * (((root + UInt256.ofNat 32).toNat + safeTransferCallAllocation true + 31) / 32)
      ≤ credit + 999921)
    (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨17031⟩
      ([m.id, UInt256.ofNat 96, user, index, assets, market, extra] ++ R)
      mem aw rdata evm.accountMap k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (RDrev midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock config frame evm (supplyCollateralTransition.body.drop 5) .reverted) ∨
    (RDstatic midnightBytecode (Sat256.ofUInt256 g) s0 ∧
      ExecBlock config frame evm (supplyCollateralTransition.body.drop 5) .staticViolation) ∨
    ∃ frame' evm',
      ExecBlock config frame evm (supplyCollateralTransition.body.drop 5) (.ok frame' evm') ∧
      RDret midnightBytecode (Sat256.ofUInt256 g) s0 evm'.accountMap ByteArray.empty := by
  simp only [List.cons_append, List.nil_append] at rd
  rcases midnightSupplyCollateralRead (R := extra :: R)
      (by simp only [List.length_cons]; omega) (by omega) hm hb rd with
    ⟨hbad, hr⟩ | ⟨hi, hi128, check, aw1, k1, C1, hb1, hcheck, rd1⟩
  · exact Or.inr (Or.inl ⟨hr, supplyReadRevert hf hbad⟩)
  · have hload : (fun slot ↦ solcSlotWordAt slot evm.accountMap I) =
        EVM.storageLoad evm evm.executionEnv.codeOwner := by
      funext slot
      exact (storageLoad_codeOwner_eq_solcSlotWordAt evm I slot
        (congrArg ExecutionEnv.codeOwner hs.env)).symm
    rw [hload] at hcheck rd1
    let old := collateralWord (EVM.storageLoad evm evm.executionEnv.codeOwner) m.id user index
    let token := m.collaterals[index.toNat].token
    let frame1 := supplyReadFrame frame m.id user old token
    have hf1 : SupplySourceFrame frame1 m m.id user index assets old token :=
      supplyReadFrame_get hf old token
    have hm1 := hm.preserve (positionReadMemory_prefix mem m.id user limit.toNat)
    have hsize := positionReadMemory_size mem m.id user (by omega : 64 ≤ mem.size)
    have hkeep (off : UInt256) (hlo : 64 ≤ off.toNat) (hin : off.toNat + 32 ≤ mem.size) :
        memLoad off (positionReadMemory mem m.id user) = memLoad off mem := by
      unfold positionReadMemory
      rw [memLoad_twoWordHashMem _ _ _ hlo (by
        rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; exact hin),
        memLoad_twoWordHashMem _ _ _ hlo hin]
    have hn : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
      addWord_toNat root (UInt256.ofNat 32) (by change root.toNat + 32 < 2^256; omega)
    rcases supplyCollateralIf (R := R) hs hf1 hcanon hi128 hi hcheck (by omega)
        (by rw [hsize]; exact hmem) hm1 hroot hlower
        (by rw [hkeep (UInt256.ofNat 64) (by decide) (by change 96 ≤ mem.size; omega), hfree])
        (by rw [hkeep (UInt256.ofNat 96) (by decide) hmem, hzero])
        (supplyBudgetBefore32 hn hb1) hb1 (by rw [hn] at hcredit; omega)
        hcredit hgas hfork rd1 with
      hoog | ⟨hr, hbody⟩ | ⟨hr, hbody⟩ | ⟨frame', evm', hbody, hr⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨hr, supplyReadSource hf hcanon hi hi128 hbody⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hr, supplyReadSource hf hcanon hi hi128 hbody⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨frame', evm', supplyReadSource hf hcanon hi hi128 hbody, hr⟩))

end Benchmarks.Midnight
