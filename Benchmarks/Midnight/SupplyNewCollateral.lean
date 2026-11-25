import Benchmarks.Midnight.SupplyOracleCall
import Benchmarks.Midnight.SupplyBitmapPhase
import Benchmarks.Midnight.SupplySourceFrame
import Benchmarks.Midnight.ArrayIndexGas

variable {fork : Ethereum.Fork}

/-! The oracle and bitmap branch for a newly supplied collateral token. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem supplyNewCollateral {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {m : MarketData} {mem rdata : ByteArray}
    {aw market array limit root old index id user assets : UInt256} {token : AccountAddress}
    {credit k C : Nat} {R : List UInt256}
    (hs : SourceState s0 I evm.accountMap evm)
    (hf : SupplySourceFrame frame m id user index assets old token)
    (hcanon : user.toNat < EVM.addressModulus) (hi : index.toNat < 128)
    (hindex : index.toNat < m.collaterals.length)
    (hstack : R.length + 24 ≤ 1024) (hm : MarketStored mem market array limit m)
    (hroot : root.toNat + 32 < 2^64) (hlower : 128 ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hb : TransferBudget (root + UInt256.ofNat 32) credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨17211⟩
      ([market + UInt256.ofNat 96, positionSlot id user, old, index, id, user,
        UInt256.ofNat token.val, assets, positionSlot id user + UInt256.ofNat 3] ++ R)
      mem aw rdata evm.accountMap k C) :
    (RDrev fork midnightBytecode g s0 ∧ ExecBlock fork config frame evm supplyNewCollateralBody .reverted) ∨
    (RDstatic fork midnightBytecode g s0 ∧
      ExecBlock fork config frame evm supplyNewCollateralBody .staticViolation) ∨
    ∃ frame' evm' out aw' k' C',
      SourceState s0 I evm'.accountMap evm' ∧
      SupplySourceFrame frame' m id user index assets old token ∧
      ExecBlock fork config frame evm supplyNewCollateralBody (.ok frame' evm') ∧
      MemoryPrefix mem (oraclePriceMemory mem root out) root.toNat ∧
      (oraclePriceMemory mem root out).size = max mem.size (root.toNat + 32) ∧
      memLoad (UInt256.ofNat 64) (oraclePriceMemory mem root out) = root + UInt256.ofNat 32 ∧
      TransferBudget (root + UInt256.ofNat 32) credit (oraclePriceMemory mem root out) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨17462⟩
        ([index, id, old, user, UInt256.ofNat token.val, assets,
          positionSlot id user + UInt256.ofNat 3] ++ R)
        (oraclePriceMemory mem root out) aw' out evm'.accountMap k' C' := by
  let oracle := m.collaterals[index.toNat].oracle
  let frame1 := { frame with locals := frame.locals.insert "oracle" (.address oracle) }
  have hf1 : SupplySourceFrame frame1 m id user index assets old token :=
    hf.insert "oracle" (.address oracle) (by decide)
  have horacleExpr : evalExpr? config frame evm
      (.field (marketCollateralExpr "collateralIndex") "oracle") = .ok (.address oracle) := by
    rw [evalExpr?, evalMarketCollateralAt "collateralIndex" hf.market hf.index hindex]
    rfl
  have hlet : ExecStmt fork config frame evm (supplyNewCollateralBody[0]!) (.ok frame1 evm) :=
    ExecStmt.letDecl horacleExpr
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_17211
    (by simp only [List.length_cons]; omega) (by jump_dest) rd
  have hb1 := transferBudgetAt (root := root + UInt256.ofNat 32) (credit := credit) rd1
    (by transfer_budget hb)
  simp only [midnightBlocks.midnight_block_17211_stack, hm.arrayPtr, addressMask_computed] at rd1
  have hlen : (memLoad array mem).toNat = m.collaterals.length := by
    rw [hm.length, UInt256.toNat_ofNat_of_lt (by
      have := hm.collateralCount; change _ < 2^256; omega)]
  obtain ⟨aw2, k2, C2, hb2, rd2⟩ := midnightMemoryArrayIndex_funded
    (by simp only [List.length_cons]; omega) (hindex.trans hm.collateralCount)
    (by rw [hlen]; exact hindex) (by jump_dest) hb1 rd1
  obtain ⟨cp, hcp, _, _, hwords⟩ := hm.collaterals.get index.toNat hindex
  have horacle : memLoad (cp + UInt256.ofNat 96) mem = UInt256.ofNat oracle.val :=
    hwords.load_offset ⟨3, by simp [CollateralData.words]⟩ rfl
  rcases supplyOracleCall (frame := frame1) (receiver := .var "oracle")
      (R := index :: id :: old :: user :: UInt256.ofNat token.val ::
      assets :: (positionSlot id user + UInt256.ofNat 3) :: R)
      (by simp only [List.length_cons]; omega) hroot (by omega) hfree hcp horacle
      (by simp only [evalExpr?, frame1, store_get_self, EvalResult.ofOption]) hs hb2 rd2 with
        ⟨hcall, hr⟩ | ⟨evm2, σ2, out, aw3, k3, C3, hcall, _, hs2, h32, hprefix, hfree3, hb3, rd3⟩
  · exact Or.inl ⟨hr, ExecBlock.consNormal hlet (ExecBlock.consRevert hcall)⟩
  · let frame2 := wordLocal frame1 "__c1" (calldataWord out 0)
    have hf2 : SupplySourceFrame frame2 m id user index assets old token :=
      hf1.insert "__c1" (.int (calldataWord out 0).toNat) (by decide)
    have sourcePrefix {result : ExecResult}
        (ht : ExecBlock fork config frame2 evm2 (supplyNewCollateralBody.drop 2) result) :
        ExecBlock fork config frame evm supplyNewCollateralBody result :=
      ExecBlock.consNormal hlet (ExecBlock.consNormal hcall ht)
    rw [hs2.accounts] at rd3
    rcases supplyBitmapPhase hs2.env (by simp only [List.length_cons]; omega)
        hf2.contract hcanon hf2.position hf2.index hi hb3 rd3 with
      ⟨hr, hbsource⟩ | ⟨hr, hbsource⟩ | ⟨hperm, k4, C4, hb4, hbsource, rd4⟩
    · exact Or.inl ⟨hr, sourcePrefix hbsource⟩
    · exact Or.inr (Or.inl ⟨hr, sourcePrefix hbsource⟩)
    · let bitmap := bitmapSet (positionBitmapWord evm2 id user) index
      let evm3 := storeHigh128 evm2 (positionSlot id user + ⟨2⟩) bitmap
      have hs3 : SourceState s0 I evm3.accountMap evm3 := by
        refine ⟨?_, (storeHigh128_env ..).trans hs2.env, rfl⟩
        simpa only [evm3, storeHigh128, storageStore_σ₀] using hs2.world
      refine Or.inr (Or.inr ⟨_, evm3, out, aw3, k4, C4, hs3, hf2.countFrame bitmap,
        sourcePrefix hbsource, hprefix, ?_, hfree3, hb4, rd4⟩)
      exact (oraclePriceMemory_properties mem root h32 (by omega)).1

end Benchmarks.Midnight
