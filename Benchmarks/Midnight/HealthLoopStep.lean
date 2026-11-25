import Benchmarks.Midnight.HealthArithmeticSource
import Benchmarks.Midnight.OracleCall
import Benchmarks.Midnight.MemoryArrayIndex
import Benchmarks.Midnight.MarketBytesMemory

variable {fork : Ethereum.Fork}

/-! One health-loop iteration, with source execution and bytecode reachability kept together. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightHealthLoopStep {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {frame : Frame}
    {mem rdata : ByteArray} {aw market arrayPtr heap root id user bitmap maxDebt debt : UInt256}
    {m : MarketData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 22 ≤ 1024) (hfork : fork ≥ .osaka)
    (hcanon : user.toNat < EVM.addressModulus) (hbitmap : bitmap.toNat < 2^128)
    (hnz : bitmap.toNat ≠ 0) (hroot : root.toNat + 32 < 2^64)
    (hheap : heap.toNat ≤ root.toNat) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hm : MarketStored mem market arrayPtr heap m)
    (hf : HealthSourceFrame frame m id user bitmap maxDebt debt)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I g s0 ⟨19847⟩
      ([positionSlot id user + ⟨3⟩, market, bitmap, maxDebt] ++ R) mem aw rdata σ k C) :
    (ExecBlock fork config frame evm healthLoopBody .reverted ∧ RDrev fork midnightBytecode g s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (frame' : Frame) (mem' out : ByteArray)
      (maxDebt' aw' : UInt256) (k' C' : Nat),
      ExecBlock fork config frame evm healthLoopBody (.ok frame' evm') ∧
      SourceState s0 I σ' evm' ∧
      HealthSourceFrame frame' m id user (bitmapClear bitmap (bitmapMsb bitmap)) maxDebt' debt ∧
      MarketStored mem' market arrayPtr heap m ∧
      memLoad (UInt256.ofNat 64) mem' = root + UInt256.ofNat 32 ∧
      RD fork midnightBytecode I g s0 ⟨19847⟩
        ([positionSlot id user + ⟨3⟩, market, bitmapClear bitmap (bitmapMsb bitmap), maxDebt'] ++ R)
        mem' aw' out σ' k' C' := by
  let index := bitmapMsb bitmap
  let frame₁ := wordLocal frame "i" index
  have hi : index.toNat < 128 := bitmapMsb_lt hnz hbitmap
  have hnonzero : bitmap ≠ ⟨0⟩ := fun hz ↦ hnz (congrArg UInt256.toNat hz)
  have hclean : UInt256.land bitmap (UInt256.ofNat (2^128-1)) = bitmap := uint128Mask_clean hbitmap
  have rd1 := midnightBlocks.midnight_block_19847_fallthrough (R := maxDebt :: R)
    (by simp only [List.length_cons]; omega)
    (by rw [uint128Mask_computed, hclean]; exact isZero_eq_zero_of_ne hnonzero) rd
  obtain ⟨aw2, k2, C2, rd2⟩ := midnightBlocks.midnight_block_19863_packed
    (by omega) hfork (by jump_dest) rd1
  simp only [midnightBlocks.midnight_block_19863_stack, hm.arrayPtr] at rd2
  have hs1 := healthMsbCall (fork := fork) (cfg := config) (evm := evm) hf.contract hf.bitmap
  have hf1 : HealthSourceFrame frame₁ m id user bitmap maxDebt debt := hf.insert _ _ (by decide)
  have hcount : (UInt256.ofNat m.collaterals.length).toNat = m.collaterals.length :=
    UInt256.toNat_ofNat_of_lt (lt_trans hm.collateralCount (by decide))
  by_cases hindex : index.toNat < m.collaterals.length
  · obtain ⟨aw3, k3, C3, rd3⟩ := midnightMemoryArrayIndex (index := index)
      (by simp only [List.length_cons]; omega) (by omega)
      (by rw [hm.length, hcount]; exact hindex) (by jump_dest) rd2
    obtain ⟨cp, hcp, hcplo, hcplim, hwords⟩ := hm.collaterals.get index.toNat hindex
    let c := m.collaterals[index.toNat]
    let frame₂ := healthCollateralFrame frame₁ c
    have hs2 : ExecStmt fork config frame₁ evm (healthLoopBody[1]!) (.ok frame₂ evm) :=
      ExecStmt.letDecl (evalHealthCollateralAt hf1.market (wordLocal_get ..) hindex)
    have hf2 : HealthSourceFrame frame₂ m id user bitmap maxDebt debt :=
      hf1.insert _ _ (by decide)
    have horacle : memLoad (cp + UInt256.ofNat 96) mem = UInt256.ofNat c.oracle.val :=
      hwords.load_offset ⟨3, by simp [CollateralData.words]⟩ rfl
    have hlo : 96 ≤ root.toNat := by
      have := hm.lower; have := hm.array; have := hm.extent; omega
    rcases midnightOracleCall (frame := frame₂) (receiver := .field (.var "collateralParam") "oracle")
        (by omega) hroot hlo hfree hcp horacle
        (evalHealthOracle (store_get_self _ _ _)) hs rd3 with
      ⟨hsource, hrev⟩ | ⟨evm', σ', out, aw4, k4, C4, hsource, hcall, hs', h32, hp, hfree', rd4⟩
    · exact Or.inl ⟨ExecBlock.consNormal hs1
        (ExecBlock.consNormal hs2 (ExecBlock.consRevert hsource)), hrev⟩
    · let frame₃ := wordLocal frame₂ "price" (calldataWord out 0)
      have hf3 : HealthSourceFrame frame₃ m id user bitmap maxDebt debt :=
        hf2.insert _ _ (by decide)
      have hwords' : MemoryWords (oraclePriceMemory mem root out) cp.toNat c.words := by
        apply hwords.preserve hp.size
        intro word hlow hhigh
        exact hp.load word (by omega)
          (by change word.toNat + 32 ≤ cp.toNat + 32 * 4 at hhigh; omega)
          (hhigh.trans hwords.size)
      have hlltv : memLoad (cp + UInt256.ofNat 32) (oraclePriceMemory mem root out) = c.lltv :=
        hwords'.load_offset ⟨1, by simp [CollateralData.words]⟩ rfl
      have hi3 : frame₃.locals.get? "i" = some (.int index.toNat) := by
        simp only [frame₃, frame₂, healthCollateralFrame, wordLocal,
          store_get_ne _ _ (show ("price" == "i") = false from rfl),
          store_get_ne _ _ (show ("collateralParam" == "i") = false from rfl), frame₁,
          store_get_self]
      have hc3 : frame₃.locals.get? "collateralParam" = some (Model.collateralValue c.value) := by
        simp only [frame₃, wordLocal_get_ne _ _ _ _ (show "price" ≠ "collateralParam" from by decide),
          frame₂, healthCollateralFrame, store_get_self]
      have hsourceMath := healthArithmeticSource (fork := fork) (evm := evm') hf3 hcanon hi3 hc3
        (wordLocal_get ..) hi
      have hload : Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner =
          fun slot ↦ solcSlotWordAt slot σ' I := by
        funext slot
        change solcSlotWordAt slot evm'.accountMap evm'.executionEnv = _
        rw [hs'.env, ← hs'.accounts]
      simp only [hload] at hsourceMath
      rcases midnightHealthArithmetic hstack hi hlltv rd4 with
        ⟨hbad, hrev⟩ | ⟨hsafe, aw5, k5, C5, rd5⟩
      · rcases hsourceMath with ⟨_, hmath⟩ | ⟨hgood, _, _⟩
        · exact Or.inl ⟨ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2
            (ExecBlock.consNormal hsource hmath)), hrev⟩
        · exact False.elim (hbad hgood)
      · rcases hsourceMath with ⟨hbad, _⟩ | ⟨_, hmath, hf5⟩
        · exact False.elim (hbad hsafe)
        · exact Or.inr ⟨evm', σ', _, _, out, _, aw5, k5, C5,
            ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2
              (ExecBlock.consNormal hsource hmath)), hs', hf5,
            hm.preserve (hp.mono hheap), hfree', rd5⟩
  · have hcond : UInt256.isZero (UInt256.lt index (memLoad arrayPtr mem)) ≠ UInt256.ofNat 0 := by
      rw [ult_zero (by rw [hm.length, hcount]; omega)]
      decide
    have rd3 := midnightBlocks.midnight_block_19460_taken
      (by simp only [List.length_cons]; omega) hcond (by jump_dest) rd2
    have hrev := midnightBlocks.midnight_block_19161
      (by simp only [List.length_cons]; omega) rd3
    exact Or.inl ⟨ExecBlock.consNormal hs1 (ExecBlock.consRevert
      (ExecStmt.letDeclRevert (evalHealthCollateralAtRevert hf1.market (wordLocal_get ..) hindex))),
      hrev⟩

end Benchmarks.Midnight
