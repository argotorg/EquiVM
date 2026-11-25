import Benchmarks.Midnight.LiquidateIterationSource
import Benchmarks.Midnight.LiquidateIterationMemory
import Benchmarks.Midnight.LiquidateCollateralRead
import Benchmarks.Midnight.LiquidateOracleCall

variable {fork : Ethereum.Fork}

/-! One complete liquidation collateral iteration, with matching source and bytecode outcomes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightLiquidateLoopStep {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata data : ByteArray} {m : MarketData}
    {id seized repaid borrower mode bitmap maxDebt savedPrice originalDebt badDebt debtWord
      reverseRep rep dp dl receiverWord selector root budgetRoot aw : UInt256}
    {receiver callback : AccountAddress} {credit : Nat} {σ : AccountMap} {k C : Nat}
    {R : List UInt256}
    (hstack : R.length + 33 ≤ 1024) (hfork : fork ≥ .osaka)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hbits : bitmap.toNat < 2^128) (hnz : bitmap.toNat ≠ 0)
    (hroot : root.toNat + 160 < 2^64) (hlower : 832 ≤ root.toNat) (hm : 832 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hbitmap : memLoad (UInt256.ofNat 704) mem = bitmap)
    (hzero : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hf : LiquidateSourceFrame frame m id (calldataWord I.calldata 36)
      seized repaid borrower mode receiver callback data)
    (ha : LiquidateAccumulators frame bitmap maxDebt savedPrice originalDebt badDebt)
    (hs : SourceState s0 I σ evm) (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨5340⟩
      ([debtWord, reverseRep, rep, maxDebt, savedPrice, positionSlot id borrower, dp, dl,
        borrower, badDebt, receiverWord, mode, selector] ++ R) mem aw rdata σ k C) :
    (ExecBlock fork config frame evm liquidateLoopBody .reverted ∧ RDrev fork midnightBytecode g s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (frame' : Frame) (preMem out : ByteArray)
      (maxDebt' savedPrice' badDebt' aw' : UInt256) (k' C' : Nat),
      ExecBlock fork config frame evm liquidateLoopBody (.ok frame' evm') ∧
      SourceState s0 I σ' evm' ∧ accountStorageStateEq evm.accountMap evm'.accountMap ∧
      LiquidateSourceFrame frame' m id (calldataWord I.calldata 36)
        seized repaid borrower mode receiver callback data ∧
      LiquidateAccumulators frame' (bitmapClear bitmap (bitmapMsb bitmap))
        maxDebt' savedPrice' originalDebt badDebt' ∧
      MemoryPrefix mem preMem root.toNat ∧
      memLoad (UInt256.ofNat 64) preMem = root + UInt256.ofNat 160 ∧
      TransferBudget budgetRoot credit
        (liquidateBitmapMemory preMem (bitmapClear bitmap (bitmapMsb bitmap))) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨5340⟩
        ([debtWord, reverseRep, rep, maxDebt', savedPrice', positionSlot id borrower, dp, dl,
          borrower, badDebt', receiverWord, mode, selector] ++ R)
        (liquidateBitmapMemory preMem (bitmapClear bitmap (bitmapMsb bitmap))) aw' out σ' k' C' := by
  let index := bitmapMsb bitmap
  let f1 := wordLocal frame "i" index
  have hi128 : index.toNat < 128 := bitmapMsb_lt hnz hbits
  have hnonzero : bitmap ≠ ⟨0⟩ := fun hz ↦ hnz (congrArg UInt256.toNat hz)
  have rd1 := midnightBlocks.midnight_block_5340_taken
    (R := [debtWord, reverseRep, rep, maxDebt, savedPrice, positionSlot id borrower,
      dp, dl, borrower, badDebt, receiverWord, mode, selector] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [hbitmap, uint128Mask_computed, uint128Mask_clean hbits]; exact hnonzero)
    (by jump_dest) rd
  have hb1 := transferBudgetAt (root := budgetRoot) (credit := credit) rd1
    (by transfer_budget hb)
  have hs1 : ExecStmt fork config frame evm (liquidateLoopBody[0]!) (.ok f1 evm) :=
    healthMsbCall hf.contract ha.bitmap
  have hf1 : LiquidateSourceFrame f1 m id (calldataWord I.calldata 36)
      seized repaid borrower mode receiver callback data := hf.insert _ _ (by decide)
  have ha1 : LiquidateAccumulators f1 bitmap maxDebt savedPrice originalDebt badDebt :=
    ha.insert _ _ (by decide)
  rcases midnightLiquidateCollateralRead (R := [receiverWord, mode, selector] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hfork hd hbitmap hbits hnz (by omega) hfree hb1 rd1 with
    ⟨hbad, hrev⟩ | ⟨hi, aw2, k2, C2, hb2, rd2⟩
  · exact Or.inl ⟨ExecBlock.consNormal hs1 (ExecBlock.consRevert
      (ExecStmt.letDeclRevert (evalHealthCollateralAtRevert hf1.market
        (wordLocal_get frame "i" index) hbad))), hrev⟩
  let c := m.collaterals[index.toNat]
  let f2 : Frame := { f1 with locals := (f1.locals.insert "_collateralParam"
    (Model.collateralValue c.value)) }
  let mem2 := collateralRecordMemory mem root c
  let oracleRoot := root + UInt256.ofNat 128
  have hr : oracleRoot.toNat = root.toNat + 128 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hp2 : MemoryPrefix mem mem2 root.toNat := collateralRecordMemory_prefix mem root c
  have hw2 : MemoryWords mem2 root.toNat c.words :=
    collateralRecordMemory_words mem c (by change _ < 2^256; omega)
  have hs2 : ExecStmt fork config f1 evm (liquidateLoopBody[1]!) (.ok f2 evm) :=
    ExecStmt.letDecl (evalHealthCollateralAt hf1.market (wordLocal_get frame "i" index) hi)
  have hf2 : LiquidateSourceFrame f2 m id (calldataWord I.calldata 36)
      seized repaid borrower mode receiver callback data := hf1.insert _ _ (by decide)
  have ha2 : LiquidateAccumulators f2 bitmap maxDebt savedPrice originalDebt badDebt :=
    ha1.insert _ _ (by decide)
  have horacle : memLoad (root + UInt256.ofNat 96) mem2 = UInt256.ofNat c.oracle.val :=
    hw2.load_offset ⟨3, by simp [CollateralData.words]⟩ rfl
  have hz2 : memLoad (UInt256.ofNat 800) mem2 = ⟨0⟩ :=
    (hp2.load (UInt256.ofNat 800) (by decide) hlower hm).trans hzero
  rcases midnightLiquidateOracleCall (frame := f2) (root := oracleRoot)
      (receiver := .field (.var "_collateralParam") "oracle")
      (R := [savedPrice, positionSlot id borrower, dp, dl, borrower, debtWord,
        receiverWord, mode, selector] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by omega) (by omega) (hm.trans hp2.size)
      (collateralRecordMemory_free mem c (by omega)) hz2 horacle
      (evalLiquidateOracle (store_get_self _ _ _)) hs hb2 rd2 with
    ⟨hsource, hrev⟩ | ⟨evm', σ', out, aw3, k3, C3, hsource, hcall, hs', h32,
      hp3, hfree3, hb3, rd3⟩
  · exact Or.inl ⟨ExecBlock.consNormal hs1
      (ExecBlock.consNormal hs2 (ExecBlock.consRevert hsource)), hrev⟩
  let f3 := wordLocal f2 "price" (calldataWord out 0)
  have hf3 : LiquidateSourceFrame f3 m id (calldataWord I.calldata 36)
      seized repaid borrower mode receiver callback data := hf2.insert _ _ (by decide)
  have ha3 : LiquidateAccumulators f3 bitmap maxDebt savedPrice originalDebt badDebt :=
    ha2.insert _ _ (by decide)
  have hi3 : f3.locals.get? "i" = some (.int index.toNat) := by
    simp only [f3, wordLocal_get_ne _ _ _ _ (show "price" ≠ "i" from by decide),
      f2, store_get_ne _ _ (show ("_collateralParam" == "i") = false from rfl),
      f1, wordLocal_get]
  have hc3 : f3.locals.get? "_collateralParam" = some (Model.collateralValue c.value) := by
    simp only [f3, wordLocal_get_ne _ _ _ _
      (show "price" ≠ "_collateralParam" from by decide), f2, store_get_self]
  have hm3 := liquidateIterationMemory_properties mem c hroot (by omega) h32
  have hbitmap3 : memLoad (UInt256.ofNat 704) (liquidateIterationMemory mem root c out) = bitmap :=
    (hm3.1.load (UInt256.ofNat 704) (by decide)
      (by change 736 ≤ root.toNat; omega) (by change 736 ≤ mem.size; omega)).trans hbitmap
  obtain ⟨aw4, k4, C4, hb4, rd4⟩ := midnightLiquidatePriceChoice (by omega) hfork
    hm3.2.2.1 hbitmap3 hb3 rd3
  have hlltv : memLoad (root + UInt256.ofNat 32) (liquidateIterationMemory mem root c out) = c.lltv :=
    hm3.2.2.2.load_offset ⟨1, by simp [CollateralData.words]⟩ rfl
  have hcursor : memLoad (root + UInt256.ofNat 64) (liquidateIterationMemory mem root c out) =
      c.liquidationCursor := hm3.2.2.2.load_offset ⟨2, by simp [CollateralData.words]⟩ rfl
  have hmath := liquidateIterationSource (fork := fork) (evm := evm') hf3 ha3 hcanon hi3 hi128 hc3
    (wordLocal_get f2 "price" (calldataWord out 0))
  have hload : Stele.EVM.storageLoad evm' evm'.executionEnv.codeOwner =
      fun slot ↦ solcSlotWordAt slot σ' I := by
    funext slot
    change solcSlotWordAt slot evm'.accountMap evm'.executionEnv = _
    rw [hs'.env, ← hs'.accounts]
  simp only [hload] at hmath
  rcases midnightLiquidateLoopArithmetic (R := [receiverWord, mode, selector] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hfork hbitmap3 hi128 hlltv hcursor hb4 rd4 with
    ⟨hbad, hrev⟩ | ⟨hsafe, aw5, k5, C5, hb5, rd5⟩
  · rcases hmath with ⟨_, hsourceMath⟩ | ⟨hgood, _⟩
    · exact Or.inl ⟨ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2
        (ExecBlock.consNormal hsource hsourceMath)), hrev⟩
    · exact False.elim (hbad hgood)
  · rcases hmath with ⟨hbad, _⟩ | ⟨_, frame', hsourceMath, hf', ha'⟩
    · exact False.elim (hbad hsafe)
    · exact Or.inr ⟨evm', σ', frame', liquidateIterationMemory mem root c out, out,
        _, _, _, aw5, k5, C5, ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2
          (ExecBlock.consNormal hsource hsourceMath)), hs',
        typedCallViaEVM_static_accountStorageStateEq hcall, hf', ha', hm3.1, hm3.2.1, hb5, rd5⟩

end Benchmarks.Midnight
