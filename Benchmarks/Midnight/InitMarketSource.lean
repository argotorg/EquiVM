import Benchmarks.Midnight.InitMarketDefaultsSource

/-! Source execution of the ordered initialization writes and static-call rejection. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def initMarketAliasFrame (frame : Frame) (id : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "_marketState" (.storageRef (marketStateRef id) marketStateType) }

def initMarketFeesFrame (frame : Frame) (id word : UInt256) : Frame :=
  { (initMarketAliasFrame frame id) with locals :=
    (initMarketAliasFrame frame id).locals.insert "_defaultSettlementFeeCbp" (settlementFeesValue word) }

def initMarketStorageState (evm : EVM.State) (id : UInt256) (token : AccountAddress) : EVM.State :=
  initMarketContinuous (initSettlementState (initMarketTick evm id) id
    (initMarketDefaultWord evm id token) 7) id token

@[simp] theorem initMarketStorageState_env (evm : EVM.State) (id : UInt256) (token : AccountAddress) :
    (initMarketStorageState evm id token).executionEnv = evm.executionEnv := by
  simp only [initMarketStorageState, initMarketContinuous_env, initSettlementState_env, initMarketTick_env]

theorem initMarketAliasPrefix {frame : Frame} {evm : EVM.State} {id : UInt256}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    ABlock config evm frame (touchMarketInitBody.drop 7) (initMarketAliasFrame frame id)
      (touchMarketInitBody.drop 8) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letStorage ?_) h⟩
  exact resolveBytes32Mapping hbase hid (by rw [hc]; rfl)

theorem assignInitMarketTick {frame : Frame} {evm : EVM.State} {id : UInt256}
    (hget : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType)) :
    assignStorageRef? config frame evm .storage { base := "_marketState", steps :=
      [.field "tickSpacing"] } (.int 4) = .ok (frame, initMarketTick evm id) := by
  apply assignStorageAliasField (loc := packedUInt8Loc (solcMappingSlot ⟨1⟩ id + ⟨2⟩) 18)
    hget rfl rfl ?_ (storageLocStore_uint8_offset18_word evm _ ⟨4⟩)
  change some (StorageAddr.leaf (packedUInt8Loc (solcMappingSlot ⟨1⟩
    (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))) + ⟨2⟩) 18)) = _
  simp only [abiBytes32Width, keyValueToWord_fixedBytes32]

theorem initMarketSourceStatic {frame : Frame} {evm : EVM.State} {id : UInt256}
    (hc : frame.contract = contract) (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hperm : evm.executionEnv.perm = false) :
    ExecBlock config frame evm (touchMarketInitBody.drop 7) .staticViolation := by
  apply (initMarketAliasPrefix hc hbase hid).run
  exact ExecBlock.consStatic (ExecStmt.assignStatic (by simp only [evalExpr?, pure])
    (assignInitMarketTick (store_get_self _ _ _)) hperm)

theorem initMarketSourceFees {frame : Frame} {evm : EVM.State} {id word : UInt256} {result : ExecResult}
    (hget : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType))
    (hfees : frame.locals.get? "_defaultSettlementFeeCbp" = some (settlementFeesValue word))
    (hperm : evm.executionEnv.perm = true)
    (htail : ExecBlock config frame (initSettlementState evm id word 7)
      (touchMarketInitBody.drop 17) result) :
    ExecBlock config frame evm (touchMarketInitBody.drop 10) result := by
  have hstep (n : Fin 7) :
      ExecStmt config frame (initSettlementState evm id word n.val)
        (.assign .storage { base := "_marketState", steps :=
          [.field ("settlementFeeCbp" ++ toString n.val)] }
          (.index (.var "_defaultSettlementFeeCbp") (.intLit n.val)))
        (.ok frame (initSettlementState evm id word (n.val + 1))) := by
    apply ExecStmt.assign (Or.inr (by simpa only [initSettlementState_env] using hperm))
      (evalSettlementFeeIndex hfees n)
    simpa only [initSettlementState, Nat.mod_eq_of_lt n.isLt] using
      assignSettlementFee (evm := initSettlementState evm id word n.val) n (settlementFeeWord word n.val) hget
  exact ExecBlock.consNormal (hstep 0) (ExecBlock.consNormal (hstep 1)
    (ExecBlock.consNormal (hstep 2) (ExecBlock.consNormal (hstep 3)
      (ExecBlock.consNormal (hstep 4) (ExecBlock.consNormal (hstep 5)
        (ExecBlock.consNormal (hstep 6) htail))))))

def initDefaultContinuousWord (evm : EVM.State) (token : AccountAddress) : UInt256 :=
  Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨5⟩ (UInt256.ofNat token.val))

theorem evalInitDefaultContinuous {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hc : frame.contract = contract) (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hbase : frame.locals.get? "defaultContinuousFee" = none) :
    evalExpr? config frame evm (.storage { base := "defaultContinuousFee", steps :=
      [.mindex (.field (.var "market") "loanToken")] }) =
      .ok (.int (Int.ofNat (initDefaultContinuousWord evm m.loanToken).toNat % packedUInt32Modulus)) := by
  apply evalExpr_storage_scalar_value (loc := packedUInt32Loc
    (solcMappingSlot ⟨5⟩ (UInt256.ofNat m.loanToken.val)) 0 (by decide))
    (er := { base := "defaultContinuousFee", steps := [.mindex (.address m.loanToken)] })
    (t := .int packedUInt32Int) hbase
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalMarketLoanToken hm,
      EvalResult.ofOption, EvalResult.bind, bind, pure, valueToKey?]
  · rw [hc]; rfl
  · rfl
  · change some (StorageAddr.leaf (packedUInt32Loc
      (solcMappingSlot ⟨5⟩ (keyValueToWord (.address m.loanToken))) 0 (by decide))) = _
    rw [keyValueToWord_address]
  · dsimp only [packedUInt32Loc, packedUInt32Int]
    rw [storageLocLoad_uint_offset0 evm _ 4 ⟨32, by decide⟩ (by decide) (by decide)]
    congr 1
    rw [uland_toNat]
    change ((Nat.land (initDefaultContinuousWord evm m.loanToken).toNat (2^32-1) : Nat) : Int) = _
    rw [nat_land_mask_eq_mod]
    norm_num only [packedUInt32Modulus, Int.natCast_mod, Int.natCast_pow,
      Int.ofNat_eq_natCast]

theorem assignInitMarketContinuous {frame : Frame} {evm : EVM.State} {id : UInt256}
    (token : AccountAddress)
    (hget : frame.locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType)) :
    assignStorageRef? config frame evm .storage { base := "_marketState", steps :=
      [.field "continuousFee"] }
      (.int (Int.ofNat (initDefaultContinuousWord evm token).toNat % packedUInt32Modulus)) =
      .ok (frame, initMarketContinuous evm id token) := by
  apply assignStorageAliasField (loc := packedUInt32Loc (solcMappingSlot ⟨1⟩ id + ⟨2⟩) 14 (by decide))
    hget rfl rfl ?_ (storageLocStore_uint32_offset14_word evm _ (initDefaultContinuousWord evm token))
  change some (StorageAddr.leaf (packedUInt32Loc (solcMappingSlot ⟨1⟩
    (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))) + ⟨2⟩) 14 (by decide))) = _
  simp only [abiBytes32Width, keyValueToWord_fixedBytes32]

theorem initMarketAliasFrame_get (frame : Frame) (id : UInt256) (name : Ident)
    (hn : name ≠ "_marketState") :
    (initMarketAliasFrame frame id).locals.get? name = frame.locals.get? name := by
  simp [initMarketAliasFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    hn, Ne.symm hn]

theorem initMarketFeesFrame_get (frame : Frame) (id word : UInt256) (name : Ident)
    (hn : name ≠ "_marketState") (hd : name ≠ "_defaultSettlementFeeCbp") :
    (initMarketFeesFrame frame id word).locals.get? name = frame.locals.get? name := by
  simp [initMarketFeesFrame, initMarketAliasFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, hn, Ne.symm hn, hd, Ne.symm hd]

theorem initMarketFeesFrame_alias (frame : Frame) (id word : UInt256) :
    (initMarketFeesFrame frame id word).locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType) := by
  simp [initMarketFeesFrame, initMarketAliasFrame, Std.HashMap.getElem_insert]

theorem initMarketSourceStores {frame : Frame} {evm : EVM.State} {m : MarketData} {id : UInt256}
    {result : ExecResult}
    (hc : frame.contract = contract) (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hbase : frame.locals.get? "marketState" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hd : frame.locals.get? "defaultSettlementFeeCbp" = none)
    (hcont : frame.locals.get? "defaultContinuousFee" = none)
    (hperm : evm.executionEnv.perm = true)
    (htail : ExecBlock config (initMarketFeesFrame frame id (initMarketDefaultWord evm id m.loanToken))
      (initMarketStorageState evm id m.loanToken) (touchMarketInitBody.drop 18) result) :
    ExecBlock config frame evm (touchMarketInitBody.drop 7) result := by
  let d := initMarketDefaultWord evm id m.loanToken
  let f := initMarketFeesFrame frame id d
  let s := initSettlementState (initMarketTick evm id) id d 7
  apply (initMarketAliasPrefix hc hbase hid).run
  refine ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
    (by simp only [evalExpr?, pure]) (assignInitMarketTick (store_get_self _ _ _))) ?_
  have hread : evalExpr? config (initMarketAliasFrame frame id) (initMarketTick evm id)
      (.storage { base := "defaultSettlementFeeCbp", steps :=
        [.mindex (.field (.var "market") "loanToken")] }) = .ok (settlementFeesValue d) := by
    simpa only [initDefaultFeeWord, initMarketDefaultWord, initMarketTick_env, d] using
      evalInitDefaultFees (frame := initMarketAliasFrame frame id) (evm := initMarketTick evm id) hc
        (by rw [initMarketAliasFrame_get _ _ _ (by decide)]; exact hm)
        (by rw [initMarketAliasFrame_get _ _ _ (by decide)]; exact hd)
  refine ExecBlock.consNormal (ExecStmt.letDecl hread) ?_
  apply initMarketSourceFees (initMarketFeesFrame_alias frame id d) (store_get_self _ _ _)
    (by simpa only [initMarketTick_env] using hperm)
  have hmc : f.locals.get? "market" = some (Model.marketValue m.value) := by
    rw [initMarketFeesFrame_get _ _ _ _ (by decide) (by decide)]; exact hm
  have hdc : f.locals.get? "defaultContinuousFee" = none := by
    rw [initMarketFeesFrame_get _ _ _ _ (by decide) (by decide)]; exact hcont
  refine ExecBlock.consNormal (ExecStmt.assign (Or.inr ?_)
    (evalInitDefaultContinuous (frame := f) (evm := s) hc hmc hdc)
    (assignInitMarketContinuous m.loanToken (initMarketFeesFrame_alias frame id d))) htail
  simpa only [s, initSettlementState_env, initMarketTick_env] using hperm

end Benchmarks.Midnight
