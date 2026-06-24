import Examples.BlindAuction.Beneficiary
import Examples.BlindAuction.Ended
import Examples.BlindAuction.Storage
import Reasoning.Refinement
import Reasoning.SolmBody
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace BlindAuction

/-! ## `auctionEnd()` local bridge facts -/

def auctionEndTimestampWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.header.timestamp

def auctionEndRevealEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)

def auctionEndBeneficiaryRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

def auctionEndBeneficiaryWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (auctionEndBeneficiaryRawWord σ I) solcAddrMask

def auctionEndHighestBidderRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨5⟩ ⟨0⟩)

def auctionEndWinnerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (auctionEndHighestBidderRawWord σ I) solcAddrMask

def auctionEndHighestBidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨6⟩ ⟨0⟩)

def auctionEndEndedRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨3⟩ ⟨0⟩)

def auctionEndEndedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (auctionEndEndedRawWord σ I) ⟨255⟩

def auctionEndSetEndedWord (old : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot ⟨255⟩)) ⟨1⟩

def auctionEndAfterEndedMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨3⟩ (auctionEndSetEndedWord (auctionEndEndedRawWord σ I))

def auctionEndedTopic : UInt256 :=
  ⟨0xdaec4582d5d9595688c8c98545fdd1c696d41c6aeaeb636737e84ed2f5c00eda⟩

noncomputable def auctionEndEventMemWinner (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (auctionEndWinnerWord σ I)).write 0 solcFreePtrMem 128 32

noncomputable def auctionEndEventMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (auctionEndHighestBidWord σ I)).write 0
    (auctionEndEventMemWinner σ I) 160 32

def auctionEndAfterEndedState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩
    (auctionEndSetEndedWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩))

def auctionEndBeneficiaryRawWordState (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩

def auctionEndBeneficiaryWordState (evm : EVM.State) : UInt256 :=
  UInt256.land (auctionEndBeneficiaryRawWordState evm) solcAddrMask

def auctionEndHighestBidWordState (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩

def auctionEndEndedRawWordState (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩

def auctionEndEndedWordState (evm : EVM.State) : UInt256 :=
  UInt256.land (auctionEndEndedRawWordState evm) ⟨255⟩

def auctionEndCallStore (success : Bool) (out : ByteArray) : Store :=
  ((∅ : Store).insert "success" (.bool success)).insert "_data" (.bytes out)

theorem auctionEndEventMemWinner_size (σ : AccountMap) (I : ExecutionEnv) :
    (auctionEndEventMemWinner σ I).size = 160 := by
  simpa [auctionEndEventMemWinner, solcReturnMem] using
    solcReturnMem_size (auctionEndWinnerWord σ I)

theorem auctionEndEventMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (auctionEndEventMem σ I).size = 192 := by
  unfold auctionEndEventMem
  rw [toByteArray_write_eq _ _ 160 (by rw [auctionEndEventMemWinner_size])
      (by rw [auctionEndEventMemWinner_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, auctionEndEventMemWinner_size,
    zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem auctionEndEventMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (auctionEndEventMem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold auctionEndEventMem
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size])
    (by rw [auctionEndEventMemWinner_size]) (by omega)]
  simpa [auctionEndEventMemWinner, solcReturnMem] using
    solcReturnMem_read64 (auctionEndWinnerWord σ I)

theorem auctionEndEventMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (auctionEndEventMem σ I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((auctionEndEventMem σ I).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [auctionEndEventMem_size]; decide) (by decide)
    (auctionEndEventMem_read64 σ I)

theorem auctionEndAddress_ofNat_toNat (w : UInt256) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat =
      AccountAddress.ofUInt256 (UInt256.land w solcAddrMask) := by
  apply Fin.ext
  unfold AccountAddress.ofNat AccountAddress.ofUInt256
  simp [UInt256.toNat]

theorem auctionEndAddress_from_toNat (a : AccountAddress) :
    EVM.address a.toNat = a := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt a.isLt

theorem auctionEndAccountMapEquiv_balance {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (addr : AccountAddress) :
    (σ.find? addr |>.elim ⟨0⟩ (·.balance)) =
      (τ.find? addr |>.elim ⟨0⟩ (·.balance)) := by
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ, accountEquiv] at hστ ⊢
  exact hστ.2.1

theorem blindAuctionStorageLocStore_bool_true_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (blindAuctionBoolLoc slot) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.lnot ⟨255⟩)) ⟨1⟩)) := by
  simpa [blindAuctionBoolLoc, boolOffset0Loc] using storageLocStore_bool_true_offset0 evm slot

theorem blindAuctionStorageLocLoad_bool_offset0_false (evm : EVM.State) (slot : UInt256)
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm (blindAuctionBoolLoc slot) = .bool false := by
  simpa [blindAuctionBoolLoc, boolOffset0Loc] using
    storageLocLoad_bool_offset0_false evm slot hzero

theorem blindAuctionStorageLocLoad_bool_offset0_true (evm : EVM.State) (slot : UInt256)
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm (blindAuctionBoolLoc slot) = .bool true := by
  simpa [blindAuctionBoolLoc, boolOffset0Loc] using
    storageLocLoad_bool_offset0_true evm slot hnz

theorem auctionEndCallStore_success_get (success : Bool) (out : ByteArray) :
    (auctionEndCallStore success out)["success"]? = some (.bool success) := by
  change (auctionEndCallStore success out).get? "success" = some (.bool success)
  unfold auctionEndCallStore
  rw [store_get_ne]
  · exact store_get_self _ _ _
  · decide

theorem evalExpr_auctionEnd_revealEnd (evm : EVM.State) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := ∅ } evm
      (.storage revealEndRef) =
        .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)) := by
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := ∅ } evm revealEndRef =
      .ok { base := "revealEnd", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, revealEndRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? blindAuctionContract.storage
      ({ base := "revealEnd", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := by simp) (her := her)
    (hty := hty) (hloc := blindAuctionConfig_storage_revealEnd)]
  rw [blindAuctionStorageLocLoad_uint256]

theorem evalExpr_auctionEnd_beneficiary (evm : EVM.State) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := ∅ } evm
      (.storage beneficiaryRef) =
        .ok (.address (AccountAddress.ofNat (auctionEndBeneficiaryWordState evm).toNat)) := by
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := ∅ } evm beneficiaryRef =
      .ok { base := "beneficiary", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, beneficiaryRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? blindAuctionContract.storage
      ({ base := "beneficiary", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address) (hbase := by simp) (her := her)
    (hty := hty) (hloc := blindAuctionConfig_storage_beneficiary)]
  rw [beneficiaryStorageLocLoad_address_offset0]
  rfl

theorem evalExpr_auctionEnd_highestBid (evm : EVM.State) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := ∅ } evm
      (.storage highestBidRef) =
        .ok (.int (Int.ofNat (auctionEndHighestBidWordState evm).toNat)) := by
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := ∅ } evm highestBidRef =
      .ok { base := "highestBid", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, highestBidRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? blindAuctionContract.storage
      ({ base := "highestBid", steps := [] } : EvaledStorageRef) =
      some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := by simp) (her := her)
    (hty := hty) (hloc := blindAuctionConfig_storage_highestBid)]
  rw [blindAuctionStorageLocLoad_uint256]
  rfl

theorem evalExpr_auctionEnd_ended_false (evm : EVM.State)
    (hzero : auctionEndEndedWordState evm = ⟨0⟩) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := ∅ } evm
      (.storage endedRef) = .ok (.bool false) := by
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := ∅ } evm endedRef =
      .ok { base := "ended", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, endedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? blindAuctionContract.storage
      ({ base := "ended", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool) (hbase := by simp) (her := her)
    (hty := hty) (hloc := blindAuctionConfig_storage_ended)]
  simpa [auctionEndEndedWordState, auctionEndEndedRawWordState] using
    blindAuctionStorageLocLoad_bool_offset0_false evm ⟨3⟩ hzero

theorem evalExpr_auctionEnd_ended_true (evm : EVM.State)
    (hnz : auctionEndEndedWordState evm ≠ ⟨0⟩) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := ∅ } evm
      (.storage endedRef) = .ok (.bool true) := by
  have her : evalStorageRef blindAuctionConfig
      { contract := blindAuctionContract, locals := ∅ } evm endedRef =
      .ok { base := "ended", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, endedRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? blindAuctionContract.storage
      ({ base := "ended", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
    decide
  rw [evalExpr_storage_scalar (t := .bool) (hbase := by simp) (her := her)
    (hty := hty) (hloc := blindAuctionConfig_storage_ended)]
  simpa [auctionEndEndedWordState, auctionEndEndedRawWordState] using
    blindAuctionStorageLocLoad_bool_offset0_true evm ⟨3⟩ hnz

theorem evalExpr_auctionEnd_time_true (evm : EVM.State)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := ∅ } evm
      (.binary .gt now (.storage revealEndRef)) = .ok (.bool true) := by
  simp only [evalExpr?, now, envValue, evalExpr_auctionEnd_revealEnd, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_auctionEnd_time_false (evm : EVM.State)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := ∅ } evm
      (.binary .gt now (.storage revealEndRef)) = .ok (.bool false) := by
  simp only [evalExpr?, now, envValue, evalExpr_auctionEnd_revealEnd, bind,
    EvalResult.bind, pure]
  simpa [evalBinaryOp?, UInt256.toNat] using htime

theorem evalExpr_auctionEnd_not_ended_true (evm : EVM.State)
    (hzero : auctionEndEndedWordState evm = ⟨0⟩) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := ∅ } evm
      (.unary .not (.storage endedRef)) = .ok (.bool true) := by
  rw [evalExpr?]
  rw [evalExpr_auctionEnd_ended_false evm hzero]
  rfl

theorem evalExpr_auctionEnd_not_ended_false (evm : EVM.State)
    (hnz : auctionEndEndedWordState evm ≠ ⟨0⟩) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := ∅ } evm
      (.unary .not (.storage endedRef)) = .ok (.bool false) := by
  rw [evalExpr?]
  rw [evalExpr_auctionEnd_ended_true evm hnz]
  rfl

theorem evalExpr_auctionEnd_emptyBytes (evm : EVM.State) :
    evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := ∅ } evm
      (.newBytes (.intLit 0)) = .ok (.bytes ByteArray.empty) := by
  simp [evalExpr?, pure, bind, EvalResult.bind]
  rfl

theorem evalExpr_auctionEnd_success (evm : EVM.State) (success : Bool) (out : ByteArray) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract, locals := auctionEndCallStore success out } evm
      (.var "success") = .ok (.bool success) := by
  rw [evalExpr?]
  simp [EvalResult.ofOption, auctionEndCallStore_success_get]

theorem auctionEndAssignEnded (evm : EVM.State) :
    assignStorageRef? blindAuctionConfig { contract := blindAuctionContract, locals := ∅ } evm
      .storage endedRef (.bool true) =
        .ok ({ contract := blindAuctionContract, locals := ∅ }, auctionEndAfterEndedState evm) := by
  apply assignStorageRef_storage_scalar_value (ty := boolSt)
      (hbase := by simp)
      (her := by
        simp [evalStorageRef, evalStorageRefSteps, endedRef, EvalResult.bind, pure, bind])
      (hty := by decide)
      (hloc := blindAuctionConfig_storage_ended)
      (hscalar := by trivial)
  rw [blindAuctionStorageLocStore_bool_true_offset0]
  rfl

theorem blindAuctionAuctionEndBodyReverts_time (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (htime :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm ∅
      auctionEndTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold auctionEndTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_auctionEnd_time_false evm htime))

theorem blindAuctionAuctionEndBodyReverts_ended (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hnz : auctionEndEndedWordState evm ≠ ⟨0⟩) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm ∅
      auctionEndTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold auctionEndTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_auctionEnd_time_true evm htime)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_auctionEnd_not_ended_false evm hnz))

theorem blindAuctionAuctionEndBodyReverts_callFailure
    (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hended : auctionEndEndedWordState evm = ⟨0⟩)
    (hcall :
      callViaEVM (auctionEndAfterEndedState evm)
        (EVM.address
          (AccountAddress.ofNat
            (auctionEndBeneficiaryWordState (auctionEndAfterEndedState evm)).toNat))
        (Int.ofNat (auctionEndHighestBidWordState (auctionEndAfterEndedState evm)).toNat)
        ByteArray.empty (false, evm', out)) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm ∅
      auctionEndTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  unfold auctionEndTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_auctionEnd_time_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_auctionEnd_not_ended_true evm hended)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (auctionEndAssignEnded evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallFailure
      (evalExpr_auctionEnd_beneficiary (auctionEndAfterEndedState evm))
      (evalExpr_auctionEnd_highestBid (auctionEndAfterEndedState evm))
      (evalExpr_auctionEnd_emptyBytes (auctionEndAfterEndedState evm)) hcall) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_auctionEnd_success evm' false out))

theorem blindAuctionAuctionEndBodyReturns_callSuccess
    (evm evm' : EVM.State) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (htime :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hended : auctionEndEndedWordState evm = ⟨0⟩)
    (hcall :
      callViaEVM (auctionEndAfterEndedState evm)
        (EVM.address
          (AccountAddress.ofNat
            (auctionEndBeneficiaryWordState (auctionEndAfterEndedState evm)).toNat))
        (Int.ofNat (auctionEndHighestBidWordState (auctionEndAfterEndedState evm)).toNat)
        ByteArray.empty (true, evm', out)) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm ∅ auctionEndTransition.body
      (.returned { contract := blindAuctionContract, locals := auctionEndCallStore true out }
        evm' none) := by
  refine ExecFuncBody.execBlockOK ?_
  unfold auctionEndTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_auctionEnd_time_true evm htime)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_auctionEnd_not_ended_true evm hended)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (auctionEndAssignEnded evm)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.lowLevelCallSuccess
      (evalExpr_auctionEnd_beneficiary (auctionEndAfterEndedState evm))
      (evalExpr_auctionEnd_highestBid (auctionEndAfterEndedState evm))
      (evalExpr_auctionEnd_emptyBytes (auctionEndAfterEndedState evm)) hcall) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_auctionEnd_success evm' true out)) ?_
  exact ExecBlock.nil

theorem auctionEndAfterEndedState_accountMap (evm : EVM.State) :
    (auctionEndAfterEndedState evm).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨3⟩
        (auctionEndSetEndedWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)) := by
  simp [auctionEndAfterEndedState, blindAuctionStorageStore_accountMap]

theorem auctionEndAfterEndedState_createdAccounts (evm : EVM.State) :
    (auctionEndAfterEndedState evm).createdAccounts = evm.createdAccounts := by
  simp [auctionEndAfterEndedState, blindAuctionStorageStore_createdAccounts]

theorem auctionEndAfterEndedState_executionEnv (evm : EVM.State) :
    (auctionEndAfterEndedState evm).executionEnv = evm.executionEnv := by
  simp [auctionEndAfterEndedState, storageStore_executionEnv]

theorem auctionEndAfterEndedState_originalMap (evm : EVM.State) :
    (auctionEndAfterEndedState evm).σ₀ = evm.σ₀ := by
  unfold auctionEndAfterEndedState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem auctionEndAfterEndedState_substate (evm : EVM.State) :
    (auctionEndAfterEndedState evm).substate = evm.substate := by
  unfold auctionEndAfterEndedState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem auctionEndAfterEndedState_genesisBlockHeader (evm : EVM.State) :
    (auctionEndAfterEndedState evm).genesisBlockHeader = evm.genesisBlockHeader := by
  unfold auctionEndAfterEndedState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem auctionEndAfterEndedState_blocks (evm : EVM.State) :
    (auctionEndAfterEndedState evm).blocks = evm.blocks := by
  unfold auctionEndAfterEndedState Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? evm.executionEnv.codeOwner <;> simp [Option.option, State.setAccount]

theorem auctionEndAfterEndedState_accountMap_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    (auctionEndAfterEndedState (initState cA gh bl σ σ₀ g A I)).accountMap =
      auctionEndAfterEndedMap σ I := by
  simp [auctionEndAfterEndedState_accountMap, auctionEndAfterEndedMap,
    auctionEndEndedRawWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage]

theorem auctionEndBeneficiaryWordState_afterEnded_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    auctionEndBeneficiaryWordState
      (auctionEndAfterEndedState (initState cA gh bl σ σ₀ g A I)) =
      auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I := by
  unfold auctionEndBeneficiaryWordState auctionEndBeneficiaryRawWordState
    auctionEndBeneficiaryWord auctionEndBeneficiaryRawWord
  unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
  rw [auctionEndAfterEndedState_executionEnv, auctionEndAfterEndedState_accountMap_init]
  simp [initState]

theorem auctionEndHighestBidWordState_afterEnded_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    auctionEndHighestBidWordState
      (auctionEndAfterEndedState (initState cA gh bl σ σ₀ g A I)) =
      auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I := by
  unfold auctionEndHighestBidWordState auctionEndHighestBidWord
  unfold Solm.EVM.storageLoad State.lookupAccount Account.lookupStorage
  rw [auctionEndAfterEndedState_executionEnv, auctionEndAfterEndedState_accountMap_init]
  simp [initState]

theorem auctionEndAfterEndedState_balance_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    (auctionEndAfterEndedMap σ I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)) =
      ((auctionEndAfterEndedState (initState cA gh bl σ σ₀ g A I)).accountMap.find?
        (auctionEndAfterEndedState (initState cA gh bl σ σ₀ g A I)).executionEnv.codeOwner
          |>.elim ⟨0⟩ (·.balance)) := by
  rw [auctionEndAfterEndedState_executionEnv, auctionEndAfterEndedState_accountMap_init]
  rfl

theorem auctionEndAfterEndedState_EVMStateEquiv {evmE evmS : EVM.State}
    (hσ : EVMStateEquiv evmE evmS) :
    EVMStateEquiv (auctionEndAfterEndedState evmE) (auctionEndAfterEndedState evmS) := by
  unfold auctionEndAfterEndedState
  have hval :
      auctionEndSetEndedWord (Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner ⟨3⟩) =
        auctionEndSetEndedWord (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨3⟩) := by
    rw [hσ.storageLoad_codeOwner ⟨3⟩]
  exact hσ.storageStore_codeOwner ⟨3⟩ hval

theorem auctionEndEVMStateEquiv_balance_codeOwner {evmE evmS : EVM.State}
    (hσ : EVMStateEquiv evmE evmS) :
    (evmE.accountMap.find? evmE.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) =
      (evmS.accountMap.find? evmS.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) := by
  rw [hσ.executionEnv]
  exact auctionEndAccountMapEquiv_balance hσ.accountMap evmS.executionEnv.codeOwner

theorem blindAuctionX_auctionEnd_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨256⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd256⟩ := hreach
  have rd264 := evm_run rd256 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨267⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd264.revertStub (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionX_auctionEndToBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨256⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨566⟩ [⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd256⟩ := hreach
  exact ⟨_, _, evm_run rd256 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨267⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨276⟩, push2 ⟨566⟩, jump (by jump_dest)]⟩

noncomputable def auctionEndTimeRevertMem (arg errSel : UInt256) : ByteArray :=
  (UInt256.toByteArray arg).write 0 (solcReturnMem errSel) 132 32

theorem auctionEndTimeRevertMem_size (arg errSel : UInt256) :
    (auctionEndTimeRevertMem arg errSel).size = 164 := by
  unfold auctionEndTimeRevertMem
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [solcReturnMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, solcReturnMem_size, toByteArray_size]
  rw [show ((solcReturnMem errSel).extract (132 + 32) 160).size = 0 by
    rw [ByteArray.size_extract, solcReturnMem_size]
    norm_num]
  omega

theorem auctionEndTimeRevertMem_mload64 (arg errSel : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (auctionEndTimeRevertMem arg errSel).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((auctionEndTimeRevertMem arg errSel).readWithPadding
         (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [auctionEndTimeRevertMem_size]; decide) (by decide) (by
    unfold auctionEndTimeRevertMem
    rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [solcReturnMem_size]; omega) (by omega)]
    exact solcReturnMem_read64 errSel)

theorem blindAuctionX_auctionEnd_timeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨256⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndTimestampWord I).toNat ≤ (auctionEndRevealEndWord σ I).toNat) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd566⟩ := blindAuctionX_auctionEndToBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach
  have rd569 := evm_run rd566 with [jumpdest, push1 ⟨2⟩]
  obtain ⟨_, _, rd570₀⟩ := rd569.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd570⟩ : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨570⟩
      [auctionEndRevealEndWord σ I, ⟨276⟩, blindAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionEndRevealEndWord, initState] using rd570₀⟩
  have hgt : UInt256.gt (auctionEndTimestampWord I) (auctionEndRevealEndWord σ I) = ⟨0⟩ :=
    ugt_zero htime
  have rd571dup := evm_run rd570 with [dup1]
  have rd572 := RD.timestamp rd571dup (by decide) (by evm_ov)
  have rd573₀ := evm_run rd572 with [gt]
  have rd573 := rd573₀
  rw [show UInt256.gt (UInt256.ofNat I.header.timestamp) (auctionEndRevealEndWord σ I) =
      ⟨0⟩ from by simpa [auctionEndTimestampWord] using hgt] at rd573
  have rd577 := evm_run rd573 with [push2 ⟨609⟩, jumpiNT (by decide)]
  let errSel : UInt256 := UInt256.shiftLeft (⟨0x0a8d68c9⟩ : UInt256) ⟨226⟩
  have rd590 := evm_run rd577 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x0a8d68c9⟩, push1 ⟨226⟩, shl, dup2,
    raw mstore 6 (solcReturnMem errSel) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd600 := evm_run rd590 with [
    push1 ⟨4⟩, dup2, add, dup3, swap1,
    raw mstore 3 (auctionEndTimeRevertMem (auctionEndRevealEndWord σ I) errSel)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add, jumpdest]
  have rd608 := evm_run rd600 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (auctionEndTimeRevertMem_mload64 (auctionEndRevealEndWord σ I) errSel)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact rd608.rev 0 (by decide) mem_cost (by evm_ov)

theorem blindAuctionX_auctionEnd_afterTime {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨256⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndRevealEndWord σ I).toNat < (auctionEndTimestampWord I).toNat) :
    ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨609⟩
      [auctionEndRevealEndWord σ I, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd566⟩ := blindAuctionX_auctionEndToBody (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach
  have rd569 := evm_run rd566 with [jumpdest, push1 ⟨2⟩]
  obtain ⟨_, _, rd570₀⟩ := rd569.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd570⟩ : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨570⟩
      [auctionEndRevealEndWord σ I, ⟨276⟩, blindAuctionSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionEndRevealEndWord, initState] using rd570₀⟩
  have hgt : UInt256.gt (auctionEndTimestampWord I) (auctionEndRevealEndWord σ I) = ⟨1⟩ :=
    ugt_one htime
  have rd571dup := evm_run rd570 with [dup1]
  have rd572 := RD.timestamp rd571dup (by decide) (by evm_ov)
  have rd573₀ := evm_run rd572 with [gt]
  have rd573 := rd573₀
  rw [show UInt256.gt (UInt256.ofNat I.header.timestamp) (auctionEndRevealEndWord σ I) =
      ⟨1⟩ from by simpa [auctionEndTimestampWord] using hgt] at rd573
  exact ⟨_, _, evm_run rd573 with [push2 ⟨609⟩, jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem blindAuctionX_auctionEnd_endedRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨256⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndRevealEndWord σ I).toNat < (auctionEndTimestampWord I).toNat)
    (hended : auctionEndEndedWord σ I ≠ ⟨0⟩) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd609⟩ := blindAuctionX_auctionEnd_afterTime (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach htime
  have rd612 := evm_run rd609 with [jumpdest, push1 ⟨3⟩]
  obtain ⟨_, _, rd613₀⟩ := rd612.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd613⟩ : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨613⟩
      [auctionEndEndedRawWord σ I, auctionEndRevealEndWord σ I, ⟨276⟩,
        blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionEndEndedRawWord, initState] using rd613₀⟩
  have rd617₀ := evm_run rd613 with [push1 ⟨255⟩, and, iszero]
  have rd617 := rd617₀
  have hmask : UInt256.land ⟨255⟩ (auctionEndEndedRawWord σ I) =
      auctionEndEndedWord σ I := by
    rw [Reasoning.Theory.u256_land_comm ⟨255⟩ (auctionEndEndedRawWord σ I)]
    rfl
  rw [hmask, isZero_eq_zero_of_ne hended] at rd617
  have rd621 := evm_run rd617 with [push2 ⟨645⟩, jumpiNT (by decide)]
  let errSel : UInt256 := UInt256.shiftLeft (⟨0x0c39fb9f⟩ : UInt256) ⟨227⟩
  have rd634 := evm_run rd621 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x0c39fb9f⟩, push1 ⟨227⟩, shl, dup2,
    raw mstore 6 (solcReturnMem errSel) (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd644 := evm_run rd634 with [
    push1 ⟨4⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost (solcReturnMem_mload64 errSel) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  exact rd644.rev 0 (by decide) mem_cost (by evm_ov)

theorem blindAuctionX_auctionEnd_afterNotEnded {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨256⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndRevealEndWord σ I).toNat < (auctionEndTimestampWord I).toNat)
    (hended : auctionEndEndedWord σ I = ⟨0⟩) :
    ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨645⟩
      [auctionEndRevealEndWord σ I, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd609⟩ := blindAuctionX_auctionEnd_afterTime (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach htime
  have rd612 := evm_run rd609 with [jumpdest, push1 ⟨3⟩]
  obtain ⟨_, _, rd613₀⟩ := rd612.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd613⟩ : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨613⟩
      [auctionEndEndedRawWord σ I, auctionEndRevealEndWord σ I, ⟨276⟩,
        blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionEndEndedRawWord, initState] using rd613₀⟩
  have rd617₀ := evm_run rd613 with [push1 ⟨255⟩, and, iszero]
  have rd617 := rd617₀
  have hmask : UInt256.land ⟨255⟩ (auctionEndEndedRawWord σ I) =
      auctionEndEndedWord σ I := by
    rw [Reasoning.Theory.u256_land_comm ⟨255⟩ (auctionEndEndedRawWord σ I)]
    rfl
  rw [hmask, hended, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd617
  exact ⟨_, _, evm_run rd617 with [push2 ⟨645⟩, jumpiT one_ne_zero_uint (by jump_dest)]⟩

theorem blindAuctionX_auctionEnd_afterStoreAndLog {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨256⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndRevealEndWord σ I).toNat < (auctionEndTimestampWord I).toNat)
    (hended : auctionEndEndedWord σ I = ⟨0⟩) :
    ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨733⟩
      [auctionEndRevealEndWord σ I, ⟨276⟩, blindAuctionSelWord I]
      (auctionEndEventMem σ I) (UInt256.ofNat 6) ByteArray.empty
      (cA, auctionEndAfterEndedMap σ I) k C := by
  obtain ⟨_, _, rd645⟩ := blindAuctionX_auctionEnd_afterNotEnded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach htime hended
  have rd648 := evm_run rd645 with [jumpdest, push1 ⟨5⟩]
  obtain ⟨_, _, rd649₀⟩ := rd648.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd649⟩ : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨649⟩
      [auctionEndHighestBidderRawWord σ I, auctionEndRevealEndWord σ I, ⟨276⟩,
        blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionEndHighestBidderRawWord, initState] using rd649₀⟩
  have rd651 := evm_run rd649 with [push1 ⟨6⟩]
  obtain ⟨_, _, rd652₀⟩ := rd651.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd652⟩ : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨652⟩
      [auctionEndHighestBidWord σ I, auctionEndHighestBidderRawWord σ I,
        auctionEndRevealEndWord σ I, ⟨276⟩, blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionEndHighestBidWord, initState] using rd652₀⟩
  have rd656 := evm_run rd652 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rd667₀ := evm_run rd656 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap4, and]
  have rd667 := rd667₀
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  rw [haddrMask] at rd667
  have rd669 := evm_run rd667 with [
    dup4,
    raw mstore 6 (auctionEndEventMemWinner σ I) (UInt256.ofNat 5) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd677 := evm_run rd669 with [
    push1 ⟨32⟩, dup4, add, swap2, swap1, swap2,
    raw mstore 3 (auctionEndEventMem σ I) (UInt256.ofNat 6) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd711 := rd677.pushConst auctionEndedTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd719 := evm_run rd711 with [
    swap2, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (auctionEndEventMem_mload64 σ I) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have hlen64 : ((⟨128⟩ : UInt256) + ⟨64⟩).sub ⟨128⟩ = ⟨64⟩ := by
    decide
  have rd719' := rd719
  rw [hlen64] at rd719'
  have rd720 := RD.log1 0 (UInt256.ofNat 6) rd719' (by decide) hperm
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by decide) (by evm_ov)
  have rd723 := evm_run rd720 with [push1 ⟨3⟩, dup1]
  obtain ⟨_, _, rd724₀⟩ := rd723.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd724⟩ : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨724⟩
      [auctionEndEndedRawWord σ I, ⟨3⟩, auctionEndRevealEndWord σ I, ⟨276⟩,
        blindAuctionSelWord I]
      (auctionEndEventMem σ I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [auctionEndEndedRawWord, initState] using rd724₀⟩
  have rd728₀ := evm_run rd724 with [push1 ⟨255⟩, not, and, push1 ⟨1⟩]
  have rd728 := rd728₀
  have hland : UInt256.land (UInt256.lnot ⟨255⟩) (auctionEndEndedRawWord σ I) =
      UInt256.land (auctionEndEndedRawWord σ I) (UInt256.lnot ⟨255⟩) := by
    exact Reasoning.Theory.u256_land_comm (UInt256.lnot ⟨255⟩) (auctionEndEndedRawWord σ I)
  rw [hland] at rd728
  have rd731₀ := RD.lor rd728 (by decide) (by evm_ov)
  have rd731 := rd731₀
  have hlor : UInt256.lor ⟨1⟩
        (UInt256.land (auctionEndEndedRawWord σ I) (UInt256.lnot ⟨255⟩)) =
      auctionEndSetEndedWord (auctionEndEndedRawWord σ I) := by
    unfold auctionEndSetEndedWord
    exact u256_lor_comm ⟨1⟩
      (UInt256.land (auctionEndEndedRawWord σ I) (UInt256.lnot ⟨255⟩))
  rw [hlor] at rd731
  have rd732 := evm_run rd731 with [swap1]
  obtain ⟨_, _, rd733₀⟩ := rd732.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, by simpa [auctionEndAfterEndedMap] using rd733₀⟩

theorem blindAuctionX_auctionEnd_toCall {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨256⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndRevealEndWord σ I).toNat < (auctionEndTimestampWord I).toNat)
    (hended : auctionEndEndedWord σ I = ⟨0⟩) :
    ∃ gasArg k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨766⟩
      [gasArg, auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I,
        auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I,
        ⟨128⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨128⟩,
        auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I,
        auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I,
        ⟨0⟩, auctionEndRevealEndWord σ I, ⟨276⟩, blindAuctionSelWord I]
      (auctionEndEventMem σ I) (UInt256.ofNat 6) ByteArray.empty
      (cA, auctionEndAfterEndedMap σ I) k C := by
  obtain ⟨_, _, rd733⟩ := blindAuctionX_auctionEnd_afterStoreAndLog (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hperm hwv hreach htime hended
  let σa := auctionEndAfterEndedMap σ I
  have rd735 := evm_run rd733 with [push0, dup1]
  obtain ⟨_, _, rd736₀⟩ := rd735.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd736⟩ : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨736⟩
      [auctionEndBeneficiaryRawWord σa I, ⟨0⟩, auctionEndRevealEndWord σ I, ⟨276⟩,
        blindAuctionSelWord I]
      (auctionEndEventMem σ I) (UInt256.ofNat 6) ByteArray.empty (cA, σa) k C := by
    exact ⟨_, _, by simpa [σa, auctionEndBeneficiaryRawWord] using rd736₀⟩
  have rd738 := evm_run rd736 with [push1 ⟨6⟩]
  obtain ⟨_, _, rd739₀⟩ := rd738.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd739⟩ : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨739⟩
      [auctionEndHighestBidWord σa I, auctionEndBeneficiaryRawWord σa I, ⟨0⟩,
        auctionEndRevealEndWord σ I, ⟨276⟩, blindAuctionSelWord I]
      (auctionEndEventMem σ I) (UInt256.ofNat 6) ByteArray.empty (cA, σa) k C := by
    exact ⟨_, _, by simpa [σa, auctionEndHighestBidWord] using rd739₀⟩
  have rd742 := evm_run rd739 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (auctionEndEventMem_mload64 σ I) (by decide) (by evm_ov)]
  have rd754₀ := evm_run rd742 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap3, and, swap2,
    jumpdest]
  have rd754 := rd754₀
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  rw [haddrMask] at rd754
  have rd765 := evm_run rd754 with [
    push0, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (auctionEndEventMem_mload64 σ I) (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, dup6, dup8]
  obtain ⟨gasArg, rd766⟩ := rd765.gas (by decide) (by evm_ov)
  exact ⟨gasArg, _, _, by simpa [σa] using rd766⟩

theorem blindAuctionX_auctionEnd_postCallEmpty_toRequire {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ} {z high benef : UInt256}
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨767⟩
      [z, ⟨128⟩, high, benef, ⟨0⟩, auctionEndRevealEndWord σ I, ⟨276⟩,
        blindAuctionSelWord I]
      mem aw ByteArray.empty acc k C) :
    ∃ k' C', RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨822⟩
      [z, auctionEndRevealEndWord σ I, ⟨276⟩, blindAuctionSelWord I] mem aw
      ByteArray.empty acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    swap3, pop, pop, pop,
    returndatasize, dup1, push0, dup2, eq, push2 ⟨812⟩,
    jumpiT (by decide) (by jump_dest),
    jumpdest, push1 ⟨96⟩, swap2, pop,
    jumpdest, pop, pop, swap1, pop]⟩

theorem blindAuctionX_auctionEnd_postCallNonempty_toRequire {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {k C : ℕ} {z high benef : UInt256} {o : ByteArray}
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨767⟩
      [z, ⟨128⟩, high, benef, ⟨0⟩, auctionEndRevealEndWord σ I, ⟨276⟩,
        blindAuctionSelWord I]
      mem (UInt256.ofNat 6) o acc k C)
    (hfp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (ho0 : o.size ≠ 0) (hosz : o.size < UInt256.size) :
    ∃ mem' aw' k' C', RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨822⟩
      [z, auctionEndRevealEndWord σ I, ⟨276⟩, blindAuctionSelWord I] mem' aw' o acc k' C' := by
  let rdsz : UInt256 := UInt256.ofNat o.size
  have hrdsz_toNat : rdsz.toNat = o.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hosz
  have hrdsz_ne : rdsz ≠ ⟨0⟩ := by
    intro h
    have hnat : rdsz.toNat = 0 := by rw [h]; rfl
    exact ho0 (by rwa [hrdsz_toNat] at hnat)
  have heq0 : UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ := u256_eq_of_ne hrdsz_ne
  have rd776₀ := evm_run rd with [swap3, pop, pop, pop, returndatasize, dup1, push0, dup2, eq]
  have rd776 := rd776₀
  change UInt256.eq rdsz (⟨0⟩ : UInt256) = ⟨0⟩ at heq0
  rw [show UInt256.ofNat o.size = rdsz from rfl, heq0] at rd776
  have rd780 := evm_run rd776 with [push2 ⟨812⟩, jumpiNT (by decide)]
  let rounded : UInt256 := UInt256.land (UInt256.add rdsz ⟨63⟩) (UInt256.lnot ⟨31⟩)
  let mem2 : ByteArray := (UInt256.toByteArray (UInt256.add ⟨128⟩ rounded)).write 0 mem 64 32
  have rd798 := evm_run rd780 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost hfp (by decide) (by evm_ov),
    swap2, pop, push1 ⟨31⟩, not, push1 ⟨63⟩, returndatasize, add, and, dup3, add,
    push1 ⟨64⟩,
    raw mstore 0 mem2 (UInt256.ofNat 6) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  let mem3 : ByteArray := (UInt256.toByteArray rdsz).write 0 mem2 128 32
  have rd801 := evm_run rd798 with [
    returndatasize, dup3,
    raw mstore 0 mem3 (UInt256.ofNat 6) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd807 := evm_run rd801 with [returndatasize, push0, push1 ⟨32⟩, dup5, add]
  let copyDest : UInt256 := (⟨128⟩ : UInt256) + ⟨32⟩
  let copyLen : UInt256 := UInt256.ofNat o.size
  have hcopyLen_toNat : copyLen.toNat = o.size := by
    simpa [copyLen] using UInt256.toNat_ofNat_of_lt hosz
  let mem4 : ByteArray := o.write 0 mem3 copyDest.toNat copyLen.toNat
  have rd808 := RD.returndatacopy
    (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 6).toNat
      copyDest.toNat copyLen.toNat)) - Cₘ (UInt256.ofNat 6))
    mem4
    (UInt256.ofNat (MachineState.M (UInt256.ofNat 6).toNat copyDest.toNat copyLen.toNat))
    rd807 (by decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hcopyLen_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, copyDest, copyLen])
    (by rfl)
    (by rfl)
    (by evm_ov)
  have rd817 := evm_run rd808 with [push2 ⟨817⟩, jump (by jump_dest), jumpdest]
  exact ⟨_, _, _, _, evm_run rd817 with [pop, pop, swap1, pop]⟩

theorem blindAuctionX_auctionEnd_requireSuccess_return {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ}
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨822⟩
      [⟨1⟩, auctionEndRevealEndWord σ I, ⟨276⟩, blindAuctionSelWord I]
      mem aw rdata acc k C) :
    RDret blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) acc ByteArray.empty := by
  have rd276 := evm_run rd with [
    dup1, push2 ⟨830⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, pop, pop, jump (by jump_dest), jumpdest]
  exact rd276.stop (by decide) (by evm_ov)

theorem blindAuctionX_auctionEnd_requireSuccess_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ}
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨822⟩
      [⟨0⟩, auctionEndRevealEndWord σ I, ⟨276⟩, blindAuctionSelWord I]
      mem aw rdata acc k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd827 := evm_run rd with [dup1, push2 ⟨830⟩, jumpiNT (by decide), push0, push0]
  exact RD.rev _ rd827 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by evm_ov)

theorem blindAuctionX_auctionEnd_callMade {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨256⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndRevealEndWord σ I).toNat < (auctionEndTimestampWord I).toNat)
    (hended : auctionEndEndedWord σ I = ⟨0⟩)
    (hbalance : auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I ≤
      (auctionEndAfterEndedMap σ I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k C : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
          (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
          (initState cA gh bl σ σ₀ g A I).blocks
          (auctionEndAfterEndedMap σ I) (initState cA gh bl σ σ₀ g A I).σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I))
          (toExecute (auctionEndAfterEndedMap σ I)
            (AccountAddress.ofUInt256 (auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I)))
          callGas (UInt256.ofNat I.gasPrice)
          (auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I)
          (auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I)
          ByteArray.empty (I.depth + 1) I.header I.perm)
      ∧ RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨767⟩
          [(if z then ⟨1⟩ else ⟨0⟩), ⟨128⟩,
            auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I,
            auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I,
            ⟨0⟩, auctionEndRevealEndWord σ I, ⟨276⟩, blindAuctionSelWord I]
          (auctionEndEventMem σ I) (UInt256.ofNat 6) o
          (cA', σ') k C := by
  obtain ⟨gasArg, _, _, rd766⟩ := blindAuctionX_auctionEnd_toCall (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hperm hwv hreach htime hended
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd767₀⟩ :=
    rd766.callValueMade (by decide) hperm hbalance hdepth (by evm_ov)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  have hcd : (auctionEndEventMem σ I).readWithPadding
      (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat = ByteArray.empty := by
    exact byteArray_readWithPadding_zero _ _
  have hΘ' : ∃ (g'' : UInt256) (A' : Substate),
      (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
        (initState cA gh bl σ σ₀ g A I).genesisBlockHeader
        (initState cA gh bl σ σ₀ g A I).blocks
        (auctionEndAfterEndedMap σ I) (initState cA gh bl σ σ₀ g A I).σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
        (AccountAddress.ofUInt256 (auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I))
        (toExecute (auctionEndAfterEndedMap σ I)
          (AccountAddress.ofUInt256 (auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I)))
        callGas (UInt256.ofNat I.gasPrice)
        (auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I)
        (auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I)
        ByteArray.empty (I.depth + 1) I.header I.perm := by
    rcases hΘ with ⟨g'', A', hΘeq⟩
    refine ⟨g'', A', ?_⟩
    rw [hcd] at hΘeq
    exact hΘeq
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
      (UInt256.ofNat 6) := by
    decide
  refine ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ', ?_⟩
  rw [hmin, byteArray_write_len_zero, haw] at rd767₀
  simpa [initState] using rd767₀

theorem blindAuctionX_auctionEnd_callDepthRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨256⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndRevealEndWord σ I).toNat < (auctionEndTimestampWord I).toNat)
    (hended : auctionEndEndedWord σ I = ⟨0⟩)
    (hdepth : I.depth = 1024) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨gasArg, _, _, rd766⟩ := blindAuctionX_auctionEnd_toCall (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hperm hwv hreach htime hended
  obtain ⟨_, _, rd767⟩ := rd766.callValueDepthLimit hperm (by decide) hdepth (by evm_ov)
  obtain ⟨_, _, rd822⟩ :=
    blindAuctionX_auctionEnd_postCallEmpty_toRequire (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd767
  exact blindAuctionX_auctionEnd_requireSuccess_revert rd822

theorem blindAuctionX_auctionEnd_callInsufficientRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨256⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (htime : (auctionEndRevealEndWord σ I).toNat < (auctionEndTimestampWord I).toNat)
    (hended : auctionEndEndedWord σ I = ⟨0⟩)
    (hbalance : ¬ auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I ≤
      (auctionEndAfterEndedMap σ I |>.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨gasArg, _, _, rd766⟩ := blindAuctionX_auctionEnd_toCall (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hperm hwv hreach htime hended
  obtain ⟨_, _, rd767⟩ :=
    RD.callValueInsufficientBalance rd766 hperm (by decide)
      hbalance hdepth (by evm_ov)
  obtain ⟨_, _, rd822⟩ :=
    blindAuctionX_auctionEnd_postCallEmpty_toRequire (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd767
  exact blindAuctionX_auctionEnd_requireSuccess_revert rd822

theorem blindAuctionX_auctionEnd_afterCall_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {o : ByteArray} {k C : ℕ}
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨767⟩
      [⟨0⟩, ⟨128⟩,
        auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I,
        auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I,
        ⟨0⟩, auctionEndRevealEndWord σ I, ⟨276⟩, blindAuctionSelWord I]
      (auctionEndEventMem σ I) (UInt256.ofNat 6) o acc k C)
    (hosz : o.size < UInt256.size) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  by_cases ho : o.size = 0
  · have hoempty : o = ByteArray.empty := byteArray_eq_empty_of_size_eq_zero o ho
    subst o
    obtain ⟨_, _, rd822⟩ :=
      blindAuctionX_auctionEnd_postCallEmpty_toRequire (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd
    exact blindAuctionX_auctionEnd_requireSuccess_revert rd822
  · obtain ⟨_, _, _, _, rd822⟩ :=
      blindAuctionX_auctionEnd_postCallNonempty_toRequire (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd
        (auctionEndEventMem_mload64 σ I) ho hosz
    exact blindAuctionX_auctionEnd_requireSuccess_revert rd822

theorem blindAuctionX_auctionEnd_afterCall_return {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {o : ByteArray} {k C : ℕ}
    (rd : RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨767⟩
      [⟨1⟩, ⟨128⟩,
        auctionEndHighestBidWord (auctionEndAfterEndedMap σ I) I,
        auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ I) I,
        ⟨0⟩, auctionEndRevealEndWord σ I, ⟨276⟩, blindAuctionSelWord I]
      (auctionEndEventMem σ I) (UInt256.ofNat 6) o acc k C)
    (hosz : o.size < UInt256.size) :
    RDret blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) acc ByteArray.empty := by
  by_cases ho : o.size = 0
  · have hoempty : o = ByteArray.empty := byteArray_eq_empty_of_size_eq_zero o ho
    subst o
    obtain ⟨_, _, rd822⟩ :=
      blindAuctionX_auctionEnd_postCallEmpty_toRequire (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd
    exact blindAuctionX_auctionEnd_requireSuccess_return rd822
  · obtain ⟨_, _, _, _, rd822⟩ :=
      blindAuctionX_auctionEnd_postCallNonempty_toRequire (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd
        (auctionEndEventMem_mload64 σ I) ho hosz
    exact blindAuctionX_auctionEnd_requireSuccess_return rd822

theorem blindAuctionAuctionEndSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem blindAuctionDispatch_auctionEnd {cd : ByteArray}
    (hsel : ((⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg blindAuctionContract cd = some auctionEndTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, revealTransition, withdrawTransition])
    (post := [beneficiaryGetter, biddingEndGetter, revealEndGetter, endedGetter,
      highestBidderGetter, highestBidGetter, bidsGetter])
    rfl ?_ (by rw [selectorOf, blindAuctionAuctionEndSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · rw [selectorOf, blindAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionWithdrawSelectorBytes, hcd]; decide

theorem blindAuctionDecode_auctionEnd {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (auctionEndTransition.params.map Param.name)
      (transitionSignature auctionEndTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem blindAuctionAuctionEndBodyReverts_nonpayable {evm : EVM.State} {locals : Store}
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals
      auctionEndTransition.body .reverted := by
  dsimp [auctionEndTransition]
  exact bodyReverts_nonPayable h

/-- `auctionEnd()` body (pc 256) refines its transition. -/
theorem blindAuctionAuctionEndBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨256⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
 :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have _hAccounts : accountMapEquiv σ_evm σ_solm := hAccounts

  have hsz := blindAuctionAuctionEndSelector_size hsel
  have hd := blindAuctionDispatch_auctionEnd (cd := I.calldata) hsel
  have hdec := blindAuctionDecode_auctionEnd (I := I) hsz
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState
      (g := Sat256.ofUInt256 g) hAccounts
  have hRevealEnd : auctionEndRevealEndWord σ_evm I = auctionEndRevealEndWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hEndedRaw : auctionEndEndedRawWord σ_evm I = auctionEndEndedRawWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  have hEnded : auctionEndEndedWord σ_evm I = auctionEndEndedWord σ_solm I := by
    simp [auctionEndEndedWord, hEndedRaw]
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases htimeBad :
        (auctionEndTimestampWord I).toNat ≤ (auctionEndRevealEndWord σ_evm I).toNat
    · have htimeS :
          (auctionEndTimestampWord I).toNat ≤ (auctionEndRevealEndWord σ_solm I).toNat := by
        simpa [hRevealEnd] using htimeBad
      have hbody :
          ExecTransitionBody blindAuctionConfig blindAuctionContract evmS ∅
            auctionEndTransition.body .reverted :=
        blindAuctionAuctionEndBodyReverts_time evmS
          (by simpa [evmS, initState] using hwv)
          (by
            simpa [evmS, initState, auctionEndRevealEndWord, auctionEndTimestampWord,
              Solm.EVM.storageLoad, State.lookupAccount] using htimeS)
      exact (blindAuctionX_auctionEnd_timeRevert (g := Sat256.ofUInt256 g) hwv hreach
          htimeBad)
        |>.reEquivExecutionRevert hcode hd hdec hbody
    · have htimeLt :
          (auctionEndRevealEndWord σ_evm I).toNat < (auctionEndTimestampWord I).toNat := by
        omega
      have htimeS :
          (auctionEndRevealEndWord σ_solm I).toNat < (auctionEndTimestampWord I).toNat := by
        simpa [← hRevealEnd] using htimeLt
      by_cases hendedZero : auctionEndEndedWord σ_evm I = ⟨0⟩
      · have hendedSZero : auctionEndEndedWord σ_solm I = ⟨0⟩ := by
          simpa [hEnded] using hendedZero
        have hendedSState : auctionEndEndedWordState evmS = ⟨0⟩ := by
          simpa [evmS, initState, auctionEndEndedWordState, auctionEndEndedRawWordState,
            auctionEndEndedWord, Solm.EVM.storageLoad, State.lookupAccount] using hendedSZero
        let evmEAfter := auctionEndAfterEndedState evmE
        let evmSAfter := auctionEndAfterEndedState evmS
        have hσAfter : EVMStateEquiv evmEAfter evmSAfter := by
          simpa [evmEAfter, evmSAfter] using auctionEndAfterEndedState_EVMStateEquiv hσ
        by_cases hdepthEq : I.depth = 1024
        · let evmSFail : EVM.State :=
            { evmSAfter with
              substate := (evmSAfter.addAccessedAccount
                (EVM.address
                  (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat))).substate }
          have hcall :
              callViaEVM evmSAfter
                (EVM.address
                  (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat))
                (Int.ofNat (auctionEndHighestBidWordState evmSAfter).toNat)
                ByteArray.empty (false, evmSFail, ByteArray.empty) := by
            apply callViaEVM.callNotMade
            · rfl
            · rfl
            · rintro ⟨_, hdepthNe⟩
              exact hdepthNe (by
                simpa [evmSAfter, evmS, initState, auctionEndAfterEndedState_executionEnv]
                  using hdepthEq)
          have hbody :
              ExecTransitionBody blindAuctionConfig blindAuctionContract evmS ∅
                auctionEndTransition.body .reverted :=
            blindAuctionAuctionEndBodyReverts_callFailure evmS evmSFail ByteArray.empty
              (by simpa [evmS, initState] using hwv)
              (by
                simpa [evmS, initState, auctionEndRevealEndWord, auctionEndTimestampWord,
                  Solm.EVM.storageLoad, State.lookupAccount] using htimeS)
              hendedSState
              (by simpa [evmSAfter] using hcall)
          exact (blindAuctionX_auctionEnd_callDepthRevert (g := Sat256.ofUInt256 g) hperm
              hwv hreach htimeLt hendedZero hdepthEq)
            |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hdepthLt : I.depth.val < 1024 := by
            have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
            have hneVal : I.depth.val ≠ 1024 := by
              intro hv
              apply hdepthEq
              exact Fin.ext hv
            omega
          by_cases hbalance : (
                auctionEndHighestBidWord (auctionEndAfterEndedMap σ_evm I) I ≤
                  ((auctionEndAfterEndedMap σ_evm I).find? I.codeOwner).elim ⟨0⟩
                    (fun x => x.balance))
          · obtain ⟨cA', σ', z, out, A_in, callGas, kCall, CCall, hTheta, rd767⟩ :=
              blindAuctionX_auctionEnd_callMade (g := Sat256.ofUInt256 g) hperm hwv
                hreach htimeLt hendedZero hbalance hdepthLt
            obtain ⟨g'', A', hThetaEq⟩ := hTheta
            let targetE : EVM.Address :=
              AccountAddress.ofUInt256 (auctionEndBeneficiaryWord
                evmEAfter.accountMap evmEAfter.executionEnv)
            let valueE : ℤ :=
              Int.ofNat (auctionEndHighestBidWord evmEAfter.accountMap evmEAfter.executionEnv).toNat
            let evmECall : EVM.State :=
              { evmEAfter with accountMap := σ', substate := A', createdAccounts := cA' }
            have hBenefE :
                auctionEndBeneficiaryWordState evmEAfter =
                  auctionEndBeneficiaryWord (auctionEndAfterEndedMap σ_evm I) I := by
              simpa [evmEAfter, evmE] using
                (auctionEndBeneficiaryWordState_afterEnded_init (cA := cA) (gh := gh)
                  (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
                  (I := I) (g := Sat256.ofUInt256 g))
            have hBenefES :
                auctionEndBeneficiaryWordState evmEAfter =
                  auctionEndBeneficiaryWordState evmSAfter := by
              unfold auctionEndBeneficiaryWordState auctionEndBeneficiaryRawWordState
              rw [hσAfter.storageLoad_codeOwner ⟨0⟩]
            have hHighE :
                auctionEndHighestBidWordState evmEAfter =
                  auctionEndHighestBidWord (auctionEndAfterEndedMap σ_evm I) I := by
              simpa [evmEAfter, evmE] using
                (auctionEndHighestBidWordState_afterEnded_init (cA := cA) (gh := gh)
                  (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
                  (I := I) (g := Sat256.ofUInt256 g))
            have hHighES :
                auctionEndHighestBidWordState evmEAfter =
                  auctionEndHighestBidWordState evmSAfter := by
              unfold auctionEndHighestBidWordState
              exact hσAfter.storageLoad_codeOwner ⟨6⟩
            have hAfterMapE :
                evmEAfter.accountMap = auctionEndAfterEndedMap σ_evm I := by
              simpa [evmEAfter, evmE] using
                (auctionEndAfterEndedState_accountMap_init (cA := cA) (gh := gh)
                  (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
                  (I := I) (g := Sat256.ofUInt256 g))
            have hAfterEnvE : evmEAfter.executionEnv = I := by
              simpa [evmEAfter, evmE] using
                (auctionEndAfterEndedState_executionEnv
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
            have hCreatedE : evmEAfter.createdAccounts = cA := by
              simpa [evmEAfter, evmE, initState] using
                (auctionEndAfterEndedState_createdAccounts
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
            have hOrigE : evmEAfter.σ₀ = σ₀ := by
              simpa [evmEAfter, evmE, initState] using
                (auctionEndAfterEndedState_originalMap
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
            have hGenesisE : evmEAfter.genesisBlockHeader = gh := by
              simpa [evmEAfter, evmE, initState] using
                (auctionEndAfterEndedState_genesisBlockHeader
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
            have hBlocksE : evmEAfter.blocks = bl := by
              simpa [evmEAfter, evmE, initState] using
                (auctionEndAfterEndedState_blocks
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
            have hBalE :
                (auctionEndAfterEndedMap σ_evm I |>.find? I.codeOwner |>.elim ⟨0⟩
                    (·.balance)) =
                  (evmEAfter.accountMap.find? evmEAfter.executionEnv.codeOwner |>.elim
                    ⟨0⟩ (·.balance)) := by
              simpa [evmEAfter, evmE] using
                (auctionEndAfterEndedState_balance_init (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g))
            have hcallE :
                callViaEVM evmEAfter targetE valueE ByteArray.empty (z, evmECall, out) := by
              refine callViaEVM.callMade
                (valueWord := auctionEndHighestBidWord evmEAfter.accountMap evmEAfter.executionEnv)
                (cA' := cA') (σ' := σ') (g' := g'') (A' := A')
                ?_ ?_ ?_ ?_ ?_
              · exact (wordOfInt_ofNat_toNat
                  (auctionEndHighestBidWord evmEAfter.accountMap evmEAfter.executionEnv)).symm
              · refine ⟨callGas, A_in, ?_⟩
                rw [hAfterEnvE, hCreatedE, hGenesisE, hBlocksE, hAfterMapE, hOrigE]
                simpa [targetE, hperm, accountAddress_roundtrip, hAfterMapE, hAfterEnvE,
                  initState] using hThetaEq
              · simp [evmECall]
              · simpa [hAfterMapE, hAfterEnvE, hBalE] using hbalance
              · intro hd
                exact hdepthEq (by
                  simpa [evmEAfter, evmE, initState, auctionEndAfterEndedState_executionEnv] using hd)
            have hout255 : out.size < 2 ^ 255 := by
              have hsizeΘ := Theta_returnData_size_lt I.blobVersionedHashes cA
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).genesisBlockHeader
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).blocks
                (auctionEndAfterEndedMap σ_evm I)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).σ₀ A_in
                (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
                (AccountAddress.ofUInt256 (auctionEndBeneficiaryWord
                  (auctionEndAfterEndedMap σ_evm I) I))
                (toExecute (auctionEndAfterEndedMap σ_evm I)
                  (AccountAddress.ofUInt256 (auctionEndBeneficiaryWord
                    (auctionEndAfterEndedMap σ_evm I) I)))
                callGas (UInt256.ofNat I.gasPrice)
                (auctionEndHighestBidWord (auctionEndAfterEndedMap σ_evm I) I)
                (auctionEndHighestBidWord (auctionEndAfterEndedMap σ_evm I) I)
                ByteArray.empty (I.depth + 1) I.header I.perm
              rw [← hThetaEq] at hsizeΘ
              exact hsizeΘ
            have houtsz : out.size < UInt256.size := by
              have hpow : 2 ^ 255 < UInt256.size := by
                norm_num [UInt256.size]
              omega
            have hOrigAfter : evmEAfter.σ₀ = evmSAfter.σ₀ := by
              simpa [evmEAfter, evmSAfter, evmE, evmS, initState,
                auctionEndAfterEndedState_originalMap]
            obtain ⟨σ'_solm, A'_solm, hcallSRaw, hPostAccounts⟩ :=
              callViaEVM_accountMapEquiv (storage := blindAuctionConfig.storage)
                (evm_solm := evmSAfter) hcallE hσAfter.accountMap hOrigAfter
                hσAfter.createdAccounts.symm
                (by
                  simp [evmEAfter, evmSAfter, evmE, evmS, initState,
                    auctionEndAfterEndedState_genesisBlockHeader])
                (by
                  simp [evmEAfter, evmSAfter, evmE, evmS, initState,
                    auctionEndAfterEndedState_blocks])
                (by
                  simp [evmEAfter, evmSAfter, evmE, evmS, initState,
                    auctionEndAfterEndedState_substate])
                hσAfter.executionEnv.symm
            let evmSCall : EVM.State :=
              { evmSAfter with
                accountMap := σ'_solm
                substate := A'_solm
                createdAccounts := evmECall.createdAccounts }
            have hBenefTarget :
                auctionEndBeneficiaryWord evmEAfter.accountMap evmEAfter.executionEnv =
                  auctionEndBeneficiaryWordState evmSAfter := by
              rw [hAfterMapE, hAfterEnvE, ← hBenefE, hBenefES]
            have hTargetEq :
                targetE =
                  EVM.address
                    (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat) := by
              calc
                targetE =
                    AccountAddress.ofUInt256 (auctionEndBeneficiaryWordState evmSAfter) := by
                  simp [targetE, hBenefTarget]
                _ = AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat := by
                  simpa [auctionEndBeneficiaryWordState] using
                    (auctionEndAddress_ofNat_toNat
                      (auctionEndBeneficiaryRawWordState evmSAfter)).symm
                _ = EVM.address
                    (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat) := by
                  exact (auctionEndAddress_from_toNat
                    (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat)).symm
            have hValueTarget :
                auctionEndHighestBidWord evmEAfter.accountMap evmEAfter.executionEnv =
                  auctionEndHighestBidWordState evmSAfter := by
              rw [hAfterMapE, hAfterEnvE, ← hHighE, hHighES]
            have hValueEq :
                valueE = Int.ofNat (auctionEndHighestBidWordState evmSAfter).toNat := by
              simp [valueE, hValueTarget]
            have hcallS :
                callViaEVM evmSAfter
                  (EVM.address
                    (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat))
                  (Int.ofNat (auctionEndHighestBidWordState evmSAfter).toNat)
                  ByteArray.empty (z, evmSCall, out) := by
              simpa [evmSCall, hTargetEq, hValueEq] using hcallSRaw
            cases z
            · have hbody :
                  ExecTransitionBody blindAuctionConfig blindAuctionContract evmS ∅
                    auctionEndTransition.body .reverted :=
                blindAuctionAuctionEndBodyReverts_callFailure evmS evmSCall out
                  (by simpa [evmS, initState] using hwv)
                  (by
                    simpa [evmS, initState, auctionEndRevealEndWord, auctionEndTimestampWord,
                      Solm.EVM.storageLoad, State.lookupAccount] using htimeS)
                  hendedSState
                  (by simpa [evmSAfter] using hcallS)
              have hrev : RDrev blindAuctionBytecode (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
                blindAuctionX_auctionEnd_afterCall_revert (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g)
                  (rd := by simpa using rd767) houtsz
              exact hrev.reEquivExecutionRevert hcode hd hdec hbody
            · have hbody :
                  ExecTransitionBody blindAuctionConfig blindAuctionContract evmS ∅
                    auctionEndTransition.body
                    (.returned { contract := blindAuctionContract, locals := auctionEndCallStore true out }
                      evmSCall none) :=
                blindAuctionAuctionEndBodyReturns_callSuccess evmS evmSCall out
                  (by simpa [evmS, initState] using hwv)
                  (by
                    simpa [evmS, initState, auctionEndRevealEndWord, auctionEndTimestampWord,
                      Solm.EVM.storageLoad, State.lookupAccount] using htimeS)
                  hendedSState
                  (by simpa [evmSAfter] using hcallS)
              have hret : RDret blindAuctionBytecode (Sat256.ofUInt256 g)
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  (cA', σ') ByteArray.empty :=
                blindAuctionX_auctionEnd_afterCall_return (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g)
                  (rd := by simpa using rd767) houtsz
              exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                (by simp [evmSCall, evmECall])
                (by simpa [evmSCall, evmECall] using hPostAccounts)
                (returnEquiv.void rfl rfl rfl)
          · let evmSFail : EVM.State :=
              { evmSAfter with
                substate := (evmSAfter.addAccessedAccount
                  (EVM.address
                    (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat))).substate }
            have hHighE :
                auctionEndHighestBidWordState evmEAfter =
                  auctionEndHighestBidWord (auctionEndAfterEndedMap σ_evm I) I := by
              simpa [evmEAfter, evmE] using
                (auctionEndHighestBidWordState_afterEnded_init (cA := cA) (gh := gh)
                  (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
                  (I := I) (g := Sat256.ofUInt256 g))
            have hHighES :
                auctionEndHighestBidWordState evmEAfter =
                  auctionEndHighestBidWordState evmSAfter := by
              unfold auctionEndHighestBidWordState
              exact hσAfter.storageLoad_codeOwner ⟨6⟩
            have hBalE :
                ((auctionEndAfterEndedMap σ_evm I).find? I.codeOwner).elim ⟨0⟩
                    (fun x => x.balance) =
                  (evmEAfter.accountMap.find? evmEAfter.executionEnv.codeOwner |>.elim
                    ⟨0⟩ (·.balance)) := by
              simpa [evmEAfter, evmE] using
                (auctionEndAfterEndedState_balance_init (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := Sat256.ofUInt256 g))
            have hBalES :
                (evmEAfter.accountMap.find? evmEAfter.executionEnv.codeOwner |>.elim
                    ⟨0⟩ (·.balance)) =
                  (evmSAfter.accountMap.find? evmSAfter.executionEnv.codeOwner |>.elim
                    ⟨0⟩ (·.balance)) :=
              auctionEndEVMStateEquiv_balance_codeOwner hσAfter
            have hcall :
                callViaEVM evmSAfter
                  (EVM.address
                    (AccountAddress.ofNat (auctionEndBeneficiaryWordState evmSAfter).toNat))
                  (Int.ofNat (auctionEndHighestBidWordState evmSAfter).toNat)
                  ByteArray.empty (false, evmSFail, ByteArray.empty) := by
              apply callViaEVM.callNotMade
              · rfl
              · rfl
              · rintro ⟨hvalueBal, _⟩
                have hvalueBal' :
                    auctionEndHighestBidWordState evmSAfter ≤
                      (evmSAfter.accountMap.find? evmSAfter.executionEnv.codeOwner |>.elim
                        ⟨0⟩ (·.balance)) := by
                  rw [wordOfInt_ofNat_toNat] at hvalueBal
                  exact hvalueBal
                have hvalueBalE :
                    auctionEndHighestBidWord (auctionEndAfterEndedMap σ_evm I) I ≤
                      (evmEAfter.accountMap.find? evmEAfter.executionEnv.codeOwner |>.elim
                        ⟨0⟩ (·.balance)) := by
                  simpa [← hHighES, hHighE, ← hBalES] using hvalueBal'
                exact hbalance (by simpa [hBalE] using hvalueBalE)
            have hbody :
                ExecTransitionBody blindAuctionConfig blindAuctionContract evmS ∅
                  auctionEndTransition.body .reverted :=
              blindAuctionAuctionEndBodyReverts_callFailure evmS evmSFail ByteArray.empty
                (by simpa [evmS, initState] using hwv)
                (by
                  simpa [evmS, initState, auctionEndRevealEndWord, auctionEndTimestampWord,
                    Solm.EVM.storageLoad, State.lookupAccount] using htimeS)
                hendedSState
                (by simpa [evmSAfter] using hcall)
            exact (blindAuctionX_auctionEnd_callInsufficientRevert (g := Sat256.ofUInt256 g)
                hperm hwv hreach htimeLt hendedZero hbalance hdepthLt)
              |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hendedBad : auctionEndEndedWord σ_evm I ≠ ⟨0⟩ := hendedZero
        have hendedS : auctionEndEndedWord σ_solm I ≠ ⟨0⟩ := by
          intro hz
          exact hendedBad (by simpa [hEnded] using hz)
        have hbody :
            ExecTransitionBody blindAuctionConfig blindAuctionContract evmS ∅
              auctionEndTransition.body .reverted :=
          blindAuctionAuctionEndBodyReverts_ended evmS
            (by simpa [evmS, initState] using hwv)
            (by
              simpa [evmS, initState, auctionEndRevealEndWord, auctionEndTimestampWord,
                Solm.EVM.storageLoad, State.lookupAccount] using htimeS)
            (by
              simpa [evmS, initState, auctionEndEndedWordState, auctionEndEndedRawWordState,
                auctionEndEndedWord, Solm.EVM.storageLoad, State.lookupAccount] using hendedS)
        exact (blindAuctionX_auctionEnd_endedRevert (g := Sat256.ofUInt256 g) hwv hreach
            htimeLt hendedBad)
          |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
          auctionEndTransition.body .reverted := by
      exact blindAuctionAuctionEndBodyReverts_nonpayable (by simpa [initState] using hwv)
    exact (blindAuctionX_auctionEnd_nonpayable (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end BlindAuction
