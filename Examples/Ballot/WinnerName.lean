import Examples.Ballot.WinningProposal
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Ballot

/-! ## `winnerName()` -/

def winnerNameNameSlot (w : UInt256) : UInt256 :=
  UInt256.mul w ⟨2⟩ + proposalsDataBase

def winnerNameNameLoc (w : UInt256) : StorageLoc :=
  { slot := winnerNameNameSlot w, offset := 0, size := 32, hbound := by decide,
    type := .bytes ⟨31, by decide⟩ }

def winnerNameNameEvaledRef (w : UInt256) : EvaledStorageRef :=
  { base := "proposals",
    steps := [.aindex (.int (Int.ofNat w.toNat)), .field "name"] }

def winnerNameStoreAfterWinningProposal (w : UInt256) : Store :=
  (∅ : Store).insert "w" (.int (Int.ofNat w.toNat))

def winnerNameNameCurrent (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
    (winnerNameNameSlot (winningProposalResultCurrent evm))

def winnerNameNameWord (sigma : AccountMap) (I : ExecutionEnv) : UInt256 :=
  sigma.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (winnerNameNameSlot (winningProposalResultWord sigma I)) ⟨0⟩)

theorem winnerNameNameCurrent_init {cA gh bl σ σ₀ A I} {g : Sat256} :
    winnerNameNameCurrent (initState cA gh bl σ σ₀ g A I) =
      winnerNameNameWord σ I := by
  rw [winnerNameNameCurrent, winnerNameNameWord]
  rw [winningProposalResultCurrent_init]
  rfl

theorem winnerNameNameWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    winnerNameNameWord σ I = winnerNameNameWord τ I := by
  unfold winnerNameNameWord
  rw [winningProposalResultWord_accountMapEquiv hστ]
  exact accountMapEquiv_storage_findD hστ I.codeOwner
    (winnerNameNameSlot (winningProposalResultWord τ I)) ⟨0⟩

theorem winnerNameNameSlot_spec (w : UInt256) :
    winnerNameNameSlot w = proposalElemSlot (.int (Int.ofNat w.toNat)) := by
  unfold winnerNameNameSlot proposalElemSlot
  rw [ballotKeyValueToWord_int_ofNat_toNat]
  rw [u256_mul_two_ofNat]
  exact u256_add_comm _ _

theorem winnerNameArrayIndexInBounds_ok (evm : EVM.State) (w : UInt256)
    (hbound : w.toNat < (winningProposalLengthCurrent evm).toNat) :
    arrayIndexInBounds? ballotConfig evm ballotContract.storage "proposals" []
      (.int (Int.ofNat w.toNat)) = .ok () :=
  winningProposalArrayIndexInBounds_ok evm w hbound

theorem winnerNameArrayIndexInBounds_revert (evm : EVM.State) (w : UInt256)
    (hbound : ¬ w.toNat < (winningProposalLengthCurrent evm).toNat) :
    arrayIndexInBounds? ballotConfig evm ballotContract.storage "proposals" []
      (.int (Int.ofNat w.toNat)) = .revert := by
  have hboundStorage :
      ¬ w.toNat <
        UInt256.toNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) := by
    simpa [winningProposalLengthCurrent] using hbound
  have hleStorage :
      UInt256.toNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) ≤ w.toNat :=
    Nat.le_of_not_gt hboundStorage
  simp [arrayIndexInBounds?, storageTypeAt?, ballotConfig, ballotStorageLayout,
    ballotContract, ballotStorageDecls, proposalStructTy, uint256St, bytes32St,
    ballotStorageLocLoad_uint256, hleStorage]

theorem winnerNameEvalName (evm : EVM.State) (locals : Store) (w : UInt256)
    (hbaseProposals : locals.get? "proposals" = none)
    (hw : locals.get? "w" = some (.int (Int.ofNat w.toNat)))
    (hbound : w.toNat < (winningProposalLengthCurrent evm).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := locals } evm
      (.storage (proposalF (.var "w") "name")) =
        .ok (.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (winnerNameNameSlot w)))) := by
  have hbase : locals.get? (proposalF (.var "w") "name").base = none := by
    simpa [proposalF] using hbaseProposals
  have hwEval :
      evalExpr? ballotConfig { contract := ballotContract, locals := locals } evm
        (.var "w") = .ok (.int (Int.ofNat w.toNat)) :=
    winningProposalEvalVar evm locals "w" w hw
  have hboundsOk :
      arrayIndexInBounds? ballotConfig evm ballotContract.storage "proposals" []
        (.int (Int.ofNat w.toNat)) = .ok () :=
    winnerNameArrayIndexInBounds_ok evm w hbound
  have her :
      evalStorageRef ballotConfig { contract := ballotContract, locals := locals } evm
        (proposalF (.var "w") "name") = .ok (winnerNameNameEvaledRef w) := by
    simp only [proposalF, evalStorageRef, evalStorageRefSteps.eq_def,
      evalStorageRefStep.eq_def, hwEval, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      bind, pure, List.nil_append]
    rw [hboundsOk]
    simp [winnerNameNameEvaledRef]
  have hty :
      storageTypeAt? ballotContract.storage (winnerNameNameEvaledRef w) =
        some (.elem (.bytes ⟨31, by decide⟩)) := by
    simp [winnerNameNameEvaledRef, storageTypeAt?, storageTypeStep?, ballotContract,
      ballotStorageDecls, proposalStructTy, bytes32St]
  have hloc :
      ballotConfig.storage.layout (winnerNameNameEvaledRef w) =
        fun _ => some (winnerNameNameLoc w) := by
    funext evm'
    simp [winnerNameNameEvaledRef, winnerNameNameLoc, ballotConfig, ballotStorageLayout,
      winnerNameNameSlot_spec]
  have hload :
      storageLocLoad evm (winnerNameNameLoc w) =
        .fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (winnerNameNameSlot w))) := by
    simpa [winnerNameNameLoc] using (ballotStorageLocLoad_bytes32 evm (winnerNameNameSlot w))
  rw [evalExpr_storage_scalar (t := .bytes ⟨31, by decide⟩) (hbase := hbase)
    (her := her) (hty := hty) (hloc := hloc)]
  rw [hload]

theorem winnerNameEvalName_revert (evm : EVM.State) (locals : Store) (w : UInt256)
    (hbaseProposals : locals.get? "proposals" = none)
    (hw : locals.get? "w" = some (.int (Int.ofNat w.toNat)))
    (hbound : ¬ w.toNat < (winningProposalLengthCurrent evm).toNat) :
    evalExpr? ballotConfig { contract := ballotContract, locals := locals } evm
      (.storage (proposalF (.var "w") "name")) = .revert := by
  have hbaseNameGet :
      locals[(proposalF (.var "w") "name").base]? = none := by
    rw [← Std.HashMap.get?_eq_getElem?]
    simpa [proposalF] using hbaseProposals
  have hwEval :
      evalExpr? ballotConfig { contract := ballotContract, locals := locals } evm
        (.var "w") = .ok (.int (Int.ofNat w.toNat)) :=
    winningProposalEvalVar evm locals "w" w hw
  have hboundsRevert :
      arrayIndexInBounds? ballotConfig evm ballotContract.storage "proposals" []
        (.int (Int.ofNat w.toNat)) = .revert :=
    winnerNameArrayIndexInBounds_revert evm w hbound
  have herNameRevert :
      evalStorageRef ballotConfig { contract := ballotContract, locals := locals } evm
        (proposalF (.var "w") "name") = .revert := by
    simp only [proposalF, evalStorageRef, evalStorageRefSteps.eq_def,
      evalStorageRefStep.eq_def, hwEval, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      bind, pure, List.nil_append]
    rw [hboundsRevert]
  simp [evalExpr?, resolveStorageRef?, hbaseNameGet, herNameRevert, EvalResult.bind, bind]

theorem ballotWinningProposal_lookup :
    lookupCallable? ballotContract "winningProposal" = some winningProposalTransition.toCallable := by
  rfl

theorem ballotWinningProposal_bind :
    bindParams? winningProposalTransition.params [] = some ∅ := rfl

theorem ballotWinnerNameBodyReturns (evm : EVM.State)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound :
      (winningProposalResultCurrent evm).toNat < (winningProposalLengthCurrent evm).toNat) :
    ∃ locals', ExecTransitionBody ballotConfig ballotContract evm ∅ winnerNameTransition.body
      (.returned { contract := ballotContract, locals := locals' } evm
        (some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (winnerNameNameCurrent evm))))) := by
  let w := winningProposalResultCurrent evm
  let Lw := winnerNameStoreAfterWinningProposal w
  obtain ⟨calleeLocals, hcallee⟩ := ballotWinningProposalBodyReturns evm ∅ h (by simp)
  have hcall : ExecStmt ballotConfig { contract := ballotContract, locals := ∅ } evm
      (.internalCall "winningProposal" [] "w")
      (.ok { contract := ballotContract, locals := Lw } evm) := by
    simpa [Lw, winnerNameStoreAfterWinningProposal, w] using
      internalCallTransitionReturn (cfg := ballotConfig)
        (caller := { contract := ballotContract, locals := ∅ }) (evm := evm)
        (calleeEvm := evm) (name := "winningProposal") (args := []) (retVar := "w")
        (argVals := []) (callee := winningProposalTransition) (locals := ∅)
        (calleeSolm := { contract := ballotContract, locals := calleeLocals })
        (value := .int (Int.ofNat (winningProposalResultCurrent evm).toNat))
        (by rfl) ballotWinningProposal_lookup ballotWinningProposal_bind hcallee
  have hbase : Lw.get? "proposals" = none := by
    simp [Lw, winnerNameStoreAfterWinningProposal]
  have hw : Lw.get? "w" = some (.int (Int.ofNat w.toNat)) := by
    simp [Lw, winnerNameStoreAfterWinningProposal]
  have hret :
      evalExpr? ballotConfig { contract := ballotContract, locals := Lw } evm
        (.storage (proposalF (.var "w") "name")) =
          .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (winnerNameNameCurrent evm))) := by
    simpa [winnerNameNameCurrent, w] using winnerNameEvalName evm Lw w hbase hw hbound
  refine ⟨Lw, ExecFuncBody.execBlockRet ?_⟩
  rw [winnerNameTransition]
  exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true h)) <|
    ExecBlock.consNormal hcall <|
      ExecBlock.consReturn (ExecStmt.return hret)

theorem ballotWinnerNameBodyReverts_oob (evm : EVM.State)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound :
      ¬ (winningProposalResultCurrent evm).toNat < (winningProposalLengthCurrent evm).toNat) :
    ExecTransitionBody ballotConfig ballotContract evm ∅ winnerNameTransition.body .reverted := by
  let w := winningProposalResultCurrent evm
  let Lw := winnerNameStoreAfterWinningProposal w
  obtain ⟨calleeLocals, hcallee⟩ := ballotWinningProposalBodyReturns evm ∅ h (by simp)
  have hcall : ExecStmt ballotConfig { contract := ballotContract, locals := ∅ } evm
      (.internalCall "winningProposal" [] "w")
      (.ok { contract := ballotContract, locals := Lw } evm) := by
    simpa [Lw, winnerNameStoreAfterWinningProposal, w] using
      internalCallTransitionReturn (cfg := ballotConfig)
        (caller := { contract := ballotContract, locals := ∅ }) (evm := evm)
        (calleeEvm := evm) (name := "winningProposal") (args := []) (retVar := "w")
        (argVals := []) (callee := winningProposalTransition) (locals := ∅)
        (calleeSolm := { contract := ballotContract, locals := calleeLocals })
        (value := .int (Int.ofNat (winningProposalResultCurrent evm).toNat))
        (by rfl) ballotWinningProposal_lookup ballotWinningProposal_bind hcallee
  have hbase : Lw.get? "proposals" = none := by
    simp [Lw, winnerNameStoreAfterWinningProposal]
  have hw : Lw.get? "w" = some (.int (Int.ofNat w.toNat)) := by
    simp [Lw, winnerNameStoreAfterWinningProposal]
  have hret :
      evalExpr? ballotConfig { contract := ballotContract, locals := Lw } evm
        (.storage (proposalF (.var "w") "name")) = .revert := by
    simpa [w] using winnerNameEvalName_revert evm Lw w hbase hw hbound
  exact ExecFuncBody.execBlockRevert <| by
    rw [winnerNameTransition]
    exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true h)) <|
      ExecBlock.consNormal hcall <|
        ExecBlock.consRevert (ExecStmt.returnRevert hret)

theorem ballotBytes32ReturnEncoding (w : UInt256) :
    encodeReturnValue? bytes32 (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE w)) =
      some (UInt256.toByteArray w) := by
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  refine scalarReturnEncoding (t := .bytes ⟨31, by decide⟩) (w := w) (by native_decide) ?_ ?_
  · native_decide
  · simp [encodeABIValue?, hlen, zeroBytes]

/-! ## EVM body for `winnerName` -/

-- LIBRARY CANDIDATE: `Reasoning.EVMWord`.
theorem winnerName_u256_zero_add (w : UInt256) : (⟨0⟩ : UInt256) + w = w := by
  apply u256_inj
  show (0 + w.val).val = w.val
  simp

theorem winnerNameNameSlot_evm (w : UInt256) :
    (⟨0⟩ : UInt256) + (UInt256.mul ⟨2⟩ w + proposalsDataBase) =
      winnerNameNameSlot w := by
  unfold winnerNameNameSlot
  rw [winnerName_u256_zero_add]
  rw [winningProposal_u256_mul_comm ⟨2⟩ w]

theorem ballotX_winnerName_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hbound : (winningProposalResultWord σ I).toNat < (winningProposalLengthWord σ I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨417⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ballotBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (winnerNameNameWord σ I)) := by
  obtain ⟨_, _, rd417⟩ := hreach
  have rd1700 := evm_run rd417 with [
    jumpdest, push2 ⟨272⟩, push2 ⟨1700⟩, jump (by jump_dest)]
  have rd1315 := evm_run rd1700 with [
    jumpdest, push0, push1 ⟨2⟩, push2 ⟨1711⟩, push2 ⟨1315⟩, jump (by jump_dest)]
  obtain ⟨mem', _, _, hmem', hread64', rd1711⟩ :=
    ballotWinningProposalRoutine (cA := cA) (σ := σ) (I := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (ret := ⟨1711⟩)
      (R := [⟨2⟩, ⟨0⟩, ⟨272⟩, sel]) (mem := solcFreePtrMem)
      (rdata := ByteArray.empty) solcFreePtrMem_size solcFreePtrMem_read64 (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega) rd1315
  have rd1713 := evm_run rd1711 with [jumpdest, dup2]
  obtain ⟨_, _, rd1714⟩ := rd1713.sload (by decide) (by evm_ov)
  have hlt : UInt256.lt (winningProposalResultWord σ I) (winningProposalLengthWord σ I) = ⟨1⟩ :=
    ult_one hbound
  have rd1727 := evm_run rd1714 with [
    dup2, lt, push2 ⟨1727⟩,
    jumpiT (by
      have hlt' : UInt256.lt (winningProposalResultWord σ I)
          (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) = ⟨1⟩ := by
        simpa [winningProposalLengthWord] using hlt
      rw [hlt']; decide) (by jump_dest)]
  let nameBaseMem := winningProposalStoreBaseMem mem'
  have rd1734 := evm_run rd1727 with [
    jumpdest, swap1, push0,
    raw mstore 0 nameBaseMem (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push0]
  have hnameBaseMemSize : nameBaseMem.size = 96 := by
    simpa [nameBaseMem] using winningProposalStoreBaseMem_size mem' hmem'
  have hnameBaseMemRead64 : nameBaseMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [nameBaseMem] using winningProposalStoreBaseMem_read64 mem' hmem' hread64'
  have hkeccak :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (nameBaseMem.readWithPadding 0 32))) =
        proposalsDataBase := by
    simpa [nameBaseMem] using winningProposalStoreBaseMem_keccak mem' hmem'
  have rd1742pre := evm_run rd1734 with [
    raw keccak256 0 proposalsDataBase (UInt256.ofNat 3) (by decide)
      mem_cost hkeccak (by decide) (by evm_ov),
    swap1, push1 ⟨2⟩, mul, add, push0, add]
  obtain ⟨_, _, rd1743⟩ := rd1742pre.sload (by decide) (by evm_ov)
  have rd272raw := evm_run rd1743 with [swap1, pop, swap1, jump (by jump_dest)]
  have hrd272 : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨272⟩
      [winnerNameNameWord σ I, sel] nameBaseMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [winnerNameNameWord, winnerNameNameSlot_evm] using rd272raw⟩
  obtain ⟨_, _, rd272⟩ := hrd272
  let retMem := winningProposalReturnFromMem nameBaseMem (winnerNameNameWord σ I)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ retMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (retMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    simpa [retMem] using
      winningProposalReturnFromMem_mload64 nameBaseMem (winnerNameNameWord σ I)
        hnameBaseMemSize hnameBaseMemRead64
  have hread128 :
      retMem.readWithPadding 128 32 = UInt256.toByteArray (winnerNameNameWord σ I) := by
    simpa [retMem] using
      winningProposalReturnFromMem_read128 nameBaseMem (winnerNameNameWord σ I)
        hnameBaseMemSize
  have rd194 := evm_run rd272 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (mloadFreePtrValue (by rw [hnameBaseMemSize]; decide) (by decide) hnameBaseMemRead64)
      (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6 retMem (UInt256.ofNat 5) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨194⟩, jump (by jump_dest)]
  exact RD.ballotReturnOneWord194OfMem rd194 hmload64 hread128
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ballotX_winnerName_oob {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hbound : ¬ (winningProposalResultWord σ I).toNat < (winningProposalLengthWord σ I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨417⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd417⟩ := hreach
  have rd1700 := evm_run rd417 with [
    jumpdest, push2 ⟨272⟩, push2 ⟨1700⟩, jump (by jump_dest)]
  have rd1315 := evm_run rd1700 with [
    jumpdest, push0, push1 ⟨2⟩, push2 ⟨1711⟩, push2 ⟨1315⟩, jump (by jump_dest)]
  obtain ⟨_, _, _, _, _, rd1711⟩ :=
    ballotWinningProposalRoutine (cA := cA) (σ := σ) (I := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (ret := ⟨1711⟩)
      (R := [⟨2⟩, ⟨0⟩, ⟨272⟩, sel]) (mem := solcFreePtrMem)
      (rdata := ByteArray.empty) solcFreePtrMem_size solcFreePtrMem_read64 (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega) rd1315
  have rd1713 := evm_run rd1711 with [jumpdest, dup2]
  obtain ⟨_, _, rd1714⟩ := rd1713.sload (by decide) (by evm_ov)
  have hlt : UInt256.lt (winningProposalResultWord σ I) (winningProposalLengthWord σ I) = ⟨0⟩ :=
    ult_zero (Nat.le_of_not_gt hbound)
  have rd1815 := evm_run rd1714 with [
    dup2, lt, push2 ⟨1727⟩,
    jumpiNT (by
      have hlt' : UInt256.lt (winningProposalResultWord σ I)
          (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) = ⟨0⟩ := by
        simpa [winningProposalLengthWord] using hlt
      exact hlt'),
    push2 ⟨1727⟩, push2 ⟨1815⟩, jump (by jump_dest)]
  exact RD.ballotPanic32Revert1815 rd1815
    (by simp only [List.length_cons, List.length_nil]; omega)

/-! ## Dispatch/decode bridge -/

theorem ballotWinnerNameSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0xe2, 0xba, 0x53, 0xf0]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xe2, 0xba, 0x53, 0xf0]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ballotDispatch_winnerName {cd : ByteArray}
    (hsel : ((⟨#[0xe2, 0xba, 0x53, 0xf0]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg ballotContract cd = some winnerNameTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xe2, 0xba, 0x53, 0xf0]⟩ : ByteArray) :=
    (ballotByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [voteTransition, proposalsGetter, chairpersonGetter, delegateTransition,
      winningProposalTransition, giveRightToVoteTransition, votersGetter])
    (post := [])
    rfl ?_ (by rw [selectorOf, ballotWinnerNameSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, ballotVoteSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotProposalsSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotChairpersonSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotDelegateSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotWinningProposalSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotGiveRightToVoteSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotVotersSelectorBytes, hcd]; decide

theorem ballotDecode_winnerName {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (winnerNameTransition.params.map Param.name)
      (transitionSignature winnerNameTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem ballotWinnerNameBodyCore
    {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0xe2, 0xba, 0x53, 0xf0]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨417⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  have hsz4 := ballotWinnerNameSelector_size hsel
  have hd := ballotDispatch_winnerName (cd := I.calldata) hsel
  have hdec := ballotDecode_winnerName (I := I) hsz4
  by_cases hbound :
      (winningProposalResultWord σ_evm I).toNat < (winningProposalLengthWord σ_evm I).toNat
  · have hboundCurrent :
        (winningProposalResultCurrent
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)).toNat <
          (winningProposalLengthCurrent
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)).toNat := by
      have hres :
          winningProposalResultCurrent
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) =
              winningProposalResultWord σ_evm I := by
        rw [winningProposalResultCurrent_init]
        exact (winningProposalResultWord_accountMapEquiv hAccounts).symm
      have hlen :
          winningProposalLengthCurrent
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) =
              winningProposalLengthWord σ_evm I := by
        exact (winningProposalLengthWord_eq_current_init (g := Sat256.ofUInt256 g)).symm.trans
          (winningProposalLengthWord_accountMapEquiv hAccounts).symm
      rw [hres, hlen]
      exact hbound
    obtain ⟨locals', hbody₀⟩ := ballotWinnerNameBodyReturns
      (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv) hboundCurrent
    have hname :
        winnerNameNameCurrent
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) =
          winnerNameNameWord σ_evm I := by
      rw [winnerNameNameCurrent_init]
      exact (winnerNameNameWord_accountMapEquiv hAccounts).symm
    have hbody :
        ExecTransitionBody ballotConfig ballotContract
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          winnerNameTransition.body
          (.returned { contract := ballotContract, locals := locals' }
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
            (some (.fixedBytes ⟨31, by decide⟩
              (EVM.Word.toBytesBE (winnerNameNameWord σ_evm I))))) := by
      simpa [hname] using hbody₀
    exact (ballotX_winnerName_ok (g := Sat256.ofUInt256 g) hbound hreach)
      |>.reEquivExecution hcode hd hdec hbody
        hAccounts
        (returnEquiv_of_encode (ballotBytes32ReturnEncoding (winnerNameNameWord σ_evm I)))
  · have hboundCurrent :
        ¬ (winningProposalResultCurrent
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)).toNat <
          (winningProposalLengthCurrent
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)).toNat := by
      have hres :
          winningProposalResultCurrent
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) =
              winningProposalResultWord σ_evm I := by
        rw [winningProposalResultCurrent_init]
        exact (winningProposalResultWord_accountMapEquiv hAccounts).symm
      have hlen :
          winningProposalLengthCurrent
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) =
              winningProposalLengthWord σ_evm I := by
        exact (winningProposalLengthWord_eq_current_init (g := Sat256.ofUInt256 g)).symm.trans
          (winningProposalLengthWord_accountMapEquiv hAccounts).symm
      rw [hres, hlen]
      exact hbound
    have hbody := ballotWinnerNameBodyReverts_oob
      (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
      (by simp only [initState]; exact hwv) hboundCurrent
    exact (ballotX_winnerName_oob (g := Sat256.ofUInt256 g) hbound hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end Ballot
