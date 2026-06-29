import Examples.Ballot.Common
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Ballot

/-! ## `proposals(uint256)` getter -/

abbrev proposalsIndexWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4

abbrev proposalsIndexValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (proposalsIndexWord I).toNat)

abbrev proposalsStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "i" (proposalsIndexValue I)

def proposalNameSlot (I : ExecutionEnv) : UInt256 :=
  UInt256.mul (proposalsIndexWord I) ⟨2⟩ + proposalsDataBase

def proposalCountSlot (I : ExecutionEnv) : UInt256 :=
  proposalNameSlot I + ⟨1⟩

def proposalNameLoc (I : ExecutionEnv) : StorageLoc :=
  { slot := proposalNameSlot I, offset := 0, size := 32, hbound := by decide,
    type := .bytes ⟨31, by decide⟩ }

def proposalNameEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "proposals",
    steps := [.aindex (.int (Int.ofNat (proposalsIndexWord I).toNat)), .field "name"] }

def proposalCountEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "proposals",
    steps := [.aindex (.int (Int.ofNat (proposalsIndexWord I).toNat)), .field "voteCount"] }

def proposalsLengthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)

def proposalNameWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (proposalNameSlot I) ⟨0⟩)

def proposalCountWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (proposalCountSlot I) ⟨0⟩)

def proposalsLengthCurrent (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩

def proposalNameCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (proposalNameSlot I)

def proposalCountCurrent (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (proposalCountSlot I)

theorem proposalsLengthWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    proposalsLengthWord σ I = proposalsLengthWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner ⟨2⟩ ⟨0⟩

theorem proposalNameWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    proposalNameWord σ I = proposalNameWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (proposalNameSlot I) ⟨0⟩

theorem proposalCountWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hστ : accountMapEquiv σ τ) :
    proposalCountWord σ I = proposalCountWord τ I := by
  exact accountMapEquiv_storage_findD hστ I.codeOwner (proposalCountSlot I) ⟨0⟩

theorem proposalNameSlot_spec (I : ExecutionEnv) :
    proposalNameSlot I = proposalElemSlot (.int (Int.ofNat (proposalsIndexWord I).toNat)) := by
  unfold proposalNameSlot proposalElemSlot
  rw [keyValueToWord_uint256, u256_mul_two_ofNat]
  exact u256_add_comm _ _

theorem proposalsArrayIndexInBounds_ok (evm : EVM.State) (I : ExecutionEnv)
    (hbound : (proposalsIndexWord I).toNat < (proposalsLengthCurrent evm).toNat) :
    arrayIndexInBounds? ballotConfig evm ballotContract.storage "proposals" []
      (.int (Int.ofNat (proposalsIndexWord I).toNat)) = .ok () := by
  have hboundStorage :
      (proposalsIndexWord I).toNat <
        UInt256.toNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) := by
    simpa [proposalsLengthCurrent] using hbound
  simp [arrayIndexInBounds?, storageTypeAt?, ballotConfig,
    ballotStorageLayout, ballotContract, ballotStorageDecls, proposalStructTy, uint256St,
    bytes32St, ballotStorageLocLoad_uint256, hboundStorage]

theorem proposalsArrayIndexInBounds_revert (evm : EVM.State) (I : ExecutionEnv)
    (hbound : ¬ (proposalsIndexWord I).toNat < (proposalsLengthCurrent evm).toNat) :
    arrayIndexInBounds? ballotConfig evm ballotContract.storage "proposals" []
      (.int (Int.ofNat (proposalsIndexWord I).toNat)) = .revert := by
  have hboundStorage :
      ¬ (proposalsIndexWord I).toNat <
        UInt256.toNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) := by
    simpa [proposalsLengthCurrent] using hbound
  have hleStorage :
      UInt256.toNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) ≤
        (proposalsIndexWord I).toNat :=
    Nat.le_of_not_gt hboundStorage
  simp [arrayIndexInBounds?, storageTypeAt?, ballotConfig,
    ballotStorageLayout, ballotContract, ballotStorageDecls, proposalStructTy, uint256St,
    bytes32St, ballotStorageLocLoad_uint256, hleStorage]

theorem ballotProposalsBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound : (proposalsIndexWord I).toNat < (proposalsLengthCurrent evm).toNat) :
    ExecTransitionBody ballotConfig ballotContract evm (proposalsStore I) proposalsGetter.body
      (.returned { contract := ballotContract, locals := proposalsStore I } evm
        (some (.tuple [
          .fixedBytes ⟨31, by decide⟩
            (EVM.Word.toBytesBE (proposalNameCurrent evm I)),
          .int (Int.ofNat (proposalCountCurrent evm I).toNat)]))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have hbaseName : (proposalsStore I).get? (proposalF (Expr.var "i") "name").base = none := by
        simp [proposalsStore, proposalF]
      have hbaseCount : (proposalsStore I).get? (proposalF (Expr.var "i") "voteCount").base = none := by
        simp [proposalsStore, proposalF]
      have hi :
          evalExpr? ballotConfig { contract := ballotContract, locals := proposalsStore I } evm
            (Expr.var "i") = .ok (proposalsIndexValue I) := by
        simp only [evalExpr?, proposalsStore, proposalsIndexValue, store_get_self,
          EvalResult.ofOption]
      have hboundInt :
          0 ≤ Int.ofNat (proposalsIndexWord I).toNat ∧
            Int.ofNat (proposalsIndexWord I).toNat <
              Int.ofNat (proposalsLengthCurrent evm).toNat := by
        exact ⟨Int.natCast_nonneg _, Int.ofNat_lt_ofNat_of_lt hbound⟩
      have hboundStorage :
          (proposalsIndexWord I).toNat <
            UInt256.toNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) := by
        simpa [proposalsLengthCurrent] using hbound
      have hboundsOk :
          arrayIndexInBounds? ballotConfig evm ballotContract.storage "proposals" []
            (.int (Int.ofNat (proposalsIndexWord I).toNat)) = .ok () :=
        proposalsArrayIndexInBounds_ok evm I hbound
      have herName :
          evalStorageRef ballotConfig { contract := ballotContract, locals := proposalsStore I } evm
            (proposalF (Expr.var "i") "name") = .ok (proposalNameEvaledRef I) := by
        simp only [proposalF, evalStorageRef, evalStorageRefSteps.eq_def,
          evalStorageRefStep.eq_def, hi, proposalsIndexValue, valueToKey?, EvalResult.ofOption,
          EvalResult.bind, bind, pure, List.nil_append]
        rw [hboundsOk]
        simp [proposalNameEvaledRef]
      have herCount :
          evalStorageRef ballotConfig { contract := ballotContract, locals := proposalsStore I } evm
            (proposalF (Expr.var "i") "voteCount") = .ok (proposalCountEvaledRef I) := by
        simp only [proposalF, evalStorageRef, evalStorageRefSteps.eq_def,
          evalStorageRefStep.eq_def, hi, proposalsIndexValue, valueToKey?, EvalResult.ofOption,
          EvalResult.bind, bind, pure, List.nil_append]
        rw [hboundsOk]
        simp [proposalCountEvaledRef]
      have htyName :
          storageTypeAt? ballotContract.storage (proposalNameEvaledRef I) =
            some (.elem (.bytes ⟨31, by decide⟩)) := by
        simp [proposalNameEvaledRef, storageTypeAt?, storageTypeStep?, ballotContract,
          ballotStorageDecls, proposalStructTy, bytes32St]
      have htyCount :
          storageTypeAt? ballotContract.storage (proposalCountEvaledRef I) =
            some (.elem (.int uint256Int)) := by
        simp [proposalCountEvaledRef, storageTypeAt?, storageTypeStep?, ballotContract,
          ballotStorageDecls, proposalStructTy, uint256St]
      have hlocName :
          ballotConfig.storage.layout (proposalNameEvaledRef I) =
            fun _ => some (proposalNameLoc I) := by
        funext evm'
        simp [proposalNameEvaledRef, proposalNameLoc, ballotConfig, ballotStorageLayout,
          proposalNameSlot_spec]
      have hlocCount :
          ballotConfig.storage.layout (proposalCountEvaledRef I) =
            fun _ => some (wordLoc (proposalCountSlot I)) := by
        funext evm'
        simp [proposalCountEvaledRef, proposalCountSlot, ballotConfig, ballotStorageLayout,
          proposalNameSlot_spec, u256_add_comm]
      have hnameLoad :
          storageLocLoad evm (proposalNameLoc I) =
            .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (proposalNameCurrent evm I)) := by
        simpa [proposalNameLoc, proposalNameCurrent] using
          (ballotStorageLocLoad_bytes32 evm (proposalNameSlot I))
      have hcountLoad :
          storageLocLoad evm (wordLoc (proposalCountSlot I)) =
            .int (Int.ofNat (proposalCountCurrent evm I).toNat) := by
        simpa [proposalCountCurrent] using
          (ballotStorageLocLoad_uint256 evm (proposalCountSlot I))
      rw [evalExpr?, evalExprList?,
        evalExpr_storage_scalar (t := .bytes ⟨31, by decide⟩) (hbase := hbaseName)
          (her := herName) (hty := htyName) (hloc := hlocName)]
      rw [evalExprList?,
        evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbaseCount)
          (her := herCount) (hty := htyCount) (hloc := hlocCount)]
      simp [evalExprList?, EvalResult.bind, bind, pure, proposalNameCurrent,
        proposalCountCurrent, hnameLoad, hcountLoad])

theorem ballotProposalsBodyReverts_oob (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound : ¬ (proposalsIndexWord I).toNat < (proposalsLengthCurrent evm).toNat) :
    ExecTransitionBody ballotConfig ballotContract evm (proposalsStore I) proposalsGetter.body
      .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).run
      (ExecBlock.consRevert (ExecStmt.returnRevert (by
        have hbaseName : (proposalsStore I).get? (proposalF (Expr.var "i") "name").base = none := by
          simp [proposalsStore, proposalF]
        have hbaseNameGet :
            (proposalsStore I)[(proposalF (Expr.var "i") "name").base]? = none := by
          simp [proposalsStore, proposalF]
        have hi :
            evalExpr? ballotConfig { contract := ballotContract, locals := proposalsStore I } evm
              (Expr.var "i") = .ok (proposalsIndexValue I) := by
          simp only [evalExpr?, proposalsStore, proposalsIndexValue, store_get_self,
            EvalResult.ofOption]
        have hboundsRevert :
            arrayIndexInBounds? ballotConfig evm ballotContract.storage "proposals" []
              (.int (Int.ofNat (proposalsIndexWord I).toNat)) = .revert :=
          proposalsArrayIndexInBounds_revert evm I hbound
        have herNameRevert :
            evalStorageRef ballotConfig { contract := ballotContract, locals := proposalsStore I } evm
              (proposalF (Expr.var "i") "name") = .revert := by
          simp only [proposalF, evalStorageRef, evalStorageRefSteps.eq_def,
            evalStorageRefStep.eq_def, hi, proposalsIndexValue, valueToKey?, EvalResult.ofOption,
            EvalResult.bind, bind, pure, List.nil_append]
          rw [hboundsRevert]
        simp [evalExpr?, evalExprList?, resolveStorageRef?, hbaseNameGet, herNameRevert,
          EvalResult.bind, bind])))

/-! ## Memory used by the proposal getter -/

noncomputable def proposalsBaseSlotMem : ByteArray :=
  (UInt256.toByteArray (⟨2⟩ : UInt256)).write 0 solcFreePtrMem 0 32

noncomputable def proposalsReturnNameMem (name : UInt256) : ByteArray :=
  (UInt256.toByteArray name).write 0 proposalsBaseSlotMem 128 32

noncomputable def proposalsReturnMem (name count : UInt256) : ByteArray :=
  (UInt256.toByteArray count).write 0 (proposalsReturnNameMem name) 160 32

theorem proposalsBaseSlotMem_size : proposalsBaseSlotMem.size = 96 := by
  unfold proposalsBaseSlotMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  omega

theorem proposalsBaseSlotMem_read0 :
    proposalsBaseSlotMem.readWithPadding 0 32 = UInt256.toByteArray (⟨2⟩ : UInt256) := by
  unfold proposalsBaseSlotMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    show (UInt256.toByteArray (⟨2⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨2⟩ : UInt256) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (⟨2⟩ : UInt256)).size ≤ 32
          rw [toByteArray_size])]

theorem proposalsBaseSlotMem_read64 :
    proposalsBaseSlotMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold proposalsBaseSlotMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega) (by omega)
      (by rw [solcFreePtrMem_size]),
    solcFreePtrMem_read64]

theorem proposalsBaseSlotMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ proposalsBaseSlotMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian (proposalsBaseSlotMem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [proposalsBaseSlotMem_size]; decide) (by decide)
    proposalsBaseSlotMem_read64

theorem proposalsDataBaseKeccak :
    UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (proposalsBaseSlotMem.readWithPadding 0 32))) =
      proposalsDataBase := by
  rw [proposalsBaseSlotMem_read0]
  unfold proposalsDataBase
  exact keccakSlot_eq _

theorem proposalsReturnNameMem_size (name : UInt256) :
    (proposalsReturnNameMem name).size = 160 := by
  unfold proposalsReturnNameMem
  rw [toByteArray_write_eq _ _ _ (by rw [proposalsBaseSlotMem_size]; omega)
      (by rw [proposalsBaseSlotMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, proposalsBaseSlotMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem proposalsReturnMem_size (name count : UInt256) :
    (proposalsReturnMem name count).size = 192 := by
  unfold proposalsReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [proposalsReturnNameMem_size])
      (by rw [proposalsReturnNameMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, proposalsReturnNameMem_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (160 - 160)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem proposalsReturnNameMem_read64 (name : UInt256) :
    (proposalsReturnNameMem name).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold proposalsReturnNameMem
  rw [toByteArray_write_eq _ _ _ (by rw [proposalsBaseSlotMem_size]; omega)
      (by rw [proposalsBaseSlotMem_size]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.append_assoc]
  rw [readWithPadding_eq_extract' _ 64 32 (by norm_num) (by norm_num) (by
    rw [ByteArray.size_append, proposalsBaseSlotMem_size, ByteArray.size_append,
      ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
      toByteArray_size]
    omega)]
  rw [extract_append_left proposalsBaseSlotMem
      (ffi.ByteArray.zeroes (USize.ofNat (128 - proposalsBaseSlotMem.size)) ++ UInt256.toByteArray name)
      64 96 (by rw [proposalsBaseSlotMem_size])]
  rw [← readWithPadding_eq_extract' proposalsBaseSlotMem 64 32 (by norm_num) (by norm_num)
      (by rw [proposalsBaseSlotMem_size])]
  exact proposalsBaseSlotMem_read64

theorem proposalsReturnMem_read64 (name count : UInt256) :
    (proposalsReturnMem name count).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold proposalsReturnMem
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size])
      (by rw [proposalsReturnNameMem_size]) (by omega)]
  exact proposalsReturnNameMem_read64 name

theorem proposalsReturnMem_mload64 (name count : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (proposalsReturnMem name count).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((proposalsReturnMem name count).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [proposalsReturnMem_size]; decide) (by decide)
    (proposalsReturnMem_read64 name count)

theorem proposalsReturnMem_read128_64 (name count : UInt256) :
    (proposalsReturnMem name count).readWithPadding 128 64 =
      UInt256.toByteArray name ++ UInt256.toByteArray count := by
  rw [readWithPadding_eq_extract' _ 128 64 (by norm_num) (by norm_num)
      (by rw [proposalsReturnMem_size])]
  unfold proposalsReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [proposalsReturnNameMem_size])
      (by rw [proposalsReturnNameMem_size]; exact lt_usize _ (by norm_num))]
  rw [extract_append_span
      (proposalsReturnNameMem name ++ ffi.ByteArray.zeroes (USize.ofNat (160 - (proposalsReturnNameMem name).size)))
      (UInt256.toByteArray count) 128 192 (by
        rw [ByteArray.size_append, proposalsReturnNameMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (160 - 160)).toNat = 0 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        omega) (by
        rw [ByteArray.size_append, proposalsReturnNameMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (160 - 160)).toNat = 0 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        omega)]
  rw [ByteArray.size_append, proposalsReturnNameMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (160 - 160)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  simp
  unfold proposalsReturnNameMem
  rw [toByteArray_write_eq _ _ _ (by rw [proposalsBaseSlotMem_size]; omega)
      (by rw [proposalsBaseSlotMem_size]; exact lt_usize _ (by norm_num))]
  rw [show ffi.ByteArray.zeroes (USize.ofNat (128 - proposalsBaseSlotMem.size)) =
      ffi.ByteArray.zeroes (USize.ofNat 32) by rw [proposalsBaseSlotMem_size]]
  rw [show ffi.ByteArray.zeroes (USize.ofNat 0) = ByteArray.empty by
      exact zeroes_zero (n := USize.ofNat 0) (by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)))]
  rw [ByteArray.append_empty]
  rw [extract_append_right_window
      (proposalsBaseSlotMem ++ ffi.ByteArray.zeroes (USize.ofNat 32))
      (UInt256.toByteArray name) 128 160 (by
        rw [ByteArray.size_append, proposalsBaseSlotMem_size, ByteArray_zeroes_size,
          show (USize.ofNat 32).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, proposalsBaseSlotMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  have hnameFull : (UInt256.toByteArray name).extract 0 32 = UInt256.toByteArray name := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray name).size ≤ 32
      rw [toByteArray_size])
  have hcountFull : (UInt256.toByteArray count).extract 0 32 = UInt256.toByteArray count := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray count).size ≤ 32
      rw [toByteArray_size])
  rw [hnameFull, hcountFull]

theorem proposalsSubRet64_toNat :
    (UInt256.sub ((⟨64⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 64 := by
  decide

/-! ## EVM trace -/

theorem ballotProposalsX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨158⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1747⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨172⟩, ⟨177⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd158⟩ := hreach
  exact ⟨_, _, evm_run rd158 with [
    jumpdest, push2 ⟨177⟩, push2 ⟨172⟩, calldatasize, push1 ⟨4⟩, push2 ⟨1747⟩,
    jump (by jump_dest) ]⟩

end Ballot

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Ballot

theorem RD.ballotDecodeUint256Ok1747 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨1747⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩)
    (hret : (D_J ballotBytecode 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD ballotBytecode ee g s0 ret (calldataWord ee.calldata 4 :: R) mem aw rdata acc
      k' C' := by
  let rd := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨1763⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest),
    jumpdest, pop, calldataload, swap2, swap1, pop,
    jump hret ]
  exact ⟨_, _, by simpa [calldataWord] using rd⟩

theorem RD.ballotDecodeUint256Revert1747 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨1747⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩)
    (hov : R.length + 10 ≤ 1024) :
    RDrev ballotBytecode g s0 := by
  have h1760 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨1763⟩,
    jumpiNT (by rw [hsltval]; decide) ]
  exact h1760.revertStub (by decide) (by decide) (by decide)
    (by simp only [List.length_cons]; omega)

end Reasoning.Reach

namespace Ballot

theorem ballotProposalsX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨158⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨671⟩
      [proposalsIndexWord I, ⟨177⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd1747⟩ := ballotProposalsX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  obtain ⟨_, _, rd172⟩ := RD.ballotDecodeUint256Ok1747 rd1747 hslt (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, evm_run rd172 with [jumpdest, push2 ⟨671⟩, jump (by jump_dest)]⟩

theorem ballotProposalsX_decodeRevert_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨158⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd1747⟩ := ballotProposalsX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact RD.ballotDecodeUint256Revert1747 rd1747 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ballotProposalsX_decodeRevert_huge {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨158⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd1747⟩ := ballotProposalsX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact RD.ballotDecodeUint256Revert1747 rd1747 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ballotX_proposals_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hbound : (proposalsIndexWord I).toNat < (proposalsLengthWord σ I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨158⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ballotBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (proposalNameWord σ I) ++
        UInt256.toByteArray (proposalCountWord σ I)) := by
  obtain ⟨_, _, rd671⟩ := ballotProposalsX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz36 hsize hszhi hreach
  have rd676 := evm_run rd671 with [jumpdest, push1 ⟨2⟩, dup2, dup2]
  obtain ⟨_, _, rd677⟩ := rd676.sload (by decide) (by evm_ov)
  have hlt : UInt256.lt (proposalsIndexWord I) (proposalsLengthWord σ I) = ⟨1⟩ :=
    ult_one hbound
  have rd686 := evm_run rd677 with [
    dup2, lt, push2 ⟨686⟩,
    jumpiT (by
      have hlt' :
          (proposalsIndexWord I).lt
              (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) = ⟨1⟩ := by
        simpa [proposalsLengthWord] using hlt
      rw [hlt']; decide) (by jump_dest) ]
  have rd702 := evm_run rd686 with [
    jumpdest, push0, swap2, dup3,
    raw mstore 0 proposalsBaseSlotMem (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, swap1, swap2,
    raw keccak256 0 proposalsDataBase (UInt256.ofNat 3) (by decide)
      mem_cost proposalsDataBaseKeccak (by decide) (by evm_ov),
    push1 ⟨2⟩, swap1, swap2, mul, add, dup1 ]
  obtain ⟨_, _, rd704⟩ := rd702.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd710⟩ := (evm_run rd704 with [
    push1 ⟨1⟩, swap1, swap2, add ]).sload (by decide) (by evm_ov)
  exact evm_run rd710 with [
    swap1, swap2, pop, dup3, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost proposalsBaseSlotMem_mload64 (by decide) (by evm_ov),
    swap3, dup4,
    raw mstore 6 (proposalsReturnNameMem (proposalNameWord σ I)) (UInt256.ofNat 5)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup4, add, swap2, swap1, swap2,
    raw mstore 3 (proposalsReturnMem (proposalNameWord σ I) (proposalCountWord σ I))
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    add,
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (proposalsReturnMem_mload64 (proposalNameWord σ I) (proposalCountWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0
      (UInt256.toByteArray (proposalNameWord σ I) ++
        UInt256.toByteArray (proposalCountWord σ I))
      (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          proposalsSubRet64_toNat]
        exact proposalsReturnMem_read128_64 (proposalNameWord σ I) (proposalCountWord σ I))
      (by evm_ov) ]

theorem ballotX_proposals_oob {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hbound : ¬ (proposalsIndexWord I).toNat < (proposalsLengthWord σ I).toNat)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨158⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd671⟩ := ballotProposalsX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz36 hsize hszhi hreach
  have rd676 := evm_run rd671 with [jumpdest, push1 ⟨2⟩, dup2, dup2]
  obtain ⟨_, _, rd677⟩ := rd676.sload (by decide) (by evm_ov)
  have hlt : UInt256.lt (proposalsIndexWord I) (proposalsLengthWord σ I) = ⟨0⟩ :=
    ult_zero (by omega)
  exact evm_run rd677 with [
    dup2, lt, push2 ⟨686⟩,
    jumpiNT (by
      have hlt' :
          (proposalsIndexWord I).lt
              (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) = ⟨0⟩ := by
        simpa [proposalsLengthWord] using hlt
      exact hlt'),
    push0, dup1, raw rev 0 (by decide) mem_cost (by evm_ov) ]

/-! ## Dispatch/decode bridge -/

theorem ballotProposalsSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x01, 0x3c, 0xf0, 0x8b]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x01, 0x3c, 0xf0, 0x8b]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ballotDispatch_proposals {cd : ByteArray}
    (hsel : ((⟨#[0x01, 0x3c, 0xf0, 0x8b]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg ballotContract cd = some proposalsGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0x01, 0x3c, 0xf0, 0x8b]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split (pre := [voteTransition])
    (post := [chairpersonGetter, delegateTransition, winningProposalTransition,
      giveRightToVoteTransition, votersGetter, winnerNameTransition])
    rfl rfl ?_ (by rw [selectorOf, ballotProposalsSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_singleton] at ht
  subst ht
  rw [selectorOf, ballotVoteSelectorBytes, hcd]
  decide

theorem ballotDecode_proposals_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata (proposalsGetter.params.map Param.name)
      (transitionSignature proposalsGetter).paramTypes I.calldata = some (proposalsStore I) := by
  show decodeCalldata ["i"] [uint256] I.calldata = some (proposalsStore I)
  simpa [proposalsStore, proposalsIndexValue, proposalsIndexWord, uint256, calldataWord]
    using decodeCalldata_uint256_ok (cd := I.calldata) (x := "i") hsz36 hbig

theorem ballotDecode_proposals_none_short {I : ExecutionEnv} (hshort : I.calldata.size < 36) :
    decodeCalldata (proposalsGetter.params.map Param.name)
      (transitionSignature proposalsGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["i"] [uint256] I.calldata = none
  simpa [uint256] using decodeCalldata_uint256_none_short (cd := I.calldata) (x := "i") hshort

theorem ballotDecode_proposals_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (proposalsGetter.params.map Param.name)
      (transitionSignature proposalsGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["i"] [uint256] I.calldata = none
  simpa [uint256] using decodeCalldata_uint256_none_huge (cd := I.calldata) (x := "i") hbig

theorem ballotProposalsBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x01, 0x3c, 0xf0, 0x8b]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨158⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := ballotProposalsSelector_size hsel
  have hd := ballotDispatch_proposals (cd := I.calldata) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · have hdec := ballotDecode_proposals_ok (I := I) hsz36 hbig
      have hlen :
          proposalsLengthCurrent
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) =
            proposalsLengthWord σ_evm I := by
        simpa [proposalsLengthCurrent, proposalsLengthWord, initState] using
          (proposalsLengthWord_accountMapEquiv hAccounts).symm
      by_cases hbound : (proposalsIndexWord I).toNat < (proposalsLengthWord σ_evm I).toNat
      · have hname :
            proposalNameCurrent
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I =
              proposalNameWord σ_evm I := by
          simpa [proposalNameCurrent, proposalNameWord, initState] using
            (proposalNameWord_accountMapEquiv hAccounts).symm
        have hcount :
            proposalCountCurrent
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I =
              proposalCountWord σ_evm I := by
          simpa [proposalCountCurrent, proposalCountWord, initState] using
            (proposalCountWord_accountMapEquiv hAccounts).symm
        have hbody := ballotProposalsBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
          (by rw [hlen]; exact hbound)
        exact (ballotX_proposals_ok (g := Sat256.ofUInt256 g) hsz36 hsize hbig hbound hreach)
          |>.reEquivExecutionTransport hcode hd hdec hbody (by simp [hname, hcount])
            hAccounts
            (returnEquiv_of_encode
              (ballotProposalReturnEncoding (proposalNameWord σ_evm I)
                (proposalCountWord σ_evm I)))
      · have hbody := ballotProposalsBodyReverts_oob
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
          (by rw [hlen]; exact hbound)
        exact (ballotX_proposals_oob (g := Sat256.ofUInt256 g) hsz36 hsize hbig hbound hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := ballotDecode_proposals_none_huge (I := I) hbigge
      exact (ballotProposalsX_decodeRevert_huge (g := Sat256.ofUInt256 g) hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := ballotDecode_proposals_none_short (I := I) hshort
    exact (ballotProposalsX_decodeRevert_short (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Ballot
