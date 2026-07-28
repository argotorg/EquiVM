import Benchmarks.CompoundIII.CometRewards.Common
import Benchmarks.CompoundIII.CometRewards.Governor
import Benchmarks.CompoundIII.CometRewards.TransferGovernor
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.CompoundIII.CometRewards

/-! ## `withdrawToken(address,address,uint256)` -/

abbrev withdrawTokenTokenWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev withdrawTokenToWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev withdrawTokenAmountWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev withdrawTokenTokenValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (withdrawTokenTokenWord I).toNat)

abbrev withdrawTokenToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (withdrawTokenToWord I).toNat)

abbrev withdrawTokenAmountValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (withdrawTokenAmountWord I).toNat)

abbrev withdrawTokenStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "token" (withdrawTokenTokenValue I)).insert "to"
    (withdrawTokenToValue I)).insert "amount" (withdrawTokenAmountValue I)

abbrev withdrawTokenFrame (evm : EVM.State) (I : ExecutionEnv) : Frame :=
  { contract := contract,
    locals := (withdrawTokenStore I).insert "__calldata" (.bytes evm.executionEnv.calldata) }

abbrev withdrawTokenArgs (I : ExecutionEnv) : List Value :=
  [withdrawTokenTokenValue I, withdrawTokenToValue I, withdrawTokenAmountValue I]

abbrev withdrawTokenTransferArgs (I : ExecutionEnv) : List Value :=
  [withdrawTokenToValue I, withdrawTokenAmountValue I]

abbrev withdrawTokenTransferTarget (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (withdrawTokenTokenWord I).toNat

abbrev doTransferOutStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "amount" (withdrawTokenAmountValue I)).insert "to"
    (withdrawTokenToValue I)).insert "token" (withdrawTokenTokenValue I)

abbrev withdrawTokenCallStore (I : ExecutionEnv) (success : Bool) : Store :=
  (doTransferOutStore I).insert "success" (.bool success)

abbrev withdrawTokenTransferSelectorWord : UInt256 := ⟨2835717307⟩

abbrev withdrawTokenTransferSelectorShifted : UInt256 :=
  UInt256.shiftLeft withdrawTokenTransferSelectorWord ⟨224⟩

noncomputable def withdrawTokenTransferSelectorMem : ByteArray :=
  (UInt256.toByteArray withdrawTokenTransferSelectorShifted).write 0 solcFreePtrMem 128 32

noncomputable def withdrawTokenTransferArgsMem (recipient : UInt256) : ByteArray :=
  (UInt256.toByteArray recipient).write 0 withdrawTokenTransferSelectorMem 132 32

noncomputable def withdrawTokenTransferCalldataMem (recipient value : UInt256) : ByteArray :=
  (UInt256.toByteArray value).write 0 (withdrawTokenTransferArgsMem recipient) 164 32

abbrev withdrawTokenTransferCallPc : UInt256 :=
  (⟨3950⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
    UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩

abbrev withdrawTokenTransferCallSize : UInt256 :=
  ((⟨64⟩ : UInt256) + (⟨128⟩ + ⟨4⟩)).sub ⟨128⟩

abbrev withdrawTokenPostCallTail (I : ExecutionEnv) : List UInt256 :=
  [⟨128⟩, withdrawTokenToWord I, withdrawTokenAmountWord I, ⟨1001⟩, ⟨64⟩, ⟨0⟩,
    ⟨4⟩, cometRewardsSelWord I, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]

abbrev withdrawTokenPostCallStack (z : Bool) (I : ExecutionEnv) : List UInt256 :=
  (if z then ⟨1⟩ else ⟨0⟩) :: withdrawTokenPostCallTail I

noncomputable abbrev withdrawTokenPostCallMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  out.write 0
    (withdrawTokenTransferCalldataMem (withdrawTokenToWord I) (withdrawTokenAmountWord I))
    128 (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat

abbrev withdrawTokenPostCallAw : UInt256 :=
  UInt256.ofNat (MachineState.M
    (MachineState.M (UInt256.ofNat 7).toNat (⟨128⟩ : UInt256).toNat
      withdrawTokenTransferCallSize.toNat)
    (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat)

theorem withdrawTokenTransferCallPc_eq :
    withdrawTokenTransferCallPc = ⟨3963⟩ := by
  native_decide

theorem withdrawTokenTransferCallSize_eq :
    withdrawTokenTransferCallSize = ⟨68⟩ := by
  native_decide

theorem u256_of_accountAddress_ofNat_toNat_of_canonical {w : UInt256}
    (hw : w.toNat < EVM.addressModulus) :
    UInt256.ofNat (AccountAddress.ofNat w.toNat).val = w := by
  apply u256_inj
  rw [ulit_toNat' _ (lt_trans (AccountAddress.ofNat w.toNat).isLt
    (by decide : AccountAddress.size < UInt256.size))]
  simp [AccountAddress.ofNat]
  exact Nat.mod_eq_of_lt hw

theorem withdrawTokenStore_token (I : ExecutionEnv) :
    (withdrawTokenStore I).get? "token" = some (withdrawTokenTokenValue I) := by
  rw [withdrawTokenStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem withdrawTokenStore_to (I : ExecutionEnv) :
    (withdrawTokenStore I).get? "to" = some (withdrawTokenToValue I) := by
  rw [withdrawTokenStore, store_get_ne _ _ (by decide), store_get_self]

theorem withdrawTokenStore_amount (I : ExecutionEnv) :
    (withdrawTokenStore I).get? "amount" = some (withdrawTokenAmountValue I) := by
  rw [withdrawTokenStore, store_get_self]

theorem withdrawTokenCallStore_success (I : ExecutionEnv) (success : Bool) :
    (withdrawTokenCallStore I success).get? "success" = some (.bool success) := by
  rw [withdrawTokenCallStore, store_get_self]

theorem doTransferOutStore_token (I : ExecutionEnv) :
    (doTransferOutStore I).get? "token" = some (withdrawTokenTokenValue I) := by
  rw [doTransferOutStore, store_get_self]

theorem doTransferOutStore_to (I : ExecutionEnv) :
    (doTransferOutStore I).get? "to" = some (withdrawTokenToValue I) := by
  rw [doTransferOutStore, store_get_ne _ _ (by decide), store_get_self]

theorem doTransferOutStore_amount (I : ExecutionEnv) :
    (doTransferOutStore I).get? "amount" = some (withdrawTokenAmountValue I) := by
  rw [doTransferOutStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem evalExpr_withdrawToken_var_token (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := withdrawTokenStore I } evm
      (.var "token") = .ok (withdrawTokenTokenValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [withdrawTokenStore_token]

theorem evalExpr_withdrawToken_var_to (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := withdrawTokenStore I } evm
      (.var "to") = .ok (withdrawTokenToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [withdrawTokenStore_to]

theorem evalExpr_withdrawToken_var_amount (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := withdrawTokenStore I } evm
      (.var "amount") = .ok (withdrawTokenAmountValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [withdrawTokenStore_amount]

theorem evalExprs_withdrawToken_args (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := withdrawTokenStore I } evm
      [.var "token", .var "to", .var "amount"] = .ok (withdrawTokenArgs I) := by
  simp only [withdrawTokenArgs, evalExprs?, evalExpr_withdrawToken_var_token,
    evalExpr_withdrawToken_var_to, evalExpr_withdrawToken_var_amount, EvalResult.bind, bind]
  rfl

theorem evalExprs_withdrawToken_transfer_args (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := withdrawTokenStore I } evm
      [.var "to", .var "amount"] = .ok (withdrawTokenTransferArgs I) := by
  simp only [withdrawTokenTransferArgs, evalExprs?, evalExpr_withdrawToken_var_to,
    evalExpr_withdrawToken_var_amount, EvalResult.bind, bind]
  rfl

theorem evalExpr_withdrawToken_success (evm : EVM.State) (I : ExecutionEnv) (success : Bool) :
    evalExpr? config { contract := contract, locals := withdrawTokenCallStore I success } evm
      (.var "success") = .ok (.bool success) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [withdrawTokenCallStore_success]

theorem evalExpr_withdrawToken_frame_token (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (withdrawTokenFrame evm I) evm
      (.var "token") = .ok (withdrawTokenTokenValue I) := by
  simp only [withdrawTokenFrame, evalExpr?, EvalResult.ofOption]
  rw [store_get_ne _ _ (by decide), withdrawTokenStore_token]

theorem evalExpr_withdrawToken_frame_to (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (withdrawTokenFrame evm I) evm
      (.var "to") = .ok (withdrawTokenToValue I) := by
  simp only [withdrawTokenFrame, evalExpr?, EvalResult.ofOption]
  rw [store_get_ne _ _ (by decide), withdrawTokenStore_to]

theorem evalExpr_withdrawToken_frame_amount (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (withdrawTokenFrame evm I) evm
      (.var "amount") = .ok (withdrawTokenAmountValue I) := by
  simp only [withdrawTokenFrame, evalExpr?, EvalResult.ofOption]
  rw [store_get_ne _ _ (by decide), withdrawTokenStore_amount]

theorem evalExprs_withdrawToken_frame_args (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config (withdrawTokenFrame evm I) evm
      [.var "token", .var "to", .var "amount"] = .ok (withdrawTokenArgs I) := by
  simp only [withdrawTokenArgs, evalExprs?, evalExpr_withdrawToken_frame_token,
    evalExpr_withdrawToken_frame_to, evalExpr_withdrawToken_frame_amount, EvalResult.bind, bind]
  rfl

theorem evalExpr_doTransferOut_var_token (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := doTransferOutStore I } evm
      (.var "token") = .ok (withdrawTokenTokenValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [doTransferOutStore_token]

theorem evalExpr_doTransferOut_var_to (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := doTransferOutStore I } evm
      (.var "to") = .ok (withdrawTokenToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [doTransferOutStore_to]

theorem evalExpr_doTransferOut_var_amount (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := doTransferOutStore I } evm
      (.var "amount") = .ok (withdrawTokenAmountValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [doTransferOutStore_amount]

theorem evalExprs_doTransferOut_transfer_args (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := doTransferOutStore I } evm
      [.var "to", .var "amount"] = .ok (withdrawTokenTransferArgs I) := by
  simp only [withdrawTokenTransferArgs, evalExprs?, evalExpr_doTransferOut_var_to,
    evalExpr_doTransferOut_var_amount, EvalResult.bind, bind]
  rfl

theorem bindParams_doTransferOut (I : ExecutionEnv) :
    bindParams? doTransferOutFunction.params (withdrawTokenArgs I) =
      some (doTransferOutStore I) := by
  simp [doTransferOutFunction, withdrawTokenArgs, withdrawTokenTokenValue, doTransferOutStore,
    withdrawTokenToValue, withdrawTokenAmountValue, bindParams?]

theorem lookupCallable_doTransferOut :
    lookupCallable? contract "doTransferOut" = some doTransferOutFunction.toCallable := by
  rfl

theorem withdrawTokenTransferSelectorMem_size :
    withdrawTokenTransferSelectorMem.size = 160 :=
  solcReturnMem_size withdrawTokenTransferSelectorShifted

theorem withdrawTokenTransferArgsMem_size (recipient : UInt256) :
    (withdrawTokenTransferArgsMem recipient).size = 164 := by
  unfold withdrawTokenTransferArgsMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [withdrawTokenTransferSelectorMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, withdrawTokenTransferSelectorMem_size,
    toByteArray_size]
  omega

theorem withdrawTokenTransferCalldataMem_size (recipient value : UInt256) :
    (withdrawTokenTransferCalldataMem recipient value).size = 196 := by
  unfold withdrawTokenTransferCalldataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [withdrawTokenTransferArgsMem_size])]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, withdrawTokenTransferArgsMem_size,
    toByteArray_size]
  omega

theorem withdrawTokenTransferCalldataMem_read128_4 (recipient value : UInt256) :
    (withdrawTokenTransferCalldataMem recipient value).readWithPadding 128 4 =
      transferSelector := by
  unfold withdrawTokenTransferCalldataMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
      (by rw [withdrawTokenTransferArgsMem_size])
      (by omega)
      (by rw [withdrawTokenTransferArgsMem_size]; omega)
      (by norm_num) (by norm_num)]
  unfold withdrawTokenTransferArgsMem
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
      (by rw [withdrawTokenTransferSelectorMem_size]; omega) (by omega)
      (by rw [withdrawTokenTransferSelectorMem_size]; omega)
      (by norm_num) (by norm_num)]
  have hzero32 : (ffi.ByteArray.zeroes (USize.ofNat 32)).size = 32 := by
    rw [ByteArray_zeroes_size]
    exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))
  rw [show withdrawTokenTransferSelectorMem =
      solcReturnMem withdrawTokenTransferSelectorShifted from rfl]
  rw [readWithPadding_eq_extract' _ 128 4 (by norm_num) (by norm_num)
      (by rw [solcReturnMem_size]; omega)]
  rw [solcReturnMem_eq]
  rw [extract_append_right_window
      (solcFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat 32))
      (UInt256.toByteArray withdrawTokenTransferSelectorShifted) 128 132 (by
        simp [ByteArray.size_append, solcFreePtrMem_size, hzero32])]
  rw [ByteArray.size_append, solcFreePtrMem_size, hzero32]
  native_decide

theorem withdrawTokenTransferCalldataMem_read132_32 (recipient value : UInt256) :
    (withdrawTokenTransferCalldataMem recipient value).readWithPadding 132 32 =
      UInt256.toByteArray recipient := by
  unfold withdrawTokenTransferCalldataMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
      (by rw [withdrawTokenTransferArgsMem_size])
      (by omega)]
  unfold withdrawTokenTransferArgsMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [withdrawTokenTransferSelectorMem_size]; omega)]
  rw [show (UInt256.toByteArray recipient).extract 0 32 = UInt256.toByteArray recipient by
    rw [show 32 = (UInt256.toByteArray recipient).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem withdrawTokenTransferCalldataMem_read164_32 (recipient value : UInt256) :
    (withdrawTokenTransferCalldataMem recipient value).readWithPadding 164 32 =
      UInt256.toByteArray value := by
  unfold withdrawTokenTransferCalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [withdrawTokenTransferArgsMem_size])]
  rw [show (UInt256.toByteArray value).extract 0 32 = UInt256.toByteArray value by
    rw [show 32 = (UInt256.toByteArray value).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem withdrawTokenTransferCalldataMem_read128_68 (recipient value : UInt256) :
    (withdrawTokenTransferCalldataMem recipient value).readWithPadding 128 68 =
      transferSelector ++ UInt256.toByteArray recipient ++ UInt256.toByteArray value := by
  rw [byteArray_readWithPadding_split _ 128 4 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by simp [withdrawTokenTransferCalldataMem_size])]
  rw [byteArray_readWithPadding_split _ 132 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by simp [withdrawTokenTransferCalldataMem_size])]
  rw [withdrawTokenTransferCalldataMem_read128_4,
    withdrawTokenTransferCalldataMem_read132_32,
    withdrawTokenTransferCalldataMem_read164_32, ByteArray.append_assoc]

theorem withdrawTokenTransferCalldataMem_encode (recipient : AccountAddress) (value : UInt256) :
    config.externalABI.encode? "transfer"
        [.address recipient, .int (Int.ofNat value.toNat)] =
      some ((withdrawTokenTransferCalldataMem (UInt256.ofNat recipient.val) value)
        |>.readWithPadding 128 68) := by
  rw [withdrawTokenTransferCalldataMem_read128_68]
  change compoundRewardsExternalABI.encode? "transfer"
      [.address recipient, .int (Int.ofNat value.toNat)] =
    some (transferSelector ++
      (UInt256.ofNat recipient.val).toByteArray ++ UInt256.toByteArray value)
  have hvalueWord : EVM.word value.toNat = value := by
    exact u256_ofNat_toNat value
  have hrecipientWord : EVM.word recipient.val = UInt256.ofNat recipient.val := by
    apply u256_inj
    rfl
  have hvalueLt : value.toNat < EVM.twoPow 256 := by
    change value.val.val < UInt256.size
    exact value.val.isLt
  unfold compoundRewardsExternalABI ABI.encodeCallWithSelector? ABI.encodeABIValues?
  simp [addr, uint256, uint256Int, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
    ABI.isDynamicABIType, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.encodeABIValuesFrom?,
    hvalueLt, hrecipientWord, hvalueWord, word_toBytesBE_toByteArray_eq_toByteArray]
  rw [ByteArray.append_assoc]

theorem withdrawTokenTransferTarget_eq_targetWord (I : ExecutionEnv)
    (hcanon0 : (withdrawTokenTokenWord I).toNat < EVM.addressModulus) :
    EVM.address (withdrawTokenTransferTarget I) =
      AccountAddress.ofUInt256 (UInt256.land solcAddrMask (withdrawTokenTokenWord I)) := by
  have hcleanLeft :
      UInt256.land (withdrawTokenTokenWord I) solcAddrMask = withdrawTokenTokenWord I := by
    exact solcAddrMask_clean (by simpa [withdrawTokenTokenWord, calldataWord] using hcanon0)
  have hclean :
      UInt256.land solcAddrMask (withdrawTokenTokenWord I) = withdrawTokenTokenWord I := by
    rw [u256_land_comm solcAddrMask (withdrawTokenTokenWord I), hcleanLeft]
  rw [hclean, accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt (AccountAddress.ofNat (withdrawTokenTokenWord I).toNat).isLt

set_option maxHeartbeats 1000000 in
theorem withdrawTokenTransferCalldataMem_encode_args (I : ExecutionEnv)
    (hcanon1 : (withdrawTokenToWord I).toNat < EVM.addressModulus) :
    config.externalABI.encode? "transfer" (withdrawTokenTransferArgs I) =
      some ((withdrawTokenTransferCalldataMem (withdrawTokenToWord I) (withdrawTokenAmountWord I))
        |>.readWithPadding 128 withdrawTokenTransferCallSize.toNat) := by
  have hsz : withdrawTokenTransferCallSize.toNat = 68 := by
    rw [withdrawTokenTransferCallSize_eq]
    rfl
  rw [hsz]
  have hround :
      UInt256.ofNat (AccountAddress.ofNat (withdrawTokenToWord I).toNat).val =
        withdrawTokenToWord I :=
    u256_of_accountAddress_ofNat_toNat_of_canonical hcanon1
  have henc := withdrawTokenTransferCalldataMem_encode
    (recipient := AccountAddress.ofNat (withdrawTokenToWord I).toNat)
    (value := withdrawTokenAmountWord I)
  change config.externalABI.encode? "transfer"
      [.address (AccountAddress.ofNat (withdrawTokenToWord I).toNat),
        .int (Int.ofNat (withdrawTokenAmountWord I).toNat)] =
    some ((withdrawTokenTransferCalldataMem (withdrawTokenToWord I)
      (withdrawTokenAmountWord I)).readWithPadding 128 68)
  rw [hround] at henc
  exact henc

theorem decodeReturnValueWithMode_modern_bool_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    ABI.decodeReturnValueWithMode? DecodeMode.modern abiBool returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0n : ¬ ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [ABIType.elem ElemType.bool])
    (returndata := returndata) (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  simp only [decodeScalarWords?]
  have hscalar :
      decodeScalarWord? (ABIType.elem ElemType.bool)
        returndata.toList 0 = none := by
    simpa [abiBool] using
      (decodeScalarWord_bool_none_short (bytes := returndata.toList) (start := 0) htake0n)
  rw [hscalar]
  rfl

theorem decodeReturnValueWithMode_modern_bool_false {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) (hhi : returndata.size < 2 ^ 255)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32)) = ⟨0⟩) :
    ABI.decodeReturnValueWithMode? DecodeMode.modern abiBool returndata =
      some (.bool false) := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0 : ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  have hzero : ABI.bytesToWord ((returndata.toList.drop 0).take 32) = ⟨0⟩ := by
    simpa [List.drop_zero, hwordList] using hword
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [ABIType.elem ElemType.bool])
    (returndata := returndata) (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  simp only [decodeScalarWords?]
  have hscalar :
      decodeScalarWord? (ABIType.elem ElemType.bool)
        returndata.toList 0 = some (.bool false, 0 + 32) := by
    simpa [abiBool] using
      (decodeScalarWord_bool_ok_zero (bytes := returndata.toList) (start := 0) htake0 hzero)
  rw [hscalar]
  rfl

theorem decodeReturnValueWithMode_modern_bool_true {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) (hhi : returndata.size < 2 ^ 255)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32)) = ⟨1⟩) :
    ABI.decodeReturnValueWithMode? DecodeMode.modern abiBool returndata =
      some (.bool true) := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0 : ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  have hone : ABI.bytesToWord ((returndata.toList.drop 0).take 32) = ⟨1⟩ := by
    simpa [List.drop_zero, hwordList] using hword
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [ABIType.elem ElemType.bool])
    (returndata := returndata) (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  simp only [decodeScalarWords?]
  have hscalar :
      decodeScalarWord? (ABIType.elem ElemType.bool)
        returndata.toList 0 = some (.bool true, 0 + 32) := by
    simpa [abiBool] using
      (decodeScalarWord_bool_ok_one (bytes := returndata.toList) (start := 0) htake0 hone)
  rw [hscalar]
  rfl

theorem decodeReturnValueWithMode_modern_bool_none_noncanon {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) (hhi : returndata.size < 2 ^ 255)
    (hnz : UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32)) ≠ ⟨0⟩)
    (hno : UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32)) ≠ ⟨1⟩) :
    ABI.decodeReturnValueWithMode? DecodeMode.modern abiBool returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0 : ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  have hnzList : ABI.bytesToWord ((returndata.toList.drop 0).take 32) ≠ ⟨0⟩ := by
    intro hzero
    exact hnz (by simpa [List.drop_zero, hwordList] using hzero)
  have hnoList : ABI.bytesToWord ((returndata.toList.drop 0).take 32) ≠ ⟨1⟩ := by
    intro hone
    exact hno (by simpa [List.drop_zero, hwordList] using hone)
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [ABIType.elem ElemType.bool])
    (returndata := returndata) (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  simp only [decodeScalarWords?]
  have hscalar :
      decodeScalarWord? (ABIType.elem ElemType.bool)
        returndata.toList 0 = none := by
    simpa [abiBool] using
      (decodeScalarWord_bool_none_noncanon (bytes := returndata.toList) (start := 0)
        htake0 hnzList hnoList)
  rw [hscalar]
  rfl

theorem decodeReturnValueWithMode_modern_bool_none_huge {returndata : ByteArray}
    (hhi : 2 ^ 255 ≤ returndata.size) :
    ABI.decodeReturnValueWithMode? DecodeMode.modern abiBool returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [ABIType.elem ElemType.bool])
    (returndata := returndata) (by decide)]
  rw [if_pos (by exact ⟨by simp, by rw [hlen]; exact hhi⟩)]

theorem cometRewardsTransfer_decode_none_short {out : ByteArray}
    (hshort : out.size < 32) :
    config.externalABI.decode? "transfer" out = none := by
  change compoundRewardsExternalABI.decode? "transfer" out = none
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [boolTy, abiBool] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_bool_none_short (returndata := out) hshort)

theorem cometRewardsTransfer_decode_none_huge {out : ByteArray}
    (hhi : 2 ^ 255 ≤ out.size) :
    config.externalABI.decode? "transfer" out = none := by
  change compoundRewardsExternalABI.decode? "transfer" out = none
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [boolTy, abiBool] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_bool_none_huge (returndata := out) hhi)

theorem cometRewardsTransfer_decode_false {out : ByteArray}
    (hlo : 32 ≤ out.size) (hhi : out.size < 2 ^ 255)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩) :
    config.externalABI.decode? "transfer" out = some [.bool false] := by
  change compoundRewardsExternalABI.decode? "transfer" out = some [.bool false]
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [boolTy, abiBool] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_bool_false (returndata := out) hlo hhi hword)

theorem cometRewardsTransfer_decode_true {out : ByteArray}
    (hlo : 32 ≤ out.size) (hhi : out.size < 2 ^ 255)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨1⟩) :
    config.externalABI.decode? "transfer" out = some [.bool true] := by
  change compoundRewardsExternalABI.decode? "transfer" out = some [.bool true]
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [boolTy, abiBool] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_bool_true (returndata := out) hlo hhi hword)

theorem cometRewardsTransfer_decode_none_noncanon {out : ByteArray}
    (hlo : 32 ≤ out.size) (hhi : out.size < 2 ^ 255)
    (hnz : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨0⟩)
    (hno : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨1⟩) :
    config.externalABI.decode? "transfer" out = none := by
  change compoundRewardsExternalABI.decode? "transfer" out = none
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [boolTy, abiBool] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_bool_none_noncanon (returndata := out) hlo hhi hnz hno)

theorem doTransferOutBodyReverts_callFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (withdrawTokenTransferTarget I))
        "transfer" 0 (withdrawTokenTransferArgs I) (false, evm', out) true) :
    ExecFuncBody config { contract := contract, locals := doTransferOutStore I } evm
      doTransferOutFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config { contract := contract, locals := doTransferOutStore I } evm
    [ .externalCall (.var "token") "transfer" (.intLit 0)
        [.var "to", .var "amount"] "success",
      .require (.var "success") ] .reverted
  exact ExecBlock.consRevert
    (ExecStmt.externalCallFailure
      (evalExpr_doTransferOut_var_token evm I)
      (by simp [evalExpr?, pure])
      (evalExprs_doTransferOut_transfer_args evm I)
      hcall)

theorem doTransferOutBodyReverts_decode
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (withdrawTokenTransferTarget I))
        "transfer" 0 (withdrawTokenTransferArgs I) (true, evm', out) true)
    (hdec : config.externalABI.decode? "transfer" out = none) :
    ExecFuncBody config { contract := contract, locals := doTransferOutStore I } evm
      doTransferOutFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config { contract := contract, locals := doTransferOutStore I } evm
    [ .externalCall (.var "token") "transfer" (.intLit 0)
        [.var "to", .var "amount"] "success",
      .require (.var "success") ] .reverted
  exact ExecBlock.consRevert
    (ExecStmt.externalCallReturnDecodeRevert
      (evalExpr_doTransferOut_var_token evm I)
      (by simp [evalExpr?, pure])
      (evalExprs_doTransferOut_transfer_args evm I)
      hcall hdec)

set_option maxHeartbeats 1000000 in
theorem doTransferOutBodyReverts_false
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (withdrawTokenTransferTarget I))
        "transfer" 0 (withdrawTokenTransferArgs I) (true, evm', out) true)
    (hdec : config.externalABI.decode? "transfer" out = some [.bool false]) :
    ExecFuncBody config { contract := contract, locals := doTransferOutStore I } evm
      doTransferOutFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config { contract := contract, locals := doTransferOutStore I } evm
    [ .externalCall (.var "token") "transfer" (.intLit 0)
        [.var "to", .var "amount"] "success",
      .require (.var "success") ] .reverted
  refine ExecBlock.consNormal
    (solm' :=
      { contract := contract,
        locals := (doTransferOutStore I).insert "success" (collapseReturns [.bool false]) })
    (evm' := evm') ?_ ?_
  · exact ExecStmt.externalCallSuccess
      (cfg := config)
      (solm := { contract := contract, locals := doTransferOutStore I })
      (evm := evm)
      (receiver := .var "token") (target := withdrawTokenTransferTarget I)
      (eth := .intLit 0) (sendVal := 0)
      (args := [.var "to", .var "amount"]) (argVals := withdrawTokenTransferArgs I)
      (name := "transfer") (retVar := "success")
      (evm' := evm') (out := out) (perm := true) (value := [.bool false])
      (evalExpr_doTransferOut_var_token evm I)
      (by simp [evalExpr?, pure])
      (evalExprs_doTransferOut_transfer_args evm I)
      hcall hdec
  · simpa [withdrawTokenCallStore, collapseReturns] using
      (ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_withdrawToken_success evm' I false)))

set_option maxHeartbeats 1000000 in
theorem doTransferOutBodyReturns_true
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hcall :
      typedCallViaEVM config evm (EVM.address (withdrawTokenTransferTarget I))
        "transfer" 0 (withdrawTokenTransferArgs I) (true, evm', out) true)
    (hdec : config.externalABI.decode? "transfer" out = some [.bool true]) :
    ExecFuncBody config { contract := contract, locals := doTransferOutStore I } evm
      doTransferOutFunction.body
      (.returned { contract := contract, locals := withdrawTokenCallStore I true } evm' none) := by
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config { contract := contract, locals := doTransferOutStore I } evm
    [ .externalCall (.var "token") "transfer" (.intLit 0)
        [.var "to", .var "amount"] "success",
      .require (.var "success") ]
    (.ok { contract := contract, locals := withdrawTokenCallStore I true } evm')
  refine ExecBlock.consNormal
    (solm' :=
      { contract := contract,
        locals := (doTransferOutStore I).insert "success" (collapseReturns [.bool true]) })
    (evm' := evm') ?_ ?_
  · exact ExecStmt.externalCallSuccess
      (cfg := config)
      (solm := { contract := contract, locals := doTransferOutStore I })
      (evm := evm)
      (receiver := .var "token") (target := withdrawTokenTransferTarget I)
      (eth := .intLit 0) (sendVal := 0)
      (args := [.var "to", .var "amount"]) (argVals := withdrawTokenTransferArgs I)
      (name := "transfer") (retVar := "success")
      (evm' := evm') (out := out) (perm := true) (value := [.bool true])
      (evalExpr_doTransferOut_var_token evm I)
      (by simp [evalExpr?, pure])
      (evalExprs_doTransferOut_transfer_args evm I)
      hcall hdec
  · simpa [withdrawTokenCallStore, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.requireTrue (evalExpr_withdrawToken_success evm' I true))
        ExecBlock.nil)

theorem cometRewardsDecode_withdrawToken_ok {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (withdrawTokenTokenWord I).toNat < EVM.addressModulus)
    (hcanon1 : (withdrawTokenToWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (withdrawTokenTransition.params.map Param.name)
      (transitionSignature withdrawTokenTransition).paramTypes I.calldata =
        some (withdrawTokenStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["token", "to", "amount"]
    [addr, addr, uint256] I.calldata = _
  change decodeCalldata ["token", "to", "amount"] [.elem .address, .elem .address, abiUInt256]
      I.calldata =
    some ((((∅ : Store).insert "token"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "to"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))).insert "amount"
      (.int (Int.ofNat (calldataWord I.calldata 68).toNat)))
  exact decodeCalldata_address_address_uint256_ok (cd := I.calldata)
    (x := "token") (y := "to") (z := "amount") hsz100 hbig hcanon0 hcanon1

theorem cometRewardsDecode_withdrawToken_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode
      (withdrawTokenTransition.params.map Param.name)
      (transitionSignature withdrawTokenTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["token", "to", "amount"]
    [addr, addr, uint256] I.calldata = none
  change decodeCalldata ["token", "to", "amount"] [.elem .address, .elem .address, abiUInt256]
      I.calldata = none
  exact decodeCalldata_address_address_uint256_none_short
    (cd := I.calldata) (x := "token") (y := "to") (z := "amount") hsz4 hshort

theorem cometRewardsDecode_withdrawToken_none_noncanon_token {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (withdrawTokenTokenWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (withdrawTokenTransition.params.map Param.name)
      (transitionSignature withdrawTokenTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["token", "to", "amount"]
    [addr, addr, uint256] I.calldata = none
  change decodeCalldata ["token", "to", "amount"] [.elem .address, .elem .address, abiUInt256]
      I.calldata = none
  simpa [withdrawTokenTokenWord, calldataWord] using
    decodeCalldata_address_address_uint256_none_noncanon0
      (cd := I.calldata) (x := "token") (y := "to") (z := "amount") hsz100 hbig hnc0

theorem cometRewardsDecode_withdrawToken_none_noncanon_to {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (withdrawTokenTokenWord I).toNat < EVM.addressModulus)
    (hnc1 : ¬ (withdrawTokenToWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (withdrawTokenTransition.params.map Param.name)
      (transitionSignature withdrawTokenTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["token", "to", "amount"]
    [addr, addr, uint256] I.calldata = none
  change decodeCalldata ["token", "to", "amount"] [.elem .address, .elem .address, abiUInt256]
      I.calldata = none
  simpa [withdrawTokenTokenWord, withdrawTokenToWord, calldataWord] using
    decodeCalldata_address_address_uint256_none_noncanon1
      (cd := I.calldata) (x := "token") (y := "to") (z := "amount") hsz100 hbig
      hcanon0 hnc1

theorem cometRewardsDecode_withdrawToken_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (withdrawTokenTransition.params.map Param.name)
      (transitionSignature withdrawTokenTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["token", "to", "amount"]
    [addr, addr, uint256] I.calldata = none
  change decodeCalldata ["token", "to", "amount"] [.elem .address, .elem .address, abiUInt256]
      I.calldata = none
  exact decodeCalldata_address_address_uint256_none_huge
    (cd := I.calldata) (x := "token") (y := "to") (z := "amount") hbig

theorem cometRewardsWithdrawTokenSelector_size {I : ExecutionEnv}
    (hsel : selIs I (cometRewardsSelBytes 0)) :
    4 ≤ I.calldata.size :=
  calldata_size_ge_of_selIs I (cometRewardsSelBytes 0) rfl hsel

theorem cometRewardsDispatch_withdrawToken {cd : ByteArray}
    (hsel : (cometRewardsSelBytes 0 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some withdrawTokenTransition := by
  refine dispatchMsg_eq_some_of_split
    (pre := [claimTransition, claimToTransition, getRewardOwedTransition, governorTransition,
      rewardConfigTransition, rewardsClaimedTransition, setRewardConfigTransition,
      setRewardConfigWithMultiplierTransition, setRewardsClaimedTransition, transferGovernorTransition])
    (post := [])
    rfl rfl ?_ (by rw [selectorOf, withdrawTokenSelectorBytes]; exact hsel)
  have hcd : cd.extract 0 4 = cometRewardsSelBytes 0 :=
    (byteArray_eq_of_beq hsel).symm
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, claimSelectorBytes, hcd]
    decide
  · rw [selectorOf, claimToSelectorBytes, hcd]
    decide
  · rw [selectorOf, getRewardOwedSelectorBytes, hcd]
    decide
  · rw [selectorOf, governorSelectorBytes, hcd]
    decide
  · rw [selectorOf, rewardConfigSelectorBytes, hcd]
    decide
  · rw [selectorOf, rewardsClaimedSelectorBytes, hcd]
    decide
  · rw [selectorOf, setRewardConfigSelectorBytes, hcd]
    decide
  · rw [selectorOf, setRewardConfigWithMultiplierSelectorBytes, hcd]
    decide
  · rw [selectorOf, setRewardsClaimedSelectorBytes, hcd]
    decide
  · rw [selectorOf, transferGovernorSelectorBytes, hcd]
    decide

theorem cometRewardsWithdrawTokenCalldataCheckOk {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨96⟩ = ⟨0⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨96⟩ = ⟨0⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 (by omega) hsize]
  simpa using
    solcCalldataStaticLenCheckOk (sz := I.calldata.size) (words := 3)
      (by simpa using hsz100) hhi hsize

theorem cometRewardsWithdrawTokenCalldataCheckShort {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨96⟩ = ⟨1⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨96⟩ = ⟨1⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 hsz4 hsize]
  simpa using
    solcCalldataStaticLenCheckShort (sz := I.calldata.size) (words := 3)
      hsz4 (by simpa using hshort) hsize (by norm_num)

theorem cometRewardsWithdrawTokenCalldataCheckHuge {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨96⟩ = ⟨1⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨96⟩ = ⟨1⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 (by omega) hsize]
  simpa using
    solcCalldataStaticLenCheckHuge (sz := I.calldata.size) (words := 3)
      hbig hsize (by norm_num)

theorem withdrawTokenStore_governor (I : ExecutionEnv) :
    (withdrawTokenStore I).get? "governor" = none := by
  rw [withdrawTokenStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  native_decide

theorem evalExpr_withdrawToken_governor (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (withdrawTokenFrame evm I) evm (.storage governorRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config
      (withdrawTokenFrame evm I) evm governorRef =
        .ok { base := "governor", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, governorRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "governor", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := by
      change ((withdrawTokenStore I).insert "__calldata"
        (.bytes evm.executionEnv.calldata)).get? "governor" = none
      rw [store_get_ne _ _ (by decide)]
      exact withdrawTokenStore_governor I)
    (her := her) (hty := hty) (hloc := by rfl),
    cometRewardsStorageLocLoad_address_offset0]

theorem evalExpr_withdrawToken_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (withdrawTokenFrame evm I) evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_withdrawToken_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask ≠
        solcSourceWord evm.executionEnv) :
    evalExpr? config (withdrawTokenFrame evm I) evm
      (.binary .eq sender (.storage governorRef)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_withdrawToken_sender, evalExpr_withdrawToken_governor,
    bind, EvalResult.bind, evalBinaryOp?]
  have haddr :
      evm.executionEnv.source ≠
        AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat := by
    intro haddr
    exact hgov (by
      exact solcWord_eq_of_maskedAddress_eq_source (I := evm.executionEnv) haddr.symm)
  rw [show ((.address evm.executionEnv.source : Value) ==
        .address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat)) = false by
    simp [BEq.beq, haddr]]

theorem evalExpr_withdrawToken_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv) :
    evalExpr? config (withdrawTokenFrame evm I) evm
      (.binary .eq sender (.storage governorRef)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_withdrawToken_sender, evalExpr_withdrawToken_governor,
    bind, EvalResult.bind, evalBinaryOp?]
  have haddr :
      evm.executionEnv.source =
        AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat := by
    rw [hgov]
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
    simpa [solcSourceWord] using
      (accountAddress_roundtrip evm.executionEnv.source).symm
  rw [show ((.address evm.executionEnv.source : Value) ==
        .address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat)) = true by
    simp [BEq.beq, haddr]]

theorem cometRewardsWithdrawTokenBodyReverts_auth (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask ≠
        solcSourceWord evm.executionEnv) :
    ExecTransitionBody config contract evm (withdrawTokenStore I)
      withdrawTokenTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [withdrawTokenTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    ((((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (withdrawTokenStore I) hsize)).requireRevert
          (evalExpr_withdrawToken_auth_false evm I hgov))

theorem cometRewardsWithdrawTokenBodyRevertsHuge (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbig : 2 ^ 255 + 4 ≤ evm.executionEnv.calldata.size) :
    ExecTransitionBody config contract evm (withdrawTokenStore I)
      withdrawTokenTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [withdrawTokenTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireRevert
        (cometRewardsCalldataGuard_false evm (withdrawTokenStore I) hbig))

theorem cometRewardsWithdrawTokenBodyReverts_callFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (hcall :
      typedCallViaEVM config evm (EVM.address (withdrawTokenTransferTarget I))
        "transfer" 0 (withdrawTokenTransferArgs I) (false, evm', out) true) :
    ExecTransitionBody config contract evm (withdrawTokenStore I)
      withdrawTokenTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (withdrawTokenFrame evm I) evm
        (.internalCall "doTransferOut" [.var "token", .var "to", .var "amount"] "_sent")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := withdrawTokenFrame evm I) (evm := evm)
      (name := "doTransferOut") (retVar := "_sent")
      (args := [.var "token", .var "to", .var "amount"])
      (argVals := withdrawTokenArgs I) (callee := doTransferOutFunction)
      (locals := doTransferOutStore I)
      (evalExprs_withdrawToken_frame_args evm I)
      (by simpa [withdrawTokenFrame] using lookupCallable_doTransferOut)
      (bindParams_doTransferOut I)
      (by
        simpa [withdrawTokenFrame] using
          (doTransferOutBodyReverts_callFailure evm evm' I hcall))
  simpa [withdrawTokenTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (withdrawTokenStore I) hsize)).requireStep
          (evalExpr_withdrawToken_auth_true evm I hgov)).run
            (ExecBlock.consRevert hstmt))

theorem cometRewardsWithdrawTokenBodyReverts_decode
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (hcall :
      typedCallViaEVM config evm (EVM.address (withdrawTokenTransferTarget I))
        "transfer" 0 (withdrawTokenTransferArgs I) (true, evm', out) true)
    (hdec : config.externalABI.decode? "transfer" out = none) :
    ExecTransitionBody config contract evm (withdrawTokenStore I)
      withdrawTokenTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (withdrawTokenFrame evm I) evm
        (.internalCall "doTransferOut" [.var "token", .var "to", .var "amount"] "_sent")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := withdrawTokenFrame evm I) (evm := evm)
      (name := "doTransferOut") (retVar := "_sent")
      (args := [.var "token", .var "to", .var "amount"])
      (argVals := withdrawTokenArgs I) (callee := doTransferOutFunction)
      (locals := doTransferOutStore I)
      (evalExprs_withdrawToken_frame_args evm I)
      (by simpa [withdrawTokenFrame] using lookupCallable_doTransferOut)
      (bindParams_doTransferOut I)
      (by
        simpa [withdrawTokenFrame] using
          (doTransferOutBodyReverts_decode evm evm' I hcall hdec))
  simpa [withdrawTokenTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (withdrawTokenStore I) hsize)).requireStep
          (evalExpr_withdrawToken_auth_true evm I hgov)).run
            (ExecBlock.consRevert hstmt))

theorem cometRewardsWithdrawTokenBodyReverts_false
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (hcall :
      typedCallViaEVM config evm (EVM.address (withdrawTokenTransferTarget I))
        "transfer" 0 (withdrawTokenTransferArgs I) (true, evm', out) true)
    (hdec : config.externalABI.decode? "transfer" out = some [.bool false]) :
    ExecTransitionBody config contract evm (withdrawTokenStore I)
      withdrawTokenTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (withdrawTokenFrame evm I) evm
        (.internalCall "doTransferOut" [.var "token", .var "to", .var "amount"] "_sent")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := withdrawTokenFrame evm I) (evm := evm)
      (name := "doTransferOut") (retVar := "_sent")
      (args := [.var "token", .var "to", .var "amount"])
      (argVals := withdrawTokenArgs I) (callee := doTransferOutFunction)
      (locals := doTransferOutStore I)
      (evalExprs_withdrawToken_frame_args evm I)
      (by simpa [withdrawTokenFrame] using lookupCallable_doTransferOut)
      (bindParams_doTransferOut I)
      (by
        simpa [withdrawTokenFrame] using
          (doTransferOutBodyReverts_false evm evm' I hcall hdec))
  simpa [withdrawTokenTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (withdrawTokenStore I) hsize)).requireStep
          (evalExpr_withdrawToken_auth_true evm I hgov)).run
            (ExecBlock.consRevert hstmt))

theorem cometRewardsWithdrawTokenBodyReturns_true
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (hcall :
      typedCallViaEVM config evm (EVM.address (withdrawTokenTransferTarget I))
        "transfer" 0 (withdrawTokenTransferArgs I) (true, evm', out) true)
    (hdec : config.externalABI.decode? "transfer" out = some [.bool true]) :
    ExecTransitionBody config contract evm (withdrawTokenStore I)
      withdrawTokenTransition.body
      (.returned (resumeAfterInternalCall (withdrawTokenFrame evm I) "_sent" none) evm' none) := by
  refine ExecFuncBody.execBlockOK ?_
  have hstmt :
      ExecStmt config (withdrawTokenFrame evm I) evm
        (.internalCall "doTransferOut" [.var "token", .var "to", .var "amount"] "_sent")
        (.ok (resumeAfterInternalCall (withdrawTokenFrame evm I) "_sent" none) evm') := by
    exact internalCallFunctionReturn
      (cfg := config) (caller := withdrawTokenFrame evm I) (evm := evm)
      (calleeEvm := evm') (name := "doTransferOut") (retVar := "_sent")
      (args := [.var "token", .var "to", .var "amount"])
      (argVals := withdrawTokenArgs I) (callee := doTransferOutFunction)
      (locals := doTransferOutStore I)
      (calleeSolm := { contract := contract, locals := withdrawTokenCallStore I true })
      (value := none)
      (evalExprs_withdrawToken_frame_args evm I)
      (by simpa [withdrawTokenFrame] using lookupCallable_doTransferOut)
      (bindParams_doTransferOut I)
      (by
        simpa [withdrawTokenFrame] using
          (doTransferOutBodyReturns_true evm evm' I hcall hdec))
  simpa [withdrawTokenTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (withdrawTokenStore I) hsize)).requireStep
          (evalExpr_withdrawToken_auth_true evm I hgov)).run
            (ExecBlock.consNormal hstmt ExecBlock.nil))

theorem cometRewardsWithdrawTokenX_dec2875_args {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) withdrawTokenPc
      (dispatchArm0Stack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2875⟩
      [UInt256.ofNat I.calldata.size, ⟨2776⟩, ⟨128⟩, ⟨64⟩, ⟨0⟩, ⟨4⟩,
        cometRewardsSelWord I, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2758⟩ := hreach
  have rd2764 := evm_run rd2758 with [
    jumpdest, dup6, dup6, dup5, swap3, callvalue]
  rw [hwv] at rd2764
  have rd2775 := evm_run rd2764 with [
    push2 ⟨938⟩, jumpiNT (by decide),
    push2 ⟨2776⟩, calldatasize, push2 ⟨2875⟩]
  exact ⟨_, _, evm_run rd2775 with [jump (by native_decide)]⟩

theorem cometRewardsWithdrawTokenX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) withdrawTokenPc
      (dispatchArm0Stack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsWithdrawTokenCalldataCheckShort (I := I) hsz4 hsize hshort
  obtain ⟨_, _, rd2875⟩ :=
    cometRewardsWithdrawTokenX_dec2875_args (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach
  have rd2884 := evm_run rd2875 with [
    jumpdest, push1 ⟨96⟩, swap1, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd2884
  rw [hslt] at rd2884
  exact evm_run rd2884 with [
    push2 ⟨1004⟩, jumpiT (by decide) (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsWithdrawTokenX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) withdrawTokenPc
      (dispatchArm0Stack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsWithdrawTokenCalldataCheckHuge (I := I) hsize hbig
  obtain ⟨_, _, rd2875⟩ :=
    cometRewardsWithdrawTokenX_dec2875_args (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach
  have rd2884 := evm_run rd2875 with [
    jumpdest, push1 ⟨96⟩, swap1, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd2884
  rw [hslt] at rd2884
  exact evm_run rd2884 with [
    push2 ⟨1004⟩, jumpiT (by decide) (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsWithdrawTokenX_dec2776_args {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (withdrawTokenTokenWord I).toNat < EVM.addressModulus)
    (hcanon1 : (withdrawTokenToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) withdrawTokenPc
      (dispatchArm0Stack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2776⟩
      [withdrawTokenAmountWord I, withdrawTokenToWord I, withdrawTokenTokenWord I,
        ⟨128⟩, ⟨64⟩, ⟨0⟩, ⟨4⟩, cometRewardsSelWord I, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt := cometRewardsWithdrawTokenCalldataCheckOk (I := I) hsz100 hsize hhi
  obtain ⟨_, _, rd2875⟩ :=
    cometRewardsWithdrawTokenX_dec2875_args (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach
  have rd2884 := evm_run rd2875 with [
    jumpdest, push1 ⟨96⟩, swap1, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd2884
  rw [hslt] at rd2884
  have rd2888 := evm_run rd2884 with [
    push2 ⟨1004⟩, jumpiNT (by decide)]
  have rd2909 := evm_run rd2888 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, push1 ⟨4⟩, calldataload, dup3, dup2, and, dup2, sub,
    push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land (withdrawTokenTokenWord I) solcAddrMask =
            withdrawTokenTokenWord I := by
        exact solcAddrMask_clean (by
          simpa [withdrawTokenTokenWord, calldataWord] using hcanon0)
      have hclean' :
          UInt256.land
              (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
              solcAddrMask =
            uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) := by
        simpa [withdrawTokenTokenWord, calldataWord] using hclean
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean']
      exact u256_sub_self _),
    swap2]
  have rd2922 := evm_run rd2909 with [
    push1 ⟨36⟩, calldataload, swap1, dup2, and, dup2, sub,
    push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land (withdrawTokenToWord I) solcAddrMask =
            withdrawTokenToWord I := by
        exact solcAddrMask_clean (by
          simpa [withdrawTokenToWord, calldataWord] using hcanon1)
      have hclean' :
          UInt256.land
              (uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32))
              solcAddrMask =
            uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32) := by
        simpa [withdrawTokenToWord, calldataWord] using hclean
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean']
      exact u256_sub_self _),
    swap1]
  have rd2927 := evm_run rd2922 with [
    push1 ⟨68⟩, calldataload, swap1]
  exact ⟨_, _, evm_run rd2927 with [jump (by native_decide)]⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsWithdrawTokenX_noncanon_token {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (withdrawTokenTokenWord I)
      (UInt256.land (withdrawTokenTokenWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) withdrawTokenPc
      (dispatchArm0Stack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsWithdrawTokenCalldataCheckOk (I := I) hsz100 hsize hhi
  obtain ⟨_, _, rd2875⟩ :=
    cometRewardsWithdrawTokenX_dec2875_args (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach
  have rd2884 := evm_run rd2875 with [
    jumpdest, push1 ⟨96⟩, swap1, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd2884
  rw [hslt] at rd2884
  have rd2888 := evm_run rd2884 with [
    push2 ⟨1004⟩, jumpiNT (by decide)]
  exact evm_run rd2888 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, push1 ⟨4⟩, calldataload, dup3, dup2, and, dup2, sub,
    push2 ⟨1004⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      exact u256_sub_ne_zero_of_ne (by
        intro heq
        have hraw :
            UInt256.eq
                (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
                (UInt256.land
                  (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
                  solcAddrMask) = ⟨1⟩ := by
          rw [← heq]
          exact uInt256_eq_self _
        have hclean :
            UInt256.eq (withdrawTokenTokenWord I)
                (UInt256.land (withdrawTokenTokenWord I) solcAddrMask) = ⟨1⟩ := by
          simpa [withdrawTokenTokenWord, calldataWord] using hraw
        rw [hclean] at hnc
        exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hnc))
      (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsWithdrawTokenX_noncanon_to {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (withdrawTokenTokenWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (withdrawTokenToWord I)
      (UInt256.land (withdrawTokenToWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) withdrawTokenPc
      (dispatchArm0Stack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsWithdrawTokenCalldataCheckOk (I := I) hsz100 hsize hhi
  obtain ⟨_, _, rd2875⟩ :=
    cometRewardsWithdrawTokenX_dec2875_args (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hreach
  have rd2884 := evm_run rd2875 with [
    jumpdest, push1 ⟨96⟩, swap1, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd2884
  rw [hslt] at rd2884
  have rd2888 := evm_run rd2884 with [
    push2 ⟨1004⟩, jumpiNT (by decide)]
  have rd2909 := evm_run rd2888 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, push1 ⟨4⟩, calldataload, dup3, dup2, and, dup2, sub,
    push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land
              (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
              solcAddrMask =
            uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) := by
        have hclean' :
            UInt256.land (withdrawTokenTokenWord I) solcAddrMask =
              withdrawTokenTokenWord I := by
          exact solcAddrMask_clean (by
            simpa [withdrawTokenTokenWord, calldataWord] using hcanon0)
        simpa [withdrawTokenTokenWord, calldataWord] using hclean'
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean]
      exact u256_sub_self _),
    swap2]
  exact evm_run rd2909 with [
    push1 ⟨36⟩, calldataload, swap1, dup2, and, dup2, sub,
    push2 ⟨1004⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      exact u256_sub_ne_zero_of_ne (by
        intro heq
        have hraw :
            UInt256.eq
                (uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32))
                (UInt256.land
                  (uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32))
                  solcAddrMask) = ⟨1⟩ := by
          rw [← heq]
          exact uInt256_eq_self _
        have hclean :
            UInt256.eq (withdrawTokenToWord I)
                (UInt256.land (withdrawTokenToWord I) solcAddrMask) = ⟨1⟩ := by
          simpa [withdrawTokenToWord, calldataWord] using hraw
        rw [hclean] at hnc
        exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hnc))
      (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsX_withdrawToken_revert_auth {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (withdrawTokenTokenWord I).toNat < EVM.addressModulus)
    (hcanon1 : (withdrawTokenToWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I ≠ solcSourceWord I)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) withdrawTokenPc
      (dispatchArm0Stack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2776⟩ :=
    cometRewardsWithdrawTokenX_dec2776_args (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz100 hsize hhi hcanon0 hcanon1 hreach
  have rd2778 := evm_run rd2776 with [jumpdest, dup6]
  obtain ⟨_, _, rd2779₀⟩ := rd2778.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2779⟩ : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2779⟩
      [governorWord σ I, withdrawTokenAmountWord I, withdrawTokenToWord I,
        withdrawTokenTokenWord I, ⟨128⟩, ⟨64⟩, ⟨0⟩, ⟨4⟩,
        cometRewardsSelWord I, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [governorWord] using rd2779₀⟩
  have rd2796₀ := evm_run rd2779 with [
    swap1, swap4, swap2, swap3, swap2, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, caller, sub]
  have rd2796 := rd2796₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd2796
  have hsub : UInt256.sub (solcSourceWord I) (governorReturnWord σ I) ≠ ⟨0⟩ := by
    exact u256_sub_ne_zero_of_ne (by
      intro h
      exact hauth h.symm)
  have hsub' :
      UInt256.sub (UInt256.ofNat I.source.val) (UInt256.land solcAddrMask (governorWord σ I)) ≠
        ⟨0⟩ := by
    simpa [solcSourceWord, governorReturnWord,
      u256_land_comm solcAddrMask (governorWord σ I)] using hsub
  exact evm_run rd2796 with [
    push2 ⟨2811⟩, jumpiT hsub' (by native_decide),
    jumpdest, push4 ⟨431085831⟩, push1 ⟨227⟩, shl, dup2,
    raw mstore 6 (solcReturnMem transferGovernorUnauthorizedSelector)
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rfl)
      (by decide) (by evm_ov),
    caller, dup8, dup3, add,
    raw mstore 3 (transferGovernorUnauthorizedMem (solcSourceWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by decide,
          show (⟨132⟩ : UInt256).toNat = 132 from by decide]
        unfold transferGovernorUnauthorizedMem solcSourceWord
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, swap1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsWithdrawTokenX_dec3915_transfer {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (withdrawTokenTokenWord I).toNat < EVM.addressModulus)
    (hcanon1 : (withdrawTokenToWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I = solcSourceWord I)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) withdrawTokenPc
      (dispatchArm0Stack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3915⟩
      [withdrawTokenTokenWord I, withdrawTokenToWord I, withdrawTokenAmountWord I,
        ⟨1001⟩, ⟨64⟩, ⟨0⟩, ⟨4⟩, cometRewardsSelWord I, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2776⟩ :=
    cometRewardsWithdrawTokenX_dec2776_args (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz100 hsize hhi hcanon0 hcanon1 hreach
  have rd2778 := evm_run rd2776 with [jumpdest, dup6]
  obtain ⟨_, _, rd2779₀⟩ := rd2778.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd2779⟩ : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2779⟩
      [governorWord σ I, withdrawTokenAmountWord I, withdrawTokenToWord I,
        withdrawTokenTokenWord I, ⟨128⟩, ⟨64⟩, ⟨0⟩, ⟨4⟩,
        cometRewardsSelWord I, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [governorWord] using rd2779₀⟩
  have rd2796₀ := evm_run rd2779 with [
    swap1, swap4, swap2, swap3, swap2, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, caller, sub]
  have rd2796 := rd2796₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd2796
  have hsub' :
      UInt256.sub (UInt256.ofNat I.source.val) (UInt256.land solcAddrMask (governorWord σ I)) =
        ⟨0⟩ := by
    have hgovsrc :
        UInt256.land (governorWord σ I) solcAddrMask = UInt256.ofNat I.source.val := by
      simpa [governorReturnWord, solcSourceWord] using hauth
    rw [u256_land_comm solcAddrMask (governorWord σ I), hgovsrc]
    exact u256_sub_self _
  have rd2800 := evm_run rd2796 with [
    push2 ⟨2811⟩, jumpiNT (by simpa using hsub')]
  have rd2810 := evm_run rd2800 with [
    pop, swap1, push2 ⟨1001⟩, swap3, swap2, push2 ⟨3915⟩]
  exact ⟨_, _, evm_run rd2810 with [jump (by native_decide)]⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsWithdrawTokenX_call_transfer {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (withdrawTokenTokenWord I).toNat < EVM.addressModulus)
    (hcanon1 : (withdrawTokenToWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I = solcSourceWord I)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) withdrawTokenPc
      (dispatchArm0Stack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ gasArg k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      withdrawTokenTransferCallPc
      [gasArg, UInt256.land solcAddrMask (withdrawTokenTokenWord I), ⟨0⟩, ⟨128⟩,
        withdrawTokenTransferCallSize, ⟨128⟩, ⟨32⟩, ⟨128⟩, withdrawTokenToWord I,
        withdrawTokenAmountWord I, ⟨1001⟩, ⟨64⟩, ⟨0⟩, ⟨4⟩, cometRewardsSelWord I,
        ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]
      (withdrawTokenTransferCalldataMem (withdrawTokenToWord I) (withdrawTokenAmountWord I))
      (UInt256.ofNat 7) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3915⟩ :=
    cometRewardsWithdrawTokenX_dec3915_transfer (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz100 hsize hhi hcanon0 hcanon1 hauth hreach
  have hcleanTo :
      UInt256.land (withdrawTokenToWord I) solcAddrMask = withdrawTokenToWord I := by
    exact solcAddrMask_clean (by simpa [withdrawTokenToWord, calldataWord] using hcanon1)
  have rd3932 := evm_run rd3915 with [
    jumpdest, push1 ⟨32⟩, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    dup1, swap3, push4 ⟨2835717307⟩, push1 ⟨224⟩, shl, dup3,
    raw mstore 6 withdrawTokenTransferSelectorMem (UInt256.ofNat 5)
      (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rfl)
      (by decide) (by evm_ov)]
  have rd3949 := evm_run rd3932 with [
    dup2, push1 ⟨0⟩, dup2, push2 ⟨3950⟩, dup10, dup10, push1 ⟨4⟩, dup5,
    add, push2 ⟨3888⟩, jump (by native_decide)]
  have rd3901₀ := evm_run rd3949 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2, and,
    dup2]
  have rd3901 := rd3901₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd3901
  have rd3902 := evm_run rd3901 with [
    raw mstore 3 (withdrawTokenTransferArgsMem (withdrawTokenToWord I)) (UInt256.ofNat 6)
      (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by decide,
          show (⟨132⟩ : UInt256).toNat = 132 from by decide]
        unfold withdrawTokenTransferArgsMem
        rw [hcleanTo])
      (by decide) (by evm_ov)]
  have rd3913 := evm_run rd3902 with [
    push1 ⟨32⟩, dup2, add, swap2, swap1, swap2,
    raw mstore 3 (withdrawTokenTransferCalldataMem (withdrawTokenToWord I)
      (withdrawTokenAmountWord I)) (UInt256.ofNat 7)
      (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256) + ⟨4⟩ + ⟨32⟩ = ⟨164⟩ from by decide,
          show (⟨164⟩ : UInt256).toNat = 164 from by decide]
        unfold withdrawTokenTransferCalldataMem
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, add, swap1]
  have rd3962₀ := evm_run rd3913 with [
    jump (by native_decide), jumpdest, sub, swap3, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, and]
  have rd3962 := rd3962₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd3962
  obtain ⟨gasArg, rd3963⟩ := evm_run rd3962 with [gas]
  exact ⟨gasArg, _, _, by
    simpa [withdrawTokenTransferCallPc, withdrawTokenTransferCallSize] using rd3963⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsWithdrawTokenX_call_transfer_made
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (withdrawTokenTokenWord I).toNat < EVM.addressModulus)
    (hcanon1 : (withdrawTokenToWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ_evm I = solcSourceWord I)
    (hdepth : I.depth.val < 1024)
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) withdrawTokenPc
      (dispatchArm0Stack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    ∃ cA' σ'_evm σ'_solm A'_solm z out k C,
      typedCallViaEVM config
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (withdrawTokenTransferTarget I)) "transfer" 0
        (withdrawTokenTransferArgs I)
        (z,
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          out) true ∧
      accountMapEquiv σ'_evm σ'_solm ∧
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (withdrawTokenTransferCallPc + ⟨1⟩) (withdrawTokenPostCallStack z I)
        (withdrawTokenPostCallMem I out) withdrawTokenPostCallAw out
        (cA', σ'_evm) k C ∧
      out.size < 2 ^ 255 := by
  obtain ⟨gasArg, _k0, _C0, rd3963⟩ :=
    cometRewardsWithdrawTokenX_call_transfer (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hwv hsz100 hsize hhi hcanon0 hcanon1 hauth hreach
  have rd3963Call :
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        withdrawTokenTransferCallPc
        (gasArg :: UInt256.land solcAddrMask (withdrawTokenTokenWord I) :: ⟨0⟩ ::
          ⟨128⟩ :: withdrawTokenTransferCallSize :: ⟨128⟩ :: ⟨32⟩ ::
          withdrawTokenPostCallTail I)
        (withdrawTokenTransferCalldataMem (withdrawTokenToWord I)
          (withdrawTokenAmountWord I)) (UInt256.ofNat 7) ByteArray.empty
        (cA, σ_evm) _k0 _C0 := by
    simpa [withdrawTokenPostCallTail] using rd3963
  have hdecCall :
      decode cometRewardsBytecode withdrawTokenTransferCallPc = some (.CALL, .none) := by
    rw [withdrawTokenTransferCallPc_eq]
    native_decide
  obtain ⟨cA', σ'_evm, z, out, A_in, callGas, k', C', hΘ, rd3964, houtSize⟩ :=
    RD.call (t := withdrawTokenPostCallTail I) rd3963Call hdecCall hdepth
      (by simp [withdrawTokenPostCallTail])
  obtain ⟨g'', A'_evm, hΘeq⟩ := hΘ
  have houtSmall : out.size < 2 ^ 138 := by
    exact Theta_returnData_size_lt_2pow138_of_eq
      (blob := I.blobVersionedHashes) (cA := cA)
      (gh := (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).genesisBlockHeader)
      (blocks := (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).blocks)
      (σ := σ_evm)
      (σ₀ := (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).σ₀)
      (A := A_in)
      (s := AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner))
      (o := I.sender)
      (r := AccountAddress.ofUInt256 (UInt256.land solcAddrMask (withdrawTokenTokenWord I)))
      (c := toExecute σ_evm
        (AccountAddress.ofUInt256 (UInt256.land solcAddrMask (withdrawTokenTokenWord I))))
      (g := callGas) (p := UInt256.ofNat I.gasPrice)
      (v := ⟨0⟩) (v' := ⟨0⟩)
      (d := (withdrawTokenTransferCalldataMem (withdrawTokenToWord I)
        (withdrawTokenAmountWord I)).readWithPadding (⟨128⟩ : UInt256).toNat
          withdrawTokenTransferCallSize.toNat)
      (e := I.depth + 1) (H := I.header) (w := I.perm)
      hΘeq
      (by exact Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)
  have houtSign : out.size < 2 ^ 255 := by omega
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hEq
    rw [hEq] at hdepth
    exact absurd hdepth (by decide)
  have hdepthNe :
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.depth ≠
        1024 := by
    simpa [initState] using hdepthNeI
  have htgt := withdrawTokenTransferTarget_eq_targetWord I hcanon0
  have hcd := withdrawTokenTransferCalldataMem_encode_args I hcanon1
  have hcallE :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (withdrawTokenTransferTarget I)) "transfer" 0
        (withdrawTokenTransferArgs I)
        (z,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          out) true := by
    refine callCoincides
      (cfg := config)
      (evm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (name := "transfer") (args := withdrawTokenTransferArgs I)
      (tgt := EVM.address (withdrawTokenTransferTarget I))
      (targetWord := UInt256.land solcAddrMask (withdrawTokenTokenWord I))
      (cA' := cA') (σ' := σ'_evm) (A' := A'_evm) (A_in := A_in)
      (z := z) (o := out) (g'' := g'') (callGas := callGas)
      (mem := withdrawTokenTransferCalldataMem (withdrawTokenToWord I)
        (withdrawTokenAmountWord I))
      (inOff := ⟨128⟩) (inSize := withdrawTokenTransferCallSize)
      (callPerm := true)
      hdepthNe htgt hcd ?_
    simpa [initState, hperm] using hΘeq
  obtain ⟨σ'_solm, A'_solm, hcallSolm, hPostAccounts⟩ :=
    typedCallViaEVM_initState_accountMapEquiv hcallE hAccounts
  exact ⟨cA', σ'_evm, σ'_solm, A'_solm, z, out, k', C',
    hcallSolm, hPostAccounts, by
      simpa [withdrawTokenPostCallStack, withdrawTokenPostCallTail,
        withdrawTokenPostCallMem, withdrawTokenPostCallAw] using rd3964,
    houtSign⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsWithdrawTokenX_afterCall_failure {cA gh bl σ σ₀ A I} {g : Sat256}
    {out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (withdrawTokenTransferCallPc + ⟨1⟩) (withdrawTokenPostCallStack false I)
      (withdrawTokenPostCallMem I out) withdrawTokenPostCallAw out acc k C)
    (houtSize : out.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd3964 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3964⟩ (withdrawTokenPostCallStack false I)
      (withdrawTokenPostCallMem I out) withdrawTokenPostCallAw out acc k C := by
    simpa [withdrawTokenTransferCallPc_eq] using rd
  have rd3876 := evm_run rd3964 with [
    swap1, dup2, iszero, push2 ⟨3876⟩,
    jumpiT (by native_decide) (by jump_dest)]
  let fp : UInt256 :=
    if (⟨64⟩ : UInt256).toNat ≥ (withdrawTokenPostCallMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ withdrawTokenPostCallAw * ⟨32⟩ then
      ⟨0⟩
    else
      UInt256.ofNat (fromByteArrayBigEndian
        ((withdrawTokenPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtSize
  have rd3880pre := evm_run rd3876 with [jumpdest, push1 ⟨64⟩]
  have rd3880 := RD.mload 0 fp withdrawTokenPostCallAw rd3880pre (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        withdrawTokenPostCallAw, withdrawTokenTransferCallSize]
      native_decide)
    (by rfl)
    (by native_decide)
    (by simp)
  have rd3884pre := evm_run rd3880 with [returndatasize, push1 ⟨0⟩, dup3]
  let mem2 : ByteArray :=
    out.write 0 (withdrawTokenPostCallMem I out) fp.toNat rdsz.toNat
  let aw2 : UInt256 :=
    UInt256.ofNat (MachineState.M withdrawTokenPostCallAw.toNat fp.toNat rdsz.toNat)
  have rd3885 := RD.returndatacopy
    (Cₘ aw2 - Cₘ withdrawTokenPostCallAw) mem2 aw2 rd3884pre (by native_decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hrdsz_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2, rdsz])
    (by rfl)
    (by rfl)
    (by simp)
  have rd3887 := evm_run rd3885 with [returndatasize, swap1]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M aw2.toNat fp.toNat rdsz.toNat)) - Cₘ aw2)
    rd3887 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, rdsz])
    (by simp)

set_option maxHeartbeats 1000000 in
theorem cometRewardsWithdrawTokenX_callDepthLimit {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (withdrawTokenTokenWord I).toNat < EVM.addressModulus)
    (hcanon1 : (withdrawTokenToWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I = solcSourceWord I)
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) withdrawTokenPc
      (dispatchArm0Stack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨gasArg, k0, C0, rd3963⟩ :=
    cometRewardsWithdrawTokenX_call_transfer (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hwv hsz100 hsize hhi hcanon0 hcanon1 hauth hreach
  have rd3963Call :
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        withdrawTokenTransferCallPc
        (gasArg :: UInt256.land solcAddrMask (withdrawTokenTokenWord I) :: ⟨0⟩ ::
          ⟨128⟩ :: withdrawTokenTransferCallSize :: ⟨128⟩ :: ⟨32⟩ ::
          withdrawTokenPostCallTail I)
        (withdrawTokenTransferCalldataMem (withdrawTokenToWord I)
          (withdrawTokenAmountWord I)) (UInt256.ofNat 7) ByteArray.empty
        (cA, σ) k0 C0 := by
    simpa [withdrawTokenPostCallTail] using rd3963
  have hdecCall :
      decode cometRewardsBytecode withdrawTokenTransferCallPc = some (.CALL, .none) := by
    rw [withdrawTokenTransferCallPc_eq]
    native_decide
  have hdepthInit :
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.depth = 1024 := by
    simpa [initState] using hdepth
  obtain ⟨k', C', rdPost₀⟩ :=
    RD.callDepthLimit (t := withdrawTokenPostCallTail I) rd3963Call hdecCall
      hdepthInit (by simp [withdrawTokenPostCallTail])
  have rdPost :
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (withdrawTokenTransferCallPc + ⟨1⟩) (withdrawTokenPostCallStack false I)
        (withdrawTokenPostCallMem I ByteArray.empty) withdrawTokenPostCallAw
        ByteArray.empty (cA, σ) k' C' := by
    simpa [withdrawTokenPostCallStack, withdrawTokenPostCallTail, withdrawTokenPostCallMem,
      withdrawTokenPostCallAw, withdrawTokenTransferCallSize] using rdPost₀
  exact cometRewardsWithdrawTokenX_afterCall_failure rdPost (by simp [UInt256.size])

theorem withdrawTokenPostCallMem_read128_of_size_ge (I : ExecutionEnv) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (withdrawTokenPostCallMem I out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold withdrawTokenPostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size)
      (by decide) hout32 houtSize
  rw [hlen]
  exact write32_read_back out
    (withdrawTokenTransferCalldataMem (withdrawTokenToWord I) (withdrawTokenAmountWord I))
    128 hout32 (by rw [withdrawTokenTransferCalldataMem_size]; omega)

theorem withdrawTokenPostCallMem_size_ge160 (I : ExecutionEnv) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    160 ≤ (withdrawTokenPostCallMem I out).size := by
  unfold withdrawTokenPostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size)
      (by decide) hout32 houtSize
  rw [hlen]
  rw [write32_eq out
    (withdrawTokenTransferCalldataMem (withdrawTokenToWord I) (withdrawTokenAmountWord I))
    128 hout32 (by rw [withdrawTokenTransferCalldataMem_size]; omega)]
  simp [withdrawTokenTransferCalldataMem_size]
  omega

theorem withdrawTokenPostCallMem_mload128_haw :
    ¬ (⟨128⟩ : UInt256) ≥ withdrawTokenPostCallAw * ⟨32⟩ := by
  native_decide

theorem withdrawTokenPostCallMem_mload128_of_size_ge (I : ExecutionEnv) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (withdrawTokenPostCallMem I out).size
        ∨ (⟨128⟩ : UInt256) ≥ withdrawTokenPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((withdrawTokenPostCallMem I out).readWithPadding
          (⟨128⟩ : UInt256).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := withdrawTokenPostCallMem I out) (aw := withdrawTokenPostCallAw)
    (off := ⟨128⟩) (memSize := (withdrawTokenPostCallMem I out).size)
    rfl
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      exact lt_of_lt_of_le (by omega) (withdrawTokenPostCallMem_size_ge160 I hout32 houtSize))
    withdrawTokenPostCallMem_mload128_haw
    |>.trans (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        withdrawTokenPostCallMem_read128_of_size_ge I hout32 houtSize])

noncomputable abbrev withdrawTokenPostDecodeMem (I : ExecutionEnv) (out : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray (⟨160⟩ : UInt256)).write 0 (withdrawTokenPostCallMem I out) 64 32

theorem withdrawTokenPostDecodeMem_read128_of_size_ge (I : ExecutionEnv) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (withdrawTokenPostDecodeMem I out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold withdrawTokenPostDecodeMem
  rw [write32_read_above (UInt256.toByteArray (⟨160⟩ : UInt256))
    (withdrawTokenPostCallMem I out) 64 128
    (by rw [toByteArray_size])
    (by exact le_trans (by omega) (withdrawTokenPostCallMem_size_ge160 I hout32 houtSize))
    (by omega)
    (by exact le_trans (by omega) (withdrawTokenPostCallMem_size_ge160 I hout32 houtSize))]
  exact withdrawTokenPostCallMem_read128_of_size_ge I hout32 houtSize

theorem withdrawTokenPostDecodeMem_mload128_of_size_ge (I : ExecutionEnv) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (withdrawTokenPostDecodeMem I out).size
        ∨ (⟨128⟩ : UInt256) ≥ withdrawTokenPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((withdrawTokenPostDecodeMem I out).readWithPadding
          (⟨128⟩ : UInt256).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := withdrawTokenPostDecodeMem I out) (aw := withdrawTokenPostCallAw)
    (off := ⟨128⟩) (memSize := (withdrawTokenPostDecodeMem I out).size)
    rfl
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      unfold withdrawTokenPostDecodeMem
      rw [write32_eq (UInt256.toByteArray (⟨160⟩ : UInt256))
        (withdrawTokenPostCallMem I out) 64 (by rw [toByteArray_size])
        (by exact le_trans (by omega) (withdrawTokenPostCallMem_size_ge160 I hout32 houtSize))]
      simp
      have hsz := withdrawTokenPostCallMem_size_ge160 I hout32 houtSize
      omega)
    withdrawTokenPostCallMem_mload128_haw
    |>.trans (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        withdrawTokenPostDecodeMem_read128_of_size_ge I hout32 houtSize])

theorem withdrawTokenPostDecodeMem_mload64 (I : ExecutionEnv) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (withdrawTokenPostDecodeMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ withdrawTokenPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((withdrawTokenPostDecodeMem I out).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := withdrawTokenPostCallAw) (v := ⟨160⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      unfold withdrawTokenPostDecodeMem
      rw [write32_eq (UInt256.toByteArray (⟨160⟩ : UInt256))
        (withdrawTokenPostCallMem I out) 64 (by rw [toByteArray_size])
        (by exact le_trans (by omega) (withdrawTokenPostCallMem_size_ge160 I hout32 houtSize))]
      simp
      have hsz := withdrawTokenPostCallMem_size_ge160 I hout32 houtSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      unfold withdrawTokenPostDecodeMem
      rw [write32_read_back _ _ 64 (by rw [toByteArray_size])
        (by exact le_trans (by omega) (withdrawTokenPostCallMem_size_ge160 I hout32 houtSize))]
      rw [show (UInt256.toByteArray (⟨160⟩ : UInt256)).extract 0 32 =
          UInt256.toByteArray (⟨160⟩ : UInt256) by
        rw [show 32 = (UInt256.toByteArray (⟨160⟩ : UInt256)).size by
          rw [toByteArray_size]]
        exact byteArray_extract_self _])

set_option maxHeartbeats 1000000 in
theorem cometRewardsWithdrawTokenX_afterCall_toBoolCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    {out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (withdrawTokenTransferCallPc + ⟨1⟩) (withdrawTokenPostCallStack true I)
      (withdrawTokenPostCallMem I out) withdrawTokenPostCallAw out acc k C)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    ∃ k' C', RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3287⟩
      (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) :: ⟨4044⟩ ::
        withdrawTokenToWord I :: withdrawTokenAmountWord I :: ⟨1001⟩ :: ⟨64⟩ ::
        ⟨0⟩ :: ⟨4⟩ :: cometRewardsSelWord I :: ⟨4⟩ :: ⟨224⟩ :: ⟨64⟩ :: ⟨0⟩ :: [])
      (withdrawTokenPostDecodeMem I out) withdrawTokenPostCallAw out acc k' C' := by
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hout32
  have rd3964 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3964⟩ (withdrawTokenPostCallStack true I)
      (withdrawTokenPostCallMem I out) withdrawTokenPostCallAw out acc k C := by
    simpa [withdrawTokenTransferCallPc_eq] using rd
  have rd4031₀ := evm_run rd3964 with [
    swap1, dup2, iszero, push2 ⟨3876⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap2, push2 ⟨4020⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push2 ⟨4044⟩, swap2, pop, push1 ⟨32⟩, returndatasize, dup2, gt]
  have rd4031 := rd4031₀
  rw [show UInt256.ofNat out.size = rdsz from rfl, hgt] at rd4031
  have rd3071 := evm_run rd4031 with [
    push2 ⟨2249⟩, jumpiNT (by native_decide),
    push2 ⟨2235⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2, add,
    swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt, swap1, dup3,
    lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (withdrawTokenPostDecodeMem I out) withdrawTokenPostCallAw
      (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold withdrawTokenPostDecodeMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3274 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, swap1, push2 ⟨3274⟩,
    jump (by jump_dest)]
  have rd3286 := evm_run rd3274 with [
    jumpdest, swap1, dup2, push1 ⟨32⟩, swap2, sub, slt, push2 ⟨1004⟩,
    jumpiNT (by native_decide)]
  exact ⟨_, _, evm_run rd3286 with [
    raw mload 0 (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
      withdrawTokenPostCallAw (by native_decide) mem_cost
      (withdrawTokenPostDecodeMem_mload128_of_size_ge I hout32 houtSize)
      (by native_decide) (by evm_ov)]⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsWithdrawTokenX_afterCall_true_return {cA gh bl σ σ₀ A I} {g : Sat256}
    {out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (withdrawTokenTransferCallPc + ⟨1⟩) (withdrawTokenPostCallStack true I)
      (withdrawTokenPostCallMem I out) withdrawTokenPostCallAw out acc k C)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨1⟩) :
    RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) acc ByteArray.empty := by
  obtain ⟨_, _, rd3287₀⟩ :=
    cometRewardsWithdrawTokenX_afterCall_toBoolCheck (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd hout32 houtSize
  have rd3287 := rd3287₀
  rw [hword] at rd3287
  have rd3978 := evm_run rd3287 with [
    dup1, iszero, iszero, dup2, sub, push2 ⟨1004⟩, jumpiNT (by native_decide),
    swap1, jump (by jump_dest), jumpdest, codesize, push2 ⟨3978⟩, jump (by jump_dest)]
  have rd1001 := evm_run rd3978 with [
    jumpdest, pop, iszero, push2 ⟨3988⟩, jumpiNT (by native_decide),
    pop, pop, jump (by jump_dest), jumpdest]
  have rd1003 := evm_run rd1001 with [
    raw mload 0 ⟨160⟩ withdrawTokenPostCallAw (by native_decide)
      mem_cost (withdrawTokenPostDecodeMem_mload64 I hout32 houtSize)
      (by native_decide) (by evm_ov)]
  exact RD.ret 0 ByteArray.empty rd1003 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, withdrawTokenPostCallAw]
      native_decide)
    (by exact byteArray_readWithPadding_zero _ 160)
    (by simp)

set_option maxHeartbeats 1000000 in
theorem cometRewardsWithdrawTokenX_afterCall_noncanon_revert {cA gh bl σ σ₀ A I}
    {g : Sat256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (withdrawTokenTransferCallPc + ⟨1⟩) (withdrawTokenPostCallStack true I)
      (withdrawTokenPostCallMem I out) withdrawTokenPostCallAw out acc k C)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size)
    (hnz : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨0⟩)
    (hno : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨1⟩) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let word : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
  have hnzWord : word ≠ ⟨0⟩ := by simpa [word] using hnz
  have hnoWord : word ≠ ⟨1⟩ := by simpa [word] using hno
  have hiszero : UInt256.isZero word = ⟨0⟩ := isZero_eq_zero_of_ne hnzWord
  have hcanon : UInt256.isZero (UInt256.isZero word) = ⟨1⟩ := by
    rw [hiszero]
    native_decide
  have hsub : UInt256.sub word (UInt256.isZero (⟨0⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by native_decide]
    exact u256_sub_ne_zero_of_ne hnoWord
  obtain ⟨kBool, CBool, rd3287₀⟩ :=
    cometRewardsWithdrawTokenX_afterCall_toBoolCheck (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd hout32 houtSize
  have rd3287 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3287⟩
      (word :: ⟨4044⟩ :: withdrawTokenToWord I :: withdrawTokenAmountWord I :: ⟨1001⟩ ::
        ⟨64⟩ :: ⟨0⟩ :: ⟨4⟩ :: cometRewardsSelWord I :: ⟨4⟩ :: ⟨224⟩ :: ⟨64⟩ ::
        ⟨0⟩ :: [])
      (withdrawTokenPostDecodeMem I out) withdrawTokenPostCallAw out acc kBool CBool := by
    simpa [word] using rd3287₀
  have rd3292 := evm_run rd3287 with [dup1, iszero, iszero, dup2, sub]
  rw [hiszero] at rd3292
  have rd1004 := evm_run rd3292 with [
    push2 ⟨1004⟩, jumpiT hsub (by jump_dest)]
  exact evm_run rd1004 with [
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

noncomputable abbrev withdrawTokenPostShortDecodeMem (I : ExecutionEnv) (out : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray ((⟨128⟩ : UInt256) +
    UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat out.size + ⟨31⟩))).write 0
      (withdrawTokenPostCallMem I out) 64 32

set_option maxHeartbeats 1000000 in
theorem cometRewardsWithdrawTokenX_afterCall_short_revert {cA gh bl σ σ₀ A I}
    {g : Sat256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (withdrawTokenTransferCallPc + ⟨1⟩) (withdrawTokenPostCallStack true I)
      (withdrawTokenPostCallMem I out) withdrawTokenPostCallAw out acc k C)
    (hshort : out.size < 32) (houtSize : out.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨1⟩ := by
    apply ugt_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hshort
  have rd3964 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨3964⟩ (withdrawTokenPostCallStack true I)
      (withdrawTokenPostCallMem I out) withdrawTokenPostCallAw out acc k C := by
    simpa [withdrawTokenTransferCallPc_eq] using rd
  have rd4031₀ := evm_run rd3964 with [
    swap1, dup2, iszero, push2 ⟨3876⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap2, push2 ⟨4020⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, push2 ⟨4044⟩, swap2, pop, push1 ⟨32⟩, returndatasize, dup2, gt]
  have rd4031 := rd4031₀
  rw [show UInt256.ofNat out.size = rdsz from rfl, hgt] at rd4031
  let rounded : UInt256 := UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat out.size + ⟨31⟩)
  let ptr : UInt256 := (⟨128⟩ : UInt256) + rounded
  have hroundedLe : rounded.toNat ≤ out.size + 31 := by
    unfold rounded
    rw [uland_toNat]
    refine le_trans Nat.and_le_right ?_
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt houtSize,
      show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    exact Nat.mod_le _ _
  have hptr_toNat : ptr.toNat = 128 + rounded.toNat := by
    unfold ptr
    rw [uadd_toNat, show (⟨128⟩ : UInt256).toNat = 128 from by decide]
    exact Nat.mod_eq_of_lt (by
      have hroundSmall : rounded.toNat < 64 := by omega
      have hsz : UInt256.size = 2 ^ 256 := by decide
      omega)
  have hltPtr : UInt256.lt ptr (⟨128⟩ : UInt256) = ⟨0⟩ := by
    apply ult_zero
    rw [hptr_toNat, show (⟨128⟩ : UInt256).toNat = 128 from by decide]
    omega
  have hmax64 :
      (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩).toNat =
        18446744073709551615 := by
    native_decide
  have hgtPtr :
      UInt256.gt ptr (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    rw [hptr_toNat, hmax64]
    omega
  have hallocOk :
      UInt256.lor (UInt256.lt ptr (⟨128⟩ : UInt256))
        (UInt256.gt ptr (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)) = ⟨0⟩ := by
    rw [hltPtr, hgtPtr]
    native_decide
  have rd3071 := evm_run rd4031 with [
    push2 ⟨2249⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, returndatasize, push2 ⟨2225⟩, jump (by jump_dest),
    jumpdest, push2 ⟨2235⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2, add,
    swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt, swap1, dup3,
    lt, lor, push2 ⟨3003⟩, jumpiNT (by simpa [ptr, rounded] using hallocOk),
    push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (withdrawTokenPostShortDecodeMem I out) withdrawTokenPostCallAw
      (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
      (by native_decide) (by evm_ov)]
  have rd3274 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, swap1, push2 ⟨3274⟩,
    jump (by jump_dest)]
  have hlenCheck :
      UInt256.slt (UInt256.sub ((⟨128⟩ : UInt256) + rdsz) ⟨128⟩) ⟨32⟩ = ⟨1⟩ := by
    simpa [rdsz] using solcDecodeEndLenCheckShort_128_32 (len := out.size) hshort
  have rd3282₀ := evm_run rd3274 with [
    jumpdest, swap1, dup2, push1 ⟨32⟩, swap2, sub, slt]
  have rd3282 := rd3282₀
  rw [hlenCheck] at rd3282
  have rd1004 := evm_run rd3282 with [
    push2 ⟨1004⟩, jumpiT (by native_decide) (by jump_dest)]
  exact evm_run rd1004 with [
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

abbrev withdrawTokenTransferOutFailedSelectorWord : UInt256 := ⟨1881067739⟩

abbrev withdrawTokenTransferOutFailedSelectorShifted : UInt256 :=
  UInt256.shiftLeft withdrawTokenTransferOutFailedSelectorWord ⟨224⟩

noncomputable abbrev withdrawTokenTransferOutFailedSelectorMem
    (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  (UInt256.toByteArray withdrawTokenTransferOutFailedSelectorShifted).write 0
    (withdrawTokenPostDecodeMem I out) 160 32

noncomputable abbrev withdrawTokenTransferOutFailedArgsMem
    (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.land (withdrawTokenToWord I) solcAddrMask)).write 0
    (withdrawTokenTransferOutFailedSelectorMem I out) 164 32

noncomputable abbrev withdrawTokenTransferOutFailedMem
    (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  (UInt256.toByteArray (withdrawTokenAmountWord I)).write 0
    (withdrawTokenTransferOutFailedArgsMem I out) 196 32

set_option maxHeartbeats 1000000 in
theorem cometRewardsWithdrawTokenX_afterCall_false_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {out : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      (withdrawTokenTransferCallPc + ⟨1⟩) (withdrawTokenPostCallStack true I)
      (withdrawTokenPostCallMem I out) withdrawTokenPostCallAw out acc k C)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3287₀⟩ :=
    cometRewardsWithdrawTokenX_afterCall_toBoolCheck (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) rd hout32 houtSize
  have rd3287 := rd3287₀
  rw [hword] at rd3287
  have rd3988 := evm_run rd3287 with [
    dup1, iszero, iszero, dup2, sub, push2 ⟨1004⟩, jumpiNT (by native_decide),
    swap1, jump (by jump_dest), jumpdest, codesize, push2 ⟨3978⟩, jump (by jump_dest),
    jumpdest, pop, iszero, push2 ⟨3988⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd3994 := evm_run rd3988 with [jumpdest, push2 ⟨4016⟩, push1 ⟨64⟩]
  have rd3995 := evm_run rd3994 with [
    raw mload 0 ⟨160⟩ withdrawTokenPostCallAw (by native_decide)
      mem_cost (withdrawTokenPostDecodeMem_mload64 I hout32 houtSize)
      (by native_decide) (by evm_ov)]
  have rd4007 := evm_run rd3995 with [
    swap3, dup4, swap3, push4 withdrawTokenTransferOutFailedSelectorWord,
    push1 ⟨224⟩, shl, dup5,
    raw mstore 0 (withdrawTokenTransferOutFailedSelectorMem I out)
      withdrawTokenPostCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide])
      (by native_decide) (by evm_ov)]
  have rd3901 := evm_run rd4007 with [
    push1 ⟨4⟩, dup5, add, push2 ⟨3888⟩, jump (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2,
    and, dup2]
  have rd3902 := evm_run rd3901 with [
    raw mstore 0 (withdrawTokenTransferOutFailedArgsMem I out)
      withdrawTokenPostCallAw (by native_decide) mem_cost
      (by
        rw [show ((⟨160⟩ : UInt256) + ⟨4⟩).toNat = 164 from by native_decide]
        unfold withdrawTokenTransferOutFailedArgsMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3909 := evm_run rd3902 with [
    push1 ⟨32⟩, dup2, add, swap2, swap1, swap2,
    raw mstore (Cₘ (UInt256.ofNat 8) - Cₘ withdrawTokenPostCallAw)
      (withdrawTokenTransferOutFailedMem I out) (UInt256.ofNat 8)
      (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          withdrawTokenPostCallAw]
        native_decide)
      (by
        rw [show ((⟨160⟩ : UInt256) + ⟨4⟩ + ⟨32⟩).toNat = 196 from by native_decide])
      (by native_decide) (by evm_ov)]
  exact evm_run rd3909 with [
    push1 ⟨64⟩, add, swap1, jump (by jump_dest), jumpdest, sub, swap1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

/-- `withdrawToken(address,address,uint256)` body, reached at pc 2758. -/
theorem cometRewardsWithdrawTokenBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cometRewardsBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cometRewardsSelBytes 0))
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) withdrawTokenPc
      (dispatchArm0Stack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz4 := cometRewardsWithdrawTokenSelector_size hsel
  have hd := cometRewardsDispatch_withdrawToken (cd := I.calldata) hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon0 : (withdrawTokenTokenWord I).toNat < EVM.addressModulus
      · by_cases hcanon1 : (withdrawTokenToWord I).toNat < EVM.addressModulus
        · have hdec :=
            cometRewardsDecode_withdrawToken_ok (I := I) hsz100 hhi hcanon0 hcanon1
          have hword : governorWord σ_evm I = governorWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
          have hretWord : governorReturnWord σ_evm I = governorReturnWord σ_solm I := by
            simp [governorReturnWord, hword]
          by_cases hauth : governorReturnWord σ_evm I = solcSourceWord I
          · have hauthSolm : governorReturnWord σ_solm I = solcSourceWord I := by
              rw [← hretWord]
              exact hauth
            have hgovSolm :
                UInt256.land (Solm.EVM.storageLoad
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                  ⟨0⟩) solcAddrMask =
                  solcSourceWord
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv := by
              simpa [governorReturnWord, governorWord, initState, Solm.EVM.storageLoad,
                State.lookupAccount] using hauthSolm
            by_cases hdepth : I.depth.val < 1024
            · obtain ⟨cA', σ'_evm, σ'_solm, A'_solm, z, out, kPost, CPost,
                  hcallS, hPostAccounts, rdPost, houtSign⟩ :=
                cometRewardsWithdrawTokenX_call_transfer_made
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hperm hwv hsz100 hsize hhi hcanon0 hcanon1 hauth hdepth hreach
                  hAccounts
              let evmPost : EVM.State :=
                { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σ'_solm
                    substate := A'_solm
                    createdAccounts := cA' }
              have houtSize : out.size < UInt256.size := lt_size_of_lt_sign houtSign
              cases z
              · have hbody :
                    ExecTransitionBody config contract
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      (withdrawTokenStore I)
                      withdrawTokenTransition.body .reverted := by
                  exact cometRewardsWithdrawTokenBodyReverts_callFailure
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    evmPost I
                    (by simp only [initState]; exact hwv)
                    (by simp only [initState]; exact hhi)
                    hgovSolm
                    (by simpa [evmPost] using hcallS)
                exact (cometRewardsWithdrawTokenX_afterCall_failure rdPost houtSize)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
              · by_cases hshort : out.size < 32
                · have hdecTransfer := cometRewardsTransfer_decode_none_short
                    (out := out) hshort
                  have hbody :
                      ExecTransitionBody config contract
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                        (withdrawTokenStore I)
                        withdrawTokenTransition.body .reverted := by
                    exact cometRewardsWithdrawTokenBodyReverts_decode
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      evmPost I
                      (by simp only [initState]; exact hwv)
                      (by simp only [initState]; exact hhi)
                      hgovSolm
                      (by simpa [evmPost] using hcallS)
                      hdecTransfer
                  exact (cometRewardsWithdrawTokenX_afterCall_short_revert
                      rdPost hshort houtSize)
                    |>.reEquivExecutionRevert hcode hd hdec hbody
                · have hout32 : 32 ≤ out.size := by omega
                  let word : UInt256 :=
                    UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
                  by_cases hzero : word = ⟨0⟩
                  · have hdecTransfer := cometRewardsTransfer_decode_false
                      (out := out) hout32 houtSign (by simpa [word] using hzero)
                    have hbody :
                        ExecTransitionBody config contract
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          (withdrawTokenStore I)
                          withdrawTokenTransition.body .reverted := by
                      exact cometRewardsWithdrawTokenBodyReverts_false
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                        evmPost I
                        (by simp only [initState]; exact hwv)
                        (by simp only [initState]; exact hhi)
                        hgovSolm
                        (by simpa [evmPost] using hcallS)
                        hdecTransfer
                    exact (cometRewardsWithdrawTokenX_afterCall_false_revert
                        rdPost hout32 houtSize (by simpa [word] using hzero))
                      |>.reEquivExecutionRevert hcode hd hdec hbody
                  · by_cases hone : word = ⟨1⟩
                    · have hdecTransfer := cometRewardsTransfer_decode_true
                        (out := out) hout32 houtSign (by simpa [word] using hone)
                      have hbody :
                          ExecTransitionBody config contract
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            (withdrawTokenStore I)
                            withdrawTokenTransition.body
                            (.returned
                              (resumeAfterInternalCall
                                (withdrawTokenFrame
                                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
                                "_sent" none)
                              evmPost none) := by
                        exact cometRewardsWithdrawTokenBodyReturns_true
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          evmPost I
                          (by simp only [initState]; exact hwv)
                          (by simp only [initState]; exact hhi)
                          hgovSolm
                          (by simpa [evmPost] using hcallS)
                          hdecTransfer
                      exact (cometRewardsWithdrawTokenX_afterCall_true_return
                          rdPost hout32 houtSize (by simpa [word] using hone))
                        |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                          (by simp [evmPost])
                          (by simpa [evmPost] using hPostAccounts)
                          (returnEquiv.fallthrough rfl rfl (by native_decide))
                    · have hdecTransfer := cometRewardsTransfer_decode_none_noncanon
                        (out := out) hout32 houtSign
                        (by simpa [word] using hzero)
                        (by simpa [word] using hone)
                      have hbody :
                          ExecTransitionBody config contract
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            (withdrawTokenStore I)
                            withdrawTokenTransition.body .reverted := by
                        exact cometRewardsWithdrawTokenBodyReverts_decode
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          evmPost I
                          (by simp only [initState]; exact hwv)
                          (by simp only [initState]; exact hhi)
                          hgovSolm
                          (by simpa [evmPost] using hcallS)
                          hdecTransfer
                      exact (cometRewardsWithdrawTokenX_afterCall_noncanon_revert
                          rdPost hout32 houtSize
                          (by simpa [word] using hzero)
                          (by simpa [word] using hone))
                        |>.reEquivExecutionRevert hcode hd hdec hbody
            · rw [not_lt] at hdepth
              have hdepth1024 : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
              let evmInit : EVM.State :=
                initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
              let evmFail : EVM.State :=
                { evmInit with
                    substate :=
                      (evmInit.addAccessedAccount
                        (EVM.address (withdrawTokenTransferTarget I))).substate }
              have hcallS :
                  typedCallViaEVM config evmInit
                    (EVM.address (withdrawTokenTransferTarget I)) "transfer" 0
                    (withdrawTokenTransferArgs I)
                    (false, evmFail, ByteArray.empty) true := by
                exact callNotMade_depthLimit
                  (cfg := config) (evm := evmInit)
                  (tgt := EVM.address (withdrawTokenTransferTarget I))
                  (name := "transfer") (args := withdrawTokenTransferArgs I)
                  (calldata :=
                    (withdrawTokenTransferCalldataMem
                      (withdrawTokenToWord I) (withdrawTokenAmountWord I)).readWithPadding
                        128 withdrawTokenTransferCallSize.toNat)
                  (callPerm := true)
                  (withdrawTokenTransferCalldataMem_encode_args I hcanon1)
                  (by simpa [evmInit, initState] using hdepth1024)
              have hbody :
                  ExecTransitionBody config contract
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (withdrawTokenStore I)
                    withdrawTokenTransition.body .reverted := by
                exact cometRewardsWithdrawTokenBodyReverts_callFailure
                  evmInit evmFail I
                  (by simp only [evmInit, initState]; exact hwv)
                  (by simp only [evmInit, initState]; exact hhi)
                  (by simpa [evmInit] using hgovSolm)
                  hcallS
              exact (cometRewardsWithdrawTokenX_callDepthLimit
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g)
                  hwv hsz100 hsize hhi hcanon0 hcanon1 hauth hreach hdepth1024)
                |>.reEquivExecutionRevert hcode hd hdec hbody
          · have hauthSolm :
                governorReturnWord σ_solm I ≠ solcSourceWord I := by
              intro hbad
              exact hauth (by
                rw [hretWord]
                exact hbad)
            have hbody :
                ExecTransitionBody config contract
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (withdrawTokenStore I)
                  withdrawTokenTransition.body .reverted := by
              exact cometRewardsWithdrawTokenBodyReverts_auth
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv)
                (by simp only [initState]; exact hhi)
                (by
                  simpa [governorReturnWord, governorWord, initState, Solm.EVM.storageLoad,
                    State.lookupAccount] using hauthSolm)
            exact (cometRewardsX_withdrawToken_revert_auth (g := Sat256.ofUInt256 g)
                hwv hsz100 hsize hhi hcanon0 hcanon1 hauth hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hdec := cometRewardsDecode_withdrawToken_none_noncanon_to
            (I := I) hsz100 hhi hcanon0 hcanon1
          have hnc : UInt256.eq (withdrawTokenToWord I)
              (UInt256.land (withdrawTokenToWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne
              (fun he => hcanon1 (solcAddrCanonical_of_clean he))
          exact (cometRewardsWithdrawTokenX_noncanon_to (g := Sat256.ofUInt256 g)
              hwv hsz100 hsize hhi hcanon0 hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := cometRewardsDecode_withdrawToken_none_noncanon_token
          (I := I) hsz100 hhi hcanon0
        have hnc : UInt256.eq (withdrawTokenTokenWord I)
            (UInt256.land (withdrawTokenTokenWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne
            (fun he => hcanon0 (solcAddrCanonical_of_clean he))
        exact (cometRewardsWithdrawTokenX_noncanon_token (g := Sat256.ofUInt256 g)
            hwv hsz100 hsize hhi hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := cometRewardsDecode_withdrawToken_none_huge (I := I) hbig
      exact (cometRewardsWithdrawTokenX_hugearg (g := Sat256.ofUInt256 g)
          hwv hsize hbig hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 100 := by omega
    have hdec := cometRewardsDecode_withdrawToken_none_short (I := I) hsz4 hshort
    exact (cometRewardsWithdrawTokenX_shortarg (g := Sat256.ofUInt256 g)
        hwv hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.CompoundIII.CometRewards
