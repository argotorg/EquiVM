import Benchmarks.CompoundIII.CometRewards.Common
import Benchmarks.CompoundIII.CometRewards.Governor
import Benchmarks.CompoundIII.CometRewards.TransferGovernor
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

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
  simp [doTransferOutFunction, withdrawTokenArgs, withdrawTokenStore, withdrawTokenTokenValue,
    doTransferOutStore, withdrawTokenToValue, withdrawTokenAmountValue, bindParams?]

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
    (solm' := { contract := contract, locals := withdrawTokenCallStore I false })
    (evm' := evm') ?_ ?_
  · exact ExecStmt.externalCallSuccess
      (evalExpr_doTransferOut_var_token evm I)
      (by simp [evalExpr?, pure])
      (evalExprs_doTransferOut_transfer_args evm I)
      hcall hdec
  · exact ExecBlock.consRevert
      (ExecStmt.requireFalse (evalExpr_withdrawToken_success evm' I false))

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
    (solm' := { contract := contract, locals := withdrawTokenCallStore I true })
    (evm' := evm') ?_ ?_
  · exact ExecStmt.externalCallSuccess
      (evalExpr_doTransferOut_var_token evm I)
      (by simp [evalExpr?, pure])
      (evalExprs_doTransferOut_transfer_args evm I)
      hcall hdec
  · exact ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_withdrawToken_success evm' I true))
      ExecBlock.nil

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
          · sorry
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
