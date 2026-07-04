import Examples.UniswapV2Pair.MathRoutines
import Examples.UniswapV2Pair.MintRoutines
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace UniswapV2Pair

/-! # Shared `_mintFee` source helpers -/

abbrev mintFeeReserve0Value (reserve0 : UInt256) : Value :=
  uniswapUint256Value reserve0

abbrev mintFeeReserve1Value (reserve1 : UInt256) : Value :=
  uniswapUint256Value reserve1

abbrev mintFeeCallStore (reserve0 reserve1 : UInt256) : Store :=
  ((∅ : Store).insert "_reserve1" (mintFeeReserve1Value reserve1)).insert "_reserve0"
    (mintFeeReserve0Value reserve0)

abbrev mintFeeCallFrame (reserve0 reserve1 : UInt256) : Frame :=
  { contract := contract, locals := mintFeeCallStore reserve0 reserve1 }

theorem mintFeeCallStore_reserve0 (reserve0 reserve1 : UInt256) :
    (mintFeeCallStore reserve0 reserve1).get? "_reserve0" =
      some (mintFeeReserve0Value reserve0) := by
  rw [mintFeeCallStore, store_get_self]

theorem mintFeeCallStore_reserve1 (reserve0 reserve1 : UInt256) :
    (mintFeeCallStore reserve0 reserve1).get? "_reserve1" =
      some (mintFeeReserve1Value reserve1) := by
  rw [mintFeeCallStore, store_get_ne _ _ (by decide), store_get_self]

theorem mintFeeCallStore_factory (reserve0 reserve1 : UInt256) :
    (mintFeeCallStore reserve0 reserve1).get? "factory" = none := by
  rw [mintFeeCallStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem mintFeeCallStore_kLast (reserve0 reserve1 : UInt256) :
    (mintFeeCallStore reserve0 reserve1).get? "kLast" = none := by
  rw [mintFeeCallStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem mintFeeCallStore_totalSupply (reserve0 reserve1 : UInt256) :
    (mintFeeCallStore reserve0 reserve1).get? "totalSupply" = none := by
  rw [mintFeeCallStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem mintFeeCallStore_balanceOf (reserve0 reserve1 : UInt256) :
    (mintFeeCallStore reserve0 reserve1).get? "balanceOf" = none := by
  rw [mintFeeCallStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_mintFee_reserve0 (evm : EVM.State) (reserve0 reserve1 : UInt256) :
    evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm (.var "_reserve0") =
      .ok (mintFeeReserve0Value reserve0) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeCallStore_reserve0]

theorem evalExpr_mintFee_reserve1 (evm : EVM.State) (reserve0 reserve1 : UInt256) :
    evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm (.var "_reserve1") =
      .ok (mintFeeReserve1Value reserve1) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeCallStore_reserve1]

theorem evalExpr_mintFee_factory (evm : EVM.State) (reserve0 reserve1 : UInt256) :
    evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm (.storage factoryRef) =
      .ok (.address (uniswapAddressAtSlot evm ⟨5⟩)) := by
  exact evalExpr_uniswap_storage_address evm (mintFeeCallStore reserve0 reserve1)
    (er := { base := "factory", steps := [] }) (slot := ⟨5⟩)
    (by simp [factoryRef])
    (by simp [evalStorageRef, evalStorageRefSteps, factoryRef, EvalResult.bind, pure, bind])
    (by decide) (by rfl)

theorem evalStorageRef_mintFee_kLast (evm : EVM.State) (reserve0 reserve1 : UInt256) :
    evalStorageRef config (mintFeeCallFrame reserve0 reserve1) evm kLastRef =
      .ok ({ base := "kLast", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, kLastRef, EvalResult.bind, pure, bind]

theorem evalExpr_mintFee_kLast (evm : EVM.State) (reserve0 reserve1 : UInt256) :
    evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm (.storage kLastRef) =
      .ok (uniswapUint256Value (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [kLastRef])
    (her := evalStorageRef_mintFee_kLast evm reserve0 reserve1)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (uniswapStorageLocLoad_uint256 evm ⟨11⟩)

theorem uniswapLookupMintFeeFunction :
    lookupCallable? contract "_mintFee" = some mintFeeFunction.toCallable := by
  rfl

theorem bindParams_mintFeeFunction_call (reserve0 reserve1 : UInt256) :
    bindParams? mintFeeFunction.params
      [mintFeeReserve0Value reserve0, mintFeeReserve1Value reserve1] =
      some (mintFeeCallStore reserve0 reserve1) := by
  simp [bindParams?, mintFeeFunction, mintFeeCallStore, mintFeeReserve0Value,
    mintFeeReserve1Value]

abbrev mintFeeAfterFeeToStore
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) : Store :=
  (mintFeeCallStore reserve0 reserve1).insert "feeTo" (.address feeTo)

abbrev mintFeeAfterFeeToFrame
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) : Frame :=
  { contract := contract, locals := mintFeeAfterFeeToStore reserve0 reserve1 feeTo }

theorem mintFeeAfterFeeToStore_feeTo
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) :
    (mintFeeAfterFeeToStore reserve0 reserve1 feeTo).get? "feeTo" =
      some (.address feeTo) := by
  rw [mintFeeAfterFeeToStore, store_get_self]

theorem mintFeeAfterFeeToStore_kLast
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) :
    (mintFeeAfterFeeToStore reserve0 reserve1 feeTo).get? "kLast" = none := by
  rw [mintFeeAfterFeeToStore, store_get_ne _ _ (by decide), mintFeeCallStore_kLast]

theorem evalExpr_mintFee_afterFeeTo_feeTo
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) :
    evalExpr? config (mintFeeAfterFeeToFrame reserve0 reserve1 feeTo) evm (.var "feeTo") =
      .ok (.address feeTo) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterFeeToStore_feeTo]

theorem evalExpr_mintFee_zeroAddr (frame : Frame) (evm : EVM.State) :
    evalExpr? config frame evm zeroAddr = .ok (.address (AccountAddress.ofNat 0)) := by
  simp only [zeroAddr, evalExpr?, castValue?, addrSt, EvalResult.ofOption,
    EvalResult.bind, bind, pure]
  norm_num

theorem evalExpr_mintFee_feeOn_true
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0) :
    evalExpr? config (mintFeeAfterFeeToFrame reserve0 reserve1 feeTo) evm
      (.binary .ne (.var "feeTo") zeroAddr) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_mintFee_afterFeeTo_feeTo evm reserve0 reserve1 feeTo,
    evalExpr_mintFee_zeroAddr (mintFeeAfterFeeToFrame reserve0 reserve1 feeTo) evm,
    EvalResult.bind, bind]
  simp [evalBinaryOp?, hfeeTo]

theorem evalExpr_mintFee_feeOn_false
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (hfeeTo : feeTo = AccountAddress.ofNat 0) :
    evalExpr? config (mintFeeAfterFeeToFrame reserve0 reserve1 feeTo) evm
      (.binary .ne (.var "feeTo") zeroAddr) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_mintFee_afterFeeTo_feeTo evm reserve0 reserve1 feeTo,
    evalExpr_mintFee_zeroAddr (mintFeeAfterFeeToFrame reserve0 reserve1 feeTo) evm,
    EvalResult.bind, bind]
  simp [evalBinaryOp?, hfeeTo]

theorem uniswapMintFeeCheckedCallNoCode
    (evm : EVM.State) (reserve0 reserve1 : UInt256)
    (hguard :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
        (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool false)) :
    ExecBlock config (mintFeeCallFrame reserve0 reserve1) evm
      (checkedExternalCallStmts (.storage factoryRef) "feeTo" (.intLit 0) [] "feeTo"
        (perm := false))
      .reverted := by
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := mintFeeCallStore reserve0 reserve1)
      (receiver := .storage factoryRef) (name := "feeTo") (sendVal := 0)
      (args := []) (retVar := "feeTo") (perm := false)
      hguard

theorem uniswapMintFeeCheckedCallFailure
    (evm evmFee : EVM.State) (reserve0 reserve1 : UInt256) {out : ByteArray}
    (hguard :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
        (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
      "feeTo" 0 [] (false, evmFee, out) false) :
    ExecBlock config (mintFeeCallFrame reserve0 reserve1) evm
      (checkedExternalCallStmts (.storage factoryRef) "feeTo" (.intLit 0) [] "feeTo"
        (perm := false))
      .reverted := by
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmFee)
      (locals := mintFeeCallStore reserve0 reserve1)
      (receiver := .storage factoryRef) (name := "feeTo") (sendVal := 0)
      (args := []) (retVar := "feeTo") (perm := false)
      (target := uniswapAddressAtSlot evm ⟨5⟩) (out := out)
      hguard
      (evalExpr_mintFee_factory evm reserve0 reserve1)
      (by rfl)
      hcall

theorem uniswapMintFeeCheckedCallDecodeRevert
    (evm evmFee : EVM.State) (reserve0 reserve1 : UInt256) {out : ByteArray}
    (hguard :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
        (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = none) :
    ExecBlock config (mintFeeCallFrame reserve0 reserve1) evm
      (checkedExternalCallStmts (.storage factoryRef) "feeTo" (.intLit 0) [] "feeTo"
        (perm := false))
      .reverted := by
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm) (evm' := evmFee)
      (locals := mintFeeCallStore reserve0 reserve1)
      (receiver := .storage factoryRef) (name := "feeTo") (sendVal := 0)
      (args := []) (retVar := "feeTo") (perm := false)
      (target := uniswapAddressAtSlot evm ⟨5⟩) (out := out)
      hguard
      (evalExpr_mintFee_factory evm reserve0 reserve1)
      (by rfl)
      hcall hdec

theorem uniswapMintFeeFunctionBody_reverts_noCode
    (evm : EVM.State) (reserve0 reserve1 : UInt256)
    (hguard :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
        (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool false)) :
    ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
    .reverted := by
  have hchecked := uniswapMintFeeCheckedCallNoCode evm reserve0 reserve1 hguard
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintFeeFunction, List.append_assoc] using
      (Reasoning.Refinement.execBlock_append_term hchecked (by intro f e h; cases h)))

theorem uniswapMintFeeFunctionBody_reverts_callFailure
    (evm evmFee : EVM.State) (reserve0 reserve1 : UInt256) {out : ByteArray}
    (hguard :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
        (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
      "feeTo" 0 [] (false, evmFee, out) false) :
    ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
      .reverted := by
  have hchecked :=
    uniswapMintFeeCheckedCallFailure evm evmFee reserve0 reserve1 hguard hcall
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintFeeFunction, List.append_assoc] using
      (Reasoning.Refinement.execBlock_append_term hchecked (by intro f e h; cases h)))

theorem uniswapMintFeeFunctionBody_reverts_decode
    (evm evmFee : EVM.State) (reserve0 reserve1 : UInt256) {out : ByteArray}
    (hguard :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
        (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = none) :
    ExecFuncBody config (mintFeeCallFrame reserve0 reserve1) evm mintFeeFunction.body
      .reverted := by
  have hchecked :=
    uniswapMintFeeCheckedCallDecodeRevert evm evmFee reserve0 reserve1 hguard hcall hdec
  exact ExecFuncBody.execBlockRevert (by
    simpa [mintFeeFunction, List.append_assoc] using
      (Reasoning.Refinement.execBlock_append_term hchecked (by intro f e h; cases h)))

theorem uniswapMintFeeCheckedCallSuccess
    (evm evmFee : EVM.State) (reserve0 reserve1 : UInt256) {out : ByteArray}
    (feeTo : AccountAddress)
    (hguard :
      evalExpr? config (mintFeeCallFrame reserve0 reserve1) evm
        (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) = .ok (.bool true))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some (.address feeTo)) :
    ExecBlock config (mintFeeCallFrame reserve0 reserve1) evm
      (checkedExternalCallStmts (.storage factoryRef) "feeTo" (.intLit 0) [] "feeTo"
        (perm := false))
      (.ok (mintFeeAfterFeeToFrame reserve0 reserve1 feeTo) evmFee) := by
  simpa [checkedExternalCallStmts, mintFeeAfterFeeToFrame, mintFeeAfterFeeToStore] using
    checkedExternalCallSuccess
      (cfg := config) (C := contract) (evm := evm) (evm' := evmFee)
      (locals := mintFeeCallStore reserve0 reserve1)
      (receiver := .storage factoryRef) (name := "feeTo") (sendVal := 0)
      (args := []) (retVar := "feeTo") (perm := false)
      (target := uniswapAddressAtSlot evm ⟨5⟩) (out := out) (value := .address feeTo)
      hguard
      (evalExpr_mintFee_factory evm reserve0 reserve1)
      (by rfl)
      hcall hdec

abbrev mintFeeAfterFeeOnStore
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool) : Store :=
  (mintFeeAfterFeeToStore reserve0 reserve1 feeTo).insert "feeOn" (.bool feeOn)

abbrev mintFeeAfterFeeOnFrame
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool) : Frame :=
  { contract := contract, locals := mintFeeAfterFeeOnStore reserve0 reserve1 feeTo feeOn }

abbrev mintFeeAfterKLastStore
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) : Store :=
  (mintFeeAfterFeeOnStore reserve0 reserve1 feeTo feeOn).insert "_kLast"
    (uniswapUint256Value kLast)

abbrev mintFeeAfterKLastFrame
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) : Frame :=
  { contract := contract, locals := mintFeeAfterKLastStore reserve0 reserve1 feeTo feeOn kLast }

def mintFeeKLastClearedState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨11⟩ ⟨0⟩

abbrev mintFeeKLastWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩

theorem mintFeeAfterFeeOnStore_feeOn
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool) :
    (mintFeeAfterFeeOnStore reserve0 reserve1 feeTo feeOn).get? "feeOn" =
      some (.bool feeOn) := by
  rw [mintFeeAfterFeeOnStore, store_get_self]

theorem mintFeeAfterFeeOnStore_kLast
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool) :
    (mintFeeAfterFeeOnStore reserve0 reserve1 feeTo feeOn).get? "kLast" = none := by
  rw [mintFeeAfterFeeOnStore, store_get_ne _ _ (by decide), mintFeeAfterFeeToStore_kLast]

theorem mintFeeAfterKLastStore_feeOn
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) :
    (mintFeeAfterKLastStore reserve0 reserve1 feeTo feeOn kLast).get? "feeOn" =
      some (.bool feeOn) := by
  rw [mintFeeAfterKLastStore, store_get_ne _ _ (by decide), mintFeeAfterFeeOnStore_feeOn]

theorem mintFeeAfterKLastStore_kLastLocal
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) :
    (mintFeeAfterKLastStore reserve0 reserve1 feeTo feeOn kLast).get? "_kLast" =
      some (uniswapUint256Value kLast) := by
  rw [mintFeeAfterKLastStore, store_get_self]

theorem mintFeeAfterKLastStore_kLastStorage
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) :
    (mintFeeAfterKLastStore reserve0 reserve1 feeTo feeOn kLast).get? "kLast" = none := by
  rw [mintFeeAfterKLastStore, store_get_ne _ _ (by decide), mintFeeAfterFeeOnStore_kLast]

theorem evalStorageRef_mintFee_afterFeeOn_kLast
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool) :
    evalStorageRef config (mintFeeAfterFeeOnFrame reserve0 reserve1 feeTo feeOn) evm kLastRef =
      .ok ({ base := "kLast", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, kLastRef, EvalResult.bind, pure, bind]

theorem evalExpr_mintFee_afterFeeOn_kLast
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool) :
    evalExpr? config (mintFeeAfterFeeOnFrame reserve0 reserve1 feeTo feeOn) evm
      (.storage kLastRef) =
      .ok (uniswapUint256Value (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [kLastRef])
    (her := evalStorageRef_mintFee_afterFeeOn_kLast evm reserve0 reserve1 feeTo feeOn)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (uniswapStorageLocLoad_uint256 evm ⟨11⟩)

theorem evalExpr_mintFee_afterKLast_feeOn
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) :
    evalExpr? config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo feeOn kLast) evm
      (.var "feeOn") = .ok (.bool feeOn) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterKLastStore_feeOn]

theorem evalExpr_mintFee_afterKLast_kLastLocal
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) :
    evalExpr? config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo feeOn kLast) evm
      (.var "_kLast") = .ok (uniswapUint256Value kLast) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterKLastStore_kLastLocal]

theorem evalExpr_mintFee_afterKLast_kLast_ne_zero_true
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (hkLast : kLast.toNat ≠ 0) :
    evalExpr? config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo feeOn kLast) evm
      (.binary .ne (.var "_kLast") (.intLit 0)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_mintFee_afterKLast_kLastLocal evm reserve0 reserve1 feeTo
    feeOn kLast, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, uniswapUint256Value, uint256Value, hkLast]

theorem evalExpr_mintFee_afterKLast_kLast_ne_zero_false
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (hkLast : kLast.toNat = 0) :
    evalExpr? config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo feeOn kLast) evm
      (.binary .ne (.var "_kLast") (.intLit 0)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_mintFee_afterKLast_kLastLocal evm reserve0 reserve1 feeTo
    feeOn kLast, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, uniswapUint256Value, uint256Value, hkLast]

theorem evalExpr_mintFee_return_feeOn
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) :
    evalExpr? config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo feeOn kLast) evm
      (.var "feeOn") = .ok (.bool feeOn) :=
  evalExpr_mintFee_afterKLast_feeOn evm reserve0 reserve1 feeTo feeOn kLast

def mintFeeReserveProductNat (reserve0 reserve1 : UInt256) : Nat :=
  reserve0.toNat * reserve1.toNat

def mintFeeReserveProductWord (reserve0 reserve1 : UInt256) : UInt256 :=
  UInt256.ofNat (mintFeeReserveProductNat reserve0 reserve1)

abbrev mintFeeReserveProductValue (reserve0 reserve1 : UInt256) : Value :=
  uniswapUint256Value (mintFeeReserveProductWord reserve0 reserve1)

theorem mintFeeAfterKLastStore_reserve0
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) :
    (mintFeeAfterKLastStore reserve0 reserve1 feeTo feeOn kLast).get? "_reserve0" =
      some (mintFeeReserve0Value reserve0) := by
  rw [mintFeeAfterKLastStore, store_get_ne _ _ (by decide), mintFeeAfterFeeOnStore,
    store_get_ne _ _ (by decide), mintFeeAfterFeeToStore, store_get_ne _ _ (by decide),
    mintFeeCallStore_reserve0]

theorem mintFeeAfterKLastStore_reserve1
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) :
    (mintFeeAfterKLastStore reserve0 reserve1 feeTo feeOn kLast).get? "_reserve1" =
      some (mintFeeReserve1Value reserve1) := by
  rw [mintFeeAfterKLastStore, store_get_ne _ _ (by decide), mintFeeAfterFeeOnStore,
    store_get_ne _ _ (by decide), mintFeeAfterFeeToStore, store_get_ne _ _ (by decide),
    mintFeeCallStore_reserve1]

theorem evalExpr_mintFee_afterKLast_reserve0
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) :
    evalExpr? config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo feeOn kLast) evm
      (.var "_reserve0") = .ok (mintFeeReserve0Value reserve0) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterKLastStore_reserve0]

theorem evalExpr_mintFee_afterKLast_reserve1
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) :
    evalExpr? config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo feeOn kLast) evm
      (.var "_reserve1") = .ok (mintFeeReserve1Value reserve1) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterKLastStore_reserve1]

theorem evalExpr_mintFee_afterKLast_reserveProduct
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256)
    (hfit : mintFeeReserveProductNat reserve0 reserve1 < UInt256.size) :
    evalExpr? config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo feeOn kLast) evm
      (u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))) =
        .ok (mintFeeReserveProductValue reserve0 reserve1) := by
  have hguard :
      ¬ (Int.ofNat reserve0.toNat * Int.ofNat reserve1.toNat < 0 ∨
        (2 : Int) ^ 256 ≤ Int.ofNat reserve0.toNat * Int.ofNat reserve1.toNat) := by
    push Not
    constructor
    · exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    · have hfitNat : reserve0.toNat * reserve1.toNat < 2 ^ 256 := by
        simpa [mintFeeReserveProductNat, UInt256.size] using hfit
      simpa [Nat.cast_mul] using Int.ofNat_lt.mpr hfitNat
  have hguardBool :
      ¬ ((decide (Int.ofNat reserve0.toNat * Int.ofNat reserve1.toNat < 0) ||
        decide (Int.ofNat reserve0.toNat * Int.ofNat reserve1.toNat ≥
          (2 : Int) ^ 256)) = true) := by
    simpa [Bool.or_eq_true, ge_iff_le] using hguard
  have htoNat :
      (UInt256.ofNat (mintFeeReserveProductNat reserve0 reserve1)).toNat =
        mintFeeReserveProductNat reserve0 reserve1 := by
    exact ulit_toNat' _ hfit
  have htoNat' :
      (UInt256.ofNat (reserve0.toNat * reserve1.toNat)).toNat =
        reserve0.toNat * reserve1.toNat := by
    simpa [mintFeeReserveProductNat] using htoNat
  simp only [u256, evalExpr?, evalExpr_mintFee_afterKLast_reserve0 evm reserve0 reserve1
    feeTo feeOn kLast, evalExpr_mintFee_afterKLast_reserve1 evm reserve0 reserve1 feeTo
    feeOn kLast, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [if_neg hguardBool]
  simp [mintFeeReserveProductValue, mintFeeReserveProductWord, mintFeeReserveProductNat,
    uniswapUint256Value, uint256Value, htoNat']

theorem evalExprs_mintFee_reserveProductArg
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256)
    (hfit : mintFeeReserveProductNat reserve0 reserve1 < UInt256.size) :
    evalExprs? config (mintFeeAfterKLastFrame reserve0 reserve1 feeTo feeOn kLast) evm
      [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] =
        .ok [sqrtFunctionYValue (mintFeeReserveProductWord reserve0 reserve1)] := by
  simp [evalExprs?, evalExpr_mintFee_afterKLast_reserveProduct evm reserve0 reserve1 feeTo
    feeOn kLast hfit, sqrtFunctionYValue, mintFeeReserveProductValue, EvalResult.bind, bind,
    pure]

abbrev mintFeeAfterRootKStore
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) (rootK : Int) : Store :=
  (mintFeeAfterKLastStore reserve0 reserve1 feeTo feeOn kLast).insert "rootK" (.int rootK)

abbrev mintFeeAfterRootKFrame
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) (rootK : Int) : Frame :=
  { contract := contract, locals := mintFeeAfterRootKStore reserve0 reserve1 feeTo feeOn kLast rootK }

abbrev mintFeeAfterRootKLastStore
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) (rootK rootKLast : Int) : Store :=
  (mintFeeAfterRootKStore reserve0 reserve1 feeTo feeOn kLast rootK).insert "rootKLast"
    (.int rootKLast)

abbrev mintFeeAfterRootKLastFrame
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) (rootK rootKLast : Int) : Frame :=
  { contract := contract,
    locals := mintFeeAfterRootKLastStore reserve0 reserve1 feeTo feeOn kLast rootK rootKLast }

theorem mintFeeAfterRootKStore_kLastLocal
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) (rootK : Int) :
    (mintFeeAfterRootKStore reserve0 reserve1 feeTo feeOn kLast rootK).get? "_kLast" =
      some (uniswapUint256Value kLast) := by
  rw [mintFeeAfterRootKStore, store_get_ne _ _ (by decide), mintFeeAfterKLastStore_kLastLocal]

theorem mintFeeAfterRootKStore_rootK
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) (rootK : Int) :
    (mintFeeAfterRootKStore reserve0 reserve1 feeTo feeOn kLast rootK).get? "rootK" =
      some (.int rootK) := by
  rw [mintFeeAfterRootKStore, store_get_self]

theorem evalExpr_mintFee_afterRootK_kLastLocal
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK : Int) :
    evalExpr? config (mintFeeAfterRootKFrame reserve0 reserve1 feeTo feeOn kLast rootK) evm
      (.var "_kLast") = .ok (uniswapUint256Value kLast) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterRootKStore_kLastLocal]

theorem evalExprs_mintFee_kLastArg
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK : Int) :
    evalExprs? config (mintFeeAfterRootKFrame reserve0 reserve1 feeTo feeOn kLast rootK) evm
      [.var "_kLast"] = .ok [sqrtFunctionYValue kLast] := by
  simp [evalExprs?, evalExpr_mintFee_afterRootK_kLastLocal evm reserve0 reserve1 feeTo
    feeOn kLast rootK, sqrtFunctionYValue, EvalResult.bind, bind, pure]

theorem mintFeeAfterRootKLastStore_feeOn
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterRootKLastStore reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).get?
      "feeOn" = some (.bool feeOn) := by
  rw [mintFeeAfterRootKLastStore, store_get_ne _ _ (by decide), mintFeeAfterRootKStore,
    store_get_ne _ _ (by decide), mintFeeAfterKLastStore_feeOn]

theorem mintFeeAfterRootKLastStore_rootK
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterRootKLastStore reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).get?
      "rootK" = some (.int rootK) := by
  rw [mintFeeAfterRootKLastStore, store_get_ne _ _ (by decide), mintFeeAfterRootKStore_rootK]

theorem mintFeeAfterRootKLastStore_rootKLast
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterRootKLastStore reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).get?
      "rootKLast" = some (.int rootKLast) := by
  rw [mintFeeAfterRootKLastStore, store_get_self]

theorem evalExpr_mintFee_afterRootKLast_feeOn
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    evalExpr? config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (.var "feeOn") = .ok (.bool feeOn) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterRootKLastStore_feeOn]

theorem evalExpr_mintFee_rootK_gt_rootKLast_false
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : ¬ rootK > rootKLast) :
    evalExpr? config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (.binary .gt (.var "rootK") (.var "rootKLast")) = .ok (.bool false) := by
  have hle : rootK ≤ rootKLast := by omega
  simp only [evalExpr?, EvalResult.ofOption, mintFeeAfterRootKLastStore_rootK,
    mintFeeAfterRootKLastStore_rootKLast, EvalResult.bind, bind]
  simp [evalBinaryOp?, hle]

theorem mintFeeAfterRootKLastStore_feeTo
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterRootKLastStore reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).get?
      "feeTo" = some (.address feeTo) := by
  rw [mintFeeAfterRootKLastStore, store_get_ne _ _ (by decide), mintFeeAfterRootKStore,
    store_get_ne _ _ (by decide), mintFeeAfterKLastStore, store_get_ne _ _ (by decide),
    mintFeeAfterFeeOnStore, store_get_ne _ _ (by decide), mintFeeAfterFeeToStore_feeTo]

theorem mintFeeAfterRootKLastStore_totalSupply
    (reserve0 reserve1 : UInt256) (feeTo : AccountAddress) (feeOn : Bool)
    (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterRootKLastStore reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).get?
      "totalSupply" = none := by
  rw [mintFeeAfterRootKLastStore, store_get_ne _ _ (by decide), mintFeeAfterRootKStore,
    store_get_ne _ _ (by decide), mintFeeAfterKLastStore, store_get_ne _ _ (by decide),
    mintFeeAfterFeeOnStore, store_get_ne _ _ (by decide), mintFeeAfterFeeToStore,
    store_get_ne _ _ (by decide), mintFeeCallStore_totalSupply]

theorem evalExpr_mintFee_afterRootKLast_feeTo
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    evalExpr? config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (.var "feeTo") = .ok (.address feeTo) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterRootKLastStore_feeTo]

theorem evalStorageRef_mintFee_afterRootKLast_totalSupply
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    evalStorageRef config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      totalSupplyRef = .ok ({ base := "totalSupply", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef, EvalResult.bind, pure, bind]

theorem evalExpr_mintFee_afterRootKLast_totalSupply
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    evalExpr? config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (.storage totalSupplyRef) =
      .ok (uniswapUint256Value (mintFunctionTotalSupplyWord evm)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by
      simp [totalSupplyRef])
    (her := evalStorageRef_mintFee_afterRootKLast_totalSupply evm reserve0 reserve1 feeTo
      feeOn kLast rootK rootKLast)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (uniswapStorageLocLoad_uint256 evm ⟨0⟩)

theorem evalExpr_mintFee_rootK_gt_rootKLast_true
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) :
    evalExpr? config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (.binary .gt (.var "rootK") (.var "rootKLast")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, mintFeeAfterRootKLastStore_rootK,
    mintFeeAfterRootKLastStore_rootKLast, EvalResult.bind, bind]
  simp [evalBinaryOp?, hroot]

def mintFeeRootDiffWord (rootK rootKLast : Int) : UInt256 :=
  UInt256.ofNat (Int.toNat (rootK - rootKLast))

abbrev mintFeeRootDiffValue (rootK rootKLast : Int) : Value :=
  uniswapUint256Value (mintFeeRootDiffWord rootK rootKLast)

theorem evalExpr_mintFee_rootDiff
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast) :
    evalExpr? config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))) =
        .ok (mintFeeRootDiffValue rootK rootKLast) := by
  have hrootKIntSize : rootK < (2 : Int) ^ 256 := by
    have hcast : Int.ofNat rootK.toNat < (2 : Int) ^ 256 := by
      exact Int.ofNat_lt.mpr (by simpa [UInt256.size] using hrootKSize)
    simpa [Int.toNat_of_nonneg hrootKNonneg] using hcast
  have hguard :
      ¬ (rootK - rootKLast < 0 ∨ (2 : Int) ^ 256 ≤ rootK - rootKLast) := by
    push Not
    constructor
    · omega
    · omega
  have hguardBool :
      ¬ ((decide (rootK - rootKLast < 0) ||
        decide (rootK - rootKLast ≥ (2 : Int) ^ 256)) = true) := by
    simpa [Bool.or_eq_true, ge_iff_le] using hguard
  have hdiffNonneg : 0 ≤ rootK - rootKLast := by omega
  have hdiffSizeInt : rootK - rootKLast < (2 : Int) ^ 256 := by omega
  have hdiffSizeNat : (rootK - rootKLast).toNat < UInt256.size := by
    apply Int.ofNat_lt.mp
    simpa [UInt256.size, Int.toNat_of_nonneg hdiffNonneg] using hdiffSizeInt
  have hwordToNat :
      (UInt256.ofNat (rootK - rootKLast).toNat).toNat =
        (rootK - rootKLast).toNat := by
    exact ulit_toNat' _ hdiffSizeNat
  have hrootLe : rootKLast ≤ rootK := by omega
  simp only [u256, evalExpr?, EvalResult.ofOption, mintFeeAfterRootKLastStore_rootK,
    mintFeeAfterRootKLastStore_rootKLast, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [if_neg hguardBool]
  simp [mintFeeRootDiffValue, mintFeeRootDiffWord, uniswapUint256Value, uint256Value,
    hwordToNat, hrootLe]

def mintFeeNumeratorNat (evm : EVM.State) (rootK rootKLast : Int) : Nat :=
  (mintFunctionTotalSupplyWord evm).toNat * (mintFeeRootDiffWord rootK rootKLast).toNat

def mintFeeNumeratorWord (evm : EVM.State) (rootK rootKLast : Int) : UInt256 :=
  UInt256.ofNat (mintFeeNumeratorNat evm rootK rootKLast)

abbrev mintFeeNumeratorValue (evm : EVM.State) (rootK rootKLast : Int) : Value :=
  uniswapUint256Value (mintFeeNumeratorWord evm rootK rootKLast)

theorem evalExpr_mintFee_numerator
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hfit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size) :
    evalExpr? config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (u256 (.binary .mul (.storage totalSupplyRef)
        (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))) =
        .ok (mintFeeNumeratorValue evm rootK rootKLast) := by
  have hguard :
      ¬ (Int.ofNat (mintFunctionTotalSupplyWord evm).toNat *
            Int.ofNat (mintFeeRootDiffWord rootK rootKLast).toNat < 0 ∨
        (2 : Int) ^ 256 ≤
          Int.ofNat (mintFunctionTotalSupplyWord evm).toNat *
            Int.ofNat (mintFeeRootDiffWord rootK rootKLast).toNat) := by
    push Not
    constructor
    · exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    · have hfitNat :
          (mintFunctionTotalSupplyWord evm).toNat *
              (mintFeeRootDiffWord rootK rootKLast).toNat < 2 ^ 256 := by
        simpa [mintFeeNumeratorNat, UInt256.size] using hfit
      simpa [Nat.cast_mul] using Int.ofNat_lt.mpr hfitNat
  have hguardBool :
      ¬ ((decide (Int.ofNat (mintFunctionTotalSupplyWord evm).toNat *
              Int.ofNat (mintFeeRootDiffWord rootK rootKLast).toNat < 0) ||
        decide (Int.ofNat (mintFunctionTotalSupplyWord evm).toNat *
              Int.ofNat (mintFeeRootDiffWord rootK rootKLast).toNat ≥
            (2 : Int) ^ 256)) = true) := by
    simpa [Bool.or_eq_true, ge_iff_le] using hguard
  have htoNat :
      (UInt256.ofNat (mintFeeNumeratorNat evm rootK rootKLast)).toNat =
        mintFeeNumeratorNat evm rootK rootKLast := by
    exact ulit_toNat' _ hfit
  have htoNat' :
      (UInt256.ofNat
          ((mintFunctionTotalSupplyWord evm).toNat *
            (mintFeeRootDiffWord rootK rootKLast).toNat)).toNat =
        (mintFunctionTotalSupplyWord evm).toNat *
          (mintFeeRootDiffWord rootK rootKLast).toNat := by
    simpa [mintFeeNumeratorNat] using htoNat
  have hdiffEval :=
    evalExpr_mintFee_rootDiff evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast
      hroot hrootKNonneg hrootKSize hrootKLastNonneg
  have hdiffEval' :
      evalExpr? config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
        (.inRange uint256Int (.binary .sub (.var "rootK") (.var "rootKLast"))) =
          .ok (mintFeeRootDiffValue rootK rootKLast) := by
    simpa [u256] using hdiffEval
  simp only [u256, evalExpr?, evalExpr_mintFee_afterRootKLast_totalSupply evm reserve0
    reserve1 feeTo feeOn kLast rootK rootKLast, hdiffEval', EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [if_neg hguardBool]
  simp [mintFeeNumeratorValue, mintFeeNumeratorWord, mintFeeNumeratorNat,
    uniswapUint256Value, uint256Value, htoNat']

abbrev mintFeeAfterNumeratorStore
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) : Store :=
  (mintFeeAfterRootKLastStore reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).insert
    "numerator" (mintFeeNumeratorValue evm rootK rootKLast)

abbrev mintFeeAfterNumeratorFrame
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) : Frame :=
  { contract := contract,
    locals := mintFeeAfterNumeratorStore evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast }

theorem mintFeeAfterNumeratorStore_rootK
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterNumeratorStore evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).get?
      "rootK" = some (.int rootK) := by
  rw [mintFeeAfterNumeratorStore, store_get_ne _ _ (by decide),
    mintFeeAfterRootKLastStore_rootK]

theorem mintFeeAfterNumeratorStore_rootKLast
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterNumeratorStore evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).get?
      "rootKLast" = some (.int rootKLast) := by
  rw [mintFeeAfterNumeratorStore, store_get_ne _ _ (by decide),
    mintFeeAfterRootKLastStore_rootKLast]

theorem mintFeeAfterNumeratorStore_numerator
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterNumeratorStore evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).get?
      "numerator" = some (mintFeeNumeratorValue evm rootK rootKLast) := by
  rw [mintFeeAfterNumeratorStore, store_get_self]

theorem evalExpr_mintFee_afterNumerator_rootK
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    evalExpr? config
      (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (.var "rootK") = .ok (.int rootK) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterNumeratorStore_rootK]

theorem evalExpr_mintFee_afterNumerator_rootKLast
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    evalExpr? config
      (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (.var "rootKLast") = .ok (.int rootKLast) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterNumeratorStore_rootKLast]

def mintFeeRootTimesFiveNat (rootK : Int) : Nat :=
  rootK.toNat * 5

def mintFeeRootTimesFiveWord (rootK : Int) : UInt256 :=
  UInt256.ofNat (mintFeeRootTimesFiveNat rootK)

abbrev mintFeeRootTimesFiveValue (rootK : Int) : Value :=
  uniswapUint256Value (mintFeeRootTimesFiveWord rootK)

theorem evalExpr_mintFee_rootTimesFive
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int)
    (hrootKNonneg : 0 ≤ rootK)
    (hfit : mintFeeRootTimesFiveNat rootK < UInt256.size) :
    evalExpr? config
      (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (u256 (.binary .mul (.var "rootK") (.intLit 5))) =
        .ok (mintFeeRootTimesFiveValue rootK) := by
  have hguard :
      ¬ (rootK * 5 < 0 ∨ (2 : Int) ^ 256 ≤ rootK * 5) := by
    push Not
    constructor
    · nlinarith
    · have hfitNat : rootK.toNat * 5 < 2 ^ 256 := by
        simpa [mintFeeRootTimesFiveNat, UInt256.size] using hfit
      have hcast : Int.ofNat (rootK.toNat * 5) < (2 : Int) ^ 256 := by
        exact Int.ofNat_lt.mpr hfitNat
      simpa [Nat.cast_mul, Int.toNat_of_nonneg hrootKNonneg] using hcast
  have hguardBool :
      ¬ ((decide (rootK * 5 < 0) ||
        decide (rootK * 5 ≥ (2 : Int) ^ 256)) = true) := by
    simpa [Bool.or_eq_true, ge_iff_le] using hguard
  have htoNat :
      (UInt256.ofNat (mintFeeRootTimesFiveNat rootK)).toNat =
        mintFeeRootTimesFiveNat rootK := by
    exact ulit_toNat' _ hfit
  have htoNat' :
      (UInt256.ofNat (rootK.toNat * 5)).toNat = rootK.toNat * 5 := by
    simpa [mintFeeRootTimesFiveNat] using htoNat
  have hrootMulCast : Int.ofNat (rootK.toNat * 5) = rootK * 5 := by
    simp [Nat.cast_mul, Int.toNat_of_nonneg hrootKNonneg]
  simp only [u256, evalExpr?, evalExpr_mintFee_afterNumerator_rootK evm reserve0 reserve1
    feeTo feeOn kLast rootK rootKLast, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [if_neg hguardBool]
  simp [mintFeeRootTimesFiveValue, mintFeeRootTimesFiveWord, mintFeeRootTimesFiveNat,
    uniswapUint256Value, uint256Value, htoNat', hrootKNonneg]

def mintFeeDenominatorNat (rootK rootKLast : Int) : Nat :=
  (mintFeeRootTimesFiveWord rootK).toNat + rootKLast.toNat

def mintFeeDenominatorWord (rootK rootKLast : Int) : UInt256 :=
  UInt256.ofNat (mintFeeDenominatorNat rootK rootKLast)

abbrev mintFeeDenominatorValue (rootK rootKLast : Int) : Value :=
  uniswapUint256Value (mintFeeDenominatorWord rootK rootKLast)

theorem evalExpr_mintFee_denominator
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int)
    (hrootKNonneg : 0 ≤ rootK) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hfit : mintFeeDenominatorNat rootK rootKLast < UInt256.size) :
    evalExpr? config
      (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (u256 (.binary .add (u256 (.binary .mul (.var "rootK") (.intLit 5)))
        (.var "rootKLast"))) = .ok (mintFeeDenominatorValue rootK rootKLast) := by
  have hrootFiveEval :=
    evalExpr_mintFee_rootTimesFive evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast
      hrootKNonneg hrootFiveFit
  have hrootFiveEval' :
      evalExpr? config
        (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
        (.inRange uint256Int (.binary .mul (.var "rootK") (.intLit 5))) =
          .ok (mintFeeRootTimesFiveValue rootK) := by
    simpa [u256] using hrootFiveEval
  have hguard :
      ¬ (Int.ofNat (mintFeeRootTimesFiveWord rootK).toNat + Int.ofNat rootKLast.toNat < 0 ∨
        (2 : Int) ^ 256 ≤
          Int.ofNat (mintFeeRootTimesFiveWord rootK).toNat + Int.ofNat rootKLast.toNat) := by
    push Not
    constructor
    · exact Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    · have hfitNat :
          (mintFeeRootTimesFiveWord rootK).toNat + rootKLast.toNat < 2 ^ 256 := by
        simpa [mintFeeDenominatorNat, UInt256.size] using hfit
      simpa [Nat.cast_add] using Int.ofNat_lt.mpr hfitNat
  have hguardBool :
      ¬ ((decide (Int.ofNat (mintFeeRootTimesFiveWord rootK).toNat +
              Int.ofNat rootKLast.toNat < 0) ||
        decide (Int.ofNat (mintFeeRootTimesFiveWord rootK).toNat +
              Int.ofNat rootKLast.toNat ≥ (2 : Int) ^ 256)) = true) := by
    simpa [Bool.or_eq_true, ge_iff_le] using hguard
  have htoNat :
      (UInt256.ofNat (mintFeeDenominatorNat rootK rootKLast)).toNat =
        mintFeeDenominatorNat rootK rootKLast := by
    exact ulit_toNat' _ hfit
  have htoNat' :
      (UInt256.ofNat ((mintFeeRootTimesFiveWord rootK).toNat + rootKLast.toNat)).toNat =
        (mintFeeRootTimesFiveWord rootK).toNat + rootKLast.toNat := by
    simpa [mintFeeDenominatorNat] using htoNat
  have hrootKLastCast : Int.ofNat rootKLast.toNat = rootKLast := by
    simpa using Int.toNat_of_nonneg hrootKLastNonneg
  have hguardBool' :
      ¬ ((decide (Int.ofNat (mintFeeRootTimesFiveWord rootK).toNat + rootKLast < 0) ||
        decide (Int.ofNat (mintFeeRootTimesFiveWord rootK).toNat + rootKLast ≥
          (2 : Int) ^ 256)) = true) := by
    simpa [Int.toNat_of_nonneg hrootKLastNonneg] using hguardBool
  simp only [u256, evalExpr?, hrootFiveEval',
    evalExpr_mintFee_afterNumerator_rootKLast evm reserve0 reserve1 feeTo feeOn kLast rootK
      rootKLast, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [if_neg hguardBool']
  simp [mintFeeDenominatorValue, mintFeeDenominatorWord, mintFeeDenominatorNat,
    uniswapUint256Value, uint256Value, htoNat', hrootKLastNonneg]

abbrev mintFeeAfterDenominatorStore
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) : Store :=
  (mintFeeAfterNumeratorStore evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).insert
    "denominator" (mintFeeDenominatorValue rootK rootKLast)

abbrev mintFeeAfterDenominatorFrame
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) : Frame :=
  { contract := contract,
    locals :=
      mintFeeAfterDenominatorStore evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast }

theorem mintFeeAfterDenominatorStore_numerator
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterDenominatorStore evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).get?
      "numerator" = some (mintFeeNumeratorValue evm rootK rootKLast) := by
  rw [mintFeeAfterDenominatorStore, store_get_ne _ _ (by decide),
    mintFeeAfterNumeratorStore_numerator]

theorem mintFeeAfterDenominatorStore_denominator
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterDenominatorStore evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).get?
      "denominator" = some (mintFeeDenominatorValue rootK rootKLast) := by
  rw [mintFeeAfterDenominatorStore, store_get_self]

theorem evalExpr_mintFee_afterDenominator_numerator
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    evalExpr? config
      (mintFeeAfterDenominatorFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast)
      evm (.var "numerator") = .ok (mintFeeNumeratorValue evm rootK rootKLast) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterDenominatorStore_numerator]

theorem evalExpr_mintFee_afterDenominator_denominator
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    evalExpr? config
      (mintFeeAfterDenominatorFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast)
      evm (.var "denominator") = .ok (mintFeeDenominatorValue rootK rootKLast) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterDenominatorStore_denominator]

def mintFeeLiquidityInt (evm : EVM.State) (rootK rootKLast : Int) : Int :=
  Int.ofNat (mintFeeNumeratorWord evm rootK rootKLast).toNat /
    Int.ofNat (mintFeeDenominatorWord rootK rootKLast).toNat

abbrev mintFeeLiquidityValue (evm : EVM.State) (rootK rootKLast : Int) : Value :=
  .int (mintFeeLiquidityInt evm rootK rootKLast)

theorem evalExpr_mintFee_liquidity
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0) :
    evalExpr? config
      (mintFeeAfterDenominatorFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast)
      evm (.binary .div (.var "numerator") (.var "denominator")) =
        .ok (mintFeeLiquidityValue evm rootK rootKLast) := by
  have hdenomInt :
      Int.ofNat (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0 := by
    intro h
    exact hdenom (Int.ofNat.inj h)
  simp only [evalExpr?, evalExpr_mintFee_afterDenominator_numerator evm reserve0 reserve1
    feeTo feeOn kLast rootK rootKLast,
    evalExpr_mintFee_afterDenominator_denominator evm reserve0 reserve1 feeTo feeOn kLast
      rootK rootKLast, EvalResult.bind, bind]
  simp [evalBinaryOp?, mintFeeLiquidityValue, mintFeeLiquidityInt, hdenom]

abbrev mintFeeAfterLiquidityStore
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) : Store :=
  (mintFeeAfterDenominatorStore evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).insert
    "liquidity" (mintFeeLiquidityValue evm rootK rootKLast)

abbrev mintFeeAfterLiquidityFrame
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) : Frame :=
  { contract := contract,
    locals := mintFeeAfterLiquidityStore evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast }

theorem mintFeeAfterDenominatorStore_feeTo
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterDenominatorStore evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).get?
      "feeTo" = some (.address feeTo) := by
  rw [mintFeeAfterDenominatorStore, store_get_ne _ _ (by decide),
    mintFeeAfterNumeratorStore, store_get_ne _ _ (by decide),
    mintFeeAfterRootKLastStore_feeTo]

theorem mintFeeAfterDenominatorStore_feeOn
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterDenominatorStore evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).get?
      "feeOn" = some (.bool feeOn) := by
  rw [mintFeeAfterDenominatorStore, store_get_ne _ _ (by decide),
    mintFeeAfterNumeratorStore, store_get_ne _ _ (by decide),
    mintFeeAfterRootKLastStore_feeOn]

theorem mintFeeAfterLiquidityStore_liquidity
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterLiquidityStore evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).get?
      "liquidity" = some (mintFeeLiquidityValue evm rootK rootKLast) := by
  rw [mintFeeAfterLiquidityStore, store_get_self]

theorem mintFeeAfterLiquidityStore_feeTo
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterLiquidityStore evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).get?
      "feeTo" = some (.address feeTo) := by
  rw [mintFeeAfterLiquidityStore, store_get_ne _ _ (by decide),
    mintFeeAfterDenominatorStore_feeTo]

theorem mintFeeAfterLiquidityStore_feeOn
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterLiquidityStore evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast).get?
      "feeOn" = some (.bool feeOn) := by
  rw [mintFeeAfterLiquidityStore, store_get_ne _ _ (by decide),
    mintFeeAfterDenominatorStore_feeOn]

theorem evalExpr_mintFee_afterLiquidity_liquidity
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    evalExpr? config
      (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (.var "liquidity") = .ok (mintFeeLiquidityValue evm rootK rootKLast) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterLiquidityStore_liquidity]

theorem evalExpr_mintFee_afterLiquidity_feeTo
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    evalExpr? config
      (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (.var "feeTo") = .ok (.address feeTo) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterLiquidityStore_feeTo]

theorem evalExpr_mintFee_afterLiquidity_feeOn
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int) :
    evalExpr? config
      (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (.var "feeOn") = .ok (.bool feeOn) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterLiquidityStore_feeOn]

theorem evalExpr_mintFee_liquidity_gt_zero_true
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int)
    (hliq : mintFeeLiquidityInt evm rootK rootKLast > 0) :
    evalExpr? config
      (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (.binary .gt (.var "liquidity") (.intLit 0)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_mintFee_afterLiquidity_liquidity evm reserve0 reserve1 feeTo
    feeOn kLast rootK rootKLast, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, hliq]

theorem evalExpr_mintFee_liquidity_gt_zero_false
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (feeOn : Bool) (kLast : UInt256) (rootK rootKLast : Int)
    (hliq : ¬ mintFeeLiquidityInt evm rootK rootKLast > 0) :
    evalExpr? config
      (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo feeOn kLast rootK rootKLast) evm
      (.binary .gt (.var "liquidity") (.intLit 0)) = .ok (.bool false) := by
  have hle : mintFeeLiquidityInt evm rootK rootKLast ≤ 0 := by omega
  simp only [evalExpr?, evalExpr_mintFee_afterLiquidity_liquidity evm reserve0 reserve1 feeTo
    feeOn kLast rootK rootKLast, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, hle]

def mintFeeLiquidityWord (evm : EVM.State) (rootK rootKLast : Int) : UInt256 :=
  UInt256.ofNat (mintFeeLiquidityInt evm rootK rootKLast).toNat

theorem evalExprs_mintFee_mintArgs
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hliqNonneg : 0 ≤ mintFeeLiquidityInt evm rootK rootKLast)
    (hliqFit : (mintFeeLiquidityInt evm rootK rootKLast).toNat < UInt256.size) :
    evalExprs? config
      (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      [.var "feeTo", .var "liquidity"] =
        .ok [mintFunctionToValue feeTo,
          mintFunctionValueValue (mintFeeLiquidityWord evm rootK rootKLast)] := by
  have htoNat :
      (UInt256.ofNat (mintFeeLiquidityInt evm rootK rootKLast).toNat).toNat =
        (mintFeeLiquidityInt evm rootK rootKLast).toNat := by
    exact ulit_toNat' _ hliqFit
  have hliqCast :
      Int.ofNat (mintFeeLiquidityInt evm rootK rootKLast).toNat =
        mintFeeLiquidityInt evm rootK rootKLast := by
    simpa using Int.toNat_of_nonneg hliqNonneg
  simp [evalExprs?, evalExpr_mintFee_afterLiquidity_feeTo evm reserve0 reserve1 feeTo true
    kLast rootK rootKLast,
    evalExpr_mintFee_afterLiquidity_liquidity evm reserve0 reserve1 feeTo true kLast rootK
      rootKLast,
    mintFunctionToValue, mintFunctionValueValue, mintFeeLiquidityValue, mintFeeLiquidityWord,
    uniswapUint256Value, uint256Value, htoNat, hliqNonneg, EvalResult.bind, bind, pure]

abbrev mintFeePositiveRootBranchStmts : List Stmt :=
  [ .letDecl "numerator" (some uint256)
      (u256 (.binary .mul (.storage totalSupplyRef)
        (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))),
    .letDecl "denominator" (some uint256)
      (u256 (.binary .add (u256 (.binary .mul (.var "rootK") (.intLit 5)))
        (.var "rootKLast"))),
    .letDecl "liquidity" (some uint256)
      (.binary .div (.var "numerator") (.var "denominator")),
    .ite (.binary .gt (.var "liquidity") (.intLit 0))
      [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
      [] ]

theorem uniswapMintFeePositiveRootBranch_noLiquidity
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hliq : ¬ mintFeeLiquidityInt evm rootK rootKLast > 0) :
    ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      mintFeePositiveRootBranchStmts
      (.ok (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm) := by
  have hnumStmt :
      ExecStmt config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
        (.letDecl "numerator" (some uint256)
          (u256 (.binary .mul (.storage totalSupplyRef)
            (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))))
        (.ok (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    simpa [mintFeeAfterNumeratorFrame, mintFeeAfterNumeratorStore] using
      ExecStmt.letDecl
        (evalExpr_mintFee_numerator evm reserve0 reserve1 feeTo true kLast rootK rootKLast
          hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit)
  have hdenStmt :
      ExecStmt config
        (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm
        (.letDecl "denominator" (some uint256)
          (u256 (.binary .add (u256 (.binary .mul (.var "rootK") (.intLit 5)))
            (.var "rootKLast"))))
        (.ok
          (mintFeeAfterDenominatorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    simpa [mintFeeAfterDenominatorFrame, mintFeeAfterDenominatorStore] using
      ExecStmt.letDecl
        (evalExpr_mintFee_denominator evm reserve0 reserve1 feeTo true kLast rootK rootKLast
          hrootKNonneg hrootKLastNonneg hrootFiveFit hdenFit)
  have hliqStmt :
      ExecStmt config
        (mintFeeAfterDenominatorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm
        (.letDecl "liquidity" (some uint256)
          (.binary .div (.var "numerator") (.var "denominator")))
        (.ok (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    simpa [mintFeeAfterLiquidityFrame, mintFeeAfterLiquidityStore] using
      ExecStmt.letDecl
        (evalExpr_mintFee_liquidity evm reserve0 reserve1 feeTo true kLast rootK rootKLast
          hdenom)
  have hite :
      ExecStmt config
        (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm
        (.ite (.binary .gt (.var "liquidity") (.intLit 0))
          [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
          [])
        (.ok (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    exact ExecStmt.iteFalse
      (evalExpr_mintFee_liquidity_gt_zero_false evm reserve0 reserve1 feeTo true kLast rootK
        rootKLast hliq)
      ExecBlock.nil
  simpa [mintFeePositiveRootBranchStmts] using
    ExecBlock.consNormal hnumStmt
      (ExecBlock.consNormal hdenStmt
        (ExecBlock.consNormal hliqStmt
          (ExecBlock.consNormal hite ExecBlock.nil)))

abbrev mintFeeAfterFeeMintStore
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int) : Store :=
  (mintFeeAfterLiquidityStore evm reserve0 reserve1 feeTo true kLast rootK rootKLast).insert
    "_feeMint" .unit

abbrev mintFeeAfterFeeMintFrame
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int) : Frame :=
  { contract := contract,
    locals := mintFeeAfterFeeMintStore evm reserve0 reserve1 feeTo kLast rootK rootKLast }

theorem mintFeeAfterFeeMintStore_feeOn
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int) :
    (mintFeeAfterFeeMintStore evm reserve0 reserve1 feeTo kLast rootK rootKLast).get?
      "feeOn" = some (.bool true) := by
  rw [mintFeeAfterFeeMintStore, store_get_ne _ _ (by decide),
    mintFeeAfterLiquidityStore_feeOn]

theorem evalExpr_mintFee_afterFeeMint_feeOn
    (evm evmMint : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int) :
    evalExpr? config
      (mintFeeAfterFeeMintFrame evm reserve0 reserve1 feeTo kLast rootK rootKLast) evmMint
      (.var "feeOn") = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFeeAfterFeeMintStore_feeOn]

theorem uniswapMintFeePositiveRootBranch_withLiquidity
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hliq : mintFeeLiquidityInt evm rootK rootKLast > 0)
    (hliqFit : (mintFeeLiquidityInt evm rootK rootKLast).toNat < UInt256.size)
    (hfitSupply :
      mintFunctionTotalSupplyNewNat evm (mintFeeLiquidityWord evm rootK rootKLast) <
        UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat evm feeTo (mintFeeLiquidityWord evm rootK rootKLast) <
        UInt256.size) :
    ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      mintFeePositiveRootBranchStmts
      (.ok (mintFeeAfterFeeMintFrame evm reserve0 reserve1 feeTo kLast rootK rootKLast)
        (mintFunctionPostState evm feeTo (mintFeeLiquidityWord evm rootK rootKLast))) := by
  have hliqNonneg : 0 ≤ mintFeeLiquidityInt evm rootK rootKLast := by omega
  have hnumStmt :
      ExecStmt config
        (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
        (.letDecl "numerator" (some uint256)
          (u256 (.binary .mul (.storage totalSupplyRef)
            (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))))
        (.ok (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    simpa [mintFeeAfterNumeratorFrame, mintFeeAfterNumeratorStore] using
      ExecStmt.letDecl
        (evalExpr_mintFee_numerator evm reserve0 reserve1 feeTo true kLast rootK rootKLast
          hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit)
  have hdenStmt :
      ExecStmt config
        (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm
        (.letDecl "denominator" (some uint256)
          (u256 (.binary .add (u256 (.binary .mul (.var "rootK") (.intLit 5)))
            (.var "rootKLast"))))
        (.ok
          (mintFeeAfterDenominatorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    simpa [mintFeeAfterDenominatorFrame, mintFeeAfterDenominatorStore] using
      ExecStmt.letDecl
        (evalExpr_mintFee_denominator evm reserve0 reserve1 feeTo true kLast rootK rootKLast
          hrootKNonneg hrootKLastNonneg hrootFiveFit hdenFit)
  have hliqStmt :
      ExecStmt config
        (mintFeeAfterDenominatorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm
        (.letDecl "liquidity" (some uint256)
          (.binary .div (.var "numerator") (.var "denominator")))
        (.ok (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
          evm) := by
    simpa [mintFeeAfterLiquidityFrame, mintFeeAfterLiquidityStore] using
      ExecStmt.letDecl
        (evalExpr_mintFee_liquidity evm reserve0 reserve1 feeTo true kLast rootK rootKLast
          hdenom)
  have hmintStmt :
      ExecStmt config
        (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
        (.internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint")
        (.ok (mintFeeAfterFeeMintFrame evm reserve0 reserve1 feeTo kLast rootK rootKLast)
          (mintFunctionPostState evm feeTo (mintFeeLiquidityWord evm rootK rootKLast))) := by
    simpa [mintFeeAfterFeeMintFrame, mintFeeAfterFeeMintStore, resumeAfterInternalCall] using
      uniswapMintFunctionCallSuccess
        (caller := mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo true kLast rootK
          rootKLast)
        (evm := evm) (recipient := feeTo)
        (value := mintFeeLiquidityWord evm rootK rootKLast)
        (args := [.var "feeTo", .var "liquidity"]) (retVar := "_feeMint") rfl
        (evalExprs_mintFee_mintArgs evm reserve0 reserve1 feeTo kLast rootK rootKLast
          hliqNonneg hliqFit)
        hfitSupply hfitBalance
  have hite :
      ExecStmt config
        (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm
        (.ite (.binary .gt (.var "liquidity") (.intLit 0))
          [ .internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint" ]
          [])
        (.ok (mintFeeAfterFeeMintFrame evm reserve0 reserve1 feeTo kLast rootK rootKLast)
          (mintFunctionPostState evm feeTo (mintFeeLiquidityWord evm rootK rootKLast))) := by
    exact ExecStmt.iteTrue
      (evalExpr_mintFee_liquidity_gt_zero_true evm reserve0 reserve1 feeTo true kLast rootK
        rootKLast hliq)
      (ExecBlock.consNormal hmintStmt ExecBlock.nil)
  simpa [mintFeePositiveRootBranchStmts] using
    ExecBlock.consNormal hnumStmt
      (ExecBlock.consNormal hdenStmt
        (ExecBlock.consNormal hliqStmt
          (ExecBlock.consNormal hite ExecBlock.nil)))


end UniswapV2Pair
