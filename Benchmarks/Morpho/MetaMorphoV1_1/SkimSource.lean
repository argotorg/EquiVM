import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferSource
import Benchmarks.Morpho.MetaMorphoV1_1.TokenBalanceCall
import Benchmarks.Morpho.MetaMorphoV1_1.Storage
import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalCalls

/-! Source paths for the recipient guard, balance lookup, transfer, and Skim event. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory
set_option autoImplicit false
set_option maxRecDepth 2000

def skimLocals (token : AccountAddress) : Store :=
  (∅ : Store).insert "token" (.address token)

def skimRecipientAddress (evm : State) : AccountAddress :=
  AccountAddress.ofNat (UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨19⟩) solcAddrMask).toNat

def skimFrame (evm : State) (imms : Store) (token : AccountAddress) : Frame :=
  ⟨contract, ((skimLocals token).insert "__calldata" (.bytes evm.executionEnv.calldata)).insert
    "recipient" (.address (skimRecipientAddress evm)), imms⟩

def skimBalanceFrame (evm : State) (imms : Store) (token : AccountAddress)
    (amount : UInt256) : Frame :=
  { skimFrame evm imms token with
    locals := (skimFrame evm imms token).locals.insert "amount" (uint256Value amount) }

def skimTransferFrame (evm : State) (imms : Store) (token : AccountAddress)
    (amount cursor : UInt256) : Frame :=
  { skimBalanceFrame evm imms token amount with
    locals := (skimBalanceFrame evm imms token amount).locals.insert "__c1" (uint256Value cursor) }

def skimFinalFrame (evm evm' : State) (imms : Store) (token : AccountAddress)
    (amount cursor : UInt256) : Frame :=
  { skimTransferFrame evm imms token amount cursor with
    locals := (skimTransferFrame evm imms token amount cursor).locals.insert "__c2"
      (.address evm'.executionEnv.source) }

def skimBalanceStatement : Stmt :=
  .externalCall (.var "token") "balanceOf" (.intLit 0) [.env .this] "amount" false

theorem skimGuardSource (evm : State) (imms : Store) (token : AccountAddress) :
    evalExpr? config (skimFrame evm imms token) evm
      (.binary .ne (.var "recipient") (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (skimRecipientAddress evm ≠ ⟨0, by decide⟩))) := by
  apply evalExpr_addressNe
  · simp only [evalExpr?, skimFrame, store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, pure, bind, EvalResult.bind, castValue?]
    rfl

theorem skimRecipientPrefix (evm : State) (imms : Store) (token : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm ⟨contract, skimLocals token, imms⟩ skimTransition.body
      (skimFrame evm imms token) (skimTransition.body.drop 4) := by
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).letStep
  exact evalStorage_skimRecipient evm _ imms (by simp [skimLocals])

theorem skimPrefix (evm : State) (imms : Store) (token : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hne : skimRecipientAddress evm ≠ ⟨0, by decide⟩) :
    ABlock config evm ⟨contract, skimLocals token, imms⟩ skimTransition.body
      (skimFrame evm imms token) (skimTransition.body.drop 5) := by
  apply (skimRecipientPrefix evm imms token hwv hhi).requireStep
  rw [skimGuardSource]
  congr 2
  exact decide_eq_true hne

theorem skimBodyRevertsRecipient (evm : State) (imms : Store) (token : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (heq : skimRecipientAddress evm = ⟨0, by decide⟩) :
    ExecTransitionBody config contract evm (skimLocals token) skimTransition.body .reverted
      imms := by
  apply ExecFuncBody.execBlockRevert
  apply (skimRecipientPrefix evm imms token hwv hhi).requireRevert
  simp only [skimGuardSource, heq, ne_eq, not_true_eq_false, decide_false]

theorem skimBalanceTarget (evm : State) (imms : Store) (token : AccountAddress) :
    evalExpr? config (skimFrame evm imms token) evm (.var "token") = .ok (.address token) := by
  simp [evalExpr?, skimFrame, skimLocals, Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem skimBalanceArgs (evm : State) (imms : Store) (token : AccountAddress) :
    evalExprs? config (skimFrame evm imms token) evm [.env .this] =
      .ok [.address evm.executionEnv.codeOwner] := by
  simp only [evalExprs?, evalExpr?, envValue, bind, EvalResult.bind, pure]

theorem skimBalanceSource {evm evm' : State} (imms : Store) (token : AccountAddress)
    (out : ByteArray)
    (hcall : typedCallViaEVM config evm token "balanceOf" 0 [.address evm.executionEnv.codeOwner]
      (true, evm', out) false) (hl : 32 ≤ out.size) (hh : out.size < 2 ^ 255) :
    ExecStmt config (skimFrame evm imms token) evm skimBalanceStatement
      (.ok (skimBalanceFrame evm imms token (calldataWord out 0)) evm') := by
  exact ExecStmt.externalCallSuccess (sendVal := 0) (eth := .intLit 0)
    (value := [uint256Value (calldataWord out 0)]) (evm' := evm') (out := out)
    (skimBalanceTarget evm imms token) (by simp only [evalExpr?, pure])
    (skimBalanceArgs evm imms token)
    (by rw [show EVM.address (token : Nat) = token from evm_address_of_address_toNat token]
        exact hcall)
    (by rw [tokenBalanceDecode hh, if_pos hl])

theorem skimBalanceReverts {evm evm' : State} (imms : Store) (token : AccountAddress)
    (ok : Bool) (out : ByteArray)
    (hcall : typedCallViaEVM config evm token "balanceOf" 0 [.address evm.executionEnv.codeOwner]
      (ok, evm', out) false) (hbad : ok = false ∨ out.size < 32) :
    ExecStmt config (skimFrame evm imms token) evm skimBalanceStatement .reverted := by
  cases ok with
  | false =>
      exact ExecStmt.externalCallFailure (sendVal := 0) (eth := .intLit 0)
        (skimBalanceTarget evm imms token) (by simp only [evalExpr?, pure])
        (skimBalanceArgs evm imms token)
        (by rw [show EVM.address (token : Nat) = token from evm_address_of_address_toNat token]
            exact hcall)
  | true =>
      have hl : out.size < 32 := hbad.resolve_left (by decide)
      exact ExecStmt.externalCallReturnDecodeRevert (sendVal := 0) (eth := .intLit 0)
        (skimBalanceTarget evm imms token) (by simp only [evalExpr?, pure])
        (skimBalanceArgs evm imms token)
        (by rw [show EVM.address (token : Nat) = token from evm_address_of_address_toNat token]
            exact hcall)
        (by rw [tokenBalanceDecode (by omega), if_neg (by omega)])

theorem skimTransferArgs (evm evm' : State) (imms : Store) (token : AccountAddress)
    (amount : UInt256) :
    evalExprs? config (skimBalanceFrame evm imms token amount) evm'
      [.var "token", .var "recipient", .var "amount", .intLit 160] =
      .ok [.address token, .address (skimRecipientAddress evm), uint256Value amount,
        uint256Value ⟨160⟩] := by
  simp [evalExprs?, evalExpr?, skimBalanceFrame, skimFrame, skimLocals,
    Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, pure]
  rfl

theorem skimEmitArgs (evm evm' : State) (imms : Store) (token : AccountAddress)
    (amount cursor : UInt256) :
    evalExprs? config (skimFinalFrame evm evm' imms token amount cursor) evm'
      [.var "__c2", .var "token", .var "amount"] =
      .ok [.address evm'.executionEnv.source, .address token, uint256Value amount] := by
  simp [evalExprs?, evalExpr?, skimFinalFrame, skimTransferFrame, skimBalanceFrame,
    skimFrame, skimLocals, Std.HashMap.getElem_insert, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

theorem skimAfterTransfer {evm evmBalance evm' : State} (imms : Store)
    (token : AccountAddress) (amount cursor : UInt256) {frame' : Frame} {result : ExecResult}
    (htransfer : ExecFuncBody config
      (safeTransferFrame imms token (skimRecipientAddress evm) amount ⟨160⟩) evmBalance
      allocatedSafeTransferFunction.body (.returned frame' evm' (some [uint256Value cursor])))
    (htail : ExecBlock config (skimFinalFrame evm evm' imms token amount cursor) evm'
      [.emit "Skim" [.var "__c2", .var "token", .var "amount"]] result) :
    ExecBlock config (skimBalanceFrame evm imms token amount) evmBalance
      (skimTransition.body.drop 6) result := by
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := allocatedSafeTransferFunction)
    (skimTransferArgs evm evmBalance imms token amount) rfl rfl htransfer)
  exact ExecBlock.consNormal (msgSenderCall _ imms evm' "__c2") htail

end Benchmarks.Morpho.MetaMorphoV1_1
