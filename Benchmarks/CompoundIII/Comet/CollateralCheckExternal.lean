import Benchmarks.CompoundIII.Comet.CollateralCheckSource
import Benchmarks.CompoundIII.Comet.CollateralCheckEvm
import Benchmarks.CompoundIII.Comet.AddressGetter
import Benchmarks.CompoundIII.Comet.FreeWordReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def collateralCheckPublicBody (borrow : Bool) : List Stmt :=
  calldataPrologue [.internalCall (collateralCheckName borrow) [.var "account"] "result",
    .return [.var "result"]]

theorem collateralCheckPublic_returns {σ σ₀ A I} {g : Sat256}
    {v : CometWithExtendedAssetListImmutables} {borrow value : Bool} {evm' : EVM.State}
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2^255 + 4)
    (ht : CollateralCheckTrace v borrow
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
      (initState σ σ₀ g A I) (some (evm', value))) :
    ∃ frame, ExecTransitionBody config contract (initState σ σ₀ g A I)
      (addressGetterArgs "account" I) (collateralCheckPublicBody borrow)
      (.returned frame evm' (some [.bool value])) (immStore v) := by
  let frame := calldataLocalFrame
    { contract := contract, locals := addressGetterArgs "account" I, immutables := immStore v }
    (initState σ σ₀ g A I)
  have hs := collateralCheck_call ht frame (.var "account") "result" rfl rfl (by
    simp only [evalExpr?, frame, calldataLocalFrame, addressGetterArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl)
  refine ⟨{ frame with locals := frame.locals.insert "result" (.bool value) },
    .execBlockRet ?_⟩
  apply (calldataPrologue_ok hv hhi).run
  apply ExecBlock.consNormal hs
  exact ABlock.start.returns (by
    simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]; rfl)

theorem collateralCheckPublic_reverts {σ σ₀ A I} {g : Sat256}
    {v : CometWithExtendedAssetListImmutables} {borrow : Bool}
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2^255 + 4)
    (ht : CollateralCheckTrace v borrow
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
      (initState σ σ₀ g A I) none) :
    ExecTransitionBody config contract (initState σ σ₀ g A I)
      (addressGetterArgs "account" I) (collateralCheckPublicBody borrow)
      .reverted (immStore v) := by
  let frame := calldataLocalFrame
    { contract := contract, locals := addressGetterArgs "account" I, immutables := immStore v }
    (initState σ σ₀ g A I)
  have hs := collateralCheck_call ht frame (.var "account") "result" rfl rfl (by
    simp only [evalExpr?, frame, calldataLocalFrame, addressGetterArgs,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl)
  apply ExecFuncBody.execBlockRevert
  apply (calldataPrologue_ok hv hhi).run
  exact ExecBlock.consRevert hs

-- LIBRARY CANDIDATE: encoding the canonical word for an arbitrary Boolean.
theorem boolWordEncoding (value : Bool) :
    encodeReturnValue? (.elem .bool) (.bool value) = some (boolWord value).toByteArray := by
  cases value
  · exact boolFalseReturnEncoding
  · exact boolTrueReturnEncoding

theorem cometReturnBool {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (value : Bool)
    (hstack : R.length + 4 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨1455⟩
      (boolWord value :: ⟨32⟩ :: R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (boolWord value).toByteArray := by
  have hr := cometWithExtendedAssetList_block_1455
    (immWords := wordsOf (immStore v)) hstack h
  have hn : UInt256.isZero (UInt256.isZero (boolWord value)) = boolWord value := by
    cases value <;> decide
  rw [hn] at hr
  exact freeWordReturnData mem (boolWord value) ▸ hr

def CollateralCheckPublicResult (v : CometWithExtendedAssetListImmutables) (borrow : Bool)
    (I : ExecutionEnv) (g : Sat256) (s0 : EVM.State) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ 36 ≤ I.calldata.size ∧ I.calldata.size < 2^255 + 4 ∧
      (calldataWord I.calldata 4).toNat < EVM.addressModulus then
    ∃ result, CollateralCheckTrace v borrow
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat) s0 result ∧
      match result with
      | none => RDrev (deployedRuntime v) g s0
      | some (evm', value) => RDret (deployedRuntime v) g s0 evm'.accountMap
          (boolWord value).toByteArray
  else RDrev (deployedRuntime v) g s0

end Benchmarks.CompoundIII.Comet
