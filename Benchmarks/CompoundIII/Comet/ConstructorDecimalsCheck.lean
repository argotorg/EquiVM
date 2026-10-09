import Benchmarks.CompoundIII.Comet.ConstructorDecimalsResponse

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometConstructorDecimalsCheck {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {σ : AccountMap} {c : ConstructorConfig} {out : ByteArray}
    {aw : UInt256} {k C : Nat} (hcanon : (calldataWord out 0).toNat < 2^8)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) ee g s0 ⟨750⟩
      (⟨672⟩ :: calldataWord out 0 :: UInt256.ofNat (constructorRecordBase c) ::
        constructorAssetLoopStack c c.assetConfigs.length)
      (constructorDecimalsReturnMemory c out) aw out σ k C) :
    if (calldataWord out 0).toNat ≤ 18 then
      ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
        ee g s0 ⟨764⟩ (calldataWord out 0 :: UInt256.ofNat (constructorRecordBase c) ::
          constructorAssetLoopStack c c.assetConfigs.length)
        (constructorDecimalsReturnMemory c out) aw' out σ k' C'
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) g s0 := by
  have hclean := u256LandMaskCleanOfToNat (bits := 8) (calldataWord out 0)
    (UInt256.ofNat 255) (by decide) hcanon
  split
  · rename_i hvalid
    have r := cometWithExtendedAssetListCreation_block_750_fallthrough
      (by change 14 ≤ 1024; decide) (by
        rw [hclean]
        apply ugt_zero
        exact hvalid) h
    exact ⟨_, _, _, r⟩
  · rename_i hvalid
    have r := cometWithExtendedAssetListCreation_block_750_taken
      (by change 14 ≤ 1024; decide) (by
        rw [hclean, ugt_one (by change 18 < _; omega)]
        decide) (by native_decide) h
    exact cometWithExtendedAssetListCreation_block_2285 (by change 14 ≤ 1024; decide) r

theorem constructorSourceDecimals_limit (c : ConstructorConfig) (w : UInt256) (evm : EVM.State) :
    evalExpr? config (constructorSourceDecimals c w) evm
      (.binary .le (.var "decimals_") (.intLit 18)) =
      .ok (.bool (decide (w.toNat ≤ 18))) := by
  simp only [evalExpr?, constructorSourceDecimals, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, EvalResult.ofOption, pure, bind, EvalResult.bind, evalBinaryOp?]
  change EvalResult.ok (Value.bool (decide ((w.toNat : Int) ≤ 18))) = _
  simp

theorem constructorSourceDecimalsChecked_exec {c : ConstructorConfig} {evm evm' : EVM.State}
    {out : ByteArray} (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hc : callViaEVM evm c.baseToken 0 decimalsPayload (true, evm', out) false)
    (hhi : out.size < 2^255) (hlo : 32 ≤ out.size) (hword : (calldataWord out 0).toNat ≤ 18) :
    ExecBlock config (constructorSourceEntry c) evm (contract.ctor.body.take 4)
      (.ok (constructorSourceDecimals c (calldataWord out 0)) evm') := by
  have hd := constructorSourceDecimals_exec hv hc hhi ⟨hlo, by omega⟩
  change ExecBlock config _ _ (contract.ctor.body.take 3 ++
    [.require (.binary .le (.var "decimals_") (.intLit 18))]) _
  apply execBlockAppendOk hd
  exact .consNormal (.requireTrue (by
    rw [constructorSourceDecimals_limit, decide_eq_true hword])) .nil

theorem constructorSourceDecimalsChecked_revert {c : ConstructorConfig} {evm evm' : EVM.State}
    {z : Bool} {out : ByteArray} (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hc : callViaEVM evm c.baseToken 0 decimalsPayload (z, evm', out) false)
    (hhi : out.size < 2^255)
    (hvalid : ¬ (z = true ∧ 32 ≤ out.size ∧ (calldataWord out 0).toNat ≤ 18)) :
    ExecBlock config (constructorSourceEntry c) evm contract.ctor.body .reverted := by
  by_cases hdecode : z = true ∧ DecimalsReturnValid out
  · rcases hdecode with ⟨rfl, hdecode⟩
    have hd := constructorSourceDecimals_exec hv hc hhi hdecode
    rw [← List.take_append_drop 3 contract.ctor.body]
    apply execBlockAppendOk hd
    apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
    rw [constructorSourceDecimals_limit, decide_eq_false (fun hw ↦ hvalid ⟨rfl, hdecode.1, hw⟩)]
  · exact constructorSourceDecimals_revert hv hc hhi hdecode

end Benchmarks.CompoundIII.Comet
