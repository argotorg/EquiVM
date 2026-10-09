import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_047
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-!
# MetaMorphoV1_1 `asset()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9581; reach lemma `metaMorphoV1_1ReachAssetBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

theorem assetBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ExecTransitionBody config contract evm locals assetTransition.body
      (.returned
        { contract := contract
          locals := (locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).insert
            "__r" (.address v._asset)
          immutables := immStore v }
        evm (some [.address v._asset])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  refine ExecBlock.consNormal (internalCallReturnExpr (retTy := [.elem .address])
    (expr := .immutable "_asset") (value := .address v._asset) ?_ ?_) ?_
  · rfl
  · exact evalImmutable__asset _ _ _ _ _
  · exact ABlock.start.returns (by
      simp only [evalExpr?, store_get_self, EvalResult.ofOption])

set_option maxRecDepth 2000 in
theorem assetReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨9581⟩ R solcFreePtrMem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (EVM.word v._asset.val).toByteArray := by
  have rd9587 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9581_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd9598 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9587_fallthrough
    (immWords := wordsOf (immStore v))
    (by omega) (calldataLengthCheckOk hsz hhi hsize) rd9587
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9598
    (immWords := wordsOf (immStore v)) hstack rd9598
  have hw : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (wordsOf (immStore v) "_asset") = EVM.word v._asset.val := by
    rw [wordsOf_immStore__asset]
    exact solcAddrMask_clean_left (addressWord_val_canonical v._asset)
  exact hw ▸ (returnWordMemory _ ▸ hret)

set_option maxRecDepth 2000 in
theorem assetRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨9581⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9581_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem assetRevertHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hhi : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨9581⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd9587 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9581_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9587_taken
    (immWords := wordsOf (immStore v))
    hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩
      rw [calldataLengthCheckHuge hhi hsize]
      decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd9587
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in
/-- `asset()`: the theorem `Correct.lean` routes selector 16 to. -/
theorem metaMorphoV1_1AssetBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 16)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 16) rfl hsel
  have hd : dispatchMsg contract I.calldata = some assetTransition := by
    apply metaMorphoV1_1Dispatch_asset <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (assetTransition.params.map Param.name)
      (transitionSignature assetTransition).paramTypes I.calldata = some ∅ := by
    exact decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachAssetBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · exact (assetReturn v (by simp) hwv hsz hhi hsize rd).reEquivExecution
        hcode hd hdec (assetBodyReturns v _ ∅ hwv hhi)
        (returnEquiv_of_encode (addressReturnEncoding v._asset))
    · exact (assetRevertHuge v (by simp) hwv (by omega) hsize rd).reEquivExecutionRevert
        hcode hd hdec
        (bodyReverts_calldataBound "__calldata" (2 ^ 255 + 4) hwv (Nat.le_of_not_gt hhi))
  · exact (assetRevertNonPayable v (by simp) hwv rd).reEquivExecutionRevert
      hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
