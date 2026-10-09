import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_046
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_047
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-!
# MetaMorphoV1_1 `MORPHO()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9513; reach lemma `metaMorphoV1_1ReachMORPHOBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

theorem morphoBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ExecTransitionBody config contract evm locals mORPHOTransition.body
      (.returned
        { contract := contract
          locals := locals.insert "__calldata" (.bytes evm.executionEnv.calldata)
          immutables := immStore v }
        evm (some [.address v.MORPHO])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  exact (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).returns
    (evalImmutable_MORPHO _ _ _ _ _)

set_option maxRecDepth 2000 in
theorem morphoReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨9513⟩ R solcFreePtrMem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (EVM.word v.MORPHO.val).toByteArray := by
  have rd9519 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9513_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd9530 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9519_fallthrough
    (immWords := wordsOf (immStore v))
    (by omega) (calldataLengthCheckOk hsz hhi hsize) rd9519
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9530
    (immWords := wordsOf (immStore v)) hstack rd9530
  have hw : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (wordsOf (immStore v) "MORPHO") = EVM.word v.MORPHO.val := by
    rw [wordsOf_immStore_MORPHO]
    exact solcAddrMask_clean_left (addressWord_val_canonical v.MORPHO)
  exact hw ▸ (returnWordMemory _ ▸ hret)

set_option maxRecDepth 2000 in
theorem morphoRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨9513⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9513_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem morphoRevertHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hhi : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨9513⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd9519 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9513_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_9519_taken
    (immWords := wordsOf (immStore v))
    hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩
      rw [calldataLengthCheckHuge hhi hsize]
      decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd9519
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in
/-- `MORPHO()`: the theorem `Correct.lean` routes selector 17 to. -/
theorem metaMorphoV1_1MORPHOBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 17)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 17) rfl hsel
  have hd : dispatchMsg contract I.calldata = some mORPHOTransition := by
    apply metaMorphoV1_1Dispatch_mORPHO <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (mORPHOTransition.params.map Param.name)
      (transitionSignature mORPHOTransition).paramTypes I.calldata = some ∅ := by
    exact decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachMORPHOBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · exact (morphoReturn v (by simp) hwv hsz hhi hsize rd).reEquivExecution
        hcode hd hdec (morphoBodyReturns v _ ∅ hwv hhi)
        (returnEquiv_of_encode (addressReturnEncoding v.MORPHO))
    · exact (morphoRevertHuge v (by simp) hwv (by omega) hsize rd).reEquivExecutionRevert
        hcode hd hdec
        (bodyReverts_calldataBound "__calldata" (2 ^ 255 + 4) hwv (Nat.le_of_not_gt hhi))
  · exact (morphoRevertNonPayable v (by simp) hwv rd).reEquivExecutionRevert
      hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
