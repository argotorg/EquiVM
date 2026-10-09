import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.Storage
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_010
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_011
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-!
# MetaMorphoV1_1 `curator()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1336; reach lemma `metaMorphoV1_1ReachCuratorBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

theorem curatorBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbase : locals.get? "curator" = none) :
    ExecTransitionBody config contract evm locals curatorTransition.body
      (.returned
        { contract := contract
          locals := locals.insert "__calldata" (.bytes evm.executionEnv.calldata)
          immutables := immStore v }
        evm (some [.address (AccountAddress.ofNat (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩) solcAddrMask).toNat)]))
            (immStore v) := by
  apply ExecFuncBody.execBlockRet
  exact (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).returns
    (evalStorage_curator evm _ _ (by
      rw [store_get_ne _ _ (by decide)]
      exact hbase))

set_option maxRecDepth 2000 in
theorem curatorReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨1336⟩ R solcFreePtrMem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (UInt256.land (codeOwnerStorageWord I σ ⟨10⟩)
      solcAddrMask).toByteArray := by
  have rd1342 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1336_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd1353 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1342_fallthrough
    (immWords := wordsOf (immStore v))
    (by omega) (calldataLengthCheckOk hsz hhi hsize) rd1342
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1353
    (immWords := wordsOf (immStore v)) hstack rd1353
  exact returnWordMemory _ ▸ hret

set_option maxRecDepth 2000 in
theorem curatorRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨1336⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1336_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem curatorRevertHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hhi : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨1336⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd1342 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1336_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1342_taken
    (immWords := wordsOf (immStore v))
    hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩
      rw [calldataLengthCheckHuge hhi hsize]
      decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd1342
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in
/-- `curator()`: the theorem `Correct.lean` routes selector 70 to. -/
theorem metaMorphoV1_1CuratorBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 70)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 70) rfl hsel
  have hd : dispatchMsg contract I.calldata = some curatorTransition := by
    apply metaMorphoV1_1Dispatch_curator <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (curatorTransition.params.map Param.name)
      (transitionSignature curatorTransition).paramTypes I.calldata = some ∅ := by
    exact decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachCuratorBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · exact (curatorReturn v (by simp) hwv hsz hhi hsize rd).reEquivExecution
        hcode hd hdec (curatorBodyReturns v _ ∅ hwv hhi (by simp))
        (returnEquiv_of_encode (solcAddressReturnEncoding rfl (codeOwnerStorageWord I σ ⟨10⟩)))
    · exact (curatorRevertHuge v (by simp) hwv (by omega) hsize rd).reEquivExecutionRevert
        hcode hd hdec
        (bodyReverts_calldataBound "__calldata" (2 ^ 255 + 4) hwv (Nat.le_of_not_gt hhi))
  · exact (curatorRevertNonPayable v (by simp) hwv rd).reEquivExecutionRevert
      hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
