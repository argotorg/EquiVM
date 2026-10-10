import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.Storage
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_011

/-!
# PoolManager `owner()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 3041; reach lemma `poolManagerReachOwnerBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 2000000

theorem ownerBodyReturns (evm : EVM.State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hbase : locals.get? "owner" = none) :
    ExecTransitionBody config contract evm locals ownerTransition.body
      (.returned (calldataFrame contract locals imms evm) evm
        (some [.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat)])) imms :=
  addressGetterBodyReturns evm locals imms "owner" ⟨0⟩ hwv hhi (by decide) hbase
    (by decide +kernel) rfl

/-- All guards and return paths for the `owner()` ABI entry. -/
theorem poolManagerOwnerBodyCore {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (poolManagerSelBytes 20)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 20) rfl hsel
  have hd : dispatchMsg contract I.calldata = some ownerTransition := by
    apply poolManagerDispatch_owner <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (ownerTransition.params.map Param.name)
      (transitionSignature ownerTransition).paramTypes I.calldata = some ∅ :=
    decodeCalldataWithMode_empty_ok hsz
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachOwnerBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3041⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (immutableLayout.runtime poolManagerBytecode (wordsOf (immStore v))) 0).contains
      (UInt256.ofNat 816) = true := by
    rw [poolManagerPatchedValidJumpsRuntime v]
    jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_3041_fallthrough (by simp) hwv rdEntry
    by_cases hhi : I.calldata.size < calldataLimit
    · have rdLoad := poolManagerBlocks.poolManager_block_3047_fallthrough (by simp)
        (viaIRStaticLenCheckOk (words := 0) hsz hhi hsize) rdSize
      have hret := poolManagerBlocks.poolManager_block_3088 (by simp) rdLoad
      have hret' : RDret (deployedRuntime v) (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
          (UInt256.land (solcSlotWordAt ⟨0⟩ σ I) solcAddrMask).toByteArray := by
        simpa only [show UInt256.ofNat 64 = (⟨64⟩ : UInt256) from rfl,
          show (UInt256.ofNat 32).toNat = 32 from rfl, entryMemory_returnWord] using hret
      have hbody := ownerBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        (immStore v) hwv hhi (store_get_empty _)
      exact hret'.reEquivExecution hcode hd hdec hbody
        (returnEquiv_of_encode (solcAddressReturnEncoding (addrTy := .elem .address) rfl _))
    · have hguard := viaIRStaticLenCheckHuge (words := 0) (Nat.le_of_not_gt hhi) hsize (by decide)
      have rdRevert := poolManagerBlocks.poolManager_block_3047_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      exact (emptyRevert v (by simp) rdRevert).reEquivExecutionRevert hcode hd hdec
        (calldataSizeBodyReverts (rest := [.return [.storage {base := "owner"}]]) hwv hhi)
  · have rdRevert := poolManagerBlocks.poolManager_block_3041_taken (by simp) hwv hjump rdEntry
    exact (emptyRevert v (by simp) rdRevert).reEquivExecutionRevert hcode hd hdec
      (bodyReverts_nonPayable hwv)

/-- `owner()`: the theorem `Correct.lean` routes selector 20 to. -/
theorem poolManagerOwnerBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I) (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 20)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) :=
  poolManagerOwnerBodyCore v hcode hsize hsel

end Benchmarks.UniswapV4PoolManager
