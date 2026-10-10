import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.Storage
import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_030

/-!
# PoolManager `extsload(bytes32)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 10651; reach lemma `poolManagerReachExtsload_bytes32Body`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 2000000

theorem extsloadWordBodyReturns (evm : EVM.State) (locals imms : Store) (slot : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hslot : locals.get? "slot" = some (wordBytes32Value slot))
    (hbase : locals.get? "rawSlots" = none) :
    ExecTransitionBody config contract evm locals extsload_bytes32Transition.body
      (.returned (calldataFrame contract locals imms evm) evm
        (some [wordBytes32Value (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)]))
      imms := by
  apply guardedReturnBody hwv hhi
  apply evalCastValue (rawSlots_read rfl ?_ ?_) (castUint256ToBytes32 _)
  · exact (store_get_ne locals _ (by decide : ("__calldata" == "rawSlots") = false)).trans hbase
  · apply evalCastValue (evalLocalValue ?_) (castBytes32ToUint256 slot)
    exact (store_get_ne locals _ (by decide : ("__calldata" == "slot") = false)).trans hslot

theorem poolManagerExtsload_bytes32BodyCore {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (poolManagerSelBytes 6)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 6) rfl hsel
  have hd : dispatchMsg contract I.calldata = some extsload_bytes32Transition := by
    apply poolManagerDispatch_extsload_bytes32 <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachExtsload_bytes32Body (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨10651⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (immutableLayout.runtime poolManagerBytecode (wordsOf (immStore v))) 0).contains
      (UInt256.ofNat 816) = true := by
    rw [poolManagerPatchedValidJumpsRuntime v]
    jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_10651_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdLoad := poolManagerBlocks.poolManager_block_10657_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 1) hlen hhi hsize) rdSize
        have hret := poolManagerBlocks.poolManager_block_10699 (by simp) rdLoad
        have hret' : RDret (deployedRuntime v) (Sat256.ofUInt256 g)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
            (solcSlotWordAt (calldataWord I.calldata 4) σ I).toByteArray := by
          simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
            show (UInt256.ofNat 32).toNat = 32 from rfl, returnWordAtZero] using hret
        have hdec : decodeCalldataWithMode config.abiDecodeMode
            (extsload_bytes32Transition.params.map Param.name)
            (transitionSignature extsload_bytes32Transition).paramTypes I.calldata =
            some ((∅ : Store).insert "slot" (wordBytes32Value (calldataWord I.calldata 4))) :=
          decodeCalldataBytes32Word hlen hhi
        have hbody := extsloadWordBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          ((∅ : Store).insert "slot" (wordBytes32Value (calldataWord I.calldata 4)))
          (immStore v) (calldataWord I.calldata 4) hwv hhi (store_get_self _ _ _)
          ((store_get_ne ∅ _ (by decide : ("slot" == "rawSlots") = false)).trans (store_get_empty _))
        exact hret'.reEquivExecution hcode hd hdec hbody
          (returnEquiv_of_encode (bytes32ReturnEncoding _))
      · have hguard := viaIRStaticLenCheckHuge (words := 1) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_10657_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
          (decodeCalldata_bytes32_none_huge (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 1) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_10657_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
        (decodeCalldata_bytes32_none_short hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_10651_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

/-- `extsload(bytes32)`: the theorem `Correct.lean` routes selector 6 to. -/
theorem poolManagerExtsload_bytes32Body {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 6)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) :=
  poolManagerExtsload_bytes32BodyCore v hcode hsize hsel

end Benchmarks.UniswapV4PoolManager
