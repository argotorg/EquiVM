import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.MappingMemory
import Benchmarks.UniswapV4PoolManager.ProtocolFeesSource
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_010
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_011

/-!
# PoolManager `protocolFeesAccrued(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2942; reach lemma `poolManagerReachProtocolFeesAccruedBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 2000000

theorem protocolFeesAccruedBodyReturns (evm : EVM.State) (locals imms : Store) (w : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hcanon : w.toNat < EVM.addressModulus)
    (harg : locals.get? "arg0" = some (.address (AccountAddress.ofNat w.toNat)))
    (hbase : locals.get? "protocolFeesAccrued" = none) :
    ExecTransitionBody config contract evm locals protocolFeesAccruedTransition.body
      (.returned (calldataFrame contract locals imms evm) evm
        (some [.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mappingSlotWord w ⟨1⟩)).toNat)])) imms := by
  apply guardedReturnBody hwv hhi
  have hr := protocolFeesRead (f := calldataFrame contract locals imms evm) (evm := evm) rfl
    ((store_get_ne locals _ (by decide : ("__calldata" == "protocolFeesAccrued") = false)).trans hbase)
    (evalLocalValue ((store_get_ne locals _ (by decide : ("__calldata" == "arg0") = false)).trans harg))
  have hw : accountWord (AccountAddress.ofNat w.toNat) = w :=
    (accountWord_eq_iff _ w hcanon).1 rfl
  simpa only [protocolFeesWord, protocolFeesSlot, hw] using hr

theorem protocolFeesAccruedTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {w : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 4 ≤ 1024) (hcanon : w.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) I g s0 ⟨3018⟩ (w :: solcAddrMask :: R)
      entryMemory aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (solcSlotWordAt (mappingSlotWord w ⟨1⟩) σ I).toByteArray := by
  have hret := poolManagerBlocks.poolManager_block_3018 hstack h
  change RDret (deployedRuntime v) g s0 σ
    (((solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.land w solcAddrMask) ⟨1⟩ entryMemory)) σ I).toByteArray.write 0
      (twoWordHashMem (UInt256.land w solcAddrMask) ⟨1⟩ entryMemory)
      (memLoad ⟨64⟩ (twoWordHashMem (UInt256.land w solcAddrMask) ⟨1⟩ entryMemory)).toNat 32).readWithPadding
      (memLoad ⟨64⟩ (twoWordHashMem (UInt256.land w solcAddrMask) ⟨1⟩ entryMemory)).toNat 32) at hret
  simpa only [solcAddrMask_clean hcanon, twoWordHashMem_slot, twoWordHashMem_returnWord] using hret

theorem poolManagerProtocolFeesAccruedBodyCore {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (poolManagerSelBytes 31)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 31) rfl hsel
  have hd : dispatchMsg contract I.calldata = some protocolFeesAccruedTransition := by
    apply poolManagerDispatch_protocolFeesAccrued <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachProtocolFeesAccruedBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2942⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (immutableLayout.runtime poolManagerBytecode (wordsOf (immStore v))) 0).contains
      (UInt256.ofNat 816) = true := by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_2942_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdDecode := poolManagerBlocks.poolManager_block_2948_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 1) hlen hhi hsize) rdSize
        have hjumpDec : (D_J (immutableLayout.runtime poolManagerBytecode (wordsOf (immStore v))) 0).contains
            (UInt256.ofNat 11583) = true := by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest
        have rdAddr := poolManagerBlocks.poolManager_block_2990 (by simp) hjumpDec rdDecode
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hjumpReturn : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 3018) = true := by
            rw [deployedRuntime_jumps v]; jump_dest
          obtain ⟨k', C', rdReturn⟩ := decodeAddress4 v (by simp) hcanon hjumpReturn rdAddr
          have hret := protocolFeesAccruedTrace v (by simp) hcanon rdReturn
          have hdec : decodeCalldataWithMode config.abiDecodeMode
              (protocolFeesAccruedTransition.params.map Param.name)
              (transitionSignature protocolFeesAccruedTransition).paramTypes I.calldata =
              some ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))) :=
            decodeCalldata_address_ok hlen hhi hcanon
          have hbody := protocolFeesAccruedBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))
            (immStore v) (calldataWord I.calldata 4) hwv hhi hcanon (store_get_self _ _ _)
            ((store_get_ne ∅ _ (by decide : ("arg0" == "protocolFeesAccrued") = false)).trans (store_get_empty _))
          exact hret.reEquivExecution hcode hd hdec hbody (returnEquiv_of_encode (uint256ReturnEncoding _))
        · exact (decodeAddress4Reverts v (by simp) hcanon rdAddr).reEquivDecodingFailed hcode hd
            (decodeCalldata_address_none_noncanon hlen hhi hcanon)
      · have hguard := viaIRStaticLenCheckHuge (words := 1) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_2948_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
          (decodeCalldata_address_none_huge (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 1) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_2948_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
        (decodeCalldata_address_none_short hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_2942_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

/-- `protocolFeesAccrued(address)`: the theorem `Correct.lean` routes selector 31 to. -/
theorem poolManagerProtocolFeesAccruedBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 31)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) :=
  poolManagerProtocolFeesAccruedBodyCore v hcode hsize hsel

end Benchmarks.UniswapV4PoolManager
