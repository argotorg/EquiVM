import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.MappingMemory

/-!
# PoolManager `balanceOf(address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 11477; reach lemma `poolManagerReachBalanceOfBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 2000000

theorem balanceOfBodyReturns (evm : EVM.State) (locals imms : Store) (w id : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hcanon : w.toNat < EVM.addressModulus)
    (harg0 : locals.get? "arg0" = some (.address (AccountAddress.ofNat w.toNat)))
    (harg1 : locals.get? "arg1" = some (.int (Int.ofNat id.toNat)))
    (hbase : locals.get? "balanceOf" = none) :
    ExecTransitionBody config contract evm locals balanceOfTransition.body
      (.returned (calldataFrame contract locals imms evm) evm
        (some [.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (mappingSlotWord id (mappingSlotWord w ⟨4⟩))).toNat)])) imms := by
  apply guardedReturnBody hwv hhi
  apply evalExpr_storage_scalar_value (hbackend := rfl) (hloc := balanceOf_loc w id hcanon)
  · exact (store_get_ne locals _ (by decide : ("__calldata" == "balanceOf") = false)).trans hbase
  · apply evalMappingRef2 (v0 := .address (AccountAddress.ofNat w.toNat))
      (v1 := .int (Int.ofNat id.toNat)) (evalLocalValue ?_) rfl (evalLocalValue ?_) rfl
    · exact (store_get_ne locals _ (by decide : ("__calldata" == "arg0") = false)).trans harg0
    · exact (store_get_ne locals _ (by decide : ("__calldata" == "arg1") = false)).trans harg1
  · exact balanceOf_type _ _
  · exact storageLocLoad_uint256 _ _

theorem balanceOfTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {w : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 5 ≤ 1024) (hcanon : w.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) I g s0 ⟨11556⟩ (w :: solcAddrMask :: ⟨160⟩ :: ⟨32⟩ :: R)
      entryMemory aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      (solcSlotWordAt (mappingSlotWord (calldataWord I.calldata 36) (mappingSlotWord w ⟨4⟩)) σ I).toByteArray := by
  have hret := poolManagerBlocks.poolManager_block_11556 hstack h
  let m1 := twoWordHashMem (UInt256.land w solcAddrMask) ⟨4⟩ entryMemory
  let m2 := twoWordHashMem (calldataWord I.calldata 36) (keccakWord ⟨0⟩ ⟨64⟩ m1) m1
  change RDret (deployedRuntime v) g s0 σ
    (((solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ m2) σ I).toByteArray.write 0 m2 160 32).readWithPadding 160 32) at hret
  have hs1 : m1.size = 96 := twoWordHashMem_size_96 _ _ entryMemory_size
  have hs2 : m2.size = 96 := twoWordHashMem_size_96 _ _ hs1
  have hslot1 : keccakWord ⟨0⟩ ⟨64⟩ m1 = mappingSlotWord w ⟨4⟩ := by
    simp only [m1, twoWordHashMem_slot, solcAddrMask_clean hcanon]
  have hslot2 : keccakWord ⟨0⟩ ⟨64⟩ m2 =
      mappingSlotWord (calldataWord I.calldata 36) (mappingSlotWord w ⟨4⟩) :=
    (mappingMemory_slot _ _ hs1).trans (congrArg (mappingSlotWord (calldataWord I.calldata 36)) hslot1)
  have hout : ((solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ m2) σ I).toByteArray.write 0 m2 160 32).readWithPadding 160 32 =
      (solcSlotWordAt (mappingSlotWord (calldataWord I.calldata 36) (mappingSlotWord w ⟨4⟩)) σ I).toByteArray := by
    rw [returnWordAt160 hs2]
    exact congrArg (fun slot => (solcSlotWordAt slot σ I).toByteArray) hslot2
  exact (congrArg (fun bytes => RDret (deployedRuntime v) g s0 σ bytes) hout).mp hret

theorem poolManagerBalanceOfBodyCore {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (poolManagerSelBytes 0)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 0) rfl hsel
  have hd : dispatchMsg contract I.calldata = some balanceOfTransition := poolManagerDispatch_balanceOf hsel
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachBalanceOfBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨11477⟩ [⟨160⟩, solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (immutableLayout.runtime poolManagerBytecode (wordsOf (immStore v))) 0).contains
      (UInt256.ofNat 816) = true := by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_11477_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 68 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdDecode := poolManagerBlocks.poolManager_block_11483_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 2) hlen hhi hsize) rdSize
        have hjumpDec : (D_J (immutableLayout.runtime poolManagerBytecode (wordsOf (immStore v))) 0).contains
            (UInt256.ofNat 11583) = true := by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest
        have rdAddr := poolManagerBlocks.poolManager_block_11525 (by simp) hjumpDec rdDecode
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hjumpReturn : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 11556) = true := by
            rw [deployedRuntime_jumps v]; jump_dest
          obtain ⟨k', C', rdReturn⟩ := decodeAddress4 v (by simp) hcanon hjumpReturn rdAddr
          have hret := balanceOfTrace v (by simp) hcanon rdReturn
          have hdec : decodeCalldataWithMode config.abiDecodeMode
              (balanceOfTransition.params.map Param.name)
              (transitionSignature balanceOfTransition).paramTypes I.calldata =
              some ((((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))).insert "arg1" (.int (Int.ofNat (calldataWord I.calldata 36).toNat))) :=
            decodeCalldata_addr_uint256_ok hlen hhi hcanon
          let args := (((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))).insert "arg1" (.int (Int.ofNat (calldataWord I.calldata 36).toNat))
          have harg0 : args.get? "arg0" = some (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) :=
            (store_get_ne _ _ (by decide : ("arg1" == "arg0") = false)).trans (store_get_self _ _ _)
          have hbase : args.get? "balanceOf" = none :=
            (store_get_ne _ _ (by decide : ("arg1" == "balanceOf") = false)).trans
              ((store_get_ne _ _ (by decide : ("arg0" == "balanceOf") = false)).trans (store_get_empty _))
          have hbody := balanceOfBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I) args
            (immStore v) (calldataWord I.calldata 4) (calldataWord I.calldata 36) hwv hhi hcanon
            harg0 (store_get_self _ _ _) hbase
          exact hret.reEquivExecution hcode hd hdec hbody (returnEquiv_of_encode (uint256ReturnEncoding _))
        · exact (decodeAddress4Reverts v (by simp) hcanon rdAddr).reEquivDecodingFailed hcode hd
            (decodeCalldata_addr_uint256_none_noncanon hlen hhi hcanon)
      · have hguard := viaIRStaticLenCheckHuge (words := 2) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_11483_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
          (decodeCalldata_addr_uint256_none_huge (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 2) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_11483_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
        (decodeCalldata_addr_uint256_none_short hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_11477_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

/-- `balanceOf(address,uint256)`: the theorem `Correct.lean` routes selector 0 to. -/
theorem poolManagerBalanceOfBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 0)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) :=
  poolManagerBalanceOfBodyCore v hcode hsize hsel

end Benchmarks.UniswapV4PoolManager
