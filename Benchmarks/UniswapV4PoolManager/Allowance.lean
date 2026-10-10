import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.MappingMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_023

/-!
# PoolManager `allowance(address,address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 8163; reach lemma `poolManagerReachAllowanceBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 2000000

theorem allowanceBodyReturns (evm : EVM.State) (locals imms : Store) (a b id : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hca : a.toNat < EVM.addressModulus) (hcb : b.toNat < EVM.addressModulus)
    (harg0 : locals.get? "arg0" = some (.address (AccountAddress.ofNat a.toNat)))
    (harg1 : locals.get? "arg1" = some (.address (AccountAddress.ofNat b.toNat)))
    (harg2 : locals.get? "arg2" = some (.int (Int.ofNat id.toNat)))
    (hbase : locals.get? "allowance" = none) :
    ExecTransitionBody config contract evm locals allowanceTransition.body
      (.returned (calldataFrame contract locals imms evm) evm
        (some [.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (mappingSlotWord id (mappingSlotWord b (mappingSlotWord a ⟨5⟩)))).toNat)])) imms := by
  apply guardedReturnBody hwv hhi
  apply evalExpr_storage_scalar_value (hbackend := rfl) (hloc := allowance_loc a b id hca hcb)
  · exact (store_get_ne locals _ (by decide : ("__calldata" == "allowance") = false)).trans hbase
  · apply evalMappingRef3 (v0 := .address (AccountAddress.ofNat a.toNat))
      (v1 := .address (AccountAddress.ofNat b.toNat)) (v2 := .int (Int.ofNat id.toNat))
      (evalLocalValue ?_) rfl (evalLocalValue ?_) rfl (evalLocalValue ?_) rfl
    · exact (store_get_ne locals _ (by decide : ("__calldata" == "arg0") = false)).trans harg0
    · exact (store_get_ne locals _ (by decide : ("__calldata" == "arg1") = false)).trans harg1
    · exact (store_get_ne locals _ (by decide : ("__calldata" == "arg2") = false)).trans harg2
  · exact allowance_type _ _ _
  · exact storageLocLoad_uint256 _ _

theorem allowanceTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {a b : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 4 ≤ 1024)
    (hca : a.toNat < EVM.addressModulus) (hcb : b.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) I g s0 ⟨8247⟩ (b :: solcAddrMask :: a :: R)
      entryMemory aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      (solcSlotWordAt (mappingSlotWord (calldataWord I.calldata 68)
        (mappingSlotWord b (mappingSlotWord a ⟨5⟩))) σ I).toByteArray := by
  have hret := poolManagerBlocks.poolManager_block_8247 hstack h
  let m1 := twoWordHashMem (UInt256.land a solcAddrMask) ⟨5⟩ entryMemory
  let m2 := twoWordHashMem (UInt256.land b solcAddrMask) (keccakWord ⟨0⟩ ⟨64⟩ m1) m1
  let m3 := twoWordHashMem (calldataWord I.calldata 68) (keccakWord ⟨0⟩ ⟨64⟩ m2) m2
  let outWord := solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩ m3) σ I
  change RDret (deployedRuntime v) g s0 σ
    ((outWord.toByteArray.write 0 m3 (memLoad ⟨64⟩ m3).toNat 32).readWithPadding (memLoad ⟨64⟩ m3).toNat 32) at hret
  have hs1 : m1.size = 96 := twoWordHashMem_size_96 _ _ entryMemory_size
  have hs2 : m2.size = 96 := twoWordHashMem_size_96 _ _ hs1
  have hs3 : m3.size = 96 := twoWordHashMem_size_96 _ _ hs2
  have hp2 : memLoad ⟨64⟩ m2 = ⟨160⟩ :=
    (mappingMemory_load64 _ _ hs1).trans (twoWordHashMem_load64 _ _)
  have hp3 : memLoad ⟨64⟩ m3 = ⟨160⟩ := (mappingMemory_load64 _ _ hs2).trans hp2
  have hslot1 : keccakWord ⟨0⟩ ⟨64⟩ m1 = mappingSlotWord a ⟨5⟩ := by
    simp only [m1, twoWordHashMem_slot, solcAddrMask_clean hca]
  have hslot2 : keccakWord ⟨0⟩ ⟨64⟩ m2 = mappingSlotWord b (mappingSlotWord a ⟨5⟩) := by
    change keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem _ _ m1) = _
    rw [mappingMemory_slot _ _ hs1, solcAddrMask_clean hcb, hslot1]
  have hslot3 : keccakWord ⟨0⟩ ⟨64⟩ m3 =
      mappingSlotWord (calldataWord I.calldata 68) (mappingSlotWord b (mappingSlotWord a ⟨5⟩)) :=
    (mappingMemory_slot _ _ hs2).trans (congrArg (mappingSlotWord (calldataWord I.calldata 68)) hslot2)
  have hout : (outWord.toByteArray.write 0 m3 (memLoad ⟨64⟩ m3).toNat 32).readWithPadding (memLoad ⟨64⟩ m3).toNat 32 =
      (solcSlotWordAt (mappingSlotWord (calldataWord I.calldata 68)
        (mappingSlotWord b (mappingSlotWord a ⟨5⟩))) σ I).toByteArray := by
    rw [hp3]
    change (outWord.toByteArray.write 0 m3 160 32).readWithPadding 160 32 = _
    rw [returnWordAt160 hs3]
    exact congrArg (fun slot => (solcSlotWordAt slot σ I).toByteArray) hslot3
  exact (congrArg (fun bytes => RDret (deployedRuntime v) g s0 σ bytes) hout).mp hret

theorem poolManagerAllowanceBodyCore {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (poolManagerSelBytes 17)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 17) rfl hsel
  have hd : dispatchMsg contract I.calldata = some allowanceTransition := by
    apply poolManagerDispatch_allowance <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachAllowanceBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8163⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (immutableLayout.runtime poolManagerBytecode (wordsOf (immStore v))) 0).contains
      (UInt256.ofNat 816) = true := by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_8163_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 100 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdDecode := poolManagerBlocks.poolManager_block_8169_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 3) hlen hhi hsize) rdSize
        have hjumpDec : (D_J (immutableLayout.runtime poolManagerBytecode (wordsOf (immStore v))) 0).contains
            (UInt256.ofNat 11583) = true := by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest
        have rdAddr := poolManagerBlocks.poolManager_block_8211 (by simp) hjumpDec rdDecode
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hjumpReturn : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 8218) = true := by
            rw [deployedRuntime_jumps v]; jump_dest
          obtain ⟨k', C', rdReturn⟩ := decodeAddress4 v (by simp) hcanon hjumpReturn rdAddr
          have hjumpDec1 : (D_J (immutableLayout.runtime poolManagerBytecode (wordsOf (immStore v))) 0).contains
              (UInt256.ofNat 11618) = true := by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest
          have rdAddr1 := poolManagerBlocks.poolManager_block_8218 (by simp) hjumpDec1 rdReturn
          by_cases hcanon1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
          · have hjumpReturn1 : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 8247) = true := by
              rw [deployedRuntime_jumps v]; jump_dest
            obtain ⟨k'', C'', rdReturn1⟩ := decodeAddress36 v (by simp) hcanon1 hjumpReturn1 rdAddr1
            have hret := allowanceTrace v (by simp) hcanon hcanon1 rdReturn1
            let args := ((((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))).insert "arg1" (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))).insert "arg2" (.int (Int.ofNat (calldataWord I.calldata 68).toNat))
            have hdec : decodeCalldataWithMode config.abiDecodeMode
                (allowanceTransition.params.map Param.name)
                (transitionSignature allowanceTransition).paramTypes I.calldata = some args :=
              decodeCalldata_address_address_uint256_ok hlen hhi hcanon hcanon1
            have harg0 : args.get? "arg0" = some (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) :=
              (store_get_ne _ _ (by decide : ("arg2" == "arg0") = false)).trans
                ((store_get_ne _ _ (by decide : ("arg1" == "arg0") = false)).trans (store_get_self _ _ _))
            have harg1 : args.get? "arg1" = some (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)) :=
              (store_get_ne _ _ (by decide : ("arg2" == "arg1") = false)).trans (store_get_self _ _ _)
            have hbase : args.get? "allowance" = none :=
              (store_get_ne _ _ (by decide : ("arg2" == "allowance") = false)).trans
                ((store_get_ne _ _ (by decide : ("arg1" == "allowance") = false)).trans
                  ((store_get_ne _ _ (by decide : ("arg0" == "allowance") = false)).trans (store_get_empty _)))
            have hbody := allowanceBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I) args
              (immStore v) (calldataWord I.calldata 4) (calldataWord I.calldata 36) (calldataWord I.calldata 68)
              hwv hhi hcanon hcanon1 harg0 harg1 (store_get_self _ _ _) hbase
            exact hret.reEquivExecution hcode hd hdec hbody (returnEquiv_of_encode (uint256ReturnEncoding _))
          · exact (decodeAddress36Reverts v (by simp) hcanon1 rdAddr1).reEquivDecodingFailed hcode hd
              (decodeCalldata_address_address_uint256_none_noncanon1 hlen hhi hcanon hcanon1)
        · exact (decodeAddress4Reverts v (by simp) hcanon rdAddr).reEquivDecodingFailed hcode hd
            (decodeCalldata_address_address_uint256_none_noncanon0 hlen hhi hcanon)
      · have hguard := viaIRStaticLenCheckHuge (words := 3) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_8169_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
          (decodeCalldata_address_address_uint256_none_huge (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 3) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_8169_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
        (decodeCalldata_address_address_uint256_none_short hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_8163_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

/-- `allowance(address,address,uint256)`: the theorem `Correct.lean` routes selector 17 to. -/
theorem poolManagerAllowanceBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 17)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) :=
  poolManagerAllowanceBodyCore v hcode hsize hsel

end Benchmarks.UniswapV4PoolManager
