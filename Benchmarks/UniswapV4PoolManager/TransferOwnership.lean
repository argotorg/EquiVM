import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.Authorization
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_008

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000000

def transferOwnershipPost (evm : EVM.State) (newOwner : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) newOwner)

theorem transferOwnershipAssign (evm : EVM.State) (locals imms : Store) (newOwner : UInt256)
    (hc : newOwner.toNat < EVM.addressModulus) (hbase : locals.get? "owner" = none) :
    assignStorageRef? config (calldataFrame contract locals imms evm) evm .storage {base := "owner"}
      (.address (AccountAddress.ofNat newOwner.toNat)) =
      .ok (calldataFrame contract locals imms evm, transferOwnershipPost evm newOwner) :=
  addressScalarWrite newOwner rfl hc
    ((store_get_ne locals _ (by decide : ("__calldata" == "owner") = false)).trans hbase)
    (by decide +kernel) rfl

theorem transferOwnershipBodyReturns (evm : EVM.State) (locals imms : Store) (newOwner : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hc : newOwner.toNat < EVM.addressModulus)
    (hnew : locals.get? "newOwner" = some (.address (AccountAddress.ofNat newOwner.toNat)))
    (hbase : locals.get? "owner" = none) (hauth : ownerAuthorized evm) :
    ExecTransitionBody config contract evm locals transferOwnershipTransition.body
      (.returned (calldataFrame contract locals imms evm) (transferOwnershipPost evm newOwner) none) imms := by
  have hn := (store_get_ne locals (.bytes evm.executionEnv.calldata) (by decide : ("__calldata" == "newOwner") = false)).trans hnew
  apply ExecFuncBody.execBlockOK
  apply nonpayableCalldataBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact (ownerGuard_eval rfl ((store_get_ne locals _ (by decide : ("__calldata" == "owner") = false)).trans hbase)).trans
      (by rw [decide_eq_true hauth])
  refine ExecBlock.consNormal (ExecStmt.assign (evalLocalValue hn)
    (transferOwnershipAssign evm locals imms newOwner hc hbase)) ?_
  refine ExecBlock.consNormal (ExecStmt.emit
    (vals := [.address evm.executionEnv.source, .address (AccountAddress.ofNat newOwner.toNat)]) ?_) ExecBlock.nil
  simp only [evalExprs?, evalExpr?, calldataFrame, hn, EvalResult.ofOption,
    bind, EvalResult.bind, pure, envValue, transferOwnershipPost, storageStore_executionEnv]

theorem transferOwnershipBodyStatic (evm : EVM.State) (locals imms : Store) (newOwner : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hc : newOwner.toNat < EVM.addressModulus)
    (hnew : locals.get? "newOwner" = some (.address (AccountAddress.ofNat newOwner.toNat)))
    (hbase : locals.get? "owner" = none) (hauth : ownerAuthorized evm)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm locals transferOwnershipTransition.body .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply nonpayableCalldataBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact (ownerGuard_eval rfl ((store_get_ne locals _ (by decide : ("__calldata" == "owner") = false)).trans hbase)).trans
      (by rw [decide_eq_true hauth])
  exact ExecBlock.consStatic (ExecStmt.assignStatic
    (evalLocalValue ((store_get_ne locals _ (by decide : ("__calldata" == "newOwner") = false)).trans hnew))
    (transferOwnershipAssign evm locals imms newOwner hc hbase) hperm)


open poolManagerBlocks in
theorem transferOwnershipStaticTrace {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 2245) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RDstatic (immutableLayout.runtime poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2245⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2246⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2247⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2248⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2249⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2250⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.or (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2251⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨2252⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r8 hperm
    (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨2253⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64))
    (by evm_ov)


theorem poolManagerTransferOwnershipBodyCore {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (poolManagerSelBytes 29)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 29) rfl hsel
  have hd : dispatchMsg contract I.calldata = some transferOwnershipTransition := by
    apply poolManagerDispatch_transferOwnership <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachTransferOwnershipBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2120⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps v]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_2120_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdDecode := poolManagerBlocks.poolManager_block_2126_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 1) hlen hhi hsize) rdSize
        have hjumpDec : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 11583) = true := by
          rw [deployedRuntime_jumps v]; jump_dest
        have rdAddr := poolManagerBlocks.poolManager_block_2168 (by simp) hjumpDec rdDecode
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hjumpReturn : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 2208) = true := by
            rw [deployedRuntime_jumps v]; jump_dest
          obtain ⟨k', C', rdLoad⟩ := decodeAddress4 v (by simp) hcanon hjumpReturn rdAddr
          have hjumpAuth : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12295) = true := by
            rw [deployedRuntime_jumps v]; jump_dest
          obtain ⟨k'', C'', rdAuth⟩ := poolManagerBlocks.poolManager_block_2208 (by simp) hjumpAuth rdLoad
          let args := (∅ : Store).insert "newOwner" (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))
          have hdec : decodeCalldataWithMode config.abiDecodeMode
              (transferOwnershipTransition.params.map Param.name)
              (transitionSignature transferOwnershipTransition).paramTypes I.calldata = some args :=
            decodeCalldata_address_ok hlen hhi hcanon
          have hbase : args.get? "owner" = none :=
            (store_get_ne _ _ (by decide : ("newOwner" == "owner") = false)).trans (store_get_empty _)
          by_cases hauth : accountWord I.source = UInt256.land (solcSlotWordAt ⟨0⟩ σ I) solcAddrMask
          · have hjumpStore : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 2245) = true := by
              rw [deployedRuntime_jumps v]; jump_dest
            obtain ⟨ks, Cs, rdStore⟩ := requireAuthorizedPass v (by simp) hauth hjumpStore rdAuth
            cases hperm : I.perm with
            | false =>
              have hstatic := transferOwnershipStaticTrace (by simp) hperm rdStore
              exact hstatic.reEquivStaticHalt hcode hd hdec
                (transferOwnershipBodyStatic (initState σ σ₀ (Sat256.ofUInt256 g) A I) args (immStore v)
                  _ hwv hhi hcanon (store_get_self _ _ _) hbase hauth hperm)
            | true =>
              have hret := poolManagerBlocks.poolManager_block_2245 (by simp) hperm rdStore
              have hbody := transferOwnershipBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I) args
                (immStore v) _ hwv hhi hcanon (store_get_self _ _ _) hbase hauth
              exact hret.reEquivExecutionGen hcode hd hdec hbody
                (storageStore_accountMap (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner ⟨0⟩
                  (setAddressOffset0Word (solcSlotWordAt ⟨0⟩ σ I) (calldataWord I.calldata 4))).symm
                (.fallthrough rfl rfl (by native_decide))
          · exact (requireAuthorizedReverts v (by simp) hauth rdAuth).reEquivExecutionRevert hcode hd hdec
              (ownerGuardReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I) args (immStore v) _ hwv hhi hbase hauth)
        · exact (decodeAddress4Reverts v (by simp) hcanon rdAddr).reEquivDecodingFailed hcode hd
            (decodeCalldata_address_none_noncanon hlen hhi hcanon)
      · have hguard := viaIRStaticLenCheckHuge (words := 1) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_2126_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
          (decodeCalldata_address_none_huge (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 1) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_2126_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
        (decodeCalldata_address_none_short hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_2120_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

/-- `transferOwnership(address)`: the theorem consumed by the dispatcher. -/
theorem poolManagerTransferOwnershipBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 29)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) :=
  poolManagerTransferOwnershipBodyCore v hcode hsize hsel

end Benchmarks.UniswapV4PoolManager
