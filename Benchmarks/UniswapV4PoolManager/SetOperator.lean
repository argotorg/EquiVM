import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.MappingMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_024

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000000

def setOperatorSlot (evm : EVM.State) (operator : UInt256) : UInt256 :=
  mappingSlotWord operator (mappingSlotWord (accountWord evm.executionEnv.source) ⟨3⟩)

def setOperatorPost (evm : EVM.State) (operator approved : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (setOperatorSlot evm operator)
    (setBoolOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (setOperatorSlot evm operator)) approved)

theorem setOperatorAssign (evm : EVM.State) (locals imms : Store) (operator approved : UInt256)
    (hcanon : operator.toNat < EVM.addressModulus)
    (hop : locals.get? "operator" = some (.address (AccountAddress.ofNat operator.toNat)))
    (hbase : locals.get? "isOperator" = none) :
    assignStorageRef? config (calldataFrame contract locals imms evm) evm .storage
      {base := "isOperator", steps := [.mindex (.env .caller), .mindex (.var "operator")]}
      (wordToElem .bool approved) =
      .ok (calldataFrame contract locals imms evm, setOperatorPost evm operator approved) := by
  apply isOperatorWrite (accountWord evm.executionEnv.source) operator approved rfl
    (accountWord_canonical _) hcanon
  · exact (store_get_ne locals _ (by decide : ("__calldata" == "isOperator") = false)).trans hbase
  · rw [accountWord_address]
    simp only [evalExpr?, envValue, pure]
  · exact evalLocalValue ((store_get_ne locals _ (by decide : ("__calldata" == "operator") = false)).trans hop)

theorem setOperatorBodyReturns (evm : EVM.State) (locals imms : Store) (operator approved : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hcanon : operator.toNat < EVM.addressModulus)
    (hop : locals.get? "operator" = some (.address (AccountAddress.ofNat operator.toNat)))
    (hap : locals.get? "approved" = some (wordToElem .bool approved))
    (hbase : locals.get? "isOperator" = none) :
    ExecTransitionBody config contract evm locals setOperatorTransition.body
      (.returned (calldataFrame contract locals imms evm) (setOperatorPost evm operator approved)
        (some [.bool true])) imms := by
  have ha := (store_get_ne locals (.bytes evm.executionEnv.calldata) (by decide : ("__calldata" == "approved") = false)).trans hap
  have ho := (store_get_ne locals (.bytes evm.executionEnv.calldata) (by decide : ("__calldata" == "operator") = false)).trans hop
  apply ExecFuncBody.execBlockRet
  apply nonpayableCalldataBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.assign (evalLocalValue ha)
    (setOperatorAssign evm locals imms operator approved hcanon hop hbase)) ?_
  refine ExecBlock.consNormal (ExecStmt.emit
    (vals := [.address evm.executionEnv.source, .address (AccountAddress.ofNat operator.toNat),
      wordToElem .bool approved]) ?_) ?_
  · simp only [evalExprs?, evalExpr?, calldataFrame, ha, ho, EvalResult.ofOption,
      bind, EvalResult.bind, pure, envValue, setOperatorPost, storageStore_executionEnv]
  · exact ExecBlock.consReturn (ExecStmt.return (by simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]))

theorem setOperatorBodyStatic (evm : EVM.State) (locals imms : Store) (operator approved : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hcanon : operator.toNat < EVM.addressModulus)
    (hop : locals.get? "operator" = some (.address (AccountAddress.ofNat operator.toNat)))
    (hap : locals.get? "approved" = some (wordToElem .bool approved))
    (hbase : locals.get? "isOperator" = none) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm locals setOperatorTransition.body .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply nonpayableCalldataBlock hwv hhi
  exact ExecBlock.consStatic (ExecStmt.assignStatic
    (evalLocalValue ((store_get_ne locals _ (by decide : ("__calldata" == "approved") = false)).trans hap))
    (setOperatorAssign evm locals imms operator approved hcanon hop hbase) hperm)


theorem setOperatorTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {operator approved : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 7 ≤ 1024)
    (hc : operator.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (h : RD (deployedRuntime v) I g s0 ⟨8385⟩
      (operator :: UInt256.isZero (UInt256.isZero approved) :: R) entryMemory aw rdata σ k C) :
    let slot := mappingSlotWord operator (mappingSlotWord (accountWord I.source) ⟨3⟩)
    RDret (deployedRuntime v) g s0
      (sstoreAccountMap I.codeOwner σ slot (setBoolOffset0Word (solcSlotWordAt slot σ I) approved))
      (UInt256.toByteArray ⟨1⟩) := by
  have hret := poolManagerBlocks.poolManager_block_8385 hstack hperm h
  let m1 := twoWordHashMem (accountWord I.source) ⟨3⟩ entryMemory
  let m2 := twoWordHashMem (UInt256.land operator solcAddrMask) (keccakWord ⟨0⟩ ⟨64⟩ m1) m1
  let normalized := UInt256.isZero (UInt256.isZero approved)
  let written := normalized.toByteArray.write 0 m2 (memLoad ⟨64⟩ m2).toNat 32
  let slot := keccakWord ⟨0⟩ ⟨64⟩ m2
  let stored := UInt256.lor (UInt256.land normalized ⟨255⟩)
    (UInt256.land (solcSlotWordAt slot σ I) (UInt256.lnot ⟨255⟩))
  change RDret (deployedRuntime v) g s0 (sstoreAccountMap I.codeOwner σ slot stored)
    (((⟨1⟩ : UInt256).toByteArray.write 0 written (memLoad ⟨64⟩ written).toNat 32).readWithPadding
      (memLoad ⟨64⟩ written).toNat 32) at hret
  have hs1 : m1.size = 96 := twoWordHashMem_size_96 _ _ entryMemory_size
  have hs2 : m2.size = 96 := twoWordHashMem_size_96 _ _ hs1
  have hp2 : memLoad ⟨64⟩ m2 = ⟨160⟩ :=
    (mappingMemory_load64 _ _ hs1).trans (twoWordHashMem_load64 _ _)
  have hslot1 : keccakWord ⟨0⟩ ⟨64⟩ m1 = mappingSlotWord (accountWord I.source) ⟨3⟩ :=
    twoWordHashMem_slot _ _
  have hslot2 : slot = mappingSlotWord operator (mappingSlotWord (accountWord I.source) ⟨3⟩) := by
    change keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem _ _ m1) = _
    rw [mappingMemory_slot _ _ hs1, solcAddrMask_clean hc, hslot1]
  have hacc : sstoreAccountMap I.codeOwner σ slot stored =
      sstoreAccountMap I.codeOwner σ
        (mappingSlotWord operator (mappingSlotWord (accountWord I.source) ⟨3⟩))
        (setBoolOffset0Word (solcSlotWordAt
          (mappingSlotWord operator (mappingSlotWord (accountWord I.source) ⟨3⟩)) σ I) approved) := by
    dsimp only [stored, normalized]
    rw [hslot2, boolNormalize_mask, u256_lor_comm]
    rfl
  have hout := eventWordThenReturn hp2 (by rw [hs2]) (by decide) (by rw [hs2]; native_decide) normalized ⟨1⟩
  exact (congrArg₂ (fun acc bytes => RDret (deployedRuntime v) g s0 acc bytes) hacc hout).mp hret

open poolManagerBlocks in
theorem setOperatorStaticTrace {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 8385) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RDstatic (immutableLayout.runtime poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8385⟩ : UInt256), UInt8.ofNat 115, .Push .PUSH20, some ((UInt256.ofNat 1461501637330902918203684832716283019655932542975), 20), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8406⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.caller (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8407⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8408⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := RD.genMstore r4 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8409⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 3) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8410⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 3), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8412⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genMstore r7 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8414⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8415⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8417⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genKeccak256 r10 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8418⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8419⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8420⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8421⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8422⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := RD.genMstore r15 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8423⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8424⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := RD.genMstore r17 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8426⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8427⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8429⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := RD.genKeccak256 r20 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8430⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8431⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680), 32), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.dup2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8464⟩ : UInt256), UInt8.ofNat 129, .DUP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r24⟩ := RD.sload r23 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8465⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8466⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 255) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8467⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 255), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.dup6 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8469⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8470⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.or (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8471⟩ : UInt256), UInt8.ofNat 23, .OR, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨8472⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r30 hperm
    (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨8473⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64))
    (by evm_ov)


theorem poolManagerSetOperatorBodyCore {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (poolManagerSelBytes 16)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 16) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setOperatorTransition := by
    apply poolManagerDispatch_setOperator <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachSetOperatorBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨8315⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps v]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_8315_fallthrough (by simp) hwv rdEntry
    by_cases hlen : 68 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · have rdDecode := poolManagerBlocks.poolManager_block_8321_fallthrough (by simp)
          (viaIRStaticLenCheckOk (words := 2) hlen hhi hsize) rdSize
        have hjumpDec : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 11583) = true := by
          rw [deployedRuntime_jumps v]; jump_dest
        have rdAddr := poolManagerBlocks.poolManager_block_8363 (by simp) hjumpDec rdDecode
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hjumpReturn : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 8370) = true := by
            rw [deployedRuntime_jumps v]; jump_dest
          obtain ⟨k', C', rdBool⟩ := decodeAddress4 v (by simp) hcanon hjumpReturn rdAddr
          by_cases hbool : calldataWord I.calldata 36 = ⟨0⟩ ∨ calldataWord I.calldata 36 = ⟨1⟩
          · have rdReturn := poolManagerBlocks.poolManager_block_8370_fallthrough (by simp)
              (boolSubNormalize_zero hbool) rdBool
            let args := ((∅ : Store).insert "operator"
              (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "approved"
              (wordToElem .bool (calldataWord I.calldata 36))
            have hdec : decodeCalldataWithMode config.abiDecodeMode
                (setOperatorTransition.params.map Param.name)
                (transitionSignature setOperatorTransition).paramTypes I.calldata = some args :=
              decodeCalldata_addr_bool_ok hlen hhi hcanon hbool
            have hop : args.get? "operator" = some (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) :=
              (store_get_ne _ _ (by decide : ("approved" == "operator") = false)).trans (store_get_self _ _ _)
            have hbase : args.get? "isOperator" = none :=
              (store_get_ne _ _ (by decide : ("approved" == "isOperator") = false)).trans
                ((store_get_ne _ _ (by decide : ("operator" == "isOperator") = false)).trans (store_get_empty _))
            cases hperm : I.perm with
            | false =>
              have hstatic := setOperatorStaticTrace (by simp) hperm rdReturn
              exact hstatic.reEquivStaticHalt hcode hd hdec
                (setOperatorBodyStatic (initState σ σ₀ (Sat256.ofUInt256 g) A I) args (immStore v)
                  _ _ hwv hhi hcanon hop (store_get_self _ _ _) hbase hperm)
            | true =>
              have hret := setOperatorTrace v (by simp) hcanon hperm rdReturn
              have hbody := setOperatorBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I) args
                (immStore v) _ _ hwv hhi hcanon hop (store_get_self _ _ _) hbase
              exact hret.reEquivExecutionGen hcode hd hdec hbody
                (storageStore_accountMap (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner
                  (setOperatorSlot (initState σ σ₀ (Sat256.ofUInt256 g) A I) (calldataWord I.calldata 4))
                  (setBoolOffset0Word (Solm.EVM.storageLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner
                    (setOperatorSlot (initState σ σ₀ (Sat256.ofUInt256 g) A I) (calldataWord I.calldata 4)))
                    (calldataWord I.calldata 36))).symm
                (returnEquiv_of_encode (boolReturnEncoding true))
          · have rdRevert := poolManagerBlocks.poolManager_block_8370_taken (by simp)
              (boolSubNormalize_nonzero hbool) hjump rdBool
            exact (emptyRevert v (by simp only [poolManagerBlocks.poolManager_block_8370_taken_stack]; simp) rdRevert).reEquivDecodingFailed hcode hd
              (decodeCalldata_addr_bool_none_noncanon_bool hlen hhi hcanon
                (fun h => hbool (Or.inl h)) (fun h => hbool (Or.inr h)))
        · exact (decodeAddress4Reverts v (by simp) hcanon rdAddr).reEquivDecodingFailed hcode hd
            (decodeCalldata_addr_bool_none_noncanon_addr hlen hhi hcanon)
      · have hguard := viaIRStaticLenCheckHuge (words := 2) (Nat.le_of_not_gt hhi) hsize (by decide)
        have rdRevert := poolManagerBlocks.poolManager_block_8321_taken (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
        exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
          (decodeCalldata_addr_bool_none_huge (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 2) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have rdRevert := poolManagerBlocks.poolManager_block_8321_taken (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) hjump rdSize
      exact (emptyRevert v (by simp) rdRevert).reEquivDecodingFailed hcode hd
        (decodeCalldata_addr_bool_none_short hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_8315_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

/-- `setOperator(address,bool)`: the theorem consumed by the dispatcher. -/
theorem poolManagerSetOperatorBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 16)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) :=
  poolManagerSetOperatorBodyCore v hcode hsize hsel

end Benchmarks.UniswapV4PoolManager
