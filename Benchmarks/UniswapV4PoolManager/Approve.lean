import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.MappingMemory
import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_027
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_026

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 2000000

def approveSlot (evm : EVM.State) (spender id : UInt256) : UInt256 :=
  mappingSlotWord id (mappingSlotWord spender (mappingSlotWord (accountWord evm.executionEnv.source) ⟨5⟩))

def approvePost (evm : EVM.State) (spender id amount : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (approveSlot evm spender id) amount

theorem approveAssign (evm : EVM.State) (locals imms : Store) (spender id amount : UInt256)
    (hcanon : spender.toNat < EVM.addressModulus)
    (hsp : locals.get? "spender" = some (.address (AccountAddress.ofNat spender.toNat)))
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbase : locals.get? "allowance" = none) :
    assignStorageRef? config (calldataFrame contract locals imms evm) evm .storage
      {base := "allowance", steps := [.mindex (.env .caller), .mindex (.var "spender"), .mindex (.var "id")]}
      (.int (Int.ofNat amount.toNat)) =
      .ok (calldataFrame contract locals imms evm, approvePost evm spender id amount) := by
  apply allowanceWrite (accountWord evm.executionEnv.source) spender id amount rfl
    (accountWord_canonical _) hcanon
  · exact (store_get_ne locals _ (by decide : ("__calldata" == "allowance") = false)).trans hbase
  · rw [accountWord_address]
    simp only [evalExpr?, envValue, pure]
  · exact evalLocalValue ((store_get_ne locals _ (by decide : ("__calldata" == "spender") = false)).trans hsp)
  · exact evalLocalValue ((store_get_ne locals _ (by decide : ("__calldata" == "id") = false)).trans hid)

theorem approveBodyReturns (evm : EVM.State) (locals imms : Store) (spender id amount : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hcanon : spender.toNat < EVM.addressModulus)
    (hsp : locals.get? "spender" = some (.address (AccountAddress.ofNat spender.toNat)))
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hamt : locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hbase : locals.get? "allowance" = none) :
    ExecTransitionBody config contract evm locals approveTransition.body
      (.returned (calldataFrame contract locals imms evm) (approvePost evm spender id amount)
        (some [.bool true])) imms := by
  have ha := (store_get_ne locals (.bytes evm.executionEnv.calldata) (by decide : ("__calldata" == "amount") = false)).trans hamt
  have hs := (store_get_ne locals (.bytes evm.executionEnv.calldata) (by decide : ("__calldata" == "spender") = false)).trans hsp
  have hi := (store_get_ne locals (.bytes evm.executionEnv.calldata) (by decide : ("__calldata" == "id") = false)).trans hid
  apply ExecFuncBody.execBlockRet
  apply nonpayableCalldataBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.assign (evalLocalValue ha)
    (approveAssign evm locals imms spender id amount hcanon hsp hid hbase)) ?_
  refine ExecBlock.consNormal (ExecStmt.emit
    (vals := [.address evm.executionEnv.source, .address (AccountAddress.ofNat spender.toNat),
      .int (Int.ofNat id.toNat), .int (Int.ofNat amount.toNat)]) ?_) ?_
  · simp only [evalExprs?, evalExpr?, calldataFrame, ha, hs, hi, EvalResult.ofOption,
      bind, EvalResult.bind, pure, envValue, approvePost, storageStore_executionEnv]
  · exact ExecBlock.consReturn (ExecStmt.return (by simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]))

theorem approveBodyStatic (evm : EVM.State) (locals imms : Store) (spender id amount : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hcanon : spender.toNat < EVM.addressModulus)
    (hsp : locals.get? "spender" = some (.address (AccountAddress.ofNat spender.toNat)))
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hamt : locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hbase : locals.get? "allowance" = none) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm locals approveTransition.body .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply nonpayableCalldataBlock hwv hhi
  exact ExecBlock.consStatic (ExecStmt.assignStatic
    (evalLocalValue ((store_get_ne locals _ (by decide : ("__calldata" == "amount") = false)).trans hamt))
    (approveAssign evm locals imms spender id amount hcanon hsp hid hbase) hperm)


theorem approveTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {spender id amount : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 7 ≤ 1024)
    (hc : spender.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (h : RD (deployedRuntime v) I g s0 ⟨9496⟩ (amount :: id :: spender :: solcAddrMask :: R)
      entryMemory aw rdata σ k C) :
    RDret (deployedRuntime v) g s0
      (sstoreAccountMap I.codeOwner σ
        (mappingSlotWord id (mappingSlotWord spender (mappingSlotWord (accountWord I.source) ⟨5⟩))) amount)
      (UInt256.toByteArray ⟨1⟩) := by
  have hret := poolManagerBlocks.poolManager_block_9496 hstack hperm h
  let m1 := twoWordHashMem (accountWord I.source) ⟨5⟩ entryMemory
  let m2 := twoWordHashMem (UInt256.land spender solcAddrMask) (keccakWord ⟨0⟩ ⟨64⟩ m1) m1
  let m3 := twoWordHashMem id (keccakWord ⟨0⟩ ⟨64⟩ m2) m2
  let m4 := amount.toByteArray.write 0 m3 (memLoad ⟨64⟩ m3).toNat 32
  change RDret (deployedRuntime v) g s0
    (sstoreAccountMap I.codeOwner σ (keccakWord ⟨0⟩ ⟨64⟩ m3) amount)
    (((⟨1⟩ : UInt256).toByteArray.write 0 m4 (memLoad ⟨64⟩ m4).toNat 32).readWithPadding
      (memLoad ⟨64⟩ m4).toNat 32) at hret
  have hs1 : m1.size = 96 := twoWordHashMem_size_96 _ _ entryMemory_size
  have hs2 : m2.size = 96 := twoWordHashMem_size_96 _ _ hs1
  have hs3 : m3.size = 96 := twoWordHashMem_size_96 _ _ hs2
  have hp2 : memLoad ⟨64⟩ m2 = ⟨160⟩ :=
    (mappingMemory_load64 _ _ hs1).trans (twoWordHashMem_load64 _ _)
  have hp3 : memLoad ⟨64⟩ m3 = ⟨160⟩ := (mappingMemory_load64 _ _ hs2).trans hp2
  have hslot1 : keccakWord ⟨0⟩ ⟨64⟩ m1 = mappingSlotWord (accountWord I.source) ⟨5⟩ :=
    twoWordHashMem_slot _ _
  have hslot2 : keccakWord ⟨0⟩ ⟨64⟩ m2 = mappingSlotWord spender (mappingSlotWord (accountWord I.source) ⟨5⟩) := by
    change keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem _ _ m1) = _
    rw [mappingMemory_slot _ _ hs1, solcAddrMask_clean hc, hslot1]
  have hslot3 : keccakWord ⟨0⟩ ⟨64⟩ m3 =
      mappingSlotWord id (mappingSlotWord spender (mappingSlotWord (accountWord I.source) ⟨5⟩)) :=
    (mappingMemory_slot _ _ hs2).trans (congrArg (mappingSlotWord id) hslot2)
  have hout := eventWordThenReturn hp3 (by rw [hs3]) (by decide)
    (by rw [hs3]; native_decide) amount ⟨1⟩
  exact (congrArg₂ (fun slot bytes => RDret (deployedRuntime v) g s0
    (sstoreAccountMap I.codeOwner σ slot amount) bytes) hslot3 hout).mp hret

open poolManagerBlocks in
theorem approveStaticTrace {immWords : String → UInt256} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD (Benchmarks.UniswapV4PoolManager.immutableLayout.runtime Benchmarks.UniswapV4PoolManager.poolManagerBytecode immWords) ee g s0 (UInt256.ofNat 9496) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata σ k C)
    : RDstatic (immutableLayout.runtime poolManagerBytecode immWords) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9496⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap2 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9497⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.swap3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9498⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.swap1 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9499⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9500⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.caller (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9501⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9502⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := RD.genMstore r7 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9503⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 5) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9504⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 5), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9506⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMstore r10 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9508⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9509⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9511⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := RD.genKeccak256 r13 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9512⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9513⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9514⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.and (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9515⟩ : UInt256), UInt8.ofNat 22, .AND, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9516⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := RD.genMstore r18 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9517⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9518⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := RD.genMstore r20 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9520⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9521⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9523⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := RD.genKeccak256 r23 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9524⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.dup5 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9525⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9526⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r27 := RD.genMstore r26 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9527⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9528⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r29 := RD.genMstore r28 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9530⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.dup3 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9531⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9532⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r32 := r31.push0 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9534⟩ : UInt256), UInt8.ofNat 95, .PUSH0, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r33 := RD.genKeccak256 r32 (by immutable_decode(Benchmarks.UniswapV4PoolManager.immutableLayout, Benchmarks.UniswapV4PoolManager.poolManagerBytecode, immWords, (⟨9535⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r33 hperm
    (by immutable_decode(immutableLayout, poolManagerBytecode, immWords, (⟨9536⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, immutableLayout_inBounds, immutableTemplate_size64))
    (by evm_ov)


theorem poolManagerApproveBodyCore {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (poolManagerSelBytes 13)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 13) rfl hsel
  have hd : dispatchMsg contract I.calldata = some approveTransition := by
    apply poolManagerDispatch_approve <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachApproveBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨9461⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps v]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_9461_fallthrough (by simp) hwv rdEntry
    have hjumpDec : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 11653) = true := by
      rw [deployedRuntime_jumps v]; jump_dest
    have rdDecode := poolManagerBlocks.poolManager_block_9467 (by simp) hjumpDec rdSize
    by_cases hlen : 100 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < calldataLimit
      · by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hjumpReturn : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 9496) = true := by
            rw [deployedRuntime_jumps v]; jump_dest
          obtain ⟨k', C', rdReturn⟩ := decodeAddressUintUint v (by simp) hlen hhi hsize hcanon hjumpReturn rdDecode
          let args := (((∅ : Store).insert "spender"
            (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "id"
            (.int (Int.ofNat (calldataWord I.calldata 36).toNat))).insert "amount"
            (.int (Int.ofNat (calldataWord I.calldata 68).toNat))
          have hdec : decodeCalldataWithMode config.abiDecodeMode
              (approveTransition.params.map Param.name)
              (transitionSignature approveTransition).paramTypes I.calldata = some args :=
            decodeCalldata_address_uint256_uint256_ok hlen hhi hcanon
          have hsp : args.get? "spender" = some (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) :=
            (store_get_ne _ _ (by decide : ("amount" == "spender") = false)).trans
              ((store_get_ne _ _ (by decide : ("id" == "spender") = false)).trans (store_get_self _ _ _))
          have hid : args.get? "id" = some (.int (Int.ofNat (calldataWord I.calldata 36).toNat)) :=
            (store_get_ne _ _ (by decide : ("amount" == "id") = false)).trans (store_get_self _ _ _)
          have hbase : args.get? "allowance" = none :=
            (store_get_ne _ _ (by decide : ("amount" == "allowance") = false)).trans
              ((store_get_ne _ _ (by decide : ("id" == "allowance") = false)).trans
                ((store_get_ne _ _ (by decide : ("spender" == "allowance") = false)).trans (store_get_empty _)))
          cases hperm : I.perm with
          | false =>
            have hstatic := approveStaticTrace (by simp) hperm rdReturn
            exact hstatic.reEquivStaticHalt hcode hd hdec
              (approveBodyStatic (initState σ σ₀ (Sat256.ofUInt256 g) A I) args (immStore v)
                _ _ _ hwv hhi hcanon hsp hid (store_get_self _ _ _) hbase hperm)
          | true =>
            have hret := approveTrace v (by simp) hcanon hperm rdReturn
            have hbody := approveBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I) args
              (immStore v) _ _ _ hwv hhi hcanon hsp hid (store_get_self _ _ _) hbase
            exact hret.reEquivExecutionGen hcode hd hdec hbody
              (storageStore_accountMap (initState σ σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner
                (approveSlot (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) (calldataWord I.calldata 36))
                (calldataWord I.calldata 68)).symm
              (returnEquiv_of_encode (boolReturnEncoding true))
        · exact (decodeAddressUintUintAddressReverts v (by simp) hlen hhi hsize hcanon rdDecode).reEquivDecodingFailed hcode hd
            (decodeCalldata_address_uint256_uint256_none_noncanon0 hlen hhi hcanon)
      · have hguard := viaIRStaticLenCheckHuge (words := 3) (Nat.le_of_not_gt hhi) hsize (by decide)
        have hrev := decodeAddressUintUintLengthReverts v (by simp)
          (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) rdDecode
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_address_uint256_uint256_none_huge (Nat.le_of_not_gt hhi))
    · have hguard := viaIRStaticLenCheckShort (words := 3) hsz (Nat.lt_of_not_ge hlen) (by decide) hsize
      have hrev := decodeAddressUintUintLengthReverts v (by simp)
        (fun hz => (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hguard.symm.trans hz)) rdDecode
      exact hrev.reEquivDecodingFailed hcode hd
        (decodeCalldata_address_uint256_uint256_none_short hsz (Nat.lt_of_not_ge hlen))
  · have rdRevert := poolManagerBlocks.poolManager_block_9461_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

/-- `approve(address,uint256,uint256)`: the theorem consumed by the dispatcher. -/
theorem poolManagerApproveBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I)
    (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 13)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) :=
  poolManagerApproveBodyCore v hcode hsize hsel

end Benchmarks.UniswapV4PoolManager
