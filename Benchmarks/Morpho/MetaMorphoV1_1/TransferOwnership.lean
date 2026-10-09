import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl
import Benchmarks.Morpho.MetaMorphoV1_1.Mutation
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-!
# MetaMorphoV1_1 `transferOwnership(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 921; reach lemma `metaMorphoV1_1ReachTransferOwnershipBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

def transferOwnershipState (evm : EVM.State) (w : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨9⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩) w)

def transferOwnershipFrame (evm : EVM.State) (locals imms : Store) (w : UInt256) : Frame :=
  { adminFrame evm locals imms with
    locals := (adminFrame evm locals imms).locals.insert "__c1"
      (.address (ownerAddress (transferOwnershipState evm w))) }

theorem transferOwnershipAssign (evm : EVM.State) (locals imms : Store) (w : UInt256)
    (hbase : locals.get? "_pendingOwner" = none)
    (hget : locals.get? "newOwner" = some (.address (AccountAddress.ofNat w.toNat)))
    (hcanon : w.toNat < EVM.addressModulus) :
    ExecStmt config (adminFrame evm locals imms) evm
      (.assign .storage ⟨"_pendingOwner", []⟩ (.var "newOwner"))
      (.ok (adminFrame evm locals imms) (transferOwnershipState evm w)) := by
  apply ExecStmt.assign
  · rw [evalExpr?, adminFrame_get_ne _ _ _ _ (by decide) (by decide), hget]
    rfl
  · exact assignStorage_pendingOwner evm _ imms w
      ((adminFrame_get_ne evm locals imms "_pendingOwner" (by decide) (by decide)).trans hbase)
      hcanon

theorem transferOwnershipBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (w : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hbase : locals.get? "_pendingOwner" = none)
    (hget : locals.get? "newOwner" = some (.address (AccountAddress.ofNat w.toNat)))
    (hcanon : w.toNat < EVM.addressModulus) :
    ExecTransitionBody config contract evm locals transferOwnershipTransition.body
      (.returned (transferOwnershipFrame evm locals (immStore v) w)
        (transferOwnershipState evm w) none) (immStore v) := by
  apply ExecFuncBody.execBlockOK
  apply (adminPrefix evm locals (immStore v) _ hwv hhi howner).run
  refine ExecBlock.consNormal
    (transferOwnershipAssign evm locals (immStore v) w hbase hget hcanon) ?_
  refine ExecBlock.consNormal
    (internalCallReturnExpr (retTy := [.elem .address]) (expr := .storage ⟨"_owner", []⟩)
      (by rfl) (evalStorage_owner (transferOwnershipState evm w) ∅ _ (by simp))) ?_
  apply (ABlock.start.emitStep (vals :=
    [.address (ownerAddress (transferOwnershipState evm w)),
      .address (AccountAddress.ofNat w.toNat)]) ?_).run
  · exact ExecBlock.nil
  · simp only [evalExprs?, evalExpr?,
      store_get_ne _ _ (show ("__c1" == "newOwner") = false from by decide),
      store_get_self, adminFrame_get_ne evm locals (immStore v) "newOwner"
        (by decide) (by decide), hget, EvalResult.ofOption, EvalResult.bind, bind, pure]
    rfl

theorem transferOwnershipBodyStatic (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (w : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hbase : locals.get? "_pendingOwner" = none)
    (hget : locals.get? "newOwner" = some (.address (AccountAddress.ofNat w.toNat)))
    (hcanon : w.toNat < EVM.addressModulus) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm locals transferOwnershipTransition.body
      .staticViolation (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  apply (adminPrefix evm locals (immStore v) _ hwv hhi howner).run
  exact ExecBlock.consStatic (execStmt_assign_static
    (transferOwnershipAssign evm locals (immStore v) w hbase hget hcanon) hperm)

set_option maxRecDepth 2000 in
theorem transferOwnershipReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨921⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨11163⟩ (⟨946⟩ :: R)
      mem aw rdata σ k' C' := by
  have rd927 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_921_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd939 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_927_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_32 hsz hhi hsize) rd927
  have rd11163 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_939
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd939
  exact ⟨_, _, rd11163⟩

set_option maxRecDepth 2000 in
theorem transferOwnershipReachOwner {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨11163⟩ (⟨946⟩ :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨12917⟩
      (⟨954⟩ :: calldataWord I.calldata 4 :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, rd946⟩ := decodeAddressAt4 v hstack hcanon
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  have rd12917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_946
    (immWords := wordsOf (immStore v)) (by simpa using (show R.length + 3 ≤ 1024 by omega))
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd946
  exact ⟨_, _, rd12917⟩

set_option maxRecDepth 2000 in
theorem transferOwnershipRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨921⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_921_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem transferOwnershipRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨921⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd927 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_921_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_927_taken
    (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd927
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in
theorem transferOwnershipStoreReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {w : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024) (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨954⟩ (w :: R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0
      (sstoreAccountMap I.codeOwner σ ⟨9⟩
        (setAddressOffset0Word (codeOwnerStorageWord I σ ⟨9⟩) w)) ByteArray.empty := by
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_954
    (immWords := wordsOf (immStore v)) hstack hperm rd
  have hword : UInt256.lor (UInt256.land solcAddrMask w)
      (UInt256.land (UInt256.lnot solcAddrMask) (codeOwnerStorageWord I σ ⟨9⟩)) =
      setAddressOffset0Word (codeOwnerStorageWord I σ ⟨9⟩) w := by
    rw [u256_land_comm solcAddrMask w]
    exact setAddressOffset0Word_bytecode _ _
  exact hword ▸ hret

set_option maxRecDepth 2000 in
theorem transferOwnershipStoreStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {w : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024) (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨954⟩ (w :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  let r0 := rd
  have r1 := r0.jumpdest (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨954⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 9) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨955⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 9), 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨957⟩ : UInt256), UInt8.ofNat 128, .DUP1, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨958⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨959⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨961⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨963⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨965⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨966⟩ : UInt256), UInt8.ofNat 3, .SUB, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.not (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨967⟩ : UInt256), UInt8.ofNat 25, .NOT, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨968⟩ : UInt256), UInt8.ofNat 22, .AND, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨969⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨971⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 160) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨973⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨975⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.sub (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨976⟩ : UInt256), UInt8.ofNat 3, .SUB, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨977⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.dup4 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨978⟩ : UInt256), UInt8.ofNat 131, .DUP4, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨979⟩ : UInt256), UInt8.ofNat 22, .AND, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨980⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.dup2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨981⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.or (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨982⟩ : UInt256), UInt8.ofNat 23, .OR, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨983⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.swap2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨984⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  exact r24.sstoreStatic hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨985⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)

set_option maxRecDepth 2000 in
/-- `transferOwnership(address)`: the theorem `Correct.lean` routes selector 74 to. -/
theorem metaMorphoV1_1TransferOwnershipBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 74)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 74) rfl hsel
  have hd : dispatchMsg contract I.calldata = some transferOwnershipTransition := by
    apply metaMorphoV1_1Dispatch_transferOwnership <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachTransferOwnershipBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · obtain ⟨_, _, rd11163⟩ := transferOwnershipReachDecoder v (by simp) hwv hlen hhi hsize rd
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hdec := decodeCalldata_address_ok (x := "newOwner") hlen hhi hcanon
          obtain ⟨_, _, rd12917⟩ := transferOwnershipReachOwner v (by simp) hcanon rd11163
          by_cases howner : AccountAddress.ofNat
              (UInt256.land (codeOwnerStorageWord I σ ⟨8⟩) solcAddrMask).toNat = I.source
          · obtain ⟨_, _, rd954⟩ := checkOwnerReturn v (by simp) howner
              (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd12917
            by_cases hperm : I.perm = true
            · exact (transferOwnershipStoreReturn v (by simp) hperm rd954).reEquivExecutionGen
                hcode hd hdec
                  (transferOwnershipBodyReturns v _ _ _ hwv hhi howner
                    (by simp) (store_get_self _ _ _) hcanon)
                  (storageStore_accountMap (initState σ σ₀ (Sat256.ofUInt256 g) A I) _ _ _).symm
                  voidReturnEquiv
            · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
              exact (transferOwnershipStoreStatic v (by simp) hp rd954).reEquivStaticHalt
                hcode hd hdec (transferOwnershipBodyStatic v _ _ _ hwv hhi howner
                  (by simp) (store_get_self _ _ _) hcanon hp)
          · exact (checkOwnerRevert v (by simp) howner rd12917).reEquivExecutionRevert
              hcode hd hdec (adminBodyRevertsOwner _ _ (immStore v) _ hwv hhi howner)
        · exact (decodeAddressAt4Revert v (by simp) hcanon rd11163).reEquivDecodingFailed
            hcode hd (decodeCalldata_address_none_noncanon hlen hhi hcanon)
      · have hrev := transferOwnershipRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_32 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_address_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := transferOwnershipRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_32 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd (decodeCalldata_address_none_short hsz (by omega))
  · exact dispatchedRevert hcode hd (transferOwnershipRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
