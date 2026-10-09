import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl
import Benchmarks.Morpho.MetaMorphoV1_1.Mutation
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_010

/-!
# MetaMorphoV1_1 `setCurator(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1034; reach lemma `metaMorphoV1_1ReachSetCuratorBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

def setCuratorState (evm : EVM.State) (w : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨10⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩) w)

theorem setCuratorComparison (evm : EVM.State) (locals imms : Store) (w : UInt256)
    (hbase : locals.get? "curator" = none)
    (hget : locals.get? "newCurator" = some (.address (AccountAddress.ofNat w.toNat))) :
    evalExpr? config (adminFrame evm locals imms) evm
      (.binary .ne (.var "newCurator") (.storage ⟨"curator", []⟩)) =
      .ok (.bool (decide (AccountAddress.ofNat w.toNat ≠ AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩)
          solcAddrMask).toNat))) := by
  apply evalExpr_addressNe
  · rw [evalExpr?]
    rw [adminFrame_get_ne _ _ _ _ (by decide) (by decide), hget]
    rfl
  · exact evalStorage_curator evm _ imms
      ((adminFrame_get_ne evm locals imms "curator" (by decide) (by decide)).trans hbase)

theorem setCuratorPrefix (evm : EVM.State) (locals imms : Store) (w : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hbase : locals.get? "curator" = none)
    (hget : locals.get? "newCurator" = some (.address (AccountAddress.ofNat w.toNat)))
    (hne : AccountAddress.ofNat w.toNat ≠ AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩)
        solcAddrMask).toNat) :
    ABlock config evm { contract := contract, locals := locals, immutables := imms }
      setCuratorTransition.body (adminFrame evm locals imms)
      [.assign .storage ⟨"curator", []⟩ (.var "newCurator"),
        .emit "SetCurator" [.var "newCurator"]] := by
  apply (adminPrefix evm locals imms _ hwv hhi howner).requireStep
  rw [setCuratorComparison evm locals imms w hbase hget]
  simp [hne]

theorem setCuratorAssign (evm : EVM.State) (locals imms : Store) (w : UInt256)
    (hbase : locals.get? "curator" = none)
    (hget : locals.get? "newCurator" = some (.address (AccountAddress.ofNat w.toNat)))
    (hcanon : w.toNat < EVM.addressModulus) :
    ExecStmt config (adminFrame evm locals imms) evm
      (.assign .storage ⟨"curator", []⟩ (.var "newCurator"))
      (.ok (adminFrame evm locals imms) (setCuratorState evm w)) := by
  apply ExecStmt.assign
  · rw [evalExpr?, adminFrame_get_ne _ _ _ _ (by decide) (by decide), hget]
    rfl
  · exact assignStorage_curator evm _ imms w
      ((adminFrame_get_ne evm locals imms "curator" (by decide) (by decide)).trans hbase) hcanon

theorem setCuratorBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (w : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hbase : locals.get? "curator" = none)
    (hget : locals.get? "newCurator" = some (.address (AccountAddress.ofNat w.toNat)))
    (hcanon : w.toNat < EVM.addressModulus)
    (hne : AccountAddress.ofNat w.toNat ≠ AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩)
        solcAddrMask).toNat) :
    ExecTransitionBody config contract evm locals setCuratorTransition.body
      (.returned (adminFrame evm locals (immStore v)) (setCuratorState evm w) none)
      (immStore v) := by
  apply ExecFuncBody.execBlockOK
  apply (setCuratorPrefix evm locals (immStore v) w hwv hhi howner hbase hget hne).run
  refine ExecBlock.consNormal (setCuratorAssign evm locals (immStore v) w hbase hget hcanon) ?_
  apply (ABlock.start.emitStep (vals := [.address (AccountAddress.ofNat w.toNat)]) ?_).run
  · exact ExecBlock.nil
  · simp only [evalExprs?, evalExpr?,
      adminFrame_get_ne evm locals (immStore v) "newCurator" (by decide) (by decide), hget,
      EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem setCuratorBodyStatic (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (w : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hbase : locals.get? "curator" = none)
    (hget : locals.get? "newCurator" = some (.address (AccountAddress.ofNat w.toNat)))
    (hcanon : w.toNat < EVM.addressModulus)
    (hne : AccountAddress.ofNat w.toNat ≠ AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩)
        solcAddrMask).toNat) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm locals setCuratorTransition.body
      .staticViolation (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  apply (setCuratorPrefix evm locals (immStore v) w hwv hhi howner hbase hget hne).run
  exact ExecBlock.consStatic
    (execStmt_assign_static (setCuratorAssign evm locals (immStore v) w hbase hget hcanon) hperm)

theorem setCuratorBodyRevertsAlreadySet (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (w : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hbase : locals.get? "curator" = none)
    (hget : locals.get? "newCurator" = some (.address (AccountAddress.ofNat w.toNat)))
    (heq : AccountAddress.ofNat w.toNat = AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩)
        solcAddrMask).toNat) :
    ExecTransitionBody config contract evm locals setCuratorTransition.body
      .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  exact (adminPrefix evm locals (immStore v) _ hwv hhi howner).requireRevert (by
    simp only [setCuratorComparison evm locals (immStore v) w hbase hget, heq,
      ne_eq, not_true_eq_false, decide_false])

set_option maxRecDepth 2000 in
theorem setCuratorReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨1034⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨11163⟩ (⟨1059⟩ :: R)
      mem aw rdata σ k' C' := by
  have rd1040 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1034_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd1052 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1040_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_32 hsz hhi hsize) rd1040
  have rd11163 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1052
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd1052
  exact ⟨_, _, rd11163⟩

set_option maxRecDepth 2000 in
theorem setCuratorReachOwner {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨11163⟩ (⟨1059⟩ :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨12917⟩
      (⟨1067⟩ :: calldataWord I.calldata 4 :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, rd1059⟩ := decodeAddressAt4 v hstack hcanon
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  have rd12917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1059
    (immWords := wordsOf (immStore v)) (by simpa using (show R.length + 3 ≤ 1024 by omega))
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd1059
  exact ⟨_, _, rd12917⟩

set_option maxRecDepth 2000 in
theorem setCuratorReachStore {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {w : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hcanon : w.toNat < EVM.addressModulus)
    (hne : w ≠ UInt256.land (codeOwnerStorageWord I σ ⟨10⟩) solcAddrMask)
    (rd : RD (deployedRuntime v) I g s0 ⟨1067⟩ (w :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨1091⟩
      (codeOwnerStorageWord I σ ⟨10⟩ :: w :: R) mem aw rdata σ k' C' := by
  obtain ⟨k', C', rd1091⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1067_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.eq (UInt256.land solcAddrMask w)
        (UInt256.land (codeOwnerStorageWord I σ ⟨10⟩) solcAddrMask) = ⟨0⟩
      rw [solcAddrMask_clean_left hcanon]
      exact u256_eq_of_ne hne) rd
  exact ⟨k', C', solcAddrMask_clean_left hcanon ▸ rd1091⟩

set_option maxRecDepth 2000 in
theorem setCuratorStoreReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {old w : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hcanon : w.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨1091⟩ (old :: w :: R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0
      (sstoreAccountMap I.codeOwner σ ⟨10⟩ (setAddressOffset0Word old w)) ByteArray.empty := by
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1091
    (immWords := wordsOf (immStore v)) hstack hperm rd
  have hword : UInt256.lor w (UInt256.land (UInt256.lnot solcAddrMask) old) =
      setAddressOffset0Word old w := by
    simpa only [solcAddrMask_clean hcanon] using setAddressOffset0Word_bytecode old w
  exact hword ▸ hret

set_option maxRecDepth 2000 in
theorem setCuratorRevertAlreadySet {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {w : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hcanon : w.toNat < EVM.addressModulus)
    (heq : w = UInt256.land (codeOwnerStorageWord I σ ⟨10⟩) solcAddrMask)
    (rd : RD (deployedRuntime v) I g s0 ⟨1067⟩ (w :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, rd1143⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1067_taken
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.eq (UInt256.land solcAddrMask w)
        (UInt256.land (codeOwnerStorageWord I σ ⟨10⟩) solcAddrMask) ≠ ⟨0⟩
      rw [solcAddrMask_clean_left hcanon, heq]
      simp only [UInt256.eq]
      decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_1143
    (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_1067_taken_stack,
        List.length_cons]; omega) rd1143

set_option maxRecDepth 2000 in
theorem setCuratorRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨1034⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1034_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem setCuratorRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨1034⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd1040 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1034_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1040_taken
    (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd1040
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

theorem setCuratorStoreWf (v : MetaMorphoV1_1Immutables) :
    packedAddressStoreWf (deployedRuntime v) ⟨1091⟩ ⟨10⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1091⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨1⟩, 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1093⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨1⟩, 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1095⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨160⟩, 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1097⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1098⟩ : UInt256), UInt8.ofNat 3, .SUB, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1099⟩ : UInt256), UInt8.ofNat 25, .NOT, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1100⟩ : UInt256), UInt8.ofNat 22, .AND, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1101⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1102⟩ : UInt256), UInt8.ofNat 23, .OR, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1103⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨10⟩, 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨1105⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)

set_option maxRecDepth 2000 in
/-- `setCurator(address)`: the theorem `Correct.lean` routes selector 72 to. -/
theorem metaMorphoV1_1SetCuratorBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 72)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 72) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setCuratorTransition := by
    apply metaMorphoV1_1Dispatch_setCurator <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachSetCuratorBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · obtain ⟨_, _, rd11163⟩ := setCuratorReachDecoder v (by simp) hwv hlen hhi hsize rd
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hdec := decodeCalldata_address_ok (x := "newCurator") hlen hhi hcanon
          obtain ⟨_, _, rd12917⟩ := setCuratorReachOwner v (by simp) hcanon rd11163
          by_cases howner : AccountAddress.ofNat
              (UInt256.land (codeOwnerStorageWord I σ ⟨8⟩) solcAddrMask).toNat = I.source
          · obtain ⟨_, _, rd1067⟩ := checkOwnerReturn v (by simp) howner
              (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd12917
            by_cases heq : calldataWord I.calldata 4 =
                UInt256.land (codeOwnerStorageWord I σ ⟨10⟩) solcAddrMask
            · exact (setCuratorRevertAlreadySet v (by simp) hcanon
                heq rd1067).reEquivExecutionRevert
                hcode hd hdec
                  (setCuratorBodyRevertsAlreadySet v _ _ _ hwv hhi howner
                    (by simp) (store_get_self _ _ _)
                    ((canonicalAddress_eq_masked _ _ hcanon).mpr heq))
            · have hne := (canonicalAddress_eq_masked _ _ hcanon).not.mpr heq
              obtain ⟨_, _, rd1091⟩ := setCuratorReachStore v (by simp) hcanon heq rd1067
              by_cases hperm : I.perm = true
              · exact (setCuratorStoreReturn v (by simp) hcanon hperm rd1091).reEquivExecutionGen
                  hcode hd hdec
                    (setCuratorBodyReturns v _ _ _ hwv hhi howner
                      (by simp) (store_get_self _ _ _) hcanon hne)
                    (storageStore_accountMap (initState σ σ₀ (Sat256.ofUInt256 g) A I) _ _ _).symm
                    voidReturnEquiv
              · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
                have hstatic := packedAddressStoreStatic (by simp) hp (setCuratorStoreWf v) rd1091
                exact hstatic.reEquivStaticHalt hcode hd hdec
                  (setCuratorBodyStatic v _ _ _ hwv hhi howner
                    (by simp) (store_get_self _ _ _) hcanon hne hp)
          · exact (checkOwnerRevert v (by simp) howner rd12917).reEquivExecutionRevert
              hcode hd hdec (adminBodyRevertsOwner _ _ (immStore v) _ hwv hhi howner)
        · exact (decodeAddressAt4Revert v (by simp) hcanon rd11163).reEquivDecodingFailed
            hcode hd (decodeCalldata_address_none_noncanon hlen hhi hcanon)
      · have hrev := setCuratorRevertLength v (by simp) hwv (by
          rw [calldataNot3_eq_sub hsz hsize,
            solcDecodeLenCheckHuge_4_32 (Nat.le_of_not_gt hhi) hsize]
          decide) rd
        exact hrev.reEquivDecodingFailed hcode hd
          (decodeCalldata_address_none_huge (Nat.le_of_not_gt hhi))
    · have hrev := setCuratorRevertLength v (by simp) hwv (by
        rw [calldataNot3_eq_sub hsz hsize,
          solcDecodeLenCheckShort_4_32 hsz (by omega) hsize]
        decide) rd
      exact hrev.reEquivDecodingFailed hcode hd (decodeCalldata_address_none_short hsz (by omega))
  · exact dispatchedRevert hcode hd (setCuratorRevertNonPayable v (by simp) hwv rd)
      (fun _ ↦ bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
