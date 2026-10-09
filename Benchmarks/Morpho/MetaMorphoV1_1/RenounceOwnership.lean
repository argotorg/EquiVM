import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.Ownership
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_036
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-!
# MetaMorphoV1_1 `renounceOwnership()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 7103; reach lemma `metaMorphoV1_1ReachRenounceOwnershipBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

theorem renounceOwnershipBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source) :
    ExecTransitionBody config contract evm locals renounceOwnershipTransition.body
      (.returned
        { adminFrame evm locals (immStore v) with
          locals := (adminFrame evm locals (immStore v)).locals.insert "__c1" .unit }
        (ownershipState evm ⟨0⟩) none) (immStore v) := by
  apply ExecFuncBody.execBlockOK
  apply (adminPrefix evm locals (immStore v) _ hwv hhi howner).run
  exact ExecBlock.consNormal
    (ownershipCall evm _ (immStore v) ⟨0⟩ "__c1" _ (by decide)
      (evalAddressLiteral _ _ _ (AccountAddress.ofNat 0))) ExecBlock.nil

theorem renounceOwnershipBodyStatic (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm locals renounceOwnershipTransition.body
      .staticViolation (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  apply (adminPrefix evm locals (immStore v) _ hwv hhi howner).run
  exact ExecBlock.consStatic
    (ownershipCallStatic evm _ (immStore v) ⟨0⟩ "__c1" _ hperm
      (evalAddressLiteral _ _ _ (AccountAddress.ofNat 0)))

set_option maxRecDepth 2000 in
theorem renounceOwnershipReachOwner {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨7103⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨12917⟩ (⟨7127⟩ :: R)
      mem aw rdata σ k' C' := by
  have rd7109 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7103_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd7120 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7109_fallthrough
    (immWords := wordsOf (immStore v)) hstack (calldataLengthCheckOk hsz hhi hsize) rd7109
  have rd12917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7120
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd7120
  exact ⟨_, _, rd12917⟩

set_option maxRecDepth 2000 in
theorem renounceOwnershipStoreReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024) (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨7127⟩ R mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 (ownershipAccounts I σ ⟨0⟩) ByteArray.empty := by
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7127
    (immWords := wordsOf (immStore v)) hstack hperm rd
  have hclear : UInt256.land (UInt256.lnot solcAddrMask) (codeOwnerStorageWord I σ ⟨9⟩) =
      setAddressOffset0Word (codeOwnerStorageWord I σ ⟨9⟩) ⟨0⟩ := by
    rw [setAddressOffset0Word_zero, u256_land_comm]
  change RDret _ _ _ (sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ ⟨9⟩
      (UInt256.land (UInt256.lnot solcAddrMask) (codeOwnerStorageWord I σ ⟨9⟩))) ⟨8⟩
    (UInt256.land (codeOwnerStorageWord I
      (sstoreAccountMap I.codeOwner σ ⟨9⟩
        (UInt256.land (UInt256.lnot solcAddrMask) (codeOwnerStorageWord I σ ⟨9⟩))) ⟨8⟩)
      (UInt256.lnot solcAddrMask))) _ at hret
  rw [hclear, ← setAddressOffset0Word_zero] at hret
  exact hret

theorem renounceOwnershipStoreWf (v : MetaMorphoV1_1Immutables) :
    clearAddressStoreWf (deployedRuntime v) ⟨7128⟩ ⟨9⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7128⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨9⟩, 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7130⟩ : UInt256), UInt8.ofNat 128, .DUP1, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7131⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7132⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨1⟩, 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7134⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨1⟩, 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7136⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨160⟩, 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7138⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7139⟩ : UInt256), UInt8.ofNat 3, .SUB, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7140⟩ : UInt256), UInt8.ofNat 25, .NOT, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7141⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7142⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7143⟩ : UInt256), UInt8.ofNat 22, .AND, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7144⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7145⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7146⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)

set_option maxRecDepth 2000 in
theorem renounceOwnershipStoreStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024) (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨7127⟩ R mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  have rd7128 := rd.jumpdest (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨7127⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)) (by evm_ov)
  exact clearAddressStoreStatic hstack hperm (renounceOwnershipStoreWf v) rd7128

set_option maxRecDepth 2000 in
theorem renounceOwnershipRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨7103⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7103_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem renounceOwnershipRevertHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hhi : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨7103⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd7109 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7103_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_7109_taken
    (immWords := wordsOf (immStore v))
    hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩
      rw [calldataLengthCheckHuge hhi hsize]
      decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd7109
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in
/-- `renounceOwnership()`: the theorem `Correct.lean` routes selector 32 to. -/
theorem metaMorphoV1_1RenounceOwnershipBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 32)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 32) rfl hsel
  have hd : dispatchMsg contract I.calldata = some renounceOwnershipTransition := by
    apply metaMorphoV1_1Dispatch_renounceOwnership <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (renounceOwnershipTransition.params.map Param.name)
      (transitionSignature renounceOwnershipTransition).paramTypes I.calldata = some ∅ := by
    exact decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachRenounceOwnershipBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · obtain ⟨_, _, rd12917⟩ := renounceOwnershipReachOwner v (by simp) hwv hsz hhi hsize rd
      by_cases howner : AccountAddress.ofNat
          (UInt256.land (codeOwnerStorageWord I σ ⟨8⟩) solcAddrMask).toNat = I.source
      · obtain ⟨_, _, rd7127⟩ := checkOwnerReturn v (by simp) howner
          (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd12917
        by_cases hperm : I.perm = true
        · exact (renounceOwnershipStoreReturn v (by simp) hperm rd7127).reEquivExecutionGen
            hcode hd hdec (renounceOwnershipBodyReturns v _ ∅ hwv hhi howner)
            (ownershipState_accounts (initState σ σ₀ (Sat256.ofUInt256 g) A I) _).symm
            voidReturnEquiv
        · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
          exact (renounceOwnershipStoreStatic v (by simp) hp rd7127).reEquivStaticHalt
            hcode hd hdec (renounceOwnershipBodyStatic v _ ∅ hwv hhi howner hp)
      · exact (checkOwnerRevert v (by simp) howner rd12917).reEquivExecutionRevert
          hcode hd hdec (adminBodyRevertsOwner _ _ (immStore v) _ hwv hhi howner)
    · exact (renounceOwnershipRevertHuge v (by simp) hwv (by omega) hsize rd).reEquivExecutionRevert
        hcode hd hdec
        (bodyReverts_calldataBound "__calldata" (2 ^ 255 + 4) hwv (Nat.le_of_not_gt hhi))
  · exact (renounceOwnershipRevertNonPayable v (by simp) hwv rd).reEquivExecutionRevert
      hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
