import Benchmarks.Morpho.MetaMorphoV1_1.Dispatch
import Benchmarks.Morpho.MetaMorphoV1_1.Ownership
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_030
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-!
# MetaMorphoV1_1 `acceptOwnership()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 5644; reach lemma `metaMorphoV1_1ReachAcceptOwnershipBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

def pendingOwnerAddress (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat (UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩) solcAddrMask).toNat

def acceptOwnershipFrame (evm : EVM.State) (locals imms : Store) : Frame :=
  { contract := contract
    locals := (((locals.insert "__calldata" (.bytes evm.executionEnv.calldata)).insert
      "sender" (.address evm.executionEnv.source)).insert "__c1"
      (.address (pendingOwnerAddress evm)))
    immutables := imms }

theorem acceptOwnershipPrefix (evm : EVM.State) (locals imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm { contract := contract, locals := locals, immutables := imms }
      acceptOwnershipTransition.body (acceptOwnershipFrame evm locals imms)
      [.require (.binary .eq (.var "__c1") (.var "sender")),
        .internalCall "_transferOwnership" [.var "sender"] "__c2"] := by
  constructor
  intro result htail
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  refine ExecBlock.consNormal
    (internalCallReturnExpr (retTy := [.elem .address]) (expr := .env .caller)
      (value := .address evm.executionEnv.source)
      (by rfl) (by simp only [evalExpr?, envValue, pure])) ?_
  exact ExecBlock.consNormal
    (internalCallReturnExpr (retTy := [.elem .address]) (expr := .storage ⟨"_pendingOwner", []⟩)
      (by rfl) (evalStorage_pendingOwner evm ∅ _ (by simp))) htail

theorem acceptOwnershipSender (evm : EVM.State) (locals imms : Store) :
    evalExpr? config (acceptOwnershipFrame evm locals imms) evm (.var "sender") =
      .ok (.address (AccountAddress.ofNat (EVM.word evm.executionEnv.source.val).toNat)) := by
  simp only [evalExpr?, acceptOwnershipFrame,
    store_get_ne _ _ (show ("__c1" == "sender") = false from by decide), store_get_self,
    EvalResult.ofOption, accountAddress_of_word_val]

theorem acceptOwnershipComparison (evm : EVM.State) (locals imms : Store) :
    evalExpr? config (acceptOwnershipFrame evm locals imms) evm
      (.binary .eq (.var "__c1") (.var "sender")) =
      .ok (.bool (decide (pendingOwnerAddress evm = evm.executionEnv.source))) := by
  apply evalExpr_addressEq
  · simp only [evalExpr?, acceptOwnershipFrame, store_get_self, EvalResult.ofOption]
  · simpa only [accountAddress_of_word_val] using acceptOwnershipSender evm locals imms

theorem acceptOwnershipBodyReturns (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : pendingOwnerAddress evm = evm.executionEnv.source) :
    ExecTransitionBody config contract evm locals acceptOwnershipTransition.body
      (.returned
        { acceptOwnershipFrame evm locals (immStore v) with
          locals := (acceptOwnershipFrame evm locals (immStore v)).locals.insert "__c2" .unit }
        (ownershipState evm (EVM.word evm.executionEnv.source.val)) none) (immStore v) := by
  apply ExecFuncBody.execBlockOK
  apply ((acceptOwnershipPrefix evm locals (immStore v) hwv hhi).requireStep (by
    simp only [acceptOwnershipComparison, howner, decide_true])).run
  exact ExecBlock.consNormal
    (ownershipCall evm _ (immStore v) _ "__c2" (.var "sender")
      (word_val_addr_canonical _) (acceptOwnershipSender evm locals (immStore v))) ExecBlock.nil

theorem acceptOwnershipBodyStatic (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : pendingOwnerAddress evm = evm.executionEnv.source)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm locals acceptOwnershipTransition.body
      .staticViolation (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  apply ((acceptOwnershipPrefix evm locals (immStore v) hwv hhi).requireStep (by
    simp only [acceptOwnershipComparison, howner, decide_true])).run
  exact ExecBlock.consStatic
    (ownershipCallStatic evm _ (immStore v) _ "__c2" (.var "sender") hperm
      (acceptOwnershipSender evm locals (immStore v)))

theorem acceptOwnershipBodyReverts (v : MetaMorphoV1_1Immutables)
    (evm : EVM.State) (locals : Store) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (howner : pendingOwnerAddress evm ≠ evm.executionEnv.source) :
    ExecTransitionBody config contract evm locals acceptOwnershipTransition.body
      .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  exact (acceptOwnershipPrefix evm locals (immStore v) hwv hhi).requireRevert (by
    simp only [acceptOwnershipComparison, howner, decide_false])

set_option maxRecDepth 2000 in
theorem acceptOwnershipReachOwner {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨5644⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨5661⟩ R mem aw rdata σ k' C' := by
  have rd5650 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5644_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd5661 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5650_fallthrough
    (immWords := wordsOf (immStore v)) hstack (calldataLengthCheckOk hsz hhi hsize) rd5650
  exact ⟨_, _, rd5661⟩

set_option maxRecDepth 2000 in
theorem acceptOwnershipReachStore {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (howner : AccountAddress.ofNat (UInt256.land (codeOwnerStorageWord I σ ⟨9⟩)
      solcAddrMask).toNat = I.source)
    (rd : RD (deployedRuntime v) I g s0 ⟨5661⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨5681⟩ R mem aw rdata σ k' C' := by
  have hw := (maskedAddress_eq_iff_word _ _).mp howner
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_5661_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.sub (UInt256.land (codeOwnerStorageWord I σ ⟨9⟩) solcAddrMask)
        (UInt256.ofNat I.source.val) = ⟨0⟩
      rw [← hw, u256_sub_self]) rd

set_option maxRecDepth 2000 in
theorem acceptOwnershipRevertOwner {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (howner : AccountAddress.ofNat (UInt256.land (codeOwnerStorageWord I σ ⟨9⟩)
      solcAddrMask).toNat ≠ I.source)
    (rd : RD (deployedRuntime v) I g s0 ⟨5661⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, rd5759⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5661_taken
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.sub (UInt256.land (codeOwnerStorageWord I σ ⟨9⟩) solcAddrMask)
        (UInt256.ofNat I.source.val) ≠ ⟨0⟩
      apply u256_sub_ne_zero_of_ne
      exact fun heq ↦ howner ((maskedAddress_eq_iff_word _ _).mpr heq.symm))
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_5759
    (immWords := wordsOf (immStore v)) (by omega) rd5759

set_option maxRecDepth 2000 in
theorem acceptOwnershipStoreReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024) (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨5681⟩ R mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 (ownershipAccounts I σ (EVM.word I.source.val))
      ByteArray.empty := by
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5681
    (immWords := wordsOf (immStore v)) hstack hperm rd
  have hclear : UInt256.land (UInt256.lnot solcAddrMask) (codeOwnerStorageWord I σ ⟨9⟩) =
      setAddressOffset0Word (codeOwnerStorageWord I σ ⟨9⟩) ⟨0⟩ := by
    rw [setAddressOffset0Word_zero, u256_land_comm]
  have hset (old : UInt256) : UInt256.lor (EVM.word I.source.val)
      (UInt256.land old (UInt256.lnot solcAddrMask)) =
      setAddressOffset0Word old (EVM.word I.source.val) := by
    rw [u256_land_comm old (UInt256.lnot solcAddrMask)]
    simpa only [addressWord_val_clean] using setAddressOffset0Word_bytecode old
      (EVM.word I.source.val)
  change RDret _ _ _ (sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ ⟨9⟩
      (UInt256.land (UInt256.lnot solcAddrMask) (codeOwnerStorageWord I σ ⟨9⟩))) ⟨8⟩
    (UInt256.lor (EVM.word I.source.val) (UInt256.land (codeOwnerStorageWord I
      (sstoreAccountMap I.codeOwner σ ⟨9⟩
        (UInt256.land (UInt256.lnot solcAddrMask) (codeOwnerStorageWord I σ ⟨9⟩))) ⟨8⟩)
      (UInt256.lnot solcAddrMask)))) _ at hret
  rw [hclear, hset] at hret
  exact hret

theorem acceptOwnershipStoreWf (v : MetaMorphoV1_1Immutables) :
    clearAddressStoreWf (deployedRuntime v) ⟨5681⟩ ⟨9⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨5681⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨9⟩, 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨5683⟩ : UInt256), UInt8.ofNat 128, .DUP1, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨5684⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨5685⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨1⟩, 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨5687⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨1⟩, 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨5689⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some (⟨160⟩, 1),
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨5691⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨5692⟩ : UInt256), UInt8.ofNat 3, .SUB, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨5693⟩ : UInt256), UInt8.ofNat 25, .NOT, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨5694⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨5695⟩ : UInt256), UInt8.ofNat 129, .DUP2, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨5696⟩ : UInt256), UInt8.ofNat 22, .AND, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨5697⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨5698⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)
  · immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨5699⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      metaMorphoV1_1Blocks.immutableLayout_inBounds,
      metaMorphoV1_1Blocks.immutableTemplate_size64)

set_option maxRecDepth 2000 in
theorem acceptOwnershipStoreStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024) (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨5681⟩ R mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  exact clearAddressStoreStatic hstack hperm (acceptOwnershipStoreWf v) rd

set_option maxRecDepth 2000 in
theorem acceptOwnershipRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨5644⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5644_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem acceptOwnershipRevertHuge {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hhi : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨5644⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd5650 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5644_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_5650_taken
    (immWords := wordsOf (immStore v))
    hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩
      rw [calldataLengthCheckHuge hhi hsize]
      decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd5650
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

set_option maxRecDepth 2000 in
/-- `acceptOwnership()`: the theorem `Correct.lean` routes selector 36 to. -/
theorem metaMorphoV1_1AcceptOwnershipBody {σ σ₀ A I} {g : UInt256} (v : MetaMorphoV1_1Immutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (metaMorphoV1_1SelBytes 36)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 36) rfl hsel
  have hd : dispatchMsg contract I.calldata = some acceptOwnershipTransition := by
    apply metaMorphoV1_1Dispatch_acceptOwnership <;>
      first | exact hsel | exact selectorMismatch hsel (by decide +kernel)
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (acceptOwnershipTransition.params.map Param.name)
      (transitionSignature acceptOwnershipTransition).paramTypes I.calldata = some ∅ := by
    exact decodeCalldata_empty_ok hsz
  obtain ⟨k, C, rd⟩ := metaMorphoV1_1ReachAcceptOwnershipBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · obtain ⟨_, _, rd5661⟩ := acceptOwnershipReachOwner v (by simp) hwv hsz hhi hsize rd
      by_cases howner : AccountAddress.ofNat
          (UInt256.land (codeOwnerStorageWord I σ ⟨9⟩) solcAddrMask).toNat = I.source
      · obtain ⟨_, _, rd5681⟩ := acceptOwnershipReachStore v (by simp) howner rd5661
        by_cases hperm : I.perm = true
        · exact (acceptOwnershipStoreReturn v (by simp) hperm rd5681).reEquivExecutionGen
            hcode hd hdec (acceptOwnershipBodyReturns v _ ∅ hwv hhi howner)
            (ownershipState_accounts (initState σ σ₀ (Sat256.ofUInt256 g) A I) _).symm
            voidReturnEquiv
        · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
          exact (acceptOwnershipStoreStatic v (by simp) hp rd5681).reEquivStaticHalt
            hcode hd hdec (acceptOwnershipBodyStatic v _ ∅ hwv hhi howner hp)
      · exact (acceptOwnershipRevertOwner v (by simp) howner rd5661).reEquivExecutionRevert
          hcode hd hdec (acceptOwnershipBodyReverts v _ ∅ hwv hhi howner)
    · exact (acceptOwnershipRevertHuge v (by simp) hwv (by omega) hsize rd).reEquivExecutionRevert
        hcode hd hdec
        (bodyReverts_calldataBound "__calldata" (2 ^ 255 + 4) hwv (Nat.le_of_not_gt hhi))
  · exact (acceptOwnershipRevertNonPayable v (by simp) hwv rd).reEquivExecutionRevert
      hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Morpho.MetaMorphoV1_1
