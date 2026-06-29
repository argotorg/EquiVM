import Examples.OpenZeppelinBench.Ownable2Step.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Ownable2Step

/-! ## `transferOwnership(address)` -/

abbrev transferOwnershipNewOwnerWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev transferOwnershipNewOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferOwnershipNewOwnerWord I).toNat)

def transferOwnershipPendingOwnerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)

def transferOwnershipOwnerWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

def transferOwnershipSetPendingWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  ownable2StepSetAddressWord (transferOwnershipPendingOwnerWord σ I)
    (transferOwnershipNewOwnerWord I)

def transferOwnershipAfterPendingMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨1⟩ (transferOwnershipSetPendingWord σ I)

def transferOwnershipOwnerWordAfterPending (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  transferOwnershipAfterPendingMap σ I |>.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

def transferOwnershipStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "newOwner" (transferOwnershipNewOwnerValue I)

def transferOwnershipAfterPendingState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
      (ownable2StepSetAddressWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
        (transferOwnershipNewOwnerWord I))

theorem transferOwnershipAfterPendingState_accountMap (evm : EVM.State) (I : ExecutionEnv) :
    (transferOwnershipAfterPendingState evm I).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨1⟩
        (ownable2StepSetAddressWord
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          (transferOwnershipNewOwnerWord I)) := by
  simp [transferOwnershipAfterPendingState, ownable2StepStorageStore_accountMap]

theorem transferOwnershipAfterPendingState_createdAccounts (evm : EVM.State)
    (I : ExecutionEnv) :
    (transferOwnershipAfterPendingState evm I).createdAccounts = evm.createdAccounts := by
  simp [transferOwnershipAfterPendingState, ownable2StepStorageStore_createdAccounts]

theorem transferOwnershipAfterPendingState_executionEnv (evm : EVM.State) (I : ExecutionEnv) :
    (transferOwnershipAfterPendingState evm I).executionEnv = evm.executionEnv := by
  simp [transferOwnershipAfterPendingState, storageStore_executionEnv]

theorem transferOwnershipStore_newOwner (I : ExecutionEnv) :
    (transferOwnershipStore I).get? "newOwner" = some (transferOwnershipNewOwnerValue I) := by
  rw [transferOwnershipStore, store_get_self]

theorem transferOwnershipStore_owner (I : ExecutionEnv) :
    (transferOwnershipStore I).get? "_owner" = none := by
  rw [transferOwnershipStore, store_get_ne _ _ (by decide)]
  native_decide

theorem transferOwnershipStore_pendingOwner (I : ExecutionEnv) :
    (transferOwnershipStore I).get? "_pendingOwner" = none := by
  rw [transferOwnershipStore, store_get_ne _ _ (by decide)]
  native_decide

theorem evalExpr_transferOwnership_owner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferOwnershipStore I } evm
      (.storage ownerRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config { contract := contract, locals := transferOwnershipStore I } evm
      ownerRef = .ok { base := "_owner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, ownerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_owner", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address) (hbase := transferOwnershipStore_owner I)
    (her := her) (hty := hty) (hloc := by rfl), ownable2StepStorageLocLoad_address_offset0]

theorem evalExpr_transferOwnership_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferOwnershipStore I } evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_transferOwnership_owner_eq_true (evm : EVM.State) (I : ExecutionEnv)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        ownable2StepSourceWord evm.executionEnv) :
    evalExpr? config { contract := contract, locals := transferOwnershipStore I } evm
      (.binary .eq (.storage ownerRef) sender) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_transferOwnership_owner, evalExpr_transferOwnership_sender,
    bind, EvalResult.bind, evalBinaryOp?]
  rw [ownable2StepMaskedAddress_eq_source_of_word_eq (I := evm.executionEnv) howner]
  simp [BEq.beq]

theorem evalExpr_transferOwnership_owner_eq_false (evm : EVM.State) (I : ExecutionEnv)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask ≠
        ownable2StepSourceWord evm.executionEnv) :
    evalExpr? config { contract := contract, locals := transferOwnershipStore I } evm
      (.binary .eq (.storage ownerRef) sender) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_transferOwnership_owner, evalExpr_transferOwnership_sender,
    bind, EvalResult.bind, evalBinaryOp?]
  have haddr :
      AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat ≠ evm.executionEnv.source := by
    intro haddr
    exact howner (ownable2StepWord_eq_of_maskedAddress_eq_source haddr)
  rw [show ((.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat) : Value) == .address evm.executionEnv.source) = false by
    simp [BEq.beq, haddr]]

theorem evalExpr_transferOwnership_newOwner (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferOwnershipStore I } evm
      (.var "newOwner") = .ok (transferOwnershipNewOwnerValue I) := by
  rw [evalExpr?, transferOwnershipStore_newOwner]
  rfl

theorem transferOwnershipAssignPending (evm : EVM.State) (I : ExecutionEnv)
    (hcanon : (transferOwnershipNewOwnerWord I).toNat < EVM.addressModulus) :
    assignStorageRef? config { contract := contract, locals := transferOwnershipStore I } evm
        .storage pendingOwnerRef (transferOwnershipNewOwnerValue I) =
      .ok ({ contract := contract, locals := transferOwnershipStore I },
        transferOwnershipAfterPendingState evm I) := by
  have her : evalStorageRef config { contract := contract, locals := transferOwnershipStore I } evm
      pendingOwnerRef = .ok { base := "_pendingOwner", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, pendingOwnerRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "_pendingOwner", steps := [] } : EvaledStorageRef) =
      some (.elem .address) := by
    decide
  have hstore :
      storageLocStore evm (addrLoc ⟨1⟩) (transferOwnershipNewOwnerValue I) =
        some (transferOwnershipAfterPendingState evm I) := by
    simpa [transferOwnershipAfterPendingState, transferOwnershipNewOwnerValue] using
      ownable2StepStorageLocStore_address_offset0 evm ⟨1⟩
        (transferOwnershipNewOwnerWord I) hcanon
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := transferOwnershipStore I })
    (evm := evm) (evm' := transferOwnershipAfterPendingState evm I)
    (slot := pendingOwnerRef) (er := { base := "_pendingOwner", steps := [] })
    (ty := .elem .address) (loc := addrLoc ⟨1⟩)
    (value := transferOwnershipNewOwnerValue I)
    (transferOwnershipStore_pendingOwner I) her hty (by rfl) (by trivial) hstore

theorem ownable2StepTransferOwnershipBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        ownable2StepSourceWord evm.executionEnv)
    (hcanon : (transferOwnershipNewOwnerWord I).toNat < EVM.addressModulus) :
    ExecTransitionBody config contract evm (transferOwnershipStore I)
      transferOwnershipTransition.body
      (.returned { contract := contract, locals := transferOwnershipStore I }
        (transferOwnershipAfterPendingState evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferOwnership_owner_eq_true evm I howner)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferOwnership_newOwner evm I)
      (transferOwnershipAssignPending evm I hcanon)) ?_
  exact ExecBlock.nil

theorem ownable2StepTransferOwnershipBodyReverts_owner (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (howner :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask ≠
        ownable2StepSourceWord evm.executionEnv) :
    ExecTransitionBody config contract evm (transferOwnershipStore I)
      transferOwnershipTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transferOwnership_owner_eq_false evm I howner))

theorem ownable2StepTransferOwnershipSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ownable2StepDispatch_transferOwnership {cd : ByteArray}
    (hsel : ((⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some transferOwnershipTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [acceptOwnershipTransition, ownerTransition, pendingOwnerTransition,
      renounceOwnershipTransition])
    (post := []) rfl rfl ?_ (by rw [selectorOf, transferOwnershipSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [selectorOf, acceptOwnershipSelectorBytes, hcd]; decide
  · rw [selectorOf, ownerSelectorBytes, hcd]; decide
  · rw [selectorOf, pendingOwnerSelectorBytes, hcd]; decide
  · rw [selectorOf, renounceOwnershipSelectorBytes, hcd]; decide

theorem ownable2StepDecode_transferOwnership_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (transferOwnershipNewOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferOwnershipTransition.params.map Param.name)
      (transitionSignature transferOwnershipTransition).paramTypes I.calldata =
        some (transferOwnershipStore I) := by
  show decodeCalldata ["newOwner"] [addr] I.calldata = some (transferOwnershipStore I)
  simpa [addr, transferOwnershipStore, transferOwnershipNewOwnerValue,
    transferOwnershipNewOwnerWord, calldataWord] using
    decodeCalldata_address_ok (cd := I.calldata) (x := "newOwner") hsz36 hbig hcanon

theorem ownable2StepDecode_transferOwnership_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (transferOwnershipTransition.params.map Param.name)
      (transitionSignature transferOwnershipTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["newOwner"] [addr] I.calldata = none
  simpa [addr] using
    decodeCalldata_address_none_short (cd := I.calldata) (x := "newOwner") hsz4 hshort

theorem ownable2StepDecode_transferOwnership_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (transferOwnershipNewOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferOwnershipTransition.params.map Param.name)
      (transitionSignature transferOwnershipTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["newOwner"] [addr] I.calldata = none
  simpa [addr, transferOwnershipNewOwnerWord, calldataWord] using
    decodeCalldata_address_none_noncanon (cd := I.calldata) (x := "newOwner") hsz36 hbig hnc

theorem ownable2StepDecode_transferOwnership_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (transferOwnershipTransition.params.map Param.name)
      (transitionSignature transferOwnershipTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["newOwner"] [addr] I.calldata = none
  simpa [addr] using
    decodeCalldata_address_none_huge (cd := I.calldata) (x := "newOwner") hbig

set_option maxHeartbeats 500000 in
theorem ownable2StepDecodeAddressOk530 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ownable2StepBenchBytecode ee g s0 ⟨530⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩)
    (hcanon : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hret : (D_J ownable2StepBenchBytecode 0).contains ret = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD ownable2StepBenchBytecode ee g s0 ret (calldataWord ee.calldata 4 :: R)
      mem aw rdata acc k' C' := by
  have hclean : UInt256.eq (calldataWord ee.calldata 4)
      (UInt256.land (calldataWord ee.calldata 4) solcAddrMask) = ⟨1⟩ :=
    solcAddrCanon_eq hcanon
  have hclean' : UInt256.eq
        (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        (UInt256.land
          (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨1⟩ := by
    simpa [calldataWord, solcAddrMask] using hclean
  exact ⟨_, _, evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨546⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, dup2, eq, push2 ⟨568⟩, jumpiT (by rw [hclean']; decide) (by jump_dest),
    jumpdest, swap4, swap3, pop, pop, pop, jump hret ]⟩

theorem ownable2StepDecodeAddressLenRevert530 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ownable2StepBenchBytecode ee g s0 ⟨530⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩)
    (hov : R.length + 10 ≤ 1024) :
    RDrev ownable2StepBenchBytecode g s0 :=
  evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨546⟩,
    jumpiNT (by rw [hsltval]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by
      have hR : R.length ≤ 1024 - 10 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega) ]

set_option maxHeartbeats 300000 in
theorem ownable2StepDecodeAddressNoncanonRevert530 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ownable2StepBenchBytecode ee g s0 ⟨530⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩)
    (hnc : UInt256.eq (calldataWord ee.calldata 4)
        (UInt256.land (calldataWord ee.calldata 4) solcAddrMask) = ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev ownable2StepBenchBytecode g s0 :=
  have hnc' : UInt256.eq
        (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        (UInt256.land
          (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨0⟩ := by
    simpa [calldataWord, solcAddrMask] using hnc
  evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨546⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, dup2, eq, push2 ⟨568⟩, jumpiNT (by rw [hnc']),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem ownable2StepTransferOwnershipX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨164⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ownable2StepBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨530⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨178⟩, ⟨97⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd164⟩ := hreach
  exact ⟨_, _, evm_run rd164 with [
    jumpdest, push2 ⟨97⟩, push2 ⟨178⟩, calldatasize, push1 ⟨4⟩, push2 ⟨530⟩,
    jump (by jump_dest) ]⟩

theorem ownable2StepTransferOwnershipX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (transferOwnershipNewOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨164⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ownable2StepBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨178⟩
      [transferOwnershipNewOwnerWord I, ⟨97⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd530⟩ := ownable2StepTransferOwnershipX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach
  simpa [transferOwnershipNewOwnerWord, calldataWord] using
    ownable2StepDecodeAddressOk530 (R := [⟨97⟩, sel]) rd530 hslt hcanon
      (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)

theorem ownable2StepTransferOwnershipX_decodeRevert_short {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨164⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev ownable2StepBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd530⟩ := ownable2StepTransferOwnershipX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach
  exact ownable2StepDecodeAddressLenRevert530 (R := [⟨97⟩, sel]) rd530 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ownable2StepTransferOwnershipX_decodeRevert_huge {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨164⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev ownable2StepBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd530⟩ := ownable2StepTransferOwnershipX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach
  exact ownable2StepDecodeAddressLenRevert530 (R := [⟨97⟩, sel]) rd530 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ownable2StepTransferOwnershipX_decodeRevert_noncanon {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (transferOwnershipNewOwnerWord I)
        (UInt256.land (transferOwnershipNewOwnerWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨164⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev ownable2StepBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd530⟩ := ownable2StepTransferOwnershipX_toDecoder (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hreach
  exact ownable2StepDecodeAddressNoncanonRevert530 (R := [⟨97⟩, sel]) rd530 hslt
    (by simpa [transferOwnershipNewOwnerWord] using hnc)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem ownable2StepX_transferOwnership_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (transferOwnershipNewOwnerWord I).toNat < EVM.addressModulus)
    (howner :
      UInt256.land (transferOwnershipOwnerWord σ I) solcAddrMask = ownable2StepSourceWord I)
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨164⟩ [ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ownable2StepBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, transferOwnershipAfterPendingMap σ I) ByteArray.empty := by
  obtain ⟨_, _, rd178⟩ := ownable2StepTransferOwnershipX_decoded (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := ownable2StepSelWord I) hsz36 hsize hszhi hcanon hreach
  have rd275 := evm_run rd178 with [jumpdest, push2 ⟨275⟩, jump (by jump_dest)]
  have rd387 := evm_run rd275 with [jumpdest, push2 ⟨283⟩, push2 ⟨387⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd283⟩ := RD.ownable2StepOnlyOwnerPass
    (ret := ⟨283⟩) (R := [transferOwnershipNewOwnerWord I, ⟨97⟩, ownable2StepSelWord I])
    rd387 (by simpa [ownable2StepOnlyOwnerWord, transferOwnershipOwnerWord] using howner)
    (by jump_dest) (by evm_ov)
  have rd287 := evm_run rd283 with [jumpdest, push1 ⟨1⟩, dup1]
  obtain ⟨_, _, rd288₀⟩ := rd287.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd288⟩ : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨288⟩
      [transferOwnershipPendingOwnerWord σ I, ⟨1⟩, transferOwnershipNewOwnerWord I, ⟨97⟩,
        ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [transferOwnershipPendingOwnerWord] using rd288₀⟩
  have rd311₀ := evm_run rd288 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and, push1 ⟨1⟩,
    push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, swap1, swap2, and, dup2]
  have rd312₀ := RD.lor rd311₀ (by decide) (by evm_ov)
  have hset :
      UInt256.lor
          (UInt256.land (transferOwnershipNewOwnerWord I) solcAddrMask)
          (UInt256.land (transferOwnershipPendingOwnerWord σ I) (UInt256.lnot solcAddrMask)) =
        transferOwnershipSetPendingWord σ I := by
    unfold transferOwnershipSetPendingWord ownable2StepSetAddressWord
    exact u256_lor_comm
      (UInt256.land (transferOwnershipNewOwnerWord I) solcAddrMask)
      (UInt256.land (transferOwnershipPendingOwnerWord σ I) (UInt256.lnot solcAddrMask))
  have rd312 := rd312₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask by decide] at rd312
  rw [hset] at rd312
  have rd314 := evm_run rd312 with [swap1, swap2]
  obtain ⟨_, _, rd315₀⟩ := rd314.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd315⟩ : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨315⟩
      [UInt256.land (transferOwnershipNewOwnerWord I) solcAddrMask,
        transferOwnershipNewOwnerWord I, ⟨97⟩, ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, transferOwnershipAfterPendingMap σ I) k C := by
    exact ⟨_, _, by simpa [transferOwnershipAfterPendingMap] using rd315₀⟩
  let σp := transferOwnershipAfterPendingMap σ I
  have rd319 := evm_run rd315 with [push2 ⟨331⟩, push0]
  obtain ⟨_, _, rd320₀⟩ := rd319.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd320⟩ : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨320⟩
      [transferOwnershipOwnerWordAfterPending σ I, ⟨331⟩,
        UInt256.land (transferOwnershipNewOwnerWord I) solcAddrMask,
        transferOwnershipNewOwnerWord I, ⟨97⟩, ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σp) k C := by
    exact ⟨_, _, by simpa [σp, transferOwnershipOwnerWordAfterPending] using rd320₀⟩
  have rd331 := evm_run rd320 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, swap1,
    jump (by jump_dest)]
  have rd341 := evm_run rd331 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and]
  have rd374 := rd341.pushConst
    (⟨0x38d16b8cac22d99fc7c124b9cd0de2d3fa1faef420bfe791d8c362d765e22700⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd383₀ := evm_run rd374 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  have rd383 := rd383₀
  rw [show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ by decide] at rd383
  have rd385 := rd383.log3 0 (UInt256.ofNat 3) (by decide) hperm mem_cost
    (by decide) (by evm_ov)
  have rd97 := evm_run rd385 with [pop, jump (by jump_dest)]
  have rd98 := evm_run rd97 with [jumpdest]
  exact rd98.stop (by decide) (by evm_ov)

theorem ownable2StepX_transferOwnership_revert_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (transferOwnershipNewOwnerWord I).toNat < EVM.addressModulus)
    (howner :
      UInt256.land (transferOwnershipOwnerWord σ I) solcAddrMask ≠ ownable2StepSourceWord I)
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨164⟩ [ownable2StepSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ownable2StepBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd178⟩ := ownable2StepTransferOwnershipX_decoded (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := ownable2StepSelWord I) hsz36 hsize hszhi hcanon hreach
  have rd275 := evm_run rd178 with [jumpdest, push2 ⟨275⟩, jump (by jump_dest)]
  have rd387 := evm_run rd275 with [jumpdest, push2 ⟨283⟩, push2 ⟨387⟩,
    jump (by jump_dest)]
  exact RD.ownable2StepOnlyOwnerRevert
    (ret := ⟨283⟩) (R := [transferOwnershipNewOwnerWord I, ⟨97⟩, ownable2StepSelWord I])
    rd387 (by simpa [ownable2StepOnlyOwnerWord, transferOwnershipOwnerWord] using howner)
    (by evm_ov)

theorem ownable2StepTransferOwnershipBody {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = ownable2StepBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩)
    (hreach : ∃ k C, RD ownable2StepBenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨164⟩
      [ownable2StepSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hsz4 := ownable2StepTransferOwnershipSelector_size hsel
  have hd := ownable2StepDispatch_transferOwnership (cd := I.calldata) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (transferOwnershipNewOwnerWord I).toNat < EVM.addressModulus
      · let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
        let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hσ : EVMStateEquiv evmE evmS := EVMStateEquiv.initState hAccounts
        have hownerWord :
            transferOwnershipOwnerWord σ_evm I = transferOwnershipOwnerWord σ_solm I := by
          exact accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
        by_cases howner :
            UInt256.land (transferOwnershipOwnerWord σ_evm I) solcAddrMask =
              ownable2StepSourceWord I
        · have hownerSolm :
              UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨0⟩)
                  solcAddrMask =
                ownable2StepSourceWord evmS.executionEnv := by
            have hmap :
                UInt256.land (transferOwnershipOwnerWord σ_solm I) solcAddrMask =
                  ownable2StepSourceWord I := by
              simpa [hownerWord] using howner
            simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
              transferOwnershipOwnerWord, ownable2StepSourceWord] using hmap
          have hdec := ownable2StepDecode_transferOwnership_ok (I := I) hsz36 hbig hcanon
          have hbody := ownable2StepTransferOwnershipBodyReturns evmS I
            (by simp only [evmS, initState]; exact hwv) hownerSolm hcanon
          have hPendingWord :
              transferOwnershipPendingOwnerWord σ_evm I =
                transferOwnershipPendingOwnerWord σ_solm I := by
            exact accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
          have hPendingVal :
              ownable2StepSetAddressWord
                  (Solm.EVM.storageLoad evmE evmE.executionEnv.codeOwner ⟨1⟩)
                  (transferOwnershipNewOwnerWord I) =
                ownable2StepSetAddressWord
                  (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨1⟩)
                  (transferOwnershipNewOwnerWord I) := by
            exact congrArg (fun old => ownable2StepSetAddressWord old
              (transferOwnershipNewOwnerWord I)) (hσ.storageLoad_codeOwner ⟨1⟩)
          have hσPost : EVMStateEquiv
              (transferOwnershipAfterPendingState evmE I)
              (transferOwnershipAfterPendingState evmS I) := by
            simpa [transferOwnershipAfterPendingState] using
              hσ.storageStore_codeOwner ⟨1⟩ hPendingVal
          exact (ownable2StepX_transferOwnership_success (g := Sat256.ofUInt256 g)
              hperm hsz36 hsize hbig hcanon howner hreach)
            |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
              (by
                rw [transferOwnershipAfterPendingState_createdAccounts]
                simp [evmE, initState])
              (accountMapEquiv.of_eq (by
                rw [transferOwnershipAfterPendingState_accountMap]
                simp [evmE, initState, transferOwnershipAfterPendingMap,
                  transferOwnershipSetPendingWord, transferOwnershipPendingOwnerWord,
                  Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]))
              hσPost
              (returnEquiv.void rfl rfl rfl)
        · have hownerSolm :
              UInt256.land (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨0⟩)
                  solcAddrMask ≠
                ownable2StepSourceWord evmS.executionEnv := by
            intro h
            apply howner
            have hmap :
                UInt256.land (transferOwnershipOwnerWord σ_solm I) solcAddrMask =
                  ownable2StepSourceWord I := by
              simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
                transferOwnershipOwnerWord, ownable2StepSourceWord] using h
            simpa [hownerWord] using hmap
          have hdec := ownable2StepDecode_transferOwnership_ok (I := I) hsz36 hbig hcanon
          have hbody := ownable2StepTransferOwnershipBodyReverts_owner evmS I
            (by simp only [evmS, initState]; exact hwv) hownerSolm
          exact (ownable2StepX_transferOwnership_revert_owner (g := Sat256.ofUInt256 g)
              hsz36 hsize hbig hcanon howner hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hnc :
            UInt256.eq (transferOwnershipNewOwnerWord I)
              (UInt256.land (transferOwnershipNewOwnerWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (ownable2StepTransferOwnershipX_decodeRevert_noncanon (g := Sat256.ofUInt256 g)
            hsz36 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd
            (ownable2StepDecode_transferOwnership_none_noncanon (I := I) hsz36 hbig hcanon)
    · have hbigLe : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      exact (ownable2StepTransferOwnershipX_decodeRevert_huge (g := Sat256.ofUInt256 g)
          hsize hbigLe hreach)
        |>.reEquivDecodingFailed hcode hd
          (ownable2StepDecode_transferOwnership_none_huge (I := I) hbigLe)
  · have hshort : I.calldata.size < 36 := by omega
    exact (ownable2StepTransferOwnershipX_decodeRevert_short (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd
        (ownable2StepDecode_transferOwnership_none_short (I := I) hsz4 hshort)

end OpenZeppelinBench.Ownable2Step
