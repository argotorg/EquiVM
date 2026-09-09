import Benchmarks.Dss.End.Bytecode
import Reasoning.ABI
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Memory
import Reasoning.Storage
import Reasoning.Dispatch
import Reasoning.SolmBody
import Reasoning.ExternalCall
import Mathlib.Tactic.IntervalCases

/-!
# MakerDAO/Sky DSS End shared proof foundation

Contract-wide helpers for the optimized runtime and creation bytecode.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.End

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev endSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

def endSlotWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I slot

abbrev endAddressReturnWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (endSlotWord slot σ I) solcAddrMask

theorem endStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa [addrLoc, addressOffset0Loc] using storageLocLoad_address_offset0 evm slot

theorem endStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

theorem endStorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (wordLoc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  simpa [wordLoc, uint256Loc] using storageLocStore_uint256 evm slot val

theorem endAccountMapExtensionalEq_of_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) : accountMapExtensionalEq σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

theorem endAccountMapEquiv_of_accountMapExtensionalEq {σ τ : AccountMap}
    (hστ : accountMapExtensionalEq σ τ) : accountMapEquiv σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

theorem endCallMade_accountMapEquiv_with_substate {cfg : Config}
    {evm_evm evm_solm : EVM.State}
    {tgt : EVM.Address} {targetWord : UInt256} {name : Ident} {args : List Value}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {A' A_in : Substate}
    {z : Bool} {out : ByteArray} {g'' callGas : UInt256}
    {mem : ByteArray} {inOff inSize : UInt256} {callPerm : Bool}
    (hdepth : evm_evm.executionEnv.depth ≠ 1024)
    (htgt : tgt = AccountAddress.ofUInt256 targetWord)
    (hcd : cfg.externalABI.encode? name args =
      some (mem.readWithPadding inOff.toNat inSize.toNat))
    (hΘ : (cA', σ', g'', A', z, out) =
        Ethereum.EVM.Θ evm_evm.executionEnv.blobVersionedHashes evm_evm.createdAccounts
          evm_evm.genesisBlockHeader evm_evm.blocks evm_evm.accountMap evm_evm.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evm_evm.executionEnv.codeOwner))
          evm_evm.executionEnv.sender (AccountAddress.ofUInt256 targetWord)
          (toExecute evm_evm.accountMap (AccountAddress.ofUInt256 targetWord))
          callGas (UInt256.ofNat evm_evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOff.toNat inSize.toNat)
          (evm_evm.executionEnv.depth + 1) evm_evm.executionEnv.header callPerm)
    (hAccounts : accountMapEquiv evm_evm.accountMap evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hCreated : evm_solm.createdAccounts = evm_evm.createdAccounts)
    (hGenesis : evm_solm.genesisBlockHeader = evm_evm.genesisBlockHeader)
    (hBlocks : evm_solm.blocks = evm_evm.blocks)
    (hEnv : evm_solm.executionEnv = evm_evm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg evm_solm tgt name 0 args
        (z,
          { evm_solm with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          out) callPerm ∧
      accountMapEquiv σ' σ'_solm ∧ A' = A'_solm := by
  have hExtEq : accountMapExtensionalEq evm_evm.accountMap evm_solm.accountMap :=
    endAccountMapExtensionalEq_of_accountMapEquiv hAccounts
  generalize hthetaSolm :
    Ethereum.EVM.Θ evm_solm.executionEnv.blobVersionedHashes evm_solm.createdAccounts
      evm_solm.genesisBlockHeader evm_solm.blocks evm_solm.accountMap evm_solm.σ₀ A_in
      evm_solm.executionEnv.codeOwner evm_solm.executionEnv.sender tgt
      (toExecute evm_solm.accountMap tgt) callGas
      (UInt256.ofNat evm_solm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
      (mem.readWithPadding inOff.toNat inSize.toNat)
      (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header callPerm = thetaRes
  have hcodeEquiv :
      toExecute evm_evm.accountMap tgt = toExecute evm_solm.accountMap tgt :=
    accountMapExtensionalEq_toExecute hExtEq tgt
  have hthetaSolm' :
      Ethereum.EVM.Θ evm_evm.executionEnv.blobVersionedHashes
        evm_evm.createdAccounts evm_evm.genesisBlockHeader evm_evm.blocks
        evm_solm.accountMap evm_evm.σ₀ A_in evm_evm.executionEnv.codeOwner
        evm_evm.executionEnv.sender tgt (toExecute evm_evm.accountMap tgt) callGas
        (UInt256.ofNat evm_evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
        (mem.readWithPadding inOff.toNat inSize.toNat)
        (evm_evm.executionEnv.depth + 1) evm_evm.executionEnv.header callPerm =
        (thetaRes.1, thetaRes.2.1, thetaRes.2.2.1, thetaRes.2.2.2.1,
          thetaRes.2.2.2.2.1, thetaRes.2.2.2.2.2) := by
    rw [← hthetaSolm]
    rw [hCreated, ← hOriginalAccounts, hGenesis, hBlocks, hEnv, hcodeEquiv]
  let a1 : AccountAddress := ⟨0, by simp [AccountAddress.size]⟩
  have hΘEvm := hΘ.symm
  rw [accountAddress_roundtrip, ← htgt] at hΘEvm
  have hThetaRel :=
    (accountMap_extensionality_of_Theta_and_Lambda
      (blobVersionedHashes := evm_evm.executionEnv.blobVersionedHashes)
      (createdAccounts := evm_evm.createdAccounts)
      (genesisBlockHeader := evm_evm.genesisBlockHeader)
      (blocks := evm_evm.blocks)
      (σ₁ := evm_evm.accountMap)
      (σ₂ := evm_solm.accountMap)
      (σ₀ := evm_evm.σ₀)
      (A := A_in)
      (s := evm_evm.executionEnv.codeOwner)
      (o := evm_evm.executionEnv.sender)
      (r := tgt)
      (g := callGas)
      (p := UInt256.ofNat evm_evm.executionEnv.gasPrice)
      (v := (⟨0⟩ : UInt256))
      (v' := (⟨0⟩ : UInt256))
      (d := mem.readWithPadding inOff.toNat inSize.toNat)
      (i := ByteArray.empty)
      (ζ := none)
      (H := evm_evm.executionEnv.header)
      (w := callPerm)
      a1 a1
      (toExecute evm_evm.accountMap tgt)
      cA' thetaRes.1
      σ' thetaRes.2.1
      g'' thetaRes.2.2.1
      A' thetaRes.2.2.2.1
      z thetaRes.2.2.2.2.1
      out thetaRes.2.2.2.2.2
      (evm_evm.executionEnv.depth + 1)
      hExtEq).1 hΘEvm hthetaSolm'
  have hCreated' : cA' = thetaRes.1 := hThetaRel.1
  have hThetaS :
      (cA', thetaRes.2.1, thetaRes.2.2.1, thetaRes.2.2.2.1, z, out) =
        Ethereum.EVM.Θ evm_solm.executionEnv.blobVersionedHashes
          evm_solm.createdAccounts evm_solm.genesisBlockHeader evm_solm.blocks
          evm_solm.accountMap evm_solm.σ₀ A_in evm_solm.executionEnv.codeOwner
          evm_solm.executionEnv.sender tgt (toExecute evm_solm.accountMap tgt)
          callGas (UInt256.ofNat evm_solm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOff.toNat inSize.toNat)
          (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header callPerm := by
    rw [hThetaRel.2.2.2.1, hThetaRel.2.2.2.2.1]
    rw [hCreated']
    exact hthetaSolm.symm
  refine ⟨thetaRes.2.1, thetaRes.2.2.2.1, ?_, ?_, ?_⟩
  · refine ⟨mem.readWithPadding inOff.toNat inSize.toNat, hcd, ?_⟩
    exact callViaEVM.callMade (perm := callPerm) wordOfInt_zero.symm
      ⟨callGas, A_in, hThetaS⟩ rfl
      (by
        rw [hEnv]
        rw [← accountMapExtensionalEq_balanceOf hExtEq evm_evm.executionEnv.codeOwner]
        show (0 : Nat) ≤
          ((evm_evm.accountMap.find? evm_evm.executionEnv.codeOwner).elim ⟨0⟩
            (fun x => x.balance)).toNat
        exact Nat.zero_le _)
      (by
        rw [hEnv]
        exact hdepth)
  · have hσext : accountMapExtensionalEq σ' thetaRes.2.1 :=
      hThetaRel.2.2.2.2.2
    exact endAccountMapEquiv_of_accountMapExtensionalEq hσext
  · exact hThetaRel.2.2.1

theorem endAddressGetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (endStorageLocLoad_address_offset0 evm slot))

theorem endUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)))
    (hloc : config.storage.layout er = fun _ => some (wordLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (endStorageLocLoad_uint256 evm slot))

theorem endAddressGetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = endBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf endBytecode entry returnPc routine)
    (hgetter : solcAddressSlotGetterWf endBytecode routine slot)
    (hroutine : (D_J endBytecode 0).contains routine = true)
    (hreturnJd : (D_J endBytecode 0).contains returnPc = true)
    (hretmem : solcReturnAddressFromMemWf endBytecode returnPc)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (endAddressReturnWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : endSlotWord slot σ_evm I = endSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.address (AccountAddress.ofNat (endAddressReturnWord slot σ_solm I).toNat)] =
        some [Value.address (AccountAddress.ofNat (endAddressReturnWord slot σ_evm I).toNat)] := by
    have hslot : endSlotWord slot σ_solm I = endSlotWord slot σ_evm I := hword.symm
    simp [endAddressReturnWord, hslot]
  have henc :
      returnEquiv (UInt256.toByteArray (endAddressReturnWord slot σ_evm I))
        (some [(.address (AccountAddress.ofNat (endAddressReturnWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    simpa [endAddressReturnWord] using
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (endSlotWord slot σ_evm I)))
  have hret := RD.solcAddressGetterExternal (code := endBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret endBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (endAddressReturnWord slot σ_evm I)) := by
    simpa [endAddressReturnWord, endSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem endUint256GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = endBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf endBytecode entry returnPc routine)
    (hgetter : solcWordSlotGetterWf endBytecode routine slot)
    (hroutine : (D_J endBytecode 0).contains routine = true)
    (hreturnJd : (D_J endBytecode 0).contains returnPc = true)
    (hretmem : solcReturnWordFromMemWf endBytecode returnPc)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (endSlotWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : endSlotWord slot σ_evm I = endSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (endSlotWord slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (endSlotWord slot σ_evm I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (endSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (endSlotWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (endSlotWord slot σ_evm I))
  have hret := RD.solcWordGetterExternal
    (code := endBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret endBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (endSlotWord slot σ_evm I)) := by
    simpa [endSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

/-! ## One-word calldata arguments -/

abbrev endBytes32ArgBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev endBytes32ArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev endBytes32ArgValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (endBytes32ArgBytes I)

abbrev endBytes32ArgKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (endBytes32ArgBytes I)

theorem endDecode_legacyBytes32_ok {cd : ByteArray} {x : Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiBytes32] cd =
      some ((∅ : Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))) := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hread : readBytes? (cd.toList.drop 4) 0 32 =
      some ((cd.toList.drop 4).take 32) := by
    unfold readBytes?
    have hlen : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_pos hlen, List.drop_zero]
  have hblen : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hpad : zeroPadding? ((cd.toList.drop 4).take 32) 32 0 = some () := by
    unfold zeroPadding? readBytes?
    simp
  have htake : List.take 32 ((cd.toList.drop 4).take 32) = (cd.toList.drop 4).take 32 :=
    List.take_of_length_le (by rw [hblen])
  have hnotArgShort : ¬ cd.toList.length - 4 < 32 := by
    rw [htlen]
    omega
  simp [decodeCalldata.decodeArgs, decodeCalldata.insertValues, abiBytes32,
    ABI.decodeABIValues?, ABI.decodeABIValue?, isDynamicABIType, staticABIEncodedSize?,
    abiTupleHeadSize?, hread, abiBytes32Width, htake, hnotArgShort]

theorem endDecode_legacyBytes32_none_short {cd : ByteArray} {x : Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiBytes32] cd = none := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ cd.toList.length < 4 := by
    rw [htlen]
    omega
  rw [if_neg hnot4]
  have hnotDyn : ¬ ([abiBytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ cd.toList.length) := by
    simp [abiBytes32, isDynamicABIType]
  rw [if_neg hnotDyn]
  have hread : readBytes? (cd.toList.drop 4) 0 32 = none := by
    unfold readBytes?
    have hlen : ¬ (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, List.length_drop, htlen]
      omega
    rw [if_neg hlen]
  simp [decodeCalldata.decodeArgs, abiBytes32, ABI.decodeABIValues?, ABI.decodeABIValue?,
    isDynamicABIType, staticABIEncodedSize?, abiTupleHeadSize?, hread]

theorem endDecodeABIValues_bytes32_address_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiAddress] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, UInt256.toNat, hlen32]

theorem endDecodeABIValues_bytes32_address_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [abiBytes32, abiAddress] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    simp [decodeABIValue?, readBytes?, htake0]
    have hnot : ¬ 32 ≤ bytes.length - 32 := by
      rw [List.length_take, List.length_drop] at htake32n
      omega
    simp [readWord?, readBytes?, hnot]

theorem endDecode_legacyBytes32_address_ok {cd : ByteArray} {x y : Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiAddress] cd =
      some (((∅ : Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress] = some 64 by decide +native]
  simp only [bind, Option.bind]
  rw [endDecodeABIValues_bytes32_address_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

theorem endDecode_legacyBytes32_address_none_short {cd : ByteArray}
    {x y : Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiAddress] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress] = some 64 by decide +native]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [endDecodeABIValues_bytes32_address_legacy_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]
      omega)]

theorem endDecode_legacyUint256_ok {cd : ByteArray} {x : Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

theorem endDecode_legacyUint256_none_short {cd : ByteArray} {x : Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
    (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem endDecodeABIValues_bytes32_uint256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, hlen32]
  rw [Int.emod_eq_of_lt]
  · simp [UInt256.toNat]
  · exact Int.natCast_nonneg _
  · exact_mod_cast (ABI.bytesToWord ((bytes.drop 32).take 32)).val.isLt

theorem endDecodeABIValues_bytes32_uint256_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [abiBytes32, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    simp [decodeABIValue?, readBytes?, htake0]
    have hnot : ¬ 32 ≤ bytes.length - 32 := by
      rw [List.length_take, List.length_drop] at htake32n
      omega
    simp [readWord?, readBytes?, hnot]

theorem endDecode_legacyBytes32_uint256_ok {cd : ByteArray} {x y : Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiUInt256] cd =
      some (((∅ : Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by decide +native]
  simp only [bind, Option.bind]
  rw [endDecodeABIValues_bytes32_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

theorem endDecode_legacyBytes32_uint256_none_short {cd : ByteArray}
    {x y : Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiUInt256] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by decide +native]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [endDecodeABIValues_bytes32_uint256_legacy_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]
      omega)]

theorem endBytes32ArgBytes_len {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (endBytes32ArgBytes I).length = bytes32Width.val + 1 := by
  unfold endBytes32ArgBytes
  rw [List.length_take, List.length_drop]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [htlen]
  simp [bytes32Width]
  omega

theorem endBytes32ArgBytes_len32 {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (endBytes32ArgBytes I).length = 32 := by
  have hlen := endBytes32ArgBytes_len (I := I) hsz36
  simpa [bytes32Width] using hlen

theorem endKeyValueToWord_bytes32ArgKey {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (endBytes32ArgKey I) = endBytes32ArgWord I := by
  have hlen32 : (endBytes32ArgBytes I).length = 32 :=
    endBytes32ArgBytes_len32 (I := I) hsz36
  have hword : ABI.bytesToWord (endBytes32ArgBytes I) = endBytes32ArgWord I := by
    simpa [endBytes32ArgBytes, endBytes32ArgWord] using
      (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
  have hbytes : endBytes32ArgBytes I = EVM.Word.toBytesBE (endBytes32ArgWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := endBytes32ArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  simpa [endBytes32ArgKey, bytes32Width, hbytes] using
    keyValueToWord_fixedBytes32 (endBytes32ArgWord I)

theorem RD.solcOneWordExternalJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hd0 : decode code decoded = some (.JUMPDEST, .none))
    (hd1 : decode code (decoded + ⟨1⟩) = some (.POP, .none))
    (hd2 : decode code (decoded + ⟨1⟩ + ⟨1⟩) = some (.CALLDATALOAD, .none))
    (hd3 :
      decode code (decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (routine, 2)))
    (hd6 :
      decode code ((decoded + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMP, .none))
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine (calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd3 := rd2.calldataload hd2 (by evm_ov)
  have rd6 := rd3.push2 routine hd3 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd6.jump hd6 hroutine (by evm_ov)⟩

theorem RD.solcNestedMappingGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot owner spender ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (spender :: owner :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcNestedMappingGetterWf code pc baseSlot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot baseSlot owner) spender) :: ret :: R)
      (solcNestedMappingHashMem baseSlot owner spender)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, hinner⟩ := RD.solcNestedMappingInnerHash h hwf hov
  obtain ⟨_, _, houter⟩ := RD.solcNestedMappingOuterHash hinner hwf hov
  obtain ⟨_, _, hload⟩ := RD.solcNestedMappingLoadAndJump houter hwf hret (by omega)
  exact ⟨_, _, hload⟩

-- LIBRARY CANDIDATE: move to `Reasoning.Solc` beside `solcSingleMappingGetterWf`.
@[reducible] def solcZeroSlotMappingGetterWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.SWAP1, .none)
  ∧ decode code p7 = some (.MSTORE, .none)
  ∧ decode code p8 = some (.SWAP1, .none)
  ∧ decode code p9 = some (.DUP2, .none)
  ∧ decode code p10 = some (.MSTORE, .none)
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.KECCAK256, .none)
  ∧ decode code p15 = some (.SLOAD, .none)
  ∧ decode code p16 = some (.DUP2, .none)
  ∧ decode code p17 = some (.JUMP, .none)

-- LIBRARY CANDIDATE: move to `Reasoning.Solc` with `solcZeroSlotMappingGetterWf`.
theorem RD.solcZeroSlotMappingGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcZeroSlotMappingGetterWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot ⟨0⟩ key) :: ret :: R)
      (solcMappingHashMem ⟨0⟩ key) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd13, hd14, hd15,
      hd16, hd17⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨0⟩ hd1 (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ hd3 (by evm_ov)
  have rd6 := rd5.dup2 hd5 (by evm_ov)
  have rd7 := rd6.swap1 hd6 (by evm_ov)
  have rd8 := rd7.mstore 0 (solcMappingBaseSlotMem ⟨0⟩)
    (UInt256.ofNat 3) hd7 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd9 := rd8.swap1 hd8 (by evm_ov)
  have rd10 := rd9.dup2 hd9 (by evm_ov)
  have rd11 := rd10.mstore 0 (solcMappingHashMem ⟨0⟩ key)
    (UInt256.ofNat 3) hd10 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd13 := rd11.push1 ⟨64⟩ hd11 (by evm_ov)
  have rd14 := rd13.swap1 hd13 (by evm_ov)
  have hslot := solcMappingKeccakSlot ⟨0⟩ key
  have rd15 := rd14.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd14 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd16⟩ := rd15.sload hd15 (by evm_ov)
  have rd17 := rd16.dup2 hd16 (by evm_ov)
  exact ⟨_, _, rd17.jump hd17 hret (by evm_ov)⟩

/-!
The reasoning library has LOG1/LOG3/LOG4 combinators; this contract also emits two-topic auth logs.
-/

-- LIBRARY CANDIDATE: move to `Reasoning.Reach` beside `RD.log1`, `RD.log3`, and `RD.log4`.
def stLog2 (s : State) (a b c d : UInt256) (t : List UInt256) : State :=
  { s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG2)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

-- LIBRARY CANDIDATE: move to `Reasoning.Stepping` with `stLog2`.
theorem log2_xstep {s : State} {code : ByteArray} {pcv a b c d : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG2, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .LOG2 +
            (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
       then .error .OutOfGass else .ok (stLog2 s a b c d t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG2, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_log2 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: t).length - 4 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, stLog2]

-- LIBRARY CANDIDATE: move to `Reasoning.Reach` beside `RD.log1`, `RD.log3`, and `RD.log4`.
theorem RD.log2 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG2, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: t →
        memoryExpansionCost s .LOG2 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 2 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc,
      hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG2 = mcost := hmc s haw hstk
    have hperms : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have st := log2_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stLog2 s a b c d t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stLog2]; exact hcode
      · simp only [stLog2]; rw [hpc]
      · simp only [stLog2]
      · simp only [stLog2, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stLog2]; exact hmem
      · simp only [stLog2]; rw [haw, hawout]
      · simp only [stLog2]; exact hrdata
      · simp only [stLog2]; exact hacc
      · simp only [stLog2]; exact hee
      · simp only [stLog2]; exact hworld

/-! ## End-local source arithmetic helpers -/

abbrev endUintBinaryLocals (x y : UInt256) : Store :=
  (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat)))

abbrev endUintBinaryLocalsZ (x y z : UInt256) : Store :=
  (endUintBinaryLocals x y).insert "z" (.int (Int.ofNat z.toNat))

abbrev endUintBinaryLocalsM (x y m : UInt256) : Store :=
  (endUintBinaryLocals x y).insert "m" (.int (Int.ofNat m.toNat))

abbrev endWadWord : UInt256 := ⟨1000000000000000000⟩

abbrev endRayWord : UInt256 := ⟨1000000000000000000000000000⟩

theorem endUintBinaryLocals_get_x (x y : UInt256) :
    (endUintBinaryLocals x y).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [endUintBinaryLocals, store_get_self]

theorem endUintBinaryLocals_get_y (x y : UInt256) :
    (endUintBinaryLocals x y).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [endUintBinaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem endUintBinaryLocalsZ_get_x (x y z : UInt256) :
    (endUintBinaryLocalsZ x y z).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [endUintBinaryLocalsZ, store_get_ne _ _ (by decide), endUintBinaryLocals_get_x]

theorem endUintBinaryLocalsZ_get_y (x y z : UInt256) :
    (endUintBinaryLocalsZ x y z).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [endUintBinaryLocalsZ, store_get_ne _ _ (by decide), endUintBinaryLocals_get_y]

theorem endUintBinaryLocalsZ_get_z (x y z : UInt256) :
    (endUintBinaryLocalsZ x y z).get? "z" = some (.int (Int.ofNat z.toNat)) := by
  rw [endUintBinaryLocalsZ, store_get_self]

theorem endUintBinaryLocalsM_get_m (x y m : UInt256) :
    (endUintBinaryLocalsM x y m).get? "m" = some (.int (Int.ofNat m.toNat)) := by
  rw [endUintBinaryLocalsM, store_get_self]

theorem endUintBinaryLocalsM_get_y (x y m : UInt256) :
    (endUintBinaryLocalsM x y m).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [endUintBinaryLocalsM, store_get_ne _ _ (by decide), endUintBinaryLocals_get_y]

theorem endEvalExpr_varUInt256 {evm : EVM.State} {locals : Store}
    {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int (Int.ofNat value.toNat))
  rw [h]
  rfl

theorem endEvalExpr_add256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b sum : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hsum : sum = a + b)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .add x y)) = .ok (.int (Int.ofNat sum.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat + b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : sum.toNat = a.toNat + b.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  simp [u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem endEvalExpr_add256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .add x y)) = .revert := by
  simp [u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem endEvalExpr_mul256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b prod : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hprod : prod = a * b)
    (hfit : a.toNat * b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .mul x y)) = .ok (.int (Int.ofNat prod.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat * b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : prod.toNat = a.toNat * b.toNat := by
    rw [hprod, umul_toNat a b hfit]
  simp [u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem endEvalExpr_mul256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .mul x y)) = .revert := by
  simp [u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem endEvalExpr_div_uint256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b q : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hb : b ≠ ⟨0⟩)
    (hq : q = UInt256.div a b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .div x y) =
      .ok (.int (Int.ofNat q.toNat)) := by
  have hbNat : ¬ b.toNat = 0 := by
    intro hzero
    exact hb (uint256_toNat_eq_zero hzero)
  have hqNat : q.toNat = a.toNat / b.toNat := by
    rw [hq, udiv_toNat]
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, hbNat, hqNat]

theorem endEvalExpr_div_uint256_revert_zero {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hb : b = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .div x y) =
      .revert := by
  subst b
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?]

theorem endEvalExpr_ge_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hge : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hge

theorem endEvalExpr_eq_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a = b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool true) := by
  subst h
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]

theorem endEvalExpr_eq_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a ≠ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem endEvalExpr_ne_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a ≠ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ne lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem endEvalExpr_ne_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a = b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ne lhs rhs) =
      .ok (.bool false) := by
  subst h
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]

theorem endEvalExpr_extCodeGuard_true {evm : EVM.State} {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem endEvalExpr_extCodeGuard_false {evm : EVM.State} {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem endUniswapExtCodeSizeWord_ne_zero_lookup_code_pos {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hne
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      exfalso
      exact hne (by simp [hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [hacc] using Nat.pos_of_ne_zero htoNatNe

theorem endUniswapExtCodeSizeWord_zero_lookup_code_zero {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.extCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hzero
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      simpa [hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by decide +native)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [hacc] using hword

theorem endEvalExpr_or_true_left {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool true)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs]

theorem endEvalExpr_or_false_right {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool false))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.bool b)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool b) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

theorem endU256_mul_div_overflow_ne (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    UInt256.div (y * x) y ≠ x := by
  intro hEq
  have hyNatNe : y.toNat ≠ 0 := by
    intro hy0
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hy0]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hnat := congrArg UInt256.toNat hEq
  rw [udiv_toNat, u256_mul_op_toNat] at hnat
  have hremLt : y.toNat * x.toNat % UInt256.size < y.toNat * x.toNat := by
    have hmodLt : y.toNat * x.toNat % UInt256.size < UInt256.size :=
      Nat.mod_lt _ (by norm_num [UInt256.size])
    have hover' : UInt256.size ≤ y.toNat * x.toNat := by
      simpa [Nat.mul_comm] using hover
    omega
  have hle0 := Nat.mul_div_le (y.toNat * x.toNat % UInt256.size) y.toNat
  rw [hnat] at hle0
  have hle : y.toNat * x.toNat ≤ y.toNat * x.toNat % UInt256.size := by
    simpa [Nat.mul_comm] using hle0
  omega

theorem endExecAddFunctionReturn (evm : EVM.State) {x y sum : UInt256}
    (hsum : sum = x + y) (hfit : x.toNat + y.toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      addFunction.body
      (.returned { contract := contract, locals := endUintBinaryLocalsZ x y sum } evm
        (some [.int (Int.ofNat sum.toNat)])) := by
  let locals := endUintBinaryLocals x y
  let localsZ := endUintBinaryLocalsZ x y sum
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (endUintBinaryLocals_get_y x y)
  have hAdd :
      evalExpr? config { contract := contract, locals := locals } evm
        (u256 (.binary .add (.var "x") (.var "y"))) =
          .ok (.int (Int.ofNat sum.toNat)) :=
    endEvalExpr_add256_ok hx hy hsum hfit
  have hz :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat sum.toNat)) := by
    simpa [localsZ] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := sum)
      (endUintBinaryLocalsZ_get_z x y sum)
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "x") (value := x)
      (endUintBinaryLocalsZ_get_x x y sum)
  have hsumNat : sum.toNat = x.toNat + y.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hReq :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .ge (.var "z") (.var "x")) = .ok (.bool true) :=
    endEvalExpr_ge_uint256_true hz hxZ (by rw [hsumNat]; omega)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (u256 (.binary .add (.var "x") (.var "y"))),
          .require (.binary .ge (.var "z") (.var "x")),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat sum.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hAdd) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hz))
  simpa [addFunction, locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem endExecAddFunctionRevert (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat + y.toNat) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      addFunction.body .reverted := by
  let locals := endUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (endUintBinaryLocals_get_y x y)
  have hAddRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (u256 (.binary .add (.var "x") (.var "y"))) = .revert :=
    endEvalExpr_add256_revert hx hy hover
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (u256 (.binary .add (.var "x") (.var "y"))),
          .require (.binary .ge (.var "z") (.var "x")),
          .return [.var "z"] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hAddRev)
  simpa [addFunction, locals] using ExecFuncBody.execBlockRevert hblock

theorem endExecMulFunctionReturn (evm : EVM.State) {x y prod : UInt256}
    (hprod : prod = x * y) (hfit : x.toNat * y.toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      mulFunction.body
      (.returned { contract := contract, locals := endUintBinaryLocalsZ x y prod } evm
        (some [.int (Int.ofNat prod.toNat)])) := by
  let locals := endUintBinaryLocals x y
  let localsZ := endUintBinaryLocalsZ x y prod
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (endUintBinaryLocals_get_y x y)
  have hMul :
      evalExpr? config { contract := contract, locals := locals } evm
        (u256 (.binary .mul (.var "x") (.var "y"))) =
          .ok (.int (Int.ofNat prod.toNat)) :=
    endEvalExpr_mul256_ok hx hy hprod hfit
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "x") (value := x)
      (endUintBinaryLocalsZ_get_x x y prod)
  have hyZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [localsZ] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "y") (value := y)
      (endUintBinaryLocalsZ_get_y x y prod)
  have hzZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsZ] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := prod)
      (endUintBinaryLocalsZ_get_z x y prod)
  have hZeroLit :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hReq :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .or
          (.binary .eq (.var "y") (.intLit 0))
          (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))) =
        .ok (.bool true) := by
    by_cases hy0 : y = (⟨0⟩ : UInt256)
    · have hyEqZero :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.var "y") (.intLit 0)) = .ok (.bool true) := by
        apply endEvalExpr_eq_int_true hyZ hZeroLit
        rw [hy0]
      exact endEvalExpr_or_true_left hyEqZero
    · have hyEqZero :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.var "y") (.intLit 0)) = .ok (.bool false) := by
        apply endEvalExpr_eq_int_false hyZ hZeroLit
        intro hbad
        exact hy0 (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
      have hyNatNe : y.toNat ≠ 0 := by
        intro hzero
        exact hy0 (uint256_toNat_eq_zero hzero)
      have hdivWord : UInt256.div prod y = x := by
        apply u256_inj
        rw [udiv_toNat]
        have hprodNat : prod.toNat = x.toNat * y.toNat := by
          rw [hprod, umul_toNat x y hfit]
        rw [hprodNat]
        simpa [Nat.mul_comm] using Nat.mul_div_right x.toNat (Nat.pos_of_ne_zero hyNatNe)
      have hDivY :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .div (.var "z") (.var "y")) = .ok (.int (Int.ofNat x.toNat)) := by
        have h := endEvalExpr_div_uint256_ok (evm := evm) (locals := localsZ)
          (x := .var "z") (y := .var "y") (a := prod) (b := y)
          (q := UInt256.div prod y) hzZ hyZ hy0 rfl
        simpa [hdivWord] using h
      have hRight :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x")) =
              .ok (.bool true) := by
        exact endEvalExpr_eq_int_true hDivY hxZ rfl
      exact endEvalExpr_or_false_right hyEqZero hRight
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (u256 (.binary .mul (.var "x") (.var "y"))),
          .require
            (.binary .or
              (.binary .eq (.var "y") (.intLit 0))
              (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat prod.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hMul) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzZ))
  simpa [mulFunction, locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem endExecMulFunctionRevert (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      mulFunction.body .reverted := by
  let locals := endUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (endUintBinaryLocals_get_y x y)
  have hMulRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (u256 (.binary .mul (.var "x") (.var "y"))) = .revert :=
    endEvalExpr_mul256_revert hx hy hover
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (u256 (.binary .mul (.var "x") (.var "y"))),
          .require
            (.binary .or
              (.binary .eq (.var "y") (.intLit 0))
              (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))),
          .return [.var "z"] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hMulRev)
  simpa [mulFunction, locals] using ExecFuncBody.execBlockRevert hblock

theorem endExecRmulFunctionReturn (evm : EVM.State) {x y prod q : UInt256}
    (hprod : prod = x * y) (hfit : x.toNat * y.toNat < UInt256.size)
    (hq : q = UInt256.div prod endRayWord) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      rmulFunction.body
      (.returned { contract := contract, locals := endUintBinaryLocalsM x y prod } evm
        (some [.int (Int.ofNat q.toNat)])) := by
  let locals := endUintBinaryLocals x y
  let localsM := endUintBinaryLocalsM x y prod
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (endUintBinaryLocals_get_y x y)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "x", .var "y"] =
        .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] := by
    simp [evalExprs?, hx, hy, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] =
        some (endUintBinaryLocals x y) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "mul" [.var "x", .var "y"] "m")
        (.ok { contract := contract, locals := localsM } evm) := by
    have hbody :=
      endExecMulFunctionReturn (evm := evm) (x := x) (y := y) (prod := prod)
        hprod hfit
    have hstmt := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "mul") (retVar := "m")
      (args := [.var "x", .var "y"])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
      (callee := mulFunction) (locals := endUintBinaryLocals x y)
      hargs (by rfl) hbind hbody
    simpa [localsM, endUintBinaryLocalsM, resumeAfterInternalCall, collapseReturns] using hstmt
  have hm :
      evalExpr? config { contract := contract, locals := localsM } evm (.var "m") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsM] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsM) (name := "m") (value := prod)
      (endUintBinaryLocalsM_get_m x y prod)
  have hRay :
      evalExpr? config { contract := contract, locals := localsM } evm (.intLit RAY) =
        .ok (.int (Int.ofNat endRayWord.toNat)) := by
    have hRayEq : RAY = Int.ofNat endRayWord.toNat := by
      decide +native
    simp [evalExpr?, pure, hRayEq]
  have hDiv :
      evalExpr? config { contract := contract, locals := localsM } evm
        (.binary .div (.var "m") (.intLit RAY)) =
          .ok (.int (Int.ofNat q.toNat)) :=
    endEvalExpr_div_uint256_ok hm hRay (by decide +native) hq
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .internalCall "mul" [.var "x", .var "y"] "m",
          .return [.binary .div (.var "m") (.intLit RAY)] ]
        (.returned { contract := contract, locals := localsM } evm
          (some [.int (Int.ofNat q.toNat)])) := by
    refine ExecBlock.consNormal hmulStmt ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hDiv))
  simpa [rmulFunction, locals, localsM] using ExecFuncBody.execBlockRet hblock

theorem endExecRmulFunctionRevertMul (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      rmulFunction.body .reverted := by
  let locals := endUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (endUintBinaryLocals_get_y x y)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "x", .var "y"] =
        .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] := by
    simp [evalExprs?, hx, hy, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] =
        some (endUintBinaryLocals x y) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "mul" [.var "x", .var "y"] "m") .reverted := by
    have hbody := endExecMulFunctionRevert (evm := evm) (x := x) (y := y) hover
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "mul") (retVar := "m")
      (args := [.var "x", .var "y"])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
      (callee := mulFunction) (locals := endUintBinaryLocals x y)
      hargs (by rfl) hbind hbody
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .internalCall "mul" [.var "x", .var "y"] "m",
          .return [.binary .div (.var "m") (.intLit RAY)] ]
        .reverted := by
    exact ExecBlock.consRevert hmulStmt
  simpa [rmulFunction, locals] using ExecFuncBody.execBlockRevert hblock

theorem endExecWdivFunctionReturn (evm : EVM.State) {x y prod q : UInt256}
    (hprod : prod = x * endWadWord) (hfit : x.toNat * endWadWord.toNat < UInt256.size)
    (hy : y ≠ ⟨0⟩) (hq : q = UInt256.div prod y) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      wdivFunction.body
      (.returned { contract := contract, locals := endUintBinaryLocalsM x y prod } evm
        (some [.int (Int.ofNat q.toNat)])) := by
  let locals := endUintBinaryLocals x y
  let localsM := endUintBinaryLocalsM x y prod
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hWad :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit WAD) =
        .ok (.int (Int.ofNat endWadWord.toNat)) := by
    have hWadEq : WAD = Int.ofNat endWadWord.toNat := by
      decide +native
    simp [evalExpr?, pure, hWadEq]
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "x", .intLit WAD] =
        .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)] := by
    simp [evalExprs?, hx, hWad, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)] =
        some (endUintBinaryLocals x endWadWord) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "mul" [.var "x", .intLit WAD] "m")
        (.ok { contract := contract, locals := localsM } evm) := by
    have hbody :=
      endExecMulFunctionReturn (evm := evm) (x := x) (y := endWadWord) (prod := prod)
        hprod hfit
    have hstmt := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "mul") (retVar := "m")
      (args := [.var "x", .intLit WAD])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)])
      (callee := mulFunction) (locals := endUintBinaryLocals x endWadWord)
      hargs (by rfl) hbind hbody
    simpa [localsM, endUintBinaryLocalsM, resumeAfterInternalCall, collapseReturns] using hstmt
  have hm :
      evalExpr? config { contract := contract, locals := localsM } evm (.var "m") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsM] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsM) (name := "m") (value := prod)
      (endUintBinaryLocalsM_get_m x y prod)
  have hyExpr :
      evalExpr? config { contract := contract, locals := localsM } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [localsM] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsM) (name := "y") (value := y)
      (endUintBinaryLocalsM_get_y x y prod)
  have hDiv :
      evalExpr? config { contract := contract, locals := localsM } evm
        (.binary .div (.var "m") (.var "y")) =
          .ok (.int (Int.ofNat q.toNat)) :=
    endEvalExpr_div_uint256_ok hm hyExpr hy hq
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .internalCall "mul" [.var "x", .intLit WAD] "m",
          .return [.binary .div (.var "m") (.var "y")] ]
        (.returned { contract := contract, locals := localsM } evm
          (some [.int (Int.ofNat q.toNat)])) := by
    refine ExecBlock.consNormal hmulStmt ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hDiv))
  simpa [wdivFunction, locals, localsM] using ExecFuncBody.execBlockRet hblock

theorem endExecWdivFunctionRevertMul (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * endWadWord.toNat) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      wdivFunction.body .reverted := by
  let locals := endUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hWad :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit WAD) =
        .ok (.int (Int.ofNat endWadWord.toNat)) := by
    have hWadEq : WAD = Int.ofNat endWadWord.toNat := by
      decide +native
    simp [evalExpr?, pure, hWadEq]
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "x", .intLit WAD] =
        .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)] := by
    simp [evalExprs?, hx, hWad, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)] =
        some (endUintBinaryLocals x endWadWord) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "mul" [.var "x", .intLit WAD] "m") .reverted := by
    have hbody :=
      endExecMulFunctionRevert (evm := evm) (x := x) (y := endWadWord) hover
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "mul") (retVar := "m")
      (args := [.var "x", .intLit WAD])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)])
      (callee := mulFunction) (locals := endUintBinaryLocals x endWadWord)
      hargs (by rfl) hbind hbody
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .internalCall "mul" [.var "x", .intLit WAD] "m",
          .return [.binary .div (.var "m") (.var "y")] ]
        .reverted := by
    exact ExecBlock.consRevert hmulStmt
  simpa [wdivFunction, locals] using ExecFuncBody.execBlockRevert hblock

theorem endExecWdivFunctionRevertDivZero (evm : EVM.State) {x y prod : UInt256}
    (hprod : prod = x * endWadWord) (hfit : x.toNat * endWadWord.toNat < UInt256.size)
    (hy : y = ⟨0⟩) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      wdivFunction.body .reverted := by
  let locals := endUintBinaryLocals x y
  let localsM := endUintBinaryLocalsM x y prod
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hWad :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit WAD) =
        .ok (.int (Int.ofNat endWadWord.toNat)) := by
    have hWadEq : WAD = Int.ofNat endWadWord.toNat := by
      decide +native
    simp [evalExpr?, pure, hWadEq]
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "x", .intLit WAD] =
        .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)] := by
    simp [evalExprs?, hx, hWad, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)] =
        some (endUintBinaryLocals x endWadWord) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "mul" [.var "x", .intLit WAD] "m")
        (.ok { contract := contract, locals := localsM } evm) := by
    have hbody :=
      endExecMulFunctionReturn (evm := evm) (x := x) (y := endWadWord) (prod := prod)
        hprod hfit
    have hstmt := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "mul") (retVar := "m")
      (args := [.var "x", .intLit WAD])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)])
      (callee := mulFunction) (locals := endUintBinaryLocals x endWadWord)
      hargs (by rfl) hbind hbody
    simpa [localsM, endUintBinaryLocalsM, resumeAfterInternalCall, collapseReturns] using hstmt
  have hm :
      evalExpr? config { contract := contract, locals := localsM } evm (.var "m") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsM] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsM) (name := "m") (value := prod)
      (endUintBinaryLocalsM_get_m x y prod)
  have hyExpr :
      evalExpr? config { contract := contract, locals := localsM } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [localsM] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsM) (name := "y") (value := y)
      (endUintBinaryLocalsM_get_y x y prod)
  have hDiv :
      evalExpr? config { contract := contract, locals := localsM } evm
        (.binary .div (.var "m") (.var "y")) = .revert :=
    endEvalExpr_div_uint256_revert_zero hm hyExpr hy
  have hReturn :
      evalExprs? config { contract := contract, locals := localsM } evm
        [.binary .div (.var "m") (.var "y")] = .revert := by
    simp [evalExprs?, hDiv, EvalResult.bind, bind]
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .internalCall "mul" [.var "x", .intLit WAD] "m",
          .return [.binary .div (.var "m") (.var "y")] ]
        .reverted := by
    refine ExecBlock.consNormal hmulStmt ?_
    exact ExecBlock.consRevert (ExecStmt.returnRevert hReturn)
  simpa [wdivFunction, locals, localsM] using ExecFuncBody.execBlockRevert hblock

end Benchmarks.Dss.End
