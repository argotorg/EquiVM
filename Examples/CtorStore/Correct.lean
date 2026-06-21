import Examples.CtorStore.Bytecode
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.Theory
import Reasoning.Dispatch
import Reasoning.SolmBody
import Reasoning.Reach

/-!
# CtorStore — whole-contract equivalence for a constructor storage write

The constructor takes one ABI-encoded `uint256` argument and stores it in slot 0.  The runtime has no
public transitions, so every runtime call reverts and corresponds to Solm no-dispatch.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 10000

/-! ## Runtime side -/

theorem ctorStoreDispatch_none (cd : ByteArray) :
    dispatchMsg CtorStore.contract cd = none := by
  rw [dispatchMsg_eq_dispatchList]
  rfl

set_option maxHeartbeats 400000 in
theorem ctorStoreRuntimeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ctorStoreRuntimeBytecode) :
    RDrev ctorStoreRuntimeBytecode g (initState cA gh bl σ σ₀ g A I) := by
  set s0 := initState cA gh bl σ σ₀ g A I with hs0
  have rd0 :
      RD ctorStoreRuntimeBytecode I g s0 ⟨0⟩ [] ByteArray.empty (UInt256.ofNat 0)
        ByteArray.empty (cA, σ) 0 0 := by
    rw [hs0]; exact RD.initState hcode
  exact evm_run rd0 with [
    push1 ⟨128⟩,
    push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    push0,
    push0,
    raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem ctorStoreRuntimeCorrect :
    runtimeEquivalence!?! ctorStoreConfig ctorStoreRuntimeBytecode CtorStore.contract := by
  refine ⟨fun cA gh bl σ σ₀ g A I hcode _hsize _hperm => ?_⟩
  exact (ctorStoreRuntimeRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode).reEquivNoDispatch hcode
      (ctorStoreDispatch_none I.calldata)

/-! ## Constructor side -/

/-- Solidity deployment accepts only an argument list of the constructor parameter length. -/
theorem ctorStoreDeployment_args_length {args : List Value} {deployedInitcode : ByteArray} :
    ctorStoreConfig.selfDeployment ctorStoreInitcode args = some deployedInitcode →
    args.length = CtorStore.contract.ctor.params.length := by
  intro h
  cases args with
  | nil =>
      simp [ctorStoreConfig, genSolidityConstructorDeployment, CtorStore.contract, CtorStore.ctor,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, CtorStore.uint256] at h
  | cons arg rest =>
      cases rest with
      | nil => rfl
      | cons arg2 rest =>
          cases arg <;>
            simp [ctorStoreConfig, genSolidityConstructorDeployment, CtorStore.contract,
              CtorStore.ctor, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
              CtorStore.uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h

theorem ctorStoreDeployment_shape {args : List Value} {deployedInitcode : ByteArray} :
    ctorStoreConfig.selfDeployment ctorStoreInitcode args = some deployedInitcode →
    ∃ i : Int,
      args = [.int i]
        ∧ 0 ≤ i
        ∧ i < Int.ofNat (EVM.twoPow 256)
        ∧ deployedInitcode = ctorStoreInitcode ++ (EVM.Word.toBytesBE (EVM.word i.toNat)).toByteArray := by
  intro h
  cases args with
  | nil =>
      simp [ctorStoreConfig, genSolidityConstructorDeployment, CtorStore.contract, CtorStore.ctor,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, CtorStore.uint256] at h
  | cons arg rest =>
      cases rest with
      | cons arg2 rest =>
          cases arg <;>
            simp [ctorStoreConfig, genSolidityConstructorDeployment, CtorStore.contract,
              CtorStore.ctor, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
              CtorStore.uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
      | nil =>
          cases arg with
          | int i =>
              by_cases hbounds : 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow 256)
              · simp [ctorStoreConfig, genSolidityConstructorDeployment, CtorStore.contract,
                  CtorStore.ctor, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                  CtorStore.uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?, hbounds] at h
                change (((if i < Int.ofNat (EVM.twoPow 256) then some (EVM.word i.toNat) else none).bind
                    fun word => some word.toBytesBE).bind
                    fun args => some (ctorStoreInitcode ++ args.toByteArray)) = some deployedInitcode at h
                split at h
                · simp at h
                  refine ⟨i, rfl, hbounds.1, hbounds.2, ?_⟩
                  exact h.symm
                · rename_i hnot
                  exact False.elim (hnot hbounds.2)
              · simp [ctorStoreConfig, genSolidityConstructorDeployment, CtorStore.contract,
                  CtorStore.ctor, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                  CtorStore.uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
                change (((if 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow 256) then some (EVM.word i.toNat) else none).bind
                    fun word => some word.toBytesBE).bind
                    fun args => some (ctorStoreInitcode ++ args.toByteArray)) = some deployedInitcode at h
                split at h
                · rename_i hpos
                  exact False.elim (hbounds hpos)
                · simp at h
          | bool b =>
              simp [ctorStoreConfig, genSolidityConstructorDeployment, CtorStore.contract,
                CtorStore.ctor, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                CtorStore.uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | address a =>
              simp [ctorStoreConfig, genSolidityConstructorDeployment, CtorStore.contract,
                CtorStore.ctor, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                CtorStore.uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | array xs =>
              simp [ctorStoreConfig, genSolidityConstructorDeployment, CtorStore.contract,
                CtorStore.ctor, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                CtorStore.uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | tuple xs =>
              simp [ctorStoreConfig, genSolidityConstructorDeployment, CtorStore.contract,
                CtorStore.ctor, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                CtorStore.uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | fixedBytes n bs =>
              simp [ctorStoreConfig, genSolidityConstructorDeployment, CtorStore.contract,
                CtorStore.ctor, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                CtorStore.uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | bytes =>
              simp [ctorStoreConfig, genSolidityConstructorDeployment, CtorStore.contract,
                CtorStore.ctor, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                CtorStore.uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | struct name fields =>
              simp [ctorStoreConfig, genSolidityConstructorDeployment, CtorStore.contract,
                CtorStore.ctor, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                CtorStore.uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | unit =>
              simp [ctorStoreConfig, genSolidityConstructorDeployment, CtorStore.contract,
                CtorStore.ctor, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                CtorStore.uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | storageRef er ty =>
              simp [ctorStoreConfig, genSolidityConstructorDeployment, CtorStore.contract,
                CtorStore.ctor, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                CtorStore.uint256, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h

theorem ctorStoreInitcode_size : ctorStoreInitcode.size = 28 := by
  native_decide

theorem ctorStoreRuntime_size : ctorStoreRuntimeBytecode.size = 8 := by
  native_decide

theorem ctorStoreRuntime_extract_all :
    ctorStoreRuntimeBytecode.extract 0 8 = ctorStoreRuntimeBytecode := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by native_decide)

theorem ctorStoreInitcode_runtime_window :
    ctorStoreInitcode.extract 20 (20 + 8) = ctorStoreRuntimeBytecode := by
  native_decide

theorem ctorStoreArgTail_extract (w : UInt256) :
    (ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray).extract 28 (28 + 32)
      = (EVM.Word.toBytesBE w).toByteArray := by
  exact extract_append_right' ctorStoreInitcode (EVM.Word.toBytesBE w).toByteArray 28 (28 + 32)
    ctorStoreInitcode_size.symm
    (by rw [ctorStoreInitcode_size, word_toBytesBE_toByteArray_size])

noncomputable def ctorStoreArgMem (w : UInt256) : ByteArray :=
  (ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray).write 28 ByteArray.empty 0 32

noncomputable def ctorStoreReturnMem (w : UInt256) : ByteArray :=
  (ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray).write 20 (ctorStoreArgMem w) 0 8

theorem ctorStoreArgMem_read (w : UInt256) :
    (ctorStoreArgMem w).readWithPadding 0 32 = UInt256.toByteArray w := by
  unfold ctorStoreArgMem
  rw [write0_read_back_from_gen (ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray) ByteArray.empty 28 32
    (by decide)
    (by rw [ByteArray.size_append, ctorStoreInitcode_size, word_toBytesBE_toByteArray_size])
    (by decide)]
  rw [ctorStoreArgTail_extract, word_toBytesBE_toByteArray_eq_toByteArray]

theorem ctorStoreArgMem_mload (w : UInt256) :
    (if (⟨0⟩ : UInt256).toNat ≥ (ctorStoreArgMem w).size
        ∨ (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 1) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian ((ctorStoreArgMem w).readWithPadding 0 32)))
      = w := by
  rw [if_neg]
  · rw [ctorStoreArgMem_read, fromByteArrayBigEndian_toByteArray]
    exact u256_inj (by
      show (UInt256.ofNat w.val).toNat = w.toNat
      rw [UInt256.toNat_ofNat_of_lt w.val.isLt]
      rfl)
  · intro hbad
    rcases hbad with hbad | hbad
    · unfold ctorStoreArgMem at hbad
      have hsz : ((ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray).write 28 ByteArray.empty 0 32).size ≥ 32 := by
        show ((ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray).write 28 ByteArray.empty 0 32).data.size ≥ 32
        rw [write0_data_from (ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray) ByteArray.empty 28 32
          (by decide)
          (by rw [ByteArray.size_append, ctorStoreInitcode_size, word_toBytesBE_toByteArray_size]),
          Array.size_append]
        have hpart : (((ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray).data.extract 28 (28 + 32)).size = 32) := by
          rw [Array.size_extract]
          have : (ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray).data.size
              = (ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray).size := rfl
          rw [ByteArray.size_append, ctorStoreInitcode_size, word_toBytesBE_toByteArray_size] at this
          omega
        omega
      have hz : (⟨0⟩ : UInt256).toNat = 0 := by decide
      rw [hz] at hbad
      omega
    · exact absurd hbad (by decide)

theorem ctorStoreRuntime_codecopy_mem (w : UInt256) :
    (ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray).write 20 (ctorStoreArgMem w) 0 8
      = ctorStoreReturnMem w := rfl

theorem ctorStoreFinal_read (w : UInt256) :
    (ctorStoreReturnMem w).readWithPadding 0 8 = ctorStoreRuntimeBytecode := by
  unfold ctorStoreReturnMem
  rw [write0_read_back_from_gen (ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray) (ctorStoreArgMem w)
    20 8 (by decide)
    (by rw [ByteArray.size_append, ctorStoreInitcode_size, word_toBytesBE_toByteArray_size]; omega)
    (by decide)]
  rw [show (ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray).extract 20 (20 + 8)
      = ctorStoreRuntimeBytecode from by
    rw [extract_append_left _ _ _ _ (by rw [ctorStoreInitcode_size]),
      ctorStoreInitcode_runtime_window]]

set_option maxHeartbeats 400000 in
theorem ctorStoreInitcodeRun {createdAccounts genesisBlockHeader blocks σ σ₀ A I} {g : Sat256}
    (w : UInt256)
    (hcode : I.code = ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray)
    (hperm : I.perm = true) :
    RDret (ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts, sstoreAccountMap I.codeOwner σ ⟨0⟩ w)
      ctorStoreRuntimeBytecode := by
  set code := ctorStoreInitcode ++ (EVM.Word.toBytesBE w).toByteArray with hcodeDef
  set s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I with hs0
  have rd0 :
      RD code I g s0 ⟨0⟩ [] ByteArray.empty (UInt256.ofNat 0) ByteArray.empty
        (createdAccounts, σ) 0 0 := by
    rw [hs0]; exact RD.initState hcode
  have rdBeforeStore : RD code I g s0 ⟨9⟩ [⟨0⟩, w] (ctorStoreArgMem w) (UInt256.ofNat 1)
      ByteArray.empty (createdAccounts, σ) 7 24 := by
    subst code
    exact evm_run rd0 with [
      raw push1 ⟨32⟩ (ctorStoreDecode0 _) (by evm_ov),
      raw push1 ⟨28⟩ (by simpa using ctorStoreDecode2 ((EVM.Word.toBytesBE w).toByteArray)) (by evm_ov),
      raw push0 (by simpa using ctorStoreDecode4 ((EVM.Word.toBytesBE w).toByteArray)) (by evm_ov),
      raw codecopy 3 (ctorStoreArgMem w) (UInt256.ofNat 1)
        (by simpa using ctorStoreDecode5 ((EVM.Word.toBytesBE w).toByteArray))
        mem_cost
        rfl
        (by decide) (by evm_ov),
      raw push0 (by simpa using ctorStoreDecode6 ((EVM.Word.toBytesBE w).toByteArray)) (by evm_ov),
      raw mload 0 w (UInt256.ofNat 1)
        (by simpa using ctorStoreDecode7 ((EVM.Word.toBytesBE w).toByteArray))
        mem_cost
        (ctorStoreArgMem_mload w)
        (by decide) (by evm_ov),
      raw push0 (by simpa using ctorStoreDecode8 ((EVM.Word.toBytesBE w).toByteArray)) (by evm_ov)]
  obtain ⟨k', C', rdAfterStore⟩ :=
    rdBeforeStore.sstore hperm
      (by simpa using ctorStoreDecode9 ((EVM.Word.toBytesBE w).toByteArray)) (by evm_ov)
  subst code
  exact evm_run rdAfterStore with [
    raw push1 ⟨8⟩ (by simpa using ctorStoreDecode10 ((EVM.Word.toBytesBE w).toByteArray)) (by evm_ov),
    raw push1 ⟨20⟩ (by simpa using ctorStoreDecode12 ((EVM.Word.toBytesBE w).toByteArray)) (by evm_ov),
    raw push0 (by simpa using ctorStoreDecode14 ((EVM.Word.toBytesBE w).toByteArray)) (by evm_ov),
    raw codecopy 0 (ctorStoreReturnMem w) (UInt256.ofNat 1)
      (by simpa using ctorStoreDecode15 ((EVM.Word.toBytesBE w).toByteArray))
      mem_cost
      (ctorStoreRuntime_codecopy_mem w)
      (by decide) (by evm_ov),
    raw push1 ⟨8⟩ (by simpa using ctorStoreDecode16 ((EVM.Word.toBytesBE w).toByteArray)) (by evm_ov),
    raw push0 (by simpa using ctorStoreDecode18 ((EVM.Word.toBytesBE w).toByteArray)) (by evm_ov),
    raw ret 0 ctorStoreRuntimeBytecode
      (by simpa using ctorStoreDecode19 ((EVM.Word.toBytesBE w).toByteArray))
      mem_cost
      (ctorStoreFinal_read w)
      (by evm_ov)]

/-! ## Constructor equivalence -/

theorem ctorStoreLocStore (evm : EVM.State) (i : Int) (h0 : 0 ≤ i) :
    storageLocStore evm
        { slot := ⟨0⟩, offset := 0, size := 32, hbound := by decide,
          type := .int (.uint ⟨256, by decide⟩) } (.int i)
      = some (EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ (EVM.word i.toNat)) := by
  unfold storageLocStore storageLocWriteWord
  simp only [valueToWord, wordOfInt_nonneg i h0, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof (EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (EVM.word i.toNat)).2
  congr 2
  apply u256_inj
  show fromBytes' (List.take (0:Fin 32).val _ ++ List.take (32:Fin 33).val _
        ++ List.drop ((0:Fin 32).val + (32:Fin 33).val) _) = (EVM.word i.toNat).toNat
  rw [show (0:Fin 32).val = 0 from rfl, show (32:Fin 33).val = 32 from rfl,
      List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by omega), List.append_nil,
      List.take_of_length_le (by omega), fromBytes'_toBytesLEWithSizeProof]

theorem ctorStoreAssign (evm : EVM.State) (L : Store) (i : Int)
    (h0 : 0 ≤ i) (hbase : L.get? "stored" = none) :
    assignStorageRef? ctorStoreConfig { contract := CtorStore.contract, locals := L } evm
        .storage { base := "stored", steps := [] } (.int i)
      = .ok ({ contract := CtorStore.contract, locals := L },
             EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ (EVM.word i.toNat)) := by
  have her : evalStorageRef ctorStoreConfig { contract := CtorStore.contract, locals := L } evm
      { base := "stored", steps := [] } = .ok { base := "stored", steps := [] } := by
    simp [evalStorageRef, bind, EvalResult.bind, pure]
  have hty : storageTypeAt? CtorStore.contract.storage { base := "stored", steps := [] } =
      some (.elem (.int (.uint ⟨256, by decide⟩))) := by
    simp [storageTypeAt?, CtorStore.contract]
  have hloc : ctorStoreConfig.storage.layout { base := "stored", steps := [] } =
      fun _ => some { slot := ⟨0⟩, offset := 0, size := 32, hbound := (by decide),
                      type := .int (.uint ⟨256, (by decide)⟩) } := rfl
  exact assignStorageRef_storage_scalar hbase her hty hloc (ctorStoreLocStore _ _ h0)

theorem ctorStoreCtorBodyReturns (evm : EVM.State) (locals : Store) (i : Int)
    (h0 : 0 ≤ i)
    (hx : locals.get? "x" = some (.int i))
    (hbase : locals.get? "stored" = none) :
    ExecTransitionBody ctorStoreConfig CtorStore.contract evm locals CtorStore.contract.ctor.body
      (.returned { contract := CtorStore.contract, locals := locals }
        (EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩ (EVM.word i.toNat)) none) := by
  refine ExecFuncBody.execBlockOK
    (ExecBlock.consNormal (ExecStmt.assign ?_ (ctorStoreAssign evm locals i h0 hbase)) ExecBlock.nil)
  show evalExpr? ctorStoreConfig _ evm (.var "x") = .ok (.int i)
  simp only [evalExpr?, EvalResult.ofOption, hx]

theorem ctorStoreSolmCtorExec
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (i : Int) (h0 : 0 ≤ i) :
    solmCtorExec ctorStoreConfig CtorStore.contract [.int i] createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I
      (.returned
        { contract := CtorStore.contract
          locals := Std.HashMap.ofList (List.zip (CtorStore.contract.ctor.params.map Param.name) [.int i]) }
        (EVM.storageStore
          (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
          I.codeOwner ⟨0⟩ (EVM.word i.toNat))
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := Std.HashMap.ofList (List.zip (CtorStore.contract.ctor.params.map Param.name) [.int i]))
    ?_ rfl rfl ?_
  · rfl
  · exact ctorStoreCtorBodyReturns _ _ i h0
      (by simp [CtorStore.contract, CtorStore.ctor])
      (by simp [CtorStore.contract, CtorStore.ctor])

/-- The creation/initcode bytecode refines the Solm constructor specification. -/
theorem ctorStoreConstructorCorrect :
    constructorEquivalence ctorStoreConfig ctorStoreInitcode CtorStore.contract
      ctorStoreRuntimeBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I args deployedInitcode
      hdeploy hcode _hcalldata hperm
  rcases ctorStoreDeployment_shape hdeploy with ⟨i, hargs, h0, _hlt, hdeployed⟩
  subst args
  rw [hdeployed] at hcode
  have hrd := ctorStoreInitcodeRun (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader) (blocks := blocks) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) (w := EVM.word i.toNat) hcode hperm
  rcases hrd with hoog | ⟨s, hX, hacc⟩
  · exact constructorEquivalenceFor.outOfGas
      (Xi_error_of_X (g := g) (by
        rw [← hcode] at hoog
        simpa [Sat256.ofUInt256] using hoog))
  · have hsuccess := Xi_success_of_X (g := g) (by
      rw [← hcode] at hX
      simpa [Sat256.ofUInt256] using hX)
    have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
    have hσ : s.accountMap = sstoreAccountMap I.codeOwner σ ⟨0⟩ (EVM.word i.toNat) :=
      congrArg Prod.snd hacc
    rw [hcA, hσ] at hsuccess
    refine constructorEquivalenceFor.execution hsuccess
      (ctorStoreSolmCtorExec (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ) (σ₀ := σ₀) (g := g) (A := A) (I := I) i h0) ?_
    refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
    · simp only [storageStore_createdAccounts, initState]
    · simp only [storageStore_accountMap, initState]

/-- The full contract equivalence combines constructor/initcode and runtime equivalence. -/
theorem ctorStoreCorrect :
    contractEquivalence ctorStoreConfig ctorStoreInitcode ctorStoreRuntimeBytecode
      CtorStore.contract :=
  contractEquivalence.intro ctorStoreConstructorCorrect ctorStoreRuntimeCorrect
