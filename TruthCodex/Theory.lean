import Init.Data.ByteArray.Lemmas
import Act.Equiv
import Ethereum.Theory.ProgressLemmas
import Ethereum.Theory.OpcodeLemmas

/-!
# Theory — reusable, compositional lemmas for runtime-equivalence proofs

General, **contract-agnostic** infrastructure for proving
`runtimeEquivalence!?! cfg bytecode contract`.

Lemmas in this file (and any further `TruthCodex.*` theory files) must not mention any
specific contract — they are about `runtimeEquivalenceFor`, `actExec`, `execResultsEquiv`,
`returnEquiv`, `ExecStmt`/`ExecBlock`/`ExecFuncBody`, `Ethereum.EVM.Ξ`, etc.
`TruthCorrect.lean` assembles them with the Truth-specific facts.
-/

open Act ABI

/-! ## Small data facts -/

instance : ReflBEq ByteArray where
  rfl := by
    intro a
    cases a with
    | mk data =>
      change (data == data) = true
      exact BEq.rfl

instance : LawfulBEq ByteArray where
  eq_of_beq := by
    intro a b h
    cases a with
    | mk dataA =>
      cases b with
      | mk dataB =>
        change (dataA == dataB) = true at h
        have hData : dataA = dataB := LawfulBEq.eq_of_beq h
        cases hData
        rfl

lemma ByteArray.beq_false_of_ne {a b : ByteArray} (h : a ≠ b) :
    (a == b) = false := by
  cases hbeq : (a == b)
  · rfl
  · exact False.elim (h (LawfulBEq.eq_of_beq hbeq))

namespace ByteArray

lemma toList_loop_length (bs : ByteArray) (i : Nat) (r : List UInt8) :
    (ByteArray.toList.loop bs i r).length = (bs.size - i) + r.length := by
  rw [ByteArray.toList.loop.eq_def]
  by_cases h : i < bs.size
  · simp [h, toList_loop_length bs (i + 1) (bs.get! i :: r)]
    omega
  · simp [h]
    have : bs.size - i = 0 := by omega
    simp [this]
termination_by bs.size - i

lemma length_toList (bs : ByteArray) :
    bs.toList.length = bs.size := by
  rw [ByteArray.toList.eq_1]
  simpa using toList_loop_length bs 0 []

lemma not_toList_length_lt_of_extract_eq_size {bytes selector : ByteArray} {n : Nat}
    (hSelectorSize : selector.size = n)
    (hExtract : bytes.extract 0 n = selector) :
    ¬ bytes.toList.length < n := by
  have hExtractSize : (bytes.extract 0 n).size = n := by
    rw [hExtract, hSelectorSize]
  rw [ByteArray.size_extract] at hExtractSize
  have hBytesSize : n ≤ bytes.size := by
    omega
  rw [length_toList]
  omega

end ByteArray

namespace Ethereum.UInt256

lemma eq_zero_of_val_val_eq_zero {x : Ethereum.UInt256} (h : x.val.val = 0) :
    x = (⟨0⟩ : Ethereum.UInt256) := by
  cases x with
  | mk val =>
      cases val with
      | mk n hn =>
          simp at h
          subst n
          rfl

lemma val_val_ne_zero_of_ne_zero {x : Ethereum.UInt256}
    (h : x ≠ (⟨0⟩ : Ethereum.UInt256)) :
    x.val.val ≠ 0 :=
  fun hZero => h (eq_zero_of_val_val_eq_zero hZero)

lemma ofNat_toNat_of_lt {n : Nat} (hn : n < Ethereum.UInt256.size) :
    (Ethereum.UInt256.ofNat n).toNat = n := by
  unfold Ethereum.UInt256.ofNat Ethereum.UInt256.toNat
  simp [Id.run, Nat.mod_eq_of_lt hn]

lemma toNat_sub_ofNat_of_le {x : Ethereum.UInt256} {n : Nat}
    (hn : n < Ethereum.UInt256.size)
    (h : n ≤ x.toNat) :
    (x - Ethereum.UInt256.ofNat n).toNat = x.toNat - n := by
  cases x with
  | mk xv =>
      unfold Ethereum.UInt256.toNat at h
      have hVal : (Fin.ofNat Ethereum.UInt256.size n).val = n := by
        simp [Nat.mod_eq_of_lt hn]
      have hLe : Fin.ofNat Ethereum.UInt256.size n ≤ xv := by
        rw [Fin.le_iff_val_le_val]
        rw [hVal]
        exact h
      change (xv - Fin.ofNat Ethereum.UInt256.size n).val = xv.val - n
      rw [Fin.sub_val_of_le hLe]
      rw [hVal]

lemma add_le_toNat_of_not_sub_ofNat_lt {x : Ethereum.UInt256} {cost remaining : Nat}
    (hCostSize : cost < Ethereum.UInt256.size)
    (hCost : cost ≤ x.toNat)
    (hRemaining :
      ¬ (x - Ethereum.UInt256.ofNat cost).toNat < remaining) :
    cost + remaining ≤ x.toNat := by
  have hSub := toNat_sub_ofNat_of_le (x := x) (n := cost) hCostSize hCost
  rw [hSub] at hRemaining
  omega

end Ethereum.UInt256

lemma Ethereum_toBytes'_one : Ethereum.toBytes' 1 = [1] := by
  unfold Ethereum.toBytes'
  simp
  constructor
  · decide
  · unfold Ethereum.toBytes'
    rfl

namespace ABI

lemma decodeCalldata_no_params_of_not_lt {calldata : ByteArray}
    (hSize : ¬ calldata.toList.length < 4) :
    decodeCalldata [] [] calldata = some (∅ : Store) := by
  simp [decodeCalldata, decodeCalldata.decodeArgs, hSize]

lemma decodeCalldata_no_params_of_lt {calldata : ByteArray}
    (hSize : calldata.toList.length < 4) :
    decodeCalldata [] [] calldata = none := by
  simp [decodeCalldata, hSize]

end ABI

/-! ## Dispatch helpers -/

lemma dispatchMsg_singleton_some_of_selector
    {contract : ContractDecl} {transition : TransitionDecl} {selector calldata : ByteArray}
    (hTransitions : contract.transitions = [transition])
    (hHash :
      (ffi.KEC (String.toByteArray (transitionSigStr transition))).extract 0 4 = selector)
    (hSelector : calldata.extract 0 4 = selector) :
    dispatchMsg contract calldata = some transition := by
  simp [dispatchMsg, hTransitions, hHash, hSelector]

lemma dispatchMsg_singleton_none_of_selector_ne
    {contract : ContractDecl} {transition : TransitionDecl} {selector calldata : ByteArray}
    (hTransitions : contract.transitions = [transition])
    (hHash :
      (ffi.KEC (String.toByteArray (transitionSigStr transition))).extract 0 4 = selector)
    (hSelector : calldata.extract 0 4 ≠ selector) :
    dispatchMsg contract calldata = none := by
  have hBeq : (selector == calldata.extract 0 4) = false :=
    ByteArray.beq_false_of_ne (fun h => hSelector h.symm)
  simp [dispatchMsg, hTransitions, hHash, hBeq]

/-! ## Runtime-equivalence constructors as compositional helpers -/

lemma runtimeEquivalence_intro
    {cfg : Config} {bytecode : ByteArray} {contract : ContractDecl}
    (h :
      ∀ (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
        (genesisBlockHeader : Ethereum.BlockHeader)
        (blocks : Ethereum.ProcessedBlocks)
        (σ : Ethereum.AccountMap)
        (σ₀ : Ethereum.AccountMap)
        (g : Ethereum.UInt256)
        (A : Ethereum.Substate)
        (I : Ethereum.ExecutionEnv),
        I.code = bytecode →
        I.calldata.size < Ethereum.UInt256.size →
        runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I) :
    runtimeEquivalence!?! cfg bytecode contract :=
  runtimeEquivalence!?!.intro h

lemma runtimeEquivalenceFor_execution
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {Ξ_res actRes returnType}
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = Ξ_res)
    (hAct :
      actExec cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I actRes returnType)
    (hEquiv : execResultsEquiv Ξ_res actRes returnType) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor.execution hΞ hAct hEquiv

lemma runtimeEquivalenceFor_noDispatch
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g g' : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {o : ByteArray}
    (hDispatch : dispatchMsg contract I.calldata = none)
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.revert g' o)) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor.noDispatch hDispatch hΞ

lemma runtimeEquivalenceFor_decodingFailed
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g g' : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {transition transitionSig o}
    (hDispatch : dispatchMsg contract I.calldata = some transition)
    (hSig : transitionSig = transitionSignature transition)
    (hDecode :
      decodeCalldata (transition.params.map Param.name) transitionSig.paramTypes I.calldata =
        none)
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.revert g' o)) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor.decodingFailed hDispatch hSig hDecode hΞ

lemma runtimeEquivalenceFor_outOfGas
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .error .OutOfGass) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor.outOfGas hΞ

/-! ## Initial EVM state used by `Ξ` and `actExec` -/

def initialEVMState
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader)
    (blocks : Ethereum.ProcessedBlocks)
    (σ : Ethereum.AccountMap)
    (σ₀ : Ethereum.AccountMap)
    (g : Ethereum.UInt256)
    (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : EVM.State :=
  { (default : EVM.State) with
    accountMap := σ
    σ₀ := σ₀
    executionEnv := I
    substate := A
    createdAccounts := createdAccounts
    machineState.gasAvailable := g
    blocks := blocks
    genesisBlockHeader := genesisBlockHeader }

@[simp] lemma initialEVMState_accountMap
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).accountMap = σ :=
  rfl

@[simp] lemma initialEVMState_createdAccounts
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).createdAccounts =
      createdAccounts :=
  rfl

@[simp] lemma initialEVMState_executionEnv
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
      (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).executionEnv = I :=
  rfl

@[simp] lemma initialEVMState_gasAvailable
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).machineState.gasAvailable =
      g :=
  rfl

@[simp] lemma initialEVMState_pc
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).machineState.pc =
      (⟨0⟩ : Ethereum.UInt256) :=
  rfl

@[simp] lemma initialEVMState_stack
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).machineState.stack =
      ([] : Ethereum.Stack Ethereum.UInt256) :=
  rfl

@[simp] lemma initialEVMState_execLength
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ : Ethereum.AccountMap}
    {σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I).machineState.execLength =
      0 :=
  rfl

/-! ## Return/result equivalence helpers -/

namespace returnEquiv

lemma returned_of_encode {o : ByteArray} {rv : Value} {abit : ABIType}
    (hEncode : encodeReturnValue? abit rv = some o) :
    returnEquiv o (some rv) (some abit) :=
  returnEquiv.returned rfl rfl hEncode

lemma void_of_null {o : ByteArray} (ho : o = null) :
    returnEquiv o none none :=
  returnEquiv.void rfl rfl ho

lemma fallthrough_of_default {o : ByteArray} {abit : ABIType} {dv : Value}
    (hDefault : defaultAbiValue abit = some dv)
    (hEncode : encodeReturnValue? abit dv = some o) :
    returnEquiv o none (some abit) :=
  returnEquiv.fallthrough rfl rfl hDefault hEncode

end returnEquiv

def abiBoolTrueReturn : ByteArray :=
  ByteArray.mk #[
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1
  ]

lemma encodeReturnValue_bool_true :
    encodeReturnValue? (.elem .bool) (.bool true) = some abiBoolTrueReturn := by
  simp [abiBoolTrueReturn, encodeReturnValue?, encodeReturnValues?, encodeABIValues?,
    encodeABIValuesFrom?, encodeABIValue?, encodeABIWord?, EVM.Word.toBytesBE,
    Ethereum.toBytesBigEndian, Ethereum.UInt256.ofNat, Ethereum.UInt256.size, Id.run,
    abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, Ethereum_toBytes'_one]

lemma returnEquiv_bool_true :
    returnEquiv abiBoolTrueReturn (some (.bool true)) (some (.elem .bool)) :=
  returnEquiv.returned_of_encode encodeReturnValue_bool_true

namespace execResultsEquiv

lemma success_of_returnEquiv
    {evmRes :
      Except Ethereum.EVM.ExecutionException
        (Ethereum.ExecutionResult
          (Batteries.RBSet Ethereum.AccountAddress compare × Ethereum.AccountMap ×
            Ethereum.UInt256 × Ethereum.Substate))}
    {actRes : ExecResult}
    {t : Option ABIType}
    {createdAccounts' : Batteries.RBSet Ethereum.AccountAddress compare}
    {σ' : Ethereum.AccountMap}
    {g' : Ethereum.UInt256}
    {A' : Ethereum.Substate}
    {o : ByteArray}
    {frame : Frame}
    {actState : EVM.State}
    {retVal : Option Value}
    (hEvm : evmRes = .ok (.success (createdAccounts', σ', g', A') o))
    (hAct : actRes = .returned frame actState retVal)
    (hCreated : createdAccounts' = actState.createdAccounts)
    (hAccounts : σ' = actState.accountMap)
    (hReturn : returnEquiv o retVal t) :
    execResultsEquiv evmRes actRes t :=
  execResultsEquiv.success hEvm hAct hCreated hAccounts hReturn

lemma success_rfl
    {t : Option ABIType}
    {g' : Ethereum.UInt256}
    {A' : Ethereum.Substate}
    {o : ByteArray}
    {frame : Frame}
    {actState : EVM.State}
    {retVal : Option Value}
    (hReturn : returnEquiv o retVal t) :
    execResultsEquiv
      (.ok (.success (actState.createdAccounts, actState.accountMap, g', A') o))
      (.returned frame actState retVal)
      t :=
  execResultsEquiv.success rfl rfl rfl rfl hReturn

lemma revert_rfl {g : Ethereum.UInt256} {o : ByteArray} {t : Option ABIType} :
    execResultsEquiv (.ok (.revert g o)) .reverted t :=
  execResultsEquiv.revert rfl rfl

lemma error_rfl {e : Ethereum.EVM.ExecutionException} {t : Option ABIType} :
    execResultsEquiv (.error e) .reverted t :=
  execResultsEquiv.error rfl rfl

end execResultsEquiv

/-! ## Act execution helpers -/

lemma actExec_of_dispatch_decode_exec
    {conf : Config}
    {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {actRes : ExecResult}
    {transition transitionSig callargs evmState}
    (hDispatch : dispatchMsg contract I.calldata = some transition)
    (hSig : transitionSig = transitionSignature transition)
    (hDecode :
      decodeCalldata (transition.params.map Param.name) transitionSig.paramTypes I.calldata =
        some callargs)
    (hState :
      evmState =
        { (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := createdAccounts
          machineState.gasAvailable := g
          blocks := blocks
          genesisBlockHeader := genesisBlockHeader })
    (hExec : ExecContractBody conf contract evmState callargs transition.body actRes) :
    actExec conf contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I actRes
      transition.returnType :=
  actExec.intro hDispatch hSig hDecode hState hExec

lemma actExec_of_dispatch_decode_initial
    {conf : Config}
    {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {actRes : ExecResult}
    {transition transitionSig callargs}
    (hDispatch : dispatchMsg contract I.calldata = some transition)
    (hSig : transitionSig = transitionSignature transition)
    (hDecode :
      decodeCalldata (transition.params.map Param.name) transitionSig.paramTypes I.calldata =
        some callargs)
    (hExec :
      ExecContractBody conf contract
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
        callargs transition.body actRes) :
    actExec conf contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I actRes
      transition.returnType :=
  actExec_of_dispatch_decode_exec
    (evmState := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    hDispatch hSig hDecode rfl hExec

lemma runtimeEquivalenceFor_success_initial
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g g' : Ethereum.UInt256}
    {A A' : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {frame : Frame}
    {retVal : Option Value}
    {returnType : Option ABIType}
    {o : ByteArray}
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.success (createdAccounts, σ, g', A') o))
    (hAct :
      actExec cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
        (.returned frame
          (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
          retVal)
        returnType)
    (hReturn : returnEquiv o retVal returnType) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor_execution hΞ hAct
    (execResultsEquiv.success rfl rfl rfl rfl hReturn)

lemma runtimeEquivalenceFor_revert_of_act_reverted
    {cfg : Config} {contract : ContractDecl}
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g g' : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {returnType : Option ABIType}
    {o : ByteArray}
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.revert g' o))
    (hAct :
      actExec cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
        .reverted returnType) :
    runtimeEquivalenceFor cfg contract createdAccounts genesisBlockHeader blocks σ σ₀ g A I :=
  runtimeEquivalenceFor_execution hΞ hAct execResultsEquiv.revert_rfl

/-! ## Relating EVM `X` traces to top-level `Ξ` results -/

lemma EVM_Xi_of_X_success
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {evmState : Ethereum.State}
    {o : ByteArray}
    (hX :
      Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .ok (.success evmState o)) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        (evmState.createdAccounts, evmState.accountMap, evmState.machineState.gasAvailable,
          evmState.substate) o) := by
  unfold Ethereum.EVM.Ξ
  change (do
      let result ← Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      match result with
      | Ethereum.ExecutionResult.success st out =>
          .ok (Ethereum.ExecutionResult.success
            (st.createdAccounts, st.accountMap, st.machineState.gasAvailable, st.substate) out)
      | Ethereum.ExecutionResult.revert gas out => .ok (Ethereum.ExecutionResult.revert gas out)) =
    .ok (.success
      (evmState.createdAccounts, evmState.accountMap, evmState.machineState.gasAvailable,
        evmState.substate) o)
  simp [hX, bind, Except.bind]

lemma EVM_Xi_of_X_revert
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g g' : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {o : ByteArray}
    (hX :
      Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .ok (.revert g' o)) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert g' o) := by
  unfold Ethereum.EVM.Ξ
  change (do
      let result ← Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      match result with
      | Ethereum.ExecutionResult.success st out =>
          .ok (Ethereum.ExecutionResult.success
            (st.createdAccounts, st.accountMap, st.machineState.gasAvailable, st.substate) out)
      | Ethereum.ExecutionResult.revert gas out => .ok (Ethereum.ExecutionResult.revert gas out)) =
    .ok (.revert g' o)
  simp [hX, bind, Except.bind]

lemma EVM_Xi_of_X_error
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {e : Ethereum.EVM.ExecutionException}
    (hX :
      Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e := by
  unfold Ethereum.EVM.Ξ
  change (do
      let result ← Ethereum.EVM.X (g.toNat + 1) (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      match result with
      | Ethereum.ExecutionResult.success st out =>
          .ok (Ethereum.ExecutionResult.success
            (st.createdAccounts, st.accountMap, st.machineState.gasAvailable, st.substate) out)
      | Ethereum.ExecutionResult.revert gas out => .ok (Ethereum.ExecutionResult.revert gas out)) =
    .error e
  simp [hX, bind, Except.bind]

lemma EVM_Xi_of_initial_Xstep_success
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {evmState : Ethereum.State}
    {o : ByteArray}
    (hStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .ok (evmState, some (true, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        (evmState.createdAccounts, evmState.accountMap, evmState.machineState.gasAvailable,
          evmState.substate) o) :=
  EVM_Xi_of_X_success
    (Ethereum.EVM.Xstep_X_X_halt_success g.toNat
      (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      evmState (Ethereum.EVM.D_J I.code ⟨0⟩) o hStep)

lemma EVM_Xi_of_initial_Xstep_revert
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {evmState : Ethereum.State}
    {o : ByteArray}
    (hStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .ok (evmState, some (false, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert evmState.machineState.gasAvailable o) :=
  EVM_Xi_of_X_revert
    (Ethereum.EVM.Xstep_X_X_halt_revert g.toNat
      (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      evmState (Ethereum.EVM.D_J I.code ⟨0⟩) o hStep)

lemma EVM_Xi_of_initial_Xstep_error
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {e : Ethereum.EVM.ExecutionException}
    (hStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩)
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) =
        .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_X_error
    (Ethereum.EVM.Xstep_X_X_except g.toNat
      (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (Ethereum.EVM.D_J I.code ⟨0⟩) e hStep)

namespace Ethereum.EVM

/-! ### Small opcode-step wrappers -/

def push1NextState (s : Ethereum.State) (arg : Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := arg :: s.machineState.stack
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + Ethereum.UInt256.ofNat 2
    machineState.execLength := s.machineState.execLength + 1}

theorem Xstep_push1_oog_of_decode {s : Ethereum.State} {arg : Ethereum.UInt256}
    (hDecode :
      decode s.executionEnv.code s.machineState.pc = some (.PUSH1, .some (arg, 1)))
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_push1 s arg hDecode
  simpa [hGas] using hStep

theorem Xstep_push1_continue_of_decode {s : Ethereum.State} {arg : Ethereum.UInt256}
    (hDecode :
      decode s.executionEnv.code s.machineState.pc = some (.PUSH1, .some (arg, 1)))
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStack : s.machineState.stack.length < 1024) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (push1NextState s arg, none) := by
  have hStep := step_push1 s arg hDecode
  have hNoOverflow : ¬ s.machineState.stack.length - 0 + 1 > 1024 := by
    omega
  have hNoOverflow' : ¬ 1024 < s.machineState.stack.length + 1 := by
    omega
  simpa [push1NextState, hGas, hNoOverflow, hNoOverflow'] using hStep

def mstoreNextState (s : Ethereum.State) (a b : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  let memoryCost := memoryExpansionCost s .MSTORE
  let gasAvailable' := s.machineState.gasAvailable - Ethereum.UInt256.ofNat memoryCost
  {s with
    machineState.stack := t
    machineState.memory := b.toByteArray.write 0 s.machineState.memory a.toNat 32
    machineState.activeWords :=
      Ethereum.UInt256.ofNat
        (Ethereum.MachineState.M s.machineState.activeWords.toNat a.toNat 32)
    machineState.gasAvailable := gasAvailable' - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

theorem Xstep_mstore_memory_oog_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.MSTORE, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hMemGas : s.machineState.gasAvailable.toNat < memoryExpansionCost s .MSTORE) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_mstore s hDecode
  simpa [hStack, hMemGas] using hStep

theorem Xstep_mstore_verylow_oog_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.MSTORE, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hMemGas : ¬ s.machineState.gasAvailable.toNat < memoryExpansionCost s .MSTORE)
    (hVerylowGas :
      (s.machineState.gasAvailable - Ethereum.UInt256.ofNat (memoryExpansionCost s .MSTORE)).toNat <
        GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_mstore s hDecode
  simpa [hStack, hMemGas, hVerylowGas] using hStep

theorem Xstep_mstore_continue_of_decode {s : Ethereum.State}
    {a b : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.MSTORE, .none))
    (hStack : s.machineState.stack = a :: b :: t)
    (hMemGas : ¬ s.machineState.gasAvailable.toNat < memoryExpansionCost s .MSTORE)
    (hVerylowGas :
      ¬ (s.machineState.gasAvailable - Ethereum.UInt256.ofNat (memoryExpansionCost s .MSTORE)).toNat <
        GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (mstoreNextState s a b t, none) := by
  have hStep := step_mstore s hDecode
  simpa [mstoreNextState, hStack, hMemGas, hVerylowGas, hStackBound] using hStep

def callvalueNextState (s : Ethereum.State) : Ethereum.State :=
  {s with
    machineState.stack := s.executionEnv.weiValue :: s.machineState.stack
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

theorem Xstep_callvalue_oog_of_decode {s : Ethereum.State}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.CALLVALUE, .none))
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gbase) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_callvalue s hDecode
  simpa [hGas] using hStep

theorem Xstep_callvalue_continue_of_decode {s : Ethereum.State}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.CALLVALUE, .none))
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase)
    (hStack : s.machineState.stack.length < 1024) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (callvalueNextState s, none) := by
  have hStep := step_callvalue s hDecode
  have hNoOverflow : ¬ s.machineState.stack.length - 0 + 1 > 1024 := by
    omega
  have hNoOverflow' : ¬ 1024 < s.machineState.stack.length + 1 := by
    omega
  simpa [callvalueNextState, hGas, hNoOverflow, hNoOverflow'] using hStep

def dup1NextState (s : Ethereum.State) (a : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := a :: a :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

theorem Xstep_dup1_oog_of_decode {s : Ethereum.State}
    {a : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.DUP1, .none))
    (hStack : s.machineState.stack = a :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_dup1 s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_dup1_continue_of_decode {s : Ethereum.State}
    {a : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.DUP1, .none))
    (hStack : s.machineState.stack = a :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 2) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (dup1NextState s a t, none) := by
  have hStep := step_dup1 s hDecode
  simpa [dup1NextState, hStack, hGas, hStackBound] using hStep

def iszeroNextState (s : Ethereum.State) (a : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := Ethereum.UInt256.isZero a :: t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gverylow
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

theorem Xstep_iszero_oog_of_decode {s : Ethereum.State}
    {a : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.ISZERO, .none))
    (hStack : s.machineState.stack = a :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gverylow) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_iszero s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_iszero_continue_of_decode {s : Ethereum.State}
    {a : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.ISZERO, .none))
    (hStack : s.machineState.stack = a :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gverylow)
    (hStackBound : ¬ 1024 < t.length + 1) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (iszeroNextState s a t, none) := by
  have hStep := step_iszero s hDecode
  simpa [iszeroNextState, hStack, hGas, hStackBound] using hStep

def push0NextState (s : Ethereum.State) : Ethereum.State :=
  {s with
    machineState.stack := (⟨0⟩ : Ethereum.UInt256) :: s.machineState.stack
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Gbase
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

theorem Xstep_push0_oog_of_decode {s : Ethereum.State}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.PUSH0, .none))
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Gbase) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_push0 s hDecode
  simpa [hGas] using hStep

theorem Xstep_push0_continue_of_decode {s : Ethereum.State}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.PUSH0, .none))
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Gbase)
    (hStack : s.machineState.stack.length < 1024) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .ok (push0NextState s, none) := by
  have hStep := step_push0 s hDecode
  have hNoOverflow : ¬ s.machineState.stack.length - 0 + 1 > 1024 := by
    omega
  have hNoOverflow' : ¬ 1024 < s.machineState.stack.length + 1 := by
    omega
  simpa [push0NextState, hGas, hNoOverflow, hNoOverflow'] using hStep

def jumpiNextState (s : Ethereum.State) (dest cond : Ethereum.UInt256)
    (t : Ethereum.Stack Ethereum.UInt256) : Ethereum.State :=
  {s with
    machineState.stack := t
    machineState.gasAvailable := s.machineState.gasAvailable - Ethereum.UInt256.ofNat GasConstants.Ghigh
    machineState.pc := if cond != (⟨0⟩ : Ethereum.UInt256) then dest else s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1}

theorem Xstep_jumpi_oog_of_decode {s : Ethereum.State}
    {dest cond : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.JUMPI, .none))
    (hStack : s.machineState.stack = dest :: cond :: t)
    (hGas : s.machineState.gasAvailable.toNat < GasConstants.Ghigh) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .OutOfGass := by
  have hStep := step_jumpi s hDecode
  simpa [hStack, hGas] using hStep

theorem Xstep_jumpi_bad_dest_of_decode {s : Ethereum.State}
    {dest cond : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.JUMPI, .none))
    (hStack : s.machineState.stack = dest :: cond :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Ghigh)
    (hCond : (cond != (⟨0⟩ : Ethereum.UInt256)) = true)
    (hDest : ¬ (D_J s.executionEnv.code ⟨0⟩).contains dest = true) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s = .error .BadJumpDestination := by
  have hStep := step_jumpi s hDecode
  have hBad :
      (cond != (⟨0⟩ : Ethereum.UInt256)) = true ∧
        ¬ (D_J s.executionEnv.code ⟨0⟩).contains dest = true :=
    ⟨hCond, hDest⟩
  simpa [hStack, hGas, hBad] using hStep

theorem Xstep_jumpi_continue_of_decode {s : Ethereum.State}
    {dest cond : Ethereum.UInt256} {t : Ethereum.Stack Ethereum.UInt256}
    (hDecode : decode s.executionEnv.code s.machineState.pc = some (.JUMPI, .none))
    (hStack : s.machineState.stack = dest :: cond :: t)
    (hGas : ¬ s.machineState.gasAvailable.toNat < GasConstants.Ghigh)
    (hNoBad :
      (cond != (⟨0⟩ : Ethereum.UInt256)) = true →
        (D_J s.executionEnv.code ⟨0⟩).contains dest = true)
    (hStackBound : ¬ 1024 < t.length) :
    Xstep (D_J s.executionEnv.code ⟨0⟩) s =
      .ok (jumpiNextState s dest cond t, none) := by
  have hStep := step_jumpi s hDecode
  have hBadFalse :
      ¬ ((cond != (⟨0⟩ : Ethereum.UInt256)) = true ∧
        (D_J s.executionEnv.code ⟨0⟩).contains dest = false) := by
    intro hBad
    have hContains := hNoBad hBad.1
    rw [hContains] at hBad
    simp at hBad
  have hNoOverflow : ¬ (dest :: cond :: t).length - 2 + 0 > 1024 := by
    simpa using hStackBound
  simpa [jumpiNextState, hStack, hGas, hBadFalse, hStackBound, hNoOverflow] using hStep

/-- A finite prefix of non-halting EVM `Xstep`s. `ContinueTrace validJumps n s t`
means `Xstep` runs from `s` to `t` in exactly `n` continuing steps. -/
inductive ContinueTrace (validJumps : Array Ethereum.UInt256) :
    Nat → Ethereum.State → Ethereum.State → Prop where
  | nil {s} : ContinueTrace validJumps 0 s s
  | cons {n s s' t} :
      Xstep validJumps s = .ok (s', none) →
      ContinueTrace validJumps n s' t →
      ContinueTrace validJumps (n + 1) s t

namespace ContinueTrace

theorem one {validJumps : Array Ethereum.UInt256} {s t : Ethereum.State}
    (hStep : Xstep validJumps s = .ok (t, none)) :
    ContinueTrace validJumps 1 s t := by
  simpa using (ContinueTrace.cons hStep ContinueTrace.nil)

theorem two {validJumps : Array Ethereum.UInt256} {s t u : Ethereum.State}
    (hStep₁ : Xstep validJumps s = .ok (t, none))
    (hStep₂ : Xstep validJumps t = .ok (u, none)) :
    ContinueTrace validJumps 2 s u := by
  simpa using
    (ContinueTrace.cons hStep₁ (ContinueTrace.cons hStep₂ ContinueTrace.nil))

theorem three {validJumps : Array Ethereum.UInt256} {s t u v : Ethereum.State}
    (hStep₁ : Xstep validJumps s = .ok (t, none))
    (hStep₂ : Xstep validJumps t = .ok (u, none))
    (hStep₃ : Xstep validJumps u = .ok (v, none)) :
    ContinueTrace validJumps 3 s v := by
  simpa using
    (ContinueTrace.cons hStep₁
      (ContinueTrace.cons hStep₂ (ContinueTrace.cons hStep₃ ContinueTrace.nil)))

theorem snoc {validJumps : Array Ethereum.UInt256}
    {n : Nat} {s t u : Ethereum.State}
    (hTrace : ContinueTrace validJumps n s t)
    (hStep : Xstep validJumps t = .ok (u, none)) :
    ContinueTrace validJumps (n + 1) s u := by
  induction hTrace with
  | nil =>
      simpa using (ContinueTrace.cons hStep ContinueTrace.nil)
  | cons hHead _ ih =>
      have hRest := ih hStep
      simpa [Nat.add_assoc] using (ContinueTrace.cons hHead hRest)

theorem X_halt_success {validJumps : Array Ethereum.UInt256}
    {n : Nat} {s t u : Ethereum.State} {o : ByteArray}
    (hTrace : ContinueTrace validJumps n s t)
    (hHalt : Xstep validJumps t = .ok (u, some (true, o))) :
    X (n + 1) validJumps s = .ok (.success u o) := by
  induction hTrace with
  | nil =>
      simpa using Xstep_X_X_halt_success 0 _ u validJumps o hHalt
  | cons hStep hRest ih =>
      exact Xstep_X_X_continue _ _ _ _ _ hStep (ih hHalt)

theorem X_halt_success_with_fuel {validJumps : Array Ethereum.UInt256}
    {n fuel : Nat} {s t u : Ethereum.State} {o : ByteArray}
    (hTrace : ContinueTrace validJumps n s t)
    (hHalt : Xstep validJumps t = .ok (u, some (true, o))) :
    X (n + fuel + 1) validJumps s = .ok (.success u o) := by
  induction hTrace with
  | nil =>
      simpa using Xstep_X_X_halt_success fuel _ u validJumps o hHalt
  | cons hStep _ ih =>
      have hX := Xstep_X_X_continue _ _ _ _ _ hStep (ih hHalt)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hX

theorem X_halt_revert {validJumps : Array Ethereum.UInt256}
    {n : Nat} {s t u : Ethereum.State} {o : ByteArray}
    (hTrace : ContinueTrace validJumps n s t)
    (hHalt : Xstep validJumps t = .ok (u, some (false, o))) :
    X (n + 1) validJumps s = .ok (.revert u.machineState.gasAvailable o) := by
  induction hTrace with
  | nil =>
      simpa using Xstep_X_X_halt_revert 0 _ u validJumps o hHalt
  | cons hStep hRest ih =>
      exact Xstep_X_X_continue _ _ _ _ _ hStep (ih hHalt)

theorem X_halt_revert_with_fuel {validJumps : Array Ethereum.UInt256}
    {n fuel : Nat} {s t u : Ethereum.State} {o : ByteArray}
    (hTrace : ContinueTrace validJumps n s t)
    (hHalt : Xstep validJumps t = .ok (u, some (false, o))) :
    X (n + fuel + 1) validJumps s = .ok (.revert u.machineState.gasAvailable o) := by
  induction hTrace with
  | nil =>
      simpa using Xstep_X_X_halt_revert fuel _ u validJumps o hHalt
  | cons hStep _ ih =>
      have hX := Xstep_X_X_continue _ _ _ _ _ hStep (ih hHalt)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hX

theorem X_error {validJumps : Array Ethereum.UInt256}
    {n : Nat} {s t : Ethereum.State} {e : ExecutionException}
    (hTrace : ContinueTrace validJumps n s t)
    (hErr : Xstep validJumps t = .error e) :
    X (n + 1) validJumps s = .error e := by
  induction hTrace with
  | nil =>
      simpa using Xstep_X_X_except 0 _ validJumps e hErr
  | cons hStep hRest ih =>
      exact Xstep_X_X_continue _ _ _ _ _ hStep (ih hErr)

theorem X_error_with_fuel {validJumps : Array Ethereum.UInt256}
    {n fuel : Nat} {s t : Ethereum.State} {e : ExecutionException}
    (hTrace : ContinueTrace validJumps n s t)
    (hErr : Xstep validJumps t = .error e) :
    X (n + fuel + 1) validJumps s = .error e := by
  induction hTrace with
  | nil =>
      simpa using Xstep_X_X_except fuel _ validJumps e hErr
  | cons hStep _ ih =>
      have hX := Xstep_X_X_continue _ _ _ _ _ hStep (ih hErr)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hX

end ContinueTrace

end Ethereum.EVM

lemma EVM_Xi_of_initial_continue_trace_success
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n fuel : Nat}
    {t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel : g.toNat = n + fuel)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (true, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success
        (evmState.createdAccounts, evmState.accountMap, evmState.machineState.gasAvailable,
          evmState.substate) o) :=
  EVM_Xi_of_X_success (by
    have hX := Ethereum.EVM.ContinueTrace.X_halt_success_with_fuel
      (fuel := fuel) hTrace hHalt
    simpa [hFuel, Nat.add_assoc] using hX)

lemma EVM_Xi_of_initial_continue_trace_revert
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n fuel : Nat}
    {t evmState : Ethereum.State}
    {o : ByteArray}
    (hFuel : g.toNat = n + fuel)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hHalt :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t =
        .ok (evmState, some (false, o))) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.revert evmState.machineState.gasAvailable o) :=
  EVM_Xi_of_X_revert (by
    have hX := Ethereum.EVM.ContinueTrace.X_halt_revert_with_fuel
      (fuel := fuel) hTrace hHalt
    simpa [hFuel, Nat.add_assoc] using hX)

lemma EVM_Xi_of_initial_continue_trace_error
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {n fuel : Nat}
    {t : Ethereum.State}
    {e : Ethereum.EVM.ExecutionException}
    (hFuel : g.toNat = n + fuel)
    (hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) n
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) t)
    (hErr :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) t = .error e) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I = .error e :=
  EVM_Xi_of_X_error (by
    have hX := Ethereum.EVM.ContinueTrace.X_error_with_fuel
      (fuel := fuel) hTrace hErr
    simpa [hFuel, Nat.add_assoc] using hX)

namespace Act

lemma ExecStmt.require_true_of_eval {cfg : Config} {act : Frame} {evm : EVM.State}
    {condExpr : Expr}
    (hEval : evalExpr? cfg act evm condExpr = .ok (.bool true)) :
    ExecStmt cfg act evm (.require condExpr) (.ok act evm) :=
  ExecStmt.requireTrue hEval

lemma ExecStmt.require_false_of_eval {cfg : Config} {act : Frame} {evm : EVM.State}
    {condExpr : Expr}
    (hEval : evalExpr? cfg act evm condExpr = .ok (.bool false)) :
    ExecStmt cfg act evm (.require condExpr) .reverted :=
  ExecStmt.requireFalse hEval

lemma ExecStmt.require_revert_of_eval {cfg : Config} {act : Frame} {evm : EVM.State}
    {condExpr : Expr}
    (hEval : evalExpr? cfg act evm condExpr = .revert) :
    ExecStmt cfg act evm (.require condExpr) .reverted :=
  ExecStmt.requireRevert hEval

lemma ExecStmt.return_of_eval {cfg : Config} {act : Frame} {evm : EVM.State}
    {expr : Expr} {value : Value}
    (hEval : evalExpr? cfg act evm expr = .ok value) :
    ExecStmt cfg act evm (.return expr) (.returned act evm (some value)) :=
  ExecStmt.return hEval

lemma ExecBlock.cons_ok {cfg : Config} {act act' : Frame} {evm evm' : EVM.State}
    {stmt : Stmt} {stmts : List Stmt} {result : ExecResult}
    (hStmt : ExecStmt cfg act evm stmt (.ok act' evm'))
    (hRest : ExecBlock cfg act' evm' stmts result) :
    ExecBlock cfg act evm (stmt :: stmts) result :=
  ExecBlock.consNormal hStmt hRest

lemma ExecBlock.cons_return {cfg : Config} {act act' : Frame} {evm evm' : EVM.State}
    {stmt : Stmt} {stmts : List Stmt} {value : Option Value}
    (hStmt : ExecStmt cfg act evm stmt (.returned act' evm' value)) :
    ExecBlock cfg act evm (stmt :: stmts) (.returned act' evm' value) :=
  ExecBlock.consReturn hStmt

lemma ExecBlock.cons_revert {cfg : Config} {act : Frame} {evm : EVM.State}
    {stmt : Stmt} {stmts : List Stmt}
    (hStmt : ExecStmt cfg act evm stmt .reverted) :
    ExecBlock cfg act evm (stmt :: stmts) .reverted :=
  ExecBlock.consRevert hStmt

lemma ExecBlock.require_true_then_return {cfg : Config} {act : Frame} {evm : EVM.State}
    {condExpr retExpr : Expr} {value : Value}
    (hCond : evalExpr? cfg act evm condExpr = .ok (.bool true))
    (hRet : evalExpr? cfg act evm retExpr = .ok value) :
    ExecBlock cfg act evm
      [.require condExpr, .return retExpr]
      (.returned act evm (some value)) :=
  ExecBlock.consNormal
    (ExecStmt.require_true_of_eval hCond)
    (ExecBlock.consReturn (ExecStmt.return_of_eval hRet))

lemma ExecBlock.require_false_then_revert {cfg : Config} {act : Frame} {evm : EVM.State}
    {condExpr retExpr : Expr}
    (hCond : evalExpr? cfg act evm condExpr = .ok (.bool false)) :
    ExecBlock cfg act evm [.require condExpr, .return retExpr] .reverted :=
  ExecBlock.consRevert (ExecStmt.require_false_of_eval hCond)

lemma ExecFuncBody.returned_of_block {cfg : Config} {act act' : Frame}
    {evm evm' : EVM.State} {body : List Stmt} {value : Option Value}
    (hBlock : ExecBlock cfg act evm body (.returned act' evm' value)) :
    ExecFuncBody cfg act evm body (.returned act' evm' value) :=
  ExecFuncBody.execBlockRet hBlock

lemma ExecFuncBody.reverted_of_block {cfg : Config} {act : Frame}
    {evm : EVM.State} {body : List Stmt}
    (hBlock : ExecBlock cfg act evm body .reverted) :
    ExecFuncBody cfg act evm body .reverted :=
  ExecFuncBody.execBlockRevert hBlock

lemma ExecFuncBody.fallthrough_of_block_ok {cfg : Config} {act act' : Frame}
    {evm evm' : EVM.State} {body : List Stmt}
    (hBlock : ExecBlock cfg act evm body (.ok act' evm')) :
    ExecFuncBody cfg act evm body (.returned act' evm' none) :=
  ExecFuncBody.execBlockOK hBlock

lemma ExecFuncBody.require_true_then_return {cfg : Config} {act : Frame} {evm : EVM.State}
    {condExpr retExpr : Expr} {value : Value}
    (hCond : evalExpr? cfg act evm condExpr = .ok (.bool true))
    (hRet : evalExpr? cfg act evm retExpr = .ok value) :
    ExecFuncBody cfg act evm
      [.require condExpr, .return retExpr]
      (.returned act evm (some value)) :=
  ExecFuncBody.returned_of_block (ExecBlock.require_true_then_return hCond hRet)

lemma ExecFuncBody.require_false_then_revert {cfg : Config} {act : Frame} {evm : EVM.State}
    {condExpr retExpr : Expr}
    (hCond : evalExpr? cfg act evm condExpr = .ok (.bool false)) :
    ExecFuncBody cfg act evm [.require condExpr, .return retExpr] .reverted :=
  ExecFuncBody.reverted_of_block (ExecBlock.require_false_then_revert hCond)

lemma ExecContractBody.require_true_then_return {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store} {condExpr retExpr : Expr} {value : Value}
    (hCond :
      evalExpr? cfg { contract := contract, locals := locals } evm condExpr =
        .ok (.bool true))
    (hRet :
      evalExpr? cfg { contract := contract, locals := locals } evm retExpr =
        .ok value) :
    ExecContractBody cfg contract evm locals
      [.require condExpr, .return retExpr]
      (.returned { contract := contract, locals := locals } evm (some value)) :=
  ExecFuncBody.require_true_then_return hCond hRet

lemma ExecContractBody.require_false_then_revert {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store} {condExpr retExpr : Expr}
    (hCond :
      evalExpr? cfg { contract := contract, locals := locals } evm condExpr =
        .ok (.bool false)) :
    ExecContractBody cfg contract evm locals [.require condExpr, .return retExpr] .reverted :=
  ExecFuncBody.require_false_then_revert hCond

lemma evalExpr_boolLit {cfg : Config} {act : Frame} {evm : EVM.State} {b : Bool} :
    evalExpr? cfg act evm (.boolLit b) = .ok (.bool b) :=
  by simp [evalExpr?, pure]

lemma evalExpr_intLit {cfg : Config} {act : Frame} {evm : EVM.State} {i : Int} :
    evalExpr? cfg act evm (.intLit i) = .ok (.int i) :=
  by simp [evalExpr?, pure]

lemma evalExpr_callvalue {cfg : Config} {act : Frame} {evm : EVM.State} :
    evalExpr? cfg act evm (.env .callvalue) =
      .ok (.int (Int.ofNat evm.executionEnv.weiValue.val)) :=
  by simp [evalExpr?, envValue, pure]

lemma evalExpr_callvalue_eq_zero_of_weiValue_zero
    {cfg : Config} {act : Frame} {evm : EVM.State}
    (hValue : evm.executionEnv.weiValue = (⟨0⟩ : Ethereum.UInt256)) :
    evalExpr? cfg act evm (.binary .eq (.env .callvalue) (.intLit 0)) =
      .ok (.bool true) := by
  have hNat : evm.executionEnv.weiValue.val.val = 0 := by
    exact congrArg (fun x : Ethereum.UInt256 => x.val.val) hValue
  simp [evalExpr?, envValue, evalBinaryOp?, pure, bind, EvalResult.bind, hNat]

lemma evalExpr_callvalue_eq_zero_of_weiValue_ne_zero
    {cfg : Config} {act : Frame} {evm : EVM.State}
    (hValue : evm.executionEnv.weiValue ≠ (⟨0⟩ : Ethereum.UInt256)) :
    evalExpr? cfg act evm (.binary .eq (.env .callvalue) (.intLit 0)) =
      .ok (.bool false) := by
  have hNat : evm.executionEnv.weiValue.val.val ≠ 0 :=
    Ethereum.UInt256.val_val_ne_zero_of_ne_zero hValue
  simp [evalExpr?, envValue, evalBinaryOp?, pure, bind, EvalResult.bind, hNat]

end Act
