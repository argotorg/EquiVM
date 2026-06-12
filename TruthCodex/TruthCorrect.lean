import TruthCodex.Trusted

/-!
# Truth — a worked runtime-equivalence example

The contract (Solidity):

```solidity
contract Truth {
  function truth() public pure returns (bool) { return true; }
}
```

This file pins down the three ingredients of a runtime-equivalence claim:
* `truthBytecode` — the deployed EVM runtime bytecode (solc output);
* `truthContract` — the Act specification;
* `truthCorrect`  — the correctness statement, assembled from reusable lemmas and
  explicit trusted bytecode/hash facts.
-/

open Act ABI

/-! ## 1. The contract's runtime bytecode -/

/-- Deployed runtime bytecode of the `Truth` contract. -/
def truthBytecode : ByteArray :=
  ⟨#[
    0x60, 0x80, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15, 0x60, 0x0e, 0x57, 0x5f,
    0x5f, 0xfd, 0x5b, 0x50, 0x60, 0x04, 0x36, 0x10, 0x60, 0x26, 0x57, 0x5f,
    0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63, 0x9e, 0x9f, 0x51, 0xd2, 0x14, 0x60,
    0x2a, 0x57, 0x5b, 0x5f, 0x5f, 0xfd, 0x5b, 0x60, 0x30, 0x60, 0x44, 0x56,
    0x5b, 0x60, 0x40, 0x51, 0x60, 0x3b, 0x91, 0x90, 0x60, 0x64, 0x56, 0x5b,
    0x60, 0x40, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3, 0x5b, 0x5f, 0x60, 0x01,
    0x90, 0x50, 0x90, 0x56, 0x5b, 0x5f, 0x81, 0x15, 0x15, 0x90, 0x50, 0x91,
    0x90, 0x50, 0x56, 0x5b, 0x60, 0x5e, 0x81, 0x60, 0x4c, 0x56, 0x5b, 0x82,
    0x52, 0x50, 0x50, 0x56, 0x5b, 0x5f, 0x60, 0x20, 0x82, 0x01, 0x90, 0x50,
    0x60, 0x75, 0x5f, 0x83, 0x01, 0x84, 0x60, 0x57, 0x56, 0x5b, 0x92, 0x91,
    0x50, 0x50, 0x56
  ]⟩

set_option maxRecDepth 10000 in
lemma truthBytecode_decode_0 :
    Ethereum.EVM.decode truthBytecode ⟨0⟩ = some (.PUSH1, .some (⟨0x80⟩, 1)) := by
  decide

set_option maxRecDepth 10000 in
lemma truthBytecode_decode_2 :
    Ethereum.EVM.decode truthBytecode ⟨2⟩ = some (.PUSH1, .some (⟨0x40⟩, 1)) := by
  decide

set_option maxRecDepth 10000 in
lemma truthBytecode_decode_4 :
    Ethereum.EVM.decode truthBytecode ⟨4⟩ = some (.MSTORE, .none) := by
  decide

set_option maxRecDepth 10000 in
lemma truthBytecode_decode_5 :
    Ethereum.EVM.decode truthBytecode ⟨5⟩ = some (.CALLVALUE, .none) := by
  decide

set_option maxRecDepth 10000 in
lemma truthBytecode_decode_6 :
    Ethereum.EVM.decode truthBytecode ⟨6⟩ = some (.DUP1, .none) := by
  decide

set_option maxRecDepth 10000 in
lemma truthBytecode_decode_7 :
    Ethereum.EVM.decode truthBytecode ⟨7⟩ = some (.ISZERO, .none) := by
  decide

set_option maxRecDepth 10000 in
lemma truthBytecode_decode_8 :
    Ethereum.EVM.decode truthBytecode ⟨8⟩ = some (.PUSH1, .some (⟨0x0e⟩, 1)) := by
  decide

set_option maxRecDepth 10000 in
lemma truthBytecode_decode_10 :
    Ethereum.EVM.decode truthBytecode ⟨10⟩ = some (.JUMPI, .none) := by
  decide

set_option maxRecDepth 10000 in
lemma truthBytecode_decode_11 :
    Ethereum.EVM.decode truthBytecode ⟨11⟩ = some (.PUSH0, .none) := by
  decide

set_option maxRecDepth 10000 in
lemma truthBytecode_decode_12 :
    Ethereum.EVM.decode truthBytecode ⟨12⟩ = some (.PUSH0, .none) := by
  decide

set_option maxRecDepth 10000 in
lemma truthBytecode_decode_13 :
    Ethereum.EVM.decode truthBytecode ⟨13⟩ = some (.REVERT, .none) := by
  decide

set_option maxRecDepth 10000 in
lemma truthBytecode_decode_14 :
    Ethereum.EVM.decode truthBytecode ⟨14⟩ = some (.JUMPDEST, .none) := by
  decide

set_option maxRecDepth 10000 in
lemma truthBytecode_decode_15 :
    Ethereum.EVM.decode truthBytecode ⟨15⟩ = some (.POP, .none) := by
  decide

/-! ## 2. The Act specification -/

/-- The single transition: `truth()` requires zero callvalue and returns `true`.
    (The `require(callvalue == 0)` mirrors the compiler-inserted non-payable guard.) -/
def truthTransition : TransitionDecl :=
  { name := "truth"
    params := []
    returnType := some (.elem .bool)
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0))
      , .return (.boolLit true) ] }

/-- Act specification of the `Truth` contract: no storage, no constructor body,
    a single transition. -/
def truthContract : ContractDecl :=
  { name := "Truth"
    storage := []
    ctor := { params := [], body := [] }
    transitions := [truthTransition] }

/-- Configuration: empty storage layout and the default external-call ABI. -/
def truthConfig : Config :=
  { storage := { layout := fun _ => none }
    externalABI := defaultExternalCallABI }

/-! ## 3. The correctness statement -/

/-! ### Truth-specific assembly facts -/

lemma trustedKeccak_truthTransition :
    (ffi.KEC (String.toByteArray (transitionSigStr truthTransition))).extract 0 4 =
      trustedTruthSelector := by
  simpa [truthTransition, transitionSigStr, transitionSignature, printSignature]
    using trustedKeccak_truth

lemma truthDispatch_some_of_selector {calldata : ByteArray}
    (hSelector : calldata.extract 0 4 = trustedTruthSelector) :
    dispatchMsg truthContract calldata = some truthTransition := by
  exact dispatchMsg_singleton_some_of_selector
    (contract := truthContract)
    (transition := truthTransition)
    (selector := trustedTruthSelector)
    (by rfl)
    trustedKeccak_truthTransition
    hSelector

lemma truthDispatch_none_of_selector_ne {calldata : ByteArray}
    (hSelector : calldata.extract 0 4 ≠ trustedTruthSelector) :
    dispatchMsg truthContract calldata = none := by
  exact dispatchMsg_singleton_none_of_selector_ne
    (contract := truthContract)
    (transition := truthTransition)
    (selector := trustedTruthSelector)
    (by rfl)
    trustedKeccak_truthTransition
    hSelector

lemma truthTransition_signature :
    transitionSignature truthTransition = ⟨"truth", []⟩ := by
  rfl

lemma truthDecodeCalldata_no_params {calldata : ByteArray}
    (hSize : ¬ calldata.toList.length < 4) :
    decodeCalldata (truthTransition.params.map Param.name)
      (transitionSignature truthTransition).paramTypes calldata =
      some (∅ : Store) := by
  simpa [truthTransition, transitionSignature]
    using ABI.decodeCalldata_no_params_of_not_lt (calldata := calldata) hSize

lemma trustedTruthSelector_size :
    trustedTruthSelector.size = 4 := by
  rfl

lemma truthDecodeCalldata_no_params_of_selector {calldata : ByteArray}
    (hSelector : calldata.extract 0 4 = trustedTruthSelector) :
    decodeCalldata (truthTransition.params.map Param.name)
      (transitionSignature truthTransition).paramTypes calldata =
      some (∅ : Store) :=
  truthDecodeCalldata_no_params
    (ByteArray.not_toList_length_lt_of_extract_eq_size trustedTruthSelector_size hSelector)

lemma truthExecContractBody_true {evm : EVM.State}
    (hValue : evm.executionEnv.weiValue = (⟨0⟩ : Ethereum.UInt256)) :
    ExecContractBody truthConfig truthContract evm ∅ truthTransition.body
      (.returned { contract := truthContract, locals := ∅ } evm (some (.bool true))) := by
  change ExecContractBody truthConfig truthContract evm ∅
    [.require (.binary .eq (.env .callvalue) (.intLit 0)), .return (.boolLit true)]
    (.returned { contract := truthContract, locals := ∅ } evm (some (.bool true)))
  exact Act.ExecContractBody.require_true_then_return
    (Act.evalExpr_callvalue_eq_zero_of_weiValue_zero hValue)
    Act.evalExpr_boolLit

lemma truthExecContractBody_revert {evm : EVM.State}
    (hValue : evm.executionEnv.weiValue ≠ (⟨0⟩ : Ethereum.UInt256)) :
    ExecContractBody truthConfig truthContract evm ∅ truthTransition.body .reverted := by
  change ExecContractBody truthConfig truthContract evm ∅
    [.require (.binary .eq (.env .callvalue) (.intLit 0)), .return (.boolLit true)]
    .reverted
  exact Act.ExecContractBody.require_false_then_revert
    (Act.evalExpr_callvalue_eq_zero_of_weiValue_ne_zero hValue)

lemma truthExecResultsEquiv_success {evmState : EVM.State}
    {g' : Ethereum.UInt256} {A' : Ethereum.Substate} :
    execResultsEquiv
      (.ok
        (.success
          (evmState.createdAccounts, evmState.accountMap, g', A')
          abiBoolTrueReturn))
      (.returned { contract := truthContract, locals := ∅ } evmState (some (.bool true)))
      truthTransition.returnType := by
  change execResultsEquiv
    (.ok
      (.success
        (evmState.createdAccounts, evmState.accountMap, g', A')
        abiBoolTrueReturn))
    (.returned { contract := truthContract, locals := ∅ } evmState (some (.bool true)))
    (some (.elem .bool))
  exact execResultsEquiv.success_rfl returnEquiv_bool_true

lemma truthActExec_true
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hSelector : I.calldata.extract 0 4 = trustedTruthSelector)
    (hValue : I.weiValue = (⟨0⟩ : Ethereum.UInt256)) :
    actExec truthConfig truthContract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      (.returned { contract := truthContract, locals := ∅ }
        (initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
        (some (.bool true)))
      truthTransition.returnType := by
  exact actExec_of_dispatch_decode_initial
    (transition := truthTransition)
    (transitionSig := transitionSignature truthTransition)
    (callargs := (∅ : Store))
    (truthDispatch_some_of_selector hSelector)
    rfl
    (truthDecodeCalldata_no_params_of_selector hSelector)
    (truthExecContractBody_true (by simpa [initialEVMState] using hValue))

lemma truthActExec_revert
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hSelector : I.calldata.extract 0 4 = trustedTruthSelector)
    (hValue : I.weiValue ≠ (⟨0⟩ : Ethereum.UInt256)) :
    actExec truthConfig truthContract createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      .reverted truthTransition.returnType := by
  exact actExec_of_dispatch_decode_initial
    (transition := truthTransition)
    (transitionSig := transitionSignature truthTransition)
    (callargs := (∅ : Store))
    (truthDispatch_some_of_selector hSelector)
    rfl
    (truthDecodeCalldata_no_params_of_selector hSelector)
    (truthExecContractBody_revert (by simpa [initialEVMState] using hValue))

lemma truthRuntime_success_of_evm
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g g' : Ethereum.UInt256}
    {A A' : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hSelector : I.calldata.extract 0 4 = trustedTruthSelector)
    (hValue : I.weiValue = (⟨0⟩ : Ethereum.UInt256))
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.success (createdAccounts, σ, g', A') abiBoolTrueReturn)) :
    runtimeEquivalenceFor truthConfig truthContract createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I := by
  exact runtimeEquivalenceFor_success_initial hΞ
    (truthActExec_true
      (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks)
      (σ := σ)
      (σ₀ := σ₀)
      (g := g)
      (A := A)
      (I := I)
      hSelector hValue)
    returnEquiv_bool_true

lemma truthRuntime_revert_of_evm
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g g' : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {o : ByteArray}
    (hSelector : I.calldata.extract 0 4 = trustedTruthSelector)
    (hValue : I.weiValue ≠ (⟨0⟩ : Ethereum.UInt256))
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.revert g' o)) :
    runtimeEquivalenceFor truthConfig truthContract createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I := by
  exact runtimeEquivalenceFor_revert_of_act_reverted hΞ
    (truthActExec_revert
      (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks)
      (σ := σ)
      (σ₀ := σ₀)
      (g := g)
      (A := A)
      (I := I)
      hSelector hValue)

lemma truthRuntime_noDispatch_revert_of_evm
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g g' : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    {o : ByteArray}
    (hSelector : I.calldata.extract 0 4 ≠ trustedTruthSelector)
    (hΞ :
      Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
        .ok (.revert g' o)) :
    runtimeEquivalenceFor truthConfig truthContract createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I :=
  runtimeEquivalenceFor_noDispatch
    (truthDispatch_none_of_selector_ne hSelector)
    hΞ

lemma truthRuntime_outOfGas_of_evm
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
    runtimeEquivalenceFor truthConfig truthContract createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I :=
  runtimeEquivalenceFor_outOfGas hΞ

lemma truthEVM_first_push_oog
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hGas : g.toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  let s := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  have hDecode :
      Ethereum.EVM.decode I.code s.machineState.pc =
        some (.PUSH1, .some ((⟨0x80⟩ : Ethereum.UInt256), 1)) := by
    simpa [s, hCode] using truthBytecode_decode_0
  have hStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s = .error .OutOfGass := by
    exact Ethereum.EVM.Xstep_push1_oog_of_decode hDecode (by simpa [s] using hGas)
  exact EVM_Xi_of_initial_Xstep_error hStep

lemma truthEVM_first_push_continue
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hGas : ¬ g.toNat < GasConstants.Gverylow) :
    let s := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s =
      .ok (Ethereum.EVM.push1NextState s (⟨0x80⟩ : Ethereum.UInt256), none) := by
  intro s
  have hDecode :
      Ethereum.EVM.decode I.code s.machineState.pc =
        some (.PUSH1, .some ((⟨0x80⟩ : Ethereum.UInt256), 1)) := by
    simpa [s, hCode] using truthBytecode_decode_0
  exact Ethereum.EVM.Xstep_push1_continue_of_decode hDecode
    (by simpa [s] using hGas)
    (by simp [s])

lemma truthEVM_second_push_oog
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
  have hFirstStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s0 = .ok (s1, none) := by
    simpa [s0, s1] using
      truthEVM_first_push_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas
  have hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 1 s0 s1 := by
    simpa using
      (Ethereum.EVM.ContinueTrace.cons hFirstStep Ethereum.EVM.ContinueTrace.nil)
  have hDecode :
      Ethereum.EVM.decode I.code s1.machineState.pc =
        some (.PUSH1, .some ((⟨0x40⟩ : Ethereum.UInt256), 1)) := by
    simpa [s0, s1, Ethereum.EVM.push1NextState, hCode, Ethereum.UInt256.ofNat,
      Ethereum.UInt256.add, Id.run] using truthBytecode_decode_2
  have hSecondStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s1 = .error .OutOfGass := by
    exact Ethereum.EVM.Xstep_push1_oog_of_decode hDecode
      (by simpa [s0, s1, Ethereum.EVM.push1NextState] using hSecondGas)
  have hFuel : g.toNat = 1 + (g.toNat - 1) := by
    omega
  exact EVM_Xi_of_initial_continue_trace_error
    (n := 1)
    (fuel := g.toNat - 1)
    hFuel
    (by simpa [s0] using hTrace)
    hSecondStep

lemma truthEVM_second_push_continue
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (_hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s1 =
      .ok (Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256), none) := by
  intro s0 s1
  have hDecode :
      Ethereum.EVM.decode I.code s1.machineState.pc =
        some (.PUSH1, .some ((⟨0x40⟩ : Ethereum.UInt256), 1)) := by
    simpa [s0, s1, Ethereum.EVM.push1NextState, hCode, Ethereum.UInt256.ofNat,
      Ethereum.UInt256.add, Id.run] using truthBytecode_decode_2
  exact Ethereum.EVM.Xstep_push1_continue_of_decode hDecode
    (by simpa [s0, s1, Ethereum.EVM.push1NextState] using hSecondGas)
    (by simp [s0, s1, Ethereum.EVM.push1NextState])

lemma truthGas_ge_six_of_second_push_continue {g : Ethereum.UInt256}
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow) :
    6 ≤ g.toNat := by
  have hCost : GasConstants.Gverylow ≤ g.toNat := by
    unfold GasConstants.Gverylow at hFirstGas
    unfold GasConstants.Gverylow
    omega
  have hGas := Ethereum.UInt256.add_le_toNat_of_not_sub_ofNat_lt
    (x := g)
    (cost := GasConstants.Gverylow)
    (remaining := GasConstants.Gverylow)
    (by decide)
    hCost
    hSecondGas
  unfold GasConstants.Gverylow at hGas
  omega

lemma truthEVM_two_push_trace
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 2 s0 s2 := by
  intro s0 s1 s2
  have hFirstStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s0 = .ok (s1, none) := by
    simpa [s0, s1] using
      truthEVM_first_push_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas
  have hSecondStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s1 = .ok (s2, none) := by
    simpa [s0, s1, s2] using
      truthEVM_second_push_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas
  exact Ethereum.EVM.ContinueTrace.two hFirstStep hSecondStep

lemma truthEVM_mstore_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    Ethereum.EVM.decode I.code s2.machineState.pc = some (.MSTORE, .none) := by
  intro s0 s1 s2
  simpa [s0, s1, s2, Ethereum.EVM.push1NextState, hCode, Ethereum.UInt256.ofNat,
    Ethereum.UInt256.add, Id.run] using truthBytecode_decode_4

lemma truthEVM_mstore_stack
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    s2.machineState.stack =
      (⟨0x40⟩ : Ethereum.UInt256) :: (⟨0x80⟩ : Ethereum.UInt256) :: [] := by
  intro s0 s1 s2
  simp [s0, s1, s2, Ethereum.EVM.push1NextState]

lemma truthEVM_mstore_memory_cost
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    Ethereum.EVM.memoryExpansionCost s2 .MSTORE = 9 := by
  intro s0 s1 s2
  simp [s0, s1, s2, Ethereum.EVM.push1NextState, Ethereum.EVM.memoryExpansionCost,
    Ethereum.EVM.memoryExpansionCost.μᵢ', Ethereum.EVM.Cₘ, Ethereum.MachineState.M,
    Ethereum.UInt256.ofNat, Ethereum.UInt256.toNat, Id.run, GasConstants.Gmemory]
  norm_num [Ethereum.UInt256.size, Ethereum.EVM.Cₘ.QuadraticCeofficient]

lemma truthGas_ge_fifteen_of_mstore_memory_continue
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE)) :
    15 ≤ g.toNat := by
  let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
  let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
  have hg6 : 6 ≤ g.toNat := truthGas_ge_six_of_second_push_continue hFirstGas hSecondGas
  have hSub :
      ((g - Ethereum.UInt256.ofNat GasConstants.Gverylow) -
        Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat =
          g.toNat - GasConstants.Gverylow - GasConstants.Gverylow :=
    Ethereum.UInt256.toNat_sub_ofNat_sub_ofNat_of_le
      (x := g) (a := GasConstants.Gverylow) (b := GasConstants.Gverylow)
      (by decide) (by decide) (by simpa [GasConstants.Gverylow] using hg6)
  have hGas2 :
      s2.machineState.gasAvailable.toNat = g.toNat - 3 - 3 := by
    simpa [s0, s1, s2, Ethereum.EVM.push1NextState, GasConstants.Gverylow] using hSub
  have hCost :
      Ethereum.EVM.memoryExpansionCost s2 .MSTORE = 9 := by
    simpa [s0, s1, s2] using
      (truthEVM_mstore_memory_cost
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I))
  have hMemGas' :
      ¬ s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE := by
    simpa [s0, s1, s2] using hMemGas
  rw [hCost, hGas2] at hMemGas'
  omega

lemma truthEVM_mstore_memory_oog
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
       let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
       let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
       s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE)) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
  let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
  have hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 2 s0 s2 := by
    simpa [s0, s1, s2] using
      truthEVM_two_push_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas
  have hDecode :
      Ethereum.EVM.decode I.code s2.machineState.pc = some (.MSTORE, .none) := by
    simpa [s0, s1, s2] using
      truthEVM_mstore_decode
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode
  have hStack :
      s2.machineState.stack =
        (⟨0x40⟩ : Ethereum.UInt256) :: (⟨0x80⟩ : Ethereum.UInt256) :: [] := by
    simpa [s0, s1, s2] using
      (truthEVM_mstore_stack
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I))
  have hMemGas' :
      s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE := by
    simpa [s0, s1, s2] using hMemGas
  have hMstoreStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s2 = .error .OutOfGass := by
    exact Ethereum.EVM.Xstep_mstore_memory_oog_of_decode hDecode hStack hMemGas'
  have hFuel : g.toNat = 2 + (g.toNat - 2) := by
    have hg2 : 2 ≤ g.toNat := by
      unfold GasConstants.Gverylow at hFirstGas
      omega
    omega
  exact EVM_Xi_of_initial_continue_trace_error
    (n := 2)
    (fuel := g.toNat - 2)
    hFuel
    (by simpa [s0] using hTrace)
    hMstoreStep

lemma truthEVM_mstore_verylow_oog
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
       let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
       let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
       (s2.machineState.gasAvailable -
          Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
          GasConstants.Gverylow)) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
  let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
  have hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 2 s0 s2 := by
    simpa [s0, s1, s2] using
      truthEVM_two_push_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas
  have hDecode :
      Ethereum.EVM.decode I.code s2.machineState.pc = some (.MSTORE, .none) := by
    simpa [s0, s1, s2] using
      truthEVM_mstore_decode
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode
  have hStack :
      s2.machineState.stack =
        (⟨0x40⟩ : Ethereum.UInt256) :: (⟨0x80⟩ : Ethereum.UInt256) :: [] := by
    simpa [s0, s1, s2] using
      (truthEVM_mstore_stack
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I))
  have hMemGas' :
      ¬ s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE := by
    simpa [s0, s1, s2] using hMemGas
  have hVerylowGas' :
      (s2.machineState.gasAvailable -
          Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
        GasConstants.Gverylow := by
    simpa [s0, s1, s2] using hVerylowGas
  have hMstoreStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s2 = .error .OutOfGass := by
    exact Ethereum.EVM.Xstep_mstore_verylow_oog_of_decode
      hDecode hStack hMemGas' hVerylowGas'
  have hFuel : g.toNat = 2 + (g.toNat - 2) := by
    have hg2 : 2 ≤ g.toNat := by
      unfold GasConstants.Gverylow at hFirstGas
      omega
    omega
  exact EVM_Xi_of_initial_continue_trace_error
    (n := 2)
    (fuel := g.toNat - 2)
    hFuel
    (by simpa [s0] using hTrace)
    hMstoreStep

lemma truthEVM_mstore_continue
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s2 = .ok (s3, none) := by
  intro s0 s1 s2 s3
  have hDecode :
      Ethereum.EVM.decode I.code s2.machineState.pc = some (.MSTORE, .none) := by
    simpa [s0, s1, s2] using
      truthEVM_mstore_decode
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode
  have hStack :
      s2.machineState.stack =
        (⟨0x40⟩ : Ethereum.UInt256) :: (⟨0x80⟩ : Ethereum.UInt256) :: [] := by
    simpa [s0, s1, s2] using
      (truthEVM_mstore_stack
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I))
  exact Ethereum.EVM.Xstep_mstore_continue_of_decode hDecode hStack
    (by simpa [s0, s1, s2] using hMemGas)
    (by simpa [s0, s1, s2] using hVerylowGas)
    (by simp)

lemma truthEVM_memory_prologue_trace
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 3 s0 s3 := by
  intro s0 s1 s2 s3
  have hFirstStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s0 = .ok (s1, none) := by
    simpa [s0, s1] using
      truthEVM_first_push_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas
  have hSecondStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s1 = .ok (s2, none) := by
    simpa [s0, s1, s2] using
      truthEVM_second_push_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas
  have hThirdStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s2 = .ok (s3, none) := by
    simpa [s0, s1, s2, s3] using
      truthEVM_mstore_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hMemGas hVerylowGas
  exact Ethereum.EVM.ContinueTrace.three hFirstStep hSecondStep hThirdStep

lemma truthEVM_callvalue_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    Ethereum.EVM.decode I.code s3.machineState.pc = some (.CALLVALUE, .none) := by
  intro s0 s1 s2 s3
  simpa [s0, s1, s2, s3, Ethereum.EVM.push1NextState, Ethereum.EVM.mstoreNextState,
    hCode, Ethereum.UInt256.ofNat, Ethereum.UInt256.add, Id.run] using truthBytecode_decode_5

lemma truthEVM_callvalue_stack
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    s3.machineState.stack = ([] : Ethereum.Stack Ethereum.UInt256) := by
  intro s0 s1 s2 s3
  simp [s0, s1, s2, s3, Ethereum.EVM.push1NextState, Ethereum.EVM.mstoreNextState]

lemma truthEVM_callvalue_oog
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow))
    (hCallvalueGas :
      (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
       let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
       let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
       let s3 := Ethereum.EVM.mstoreNextState s2
        (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
       s3.machineState.gasAvailable.toNat < GasConstants.Gbase)) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
  let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
  let s3 := Ethereum.EVM.mstoreNextState s2
    (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
  have hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 3 s0 s3 := by
    simpa [s0, s1, s2, s3] using
      truthEVM_memory_prologue_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas hMemGas hVerylowGas
  have hDecode :
      Ethereum.EVM.decode I.code s3.machineState.pc = some (.CALLVALUE, .none) := by
    simpa [s0, s1, s2, s3] using
      truthEVM_callvalue_decode
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode
  have hCallvalueGas' :
      s3.machineState.gasAvailable.toNat < GasConstants.Gbase := by
    simpa [s0, s1, s2, s3] using hCallvalueGas
  have hCallvalueStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s3 = .error .OutOfGass := by
    exact Ethereum.EVM.Xstep_callvalue_oog_of_decode hDecode hCallvalueGas'
  have hFuel : g.toNat = 3 + (g.toNat - 3) := by
    have hg3 : 3 ≤ g.toNat := by
      unfold GasConstants.Gverylow at hFirstGas
      omega
    omega
  exact EVM_Xi_of_initial_continue_trace_error
    (n := 3)
    (fuel := g.toNat - 3)
    hFuel
    (by simpa [s0] using hTrace)
    hCallvalueStep

lemma truthEVM_callvalue_continue
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hCallvalueGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         s3.machineState.gasAvailable.toNat < GasConstants.Gbase)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s3 = .ok (s4, none) := by
  intro s0 s1 s2 s3 s4
  have hDecode :
      Ethereum.EVM.decode I.code s3.machineState.pc = some (.CALLVALUE, .none) := by
    simpa [s0, s1, s2, s3] using
      truthEVM_callvalue_decode
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode
  exact Ethereum.EVM.Xstep_callvalue_continue_of_decode hDecode
    (by simpa [s0, s1, s2, s3] using hCallvalueGas)
    (by simp [s0, s1, s2, s3, Ethereum.EVM.push1NextState, Ethereum.EVM.mstoreNextState])

lemma truthEVM_callvalue_trace
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow))
    (hCallvalueGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         s3.machineState.gasAvailable.toNat < GasConstants.Gbase)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 4 s0 s4 := by
  intro s0 s1 s2 s3 s4
  have hTrace3 :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 3 s0 s3 := by
    simpa [s0, s1, s2, s3] using
      truthEVM_memory_prologue_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas hMemGas hVerylowGas
  have hCallvalueStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s3 = .ok (s4, none) := by
    simpa [s0, s1, s2, s3, s4] using
      truthEVM_callvalue_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hCallvalueGas
  simpa using Ethereum.EVM.ContinueTrace.snoc hTrace3 hCallvalueStep

lemma truthEVM_dup1_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    Ethereum.EVM.decode I.code s4.machineState.pc = some (.DUP1, .none) := by
  intro s0 s1 s2 s3 s4
  simpa [s0, s1, s2, s3, s4, Ethereum.EVM.push1NextState, Ethereum.EVM.mstoreNextState,
    Ethereum.EVM.callvalueNextState, hCode, Ethereum.UInt256.ofNat, Ethereum.UInt256.add,
    Id.run] using truthBytecode_decode_6

lemma truthEVM_dup1_stack
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    s4.machineState.stack = I.weiValue :: [] := by
  intro s0 s1 s2 s3 s4
  simp [s0, s1, s2, s3, s4, Ethereum.EVM.push1NextState, Ethereum.EVM.mstoreNextState,
    Ethereum.EVM.callvalueNextState]

lemma truthEVM_dup1_oog
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow))
    (hCallvalueGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         s3.machineState.gasAvailable.toNat < GasConstants.Gbase))
    (hDupGas :
      (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
       let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
       let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
       let s3 := Ethereum.EVM.mstoreNextState s2
        (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
       let s4 := Ethereum.EVM.callvalueNextState s3
       s4.machineState.gasAvailable.toNat < GasConstants.Gverylow)) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
  let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
  let s3 := Ethereum.EVM.mstoreNextState s2
    (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
  let s4 := Ethereum.EVM.callvalueNextState s3
  have hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 4 s0 s4 := by
    simpa [s0, s1, s2, s3, s4] using
      truthEVM_callvalue_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas hMemGas hVerylowGas hCallvalueGas
  have hDecode :
      Ethereum.EVM.decode I.code s4.machineState.pc = some (.DUP1, .none) := by
    simpa [s0, s1, s2, s3, s4] using
      truthEVM_dup1_decode
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode
  have hStack :
      s4.machineState.stack = I.weiValue :: [] := by
    simpa [s0, s1, s2, s3, s4] using
      (truthEVM_dup1_stack
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I))
  have hDupGas' :
      s4.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
    simpa [s0, s1, s2, s3, s4] using hDupGas
  have hDupStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s4 = .error .OutOfGass := by
    exact Ethereum.EVM.Xstep_dup1_oog_of_decode hDecode hStack hDupGas'
  have hFuel : g.toNat = 4 + (g.toNat - 4) := by
    have hg6 : 6 ≤ g.toNat :=
      truthGas_ge_six_of_second_push_continue hFirstGas hSecondGas
    omega
  exact EVM_Xi_of_initial_continue_trace_error
    (n := 4)
    (fuel := g.toNat - 4)
    hFuel
    (by simpa [s0] using hTrace)
    hDupStep

lemma truthEVM_dup1_continue
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hDupGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         s4.machineState.gasAvailable.toNat < GasConstants.Gverylow)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s4 = .ok (s5, none) := by
  intro s0 s1 s2 s3 s4 s5
  have hDecode :
      Ethereum.EVM.decode I.code s4.machineState.pc = some (.DUP1, .none) := by
    simpa [s0, s1, s2, s3, s4] using
      truthEVM_dup1_decode
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode
  have hStack :
      s4.machineState.stack = I.weiValue :: [] := by
    simpa [s0, s1, s2, s3, s4] using
      (truthEVM_dup1_stack
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I))
  exact Ethereum.EVM.Xstep_dup1_continue_of_decode hDecode hStack
    (by simpa [s0, s1, s2, s3, s4] using hDupGas)
    (by simp)

lemma truthEVM_dup1_trace
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow))
    (hCallvalueGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         s3.machineState.gasAvailable.toNat < GasConstants.Gbase))
    (hDupGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         s4.machineState.gasAvailable.toNat < GasConstants.Gverylow)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 5 s0 s5 := by
  intro s0 s1 s2 s3 s4 s5
  have hTrace4 :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 4 s0 s4 := by
    simpa [s0, s1, s2, s3, s4] using
      truthEVM_callvalue_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas hMemGas hVerylowGas hCallvalueGas
  have hDupStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s4 = .ok (s5, none) := by
    simpa [s0, s1, s2, s3, s4, s5] using
      truthEVM_dup1_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hDupGas
  simpa using Ethereum.EVM.ContinueTrace.snoc hTrace4 hDupStep

lemma truthEVM_iszero_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    Ethereum.EVM.decode I.code s5.machineState.pc = some (.ISZERO, .none) := by
  intro s0 s1 s2 s3 s4 s5
  simpa [s0, s1, s2, s3, s4, s5, Ethereum.EVM.push1NextState,
    Ethereum.EVM.mstoreNextState, Ethereum.EVM.callvalueNextState, Ethereum.EVM.dup1NextState,
    hCode, Ethereum.UInt256.ofNat, Ethereum.UInt256.add, Id.run] using truthBytecode_decode_7

lemma truthEVM_iszero_stack
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    s5.machineState.stack = I.weiValue :: I.weiValue :: [] := by
  intro s0 s1 s2 s3 s4 s5
  simp [s0, s1, s2, s3, s4, s5, Ethereum.EVM.push1NextState,
    Ethereum.EVM.mstoreNextState, Ethereum.EVM.callvalueNextState, Ethereum.EVM.dup1NextState]

lemma truthEVM_iszero_oog
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow))
    (hCallvalueGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         s3.machineState.gasAvailable.toNat < GasConstants.Gbase))
    (hDupGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         s4.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hIszeroGas :
      (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
       let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
       let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
       let s3 := Ethereum.EVM.mstoreNextState s2
        (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
       let s4 := Ethereum.EVM.callvalueNextState s3
       let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
       s5.machineState.gasAvailable.toNat < GasConstants.Gverylow)) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
  let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
  let s3 := Ethereum.EVM.mstoreNextState s2
    (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
  let s4 := Ethereum.EVM.callvalueNextState s3
  let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
  have hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 5 s0 s5 := by
    simpa [s0, s1, s2, s3, s4, s5] using
      truthEVM_dup1_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas hMemGas hVerylowGas hCallvalueGas hDupGas
  have hDecode :
      Ethereum.EVM.decode I.code s5.machineState.pc = some (.ISZERO, .none) := by
    simpa [s0, s1, s2, s3, s4, s5] using
      truthEVM_iszero_decode
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode
  have hStack :
      s5.machineState.stack = I.weiValue :: I.weiValue :: [] := by
    simpa [s0, s1, s2, s3, s4, s5] using
      (truthEVM_iszero_stack
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I))
  have hIszeroGas' :
      s5.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
    simpa [s0, s1, s2, s3, s4, s5] using hIszeroGas
  have hIszeroStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s5 = .error .OutOfGass := by
    exact Ethereum.EVM.Xstep_iszero_oog_of_decode hDecode hStack hIszeroGas'
  have hFuel : g.toNat = 5 + (g.toNat - 5) := by
    have hg6 : 6 ≤ g.toNat :=
      truthGas_ge_six_of_second_push_continue hFirstGas hSecondGas
    omega
  exact EVM_Xi_of_initial_continue_trace_error
    (n := 5)
    (fuel := g.toNat - 5)
    hFuel
    (by simpa [s0] using hTrace)
    hIszeroStep

lemma truthEVM_iszero_continue
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hIszeroGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         s5.machineState.gasAvailable.toNat < GasConstants.Gverylow)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s5 = .ok (s6, none) := by
  intro s0 s1 s2 s3 s4 s5 s6
  have hDecode :
      Ethereum.EVM.decode I.code s5.machineState.pc = some (.ISZERO, .none) := by
    simpa [s0, s1, s2, s3, s4, s5] using
      truthEVM_iszero_decode
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode
  have hStack :
      s5.machineState.stack = I.weiValue :: I.weiValue :: [] := by
    simpa [s0, s1, s2, s3, s4, s5] using
      (truthEVM_iszero_stack
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I))
  exact Ethereum.EVM.Xstep_iszero_continue_of_decode hDecode hStack
    (by simpa [s0, s1, s2, s3, s4, s5] using hIszeroGas)
    (by simp)

lemma truthEVM_iszero_trace
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow))
    (hCallvalueGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         s3.machineState.gasAvailable.toNat < GasConstants.Gbase))
    (hDupGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         s4.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hIszeroGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         s5.machineState.gasAvailable.toNat < GasConstants.Gverylow)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 6 s0 s6 := by
  intro s0 s1 s2 s3 s4 s5 s6
  have hTrace5 :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 5 s0 s5 := by
    simpa [s0, s1, s2, s3, s4, s5] using
      truthEVM_dup1_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas hMemGas hVerylowGas hCallvalueGas hDupGas
  have hIszeroStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s5 = .ok (s6, none) := by
    simpa [s0, s1, s2, s3, s4, s5, s6] using
      truthEVM_iszero_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hIszeroGas
  simpa using Ethereum.EVM.ContinueTrace.snoc hTrace5 hIszeroStep

lemma truthEVM_push_dest_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    Ethereum.EVM.decode I.code s6.machineState.pc =
      some (.PUSH1, .some ((⟨0x0e⟩ : Ethereum.UInt256), 1)) := by
  intro s0 s1 s2 s3 s4 s5 s6
  simpa [s0, s1, s2, s3, s4, s5, s6, Ethereum.EVM.push1NextState,
    Ethereum.EVM.mstoreNextState, Ethereum.EVM.callvalueNextState, Ethereum.EVM.dup1NextState,
    Ethereum.EVM.iszeroNextState, hCode, Ethereum.UInt256.ofNat, Ethereum.UInt256.add, Id.run]
    using truthBytecode_decode_8

lemma truthEVM_push_dest_stack
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    s6.machineState.stack =
      Ethereum.UInt256.isZero I.weiValue :: I.weiValue :: [] := by
  intro s0 s1 s2 s3 s4 s5 s6
  simp [s0, s1, s2, s3, s4, s5, s6, Ethereum.EVM.push1NextState,
    Ethereum.EVM.mstoreNextState, Ethereum.EVM.callvalueNextState, Ethereum.EVM.dup1NextState,
    Ethereum.EVM.iszeroNextState]

lemma truthEVM_push_dest_oog
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow))
    (hCallvalueGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         s3.machineState.gasAvailable.toNat < GasConstants.Gbase))
    (hDupGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         s4.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hIszeroGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         s5.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hPushDestGas :
      (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
       let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
       let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
       let s3 := Ethereum.EVM.mstoreNextState s2
        (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
       let s4 := Ethereum.EVM.callvalueNextState s3
       let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
       let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
       s6.machineState.gasAvailable.toNat < GasConstants.Gverylow)) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
  let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
  let s3 := Ethereum.EVM.mstoreNextState s2
    (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
  let s4 := Ethereum.EVM.callvalueNextState s3
  let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
  let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
  have hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 6 s0 s6 := by
    simpa [s0, s1, s2, s3, s4, s5, s6] using
      truthEVM_iszero_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas hMemGas hVerylowGas hCallvalueGas hDupGas hIszeroGas
  have hDecode :
      Ethereum.EVM.decode I.code s6.machineState.pc =
        some (.PUSH1, .some ((⟨0x0e⟩ : Ethereum.UInt256), 1)) := by
    simpa [s0, s1, s2, s3, s4, s5, s6] using
      truthEVM_push_dest_decode
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode
  have hPushDestGas' :
      s6.machineState.gasAvailable.toNat < GasConstants.Gverylow := by
    simpa [s0, s1, s2, s3, s4, s5, s6] using hPushDestGas
  have hPushDestStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s6 = .error .OutOfGass := by
    exact Ethereum.EVM.Xstep_push1_oog_of_decode hDecode hPushDestGas'
  have hFuel : g.toNat = 6 + (g.toNat - 6) := by
    have hg6 : 6 ≤ g.toNat :=
      truthGas_ge_six_of_second_push_continue hFirstGas hSecondGas
    omega
  exact EVM_Xi_of_initial_continue_trace_error
    (n := 6)
    (fuel := g.toNat - 6)
    hFuel
    (by simpa [s0] using hTrace)
    hPushDestStep

lemma truthEVM_push_dest_continue
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hPushDestGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         s6.machineState.gasAvailable.toNat < GasConstants.Gverylow)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s6 = .ok (s7, none) := by
  intro s0 s1 s2 s3 s4 s5 s6 s7
  have hDecode :
      Ethereum.EVM.decode I.code s6.machineState.pc =
        some (.PUSH1, .some ((⟨0x0e⟩ : Ethereum.UInt256), 1)) := by
    simpa [s0, s1, s2, s3, s4, s5, s6] using
      truthEVM_push_dest_decode
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode
  exact Ethereum.EVM.Xstep_push1_continue_of_decode hDecode
    (by simpa [s0, s1, s2, s3, s4, s5, s6] using hPushDestGas)
    (by simp [s0, s1, s2, s3, s4, s5, s6, Ethereum.EVM.push1NextState,
      Ethereum.EVM.mstoreNextState, Ethereum.EVM.callvalueNextState, Ethereum.EVM.dup1NextState,
      Ethereum.EVM.iszeroNextState])

lemma truthEVM_push_dest_trace
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow))
    (hCallvalueGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         s3.machineState.gasAvailable.toNat < GasConstants.Gbase))
    (hDupGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         s4.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hIszeroGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         s5.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hPushDestGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         s6.machineState.gasAvailable.toNat < GasConstants.Gverylow)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 7 s0 s7 := by
  intro s0 s1 s2 s3 s4 s5 s6 s7
  have hTrace6 :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 6 s0 s6 := by
    simpa [s0, s1, s2, s3, s4, s5, s6] using
      truthEVM_iszero_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas hMemGas hVerylowGas hCallvalueGas hDupGas hIszeroGas
  have hPushDestStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s6 = .ok (s7, none) := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7] using
      truthEVM_push_dest_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hPushDestGas
  simpa using Ethereum.EVM.ContinueTrace.snoc hTrace6 hPushDestStep

lemma truthEVM_jumpi_decode
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    Ethereum.EVM.decode I.code s7.machineState.pc = some (.JUMPI, .none) := by
  intro s0 s1 s2 s3 s4 s5 s6 s7
  simpa [s0, s1, s2, s3, s4, s5, s6, s7, Ethereum.EVM.push1NextState,
    Ethereum.EVM.mstoreNextState, Ethereum.EVM.callvalueNextState, Ethereum.EVM.dup1NextState,
    Ethereum.EVM.iszeroNextState, hCode, Ethereum.UInt256.ofNat, Ethereum.UInt256.add, Id.run]
    using truthBytecode_decode_10

lemma truthEVM_jumpi_stack
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    s7.machineState.stack =
      (⟨0x0e⟩ : Ethereum.UInt256) :: Ethereum.UInt256.isZero I.weiValue :: I.weiValue :: [] := by
  intro s0 s1 s2 s3 s4 s5 s6 s7
  simp [s0, s1, s2, s3, s4, s5, s6, s7, Ethereum.EVM.push1NextState,
    Ethereum.EVM.mstoreNextState, Ethereum.EVM.callvalueNextState, Ethereum.EVM.dup1NextState,
    Ethereum.EVM.iszeroNextState]

lemma truthEVM_jumpi_oog_step
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hJumpiGas :
      (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
       let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
       let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
       let s3 := Ethereum.EVM.mstoreNextState s2
        (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
       let s4 := Ethereum.EVM.callvalueNextState s3
       let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
       let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
       let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
       s7.machineState.gasAvailable.toNat < GasConstants.Ghigh)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s7 = .error .OutOfGass := by
  intro s0 s1 s2 s3 s4 s5 s6 s7
  have hDecode :
      Ethereum.EVM.decode I.code s7.machineState.pc = some (.JUMPI, .none) := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7] using
      truthEVM_jumpi_decode
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode
  have hStack :
      s7.machineState.stack =
        (⟨0x0e⟩ : Ethereum.UInt256) :: Ethereum.UInt256.isZero I.weiValue :: I.weiValue :: [] := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7] using
      (truthEVM_jumpi_stack
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I))
  exact Ethereum.EVM.Xstep_jumpi_oog_of_decode hDecode hStack
    (by simpa [s0, s1, s2, s3, s4, s5, s6, s7] using hJumpiGas)

lemma truthEVM_jumpi_oog
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow))
    (hCallvalueGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         s3.machineState.gasAvailable.toNat < GasConstants.Gbase))
    (hDupGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         s4.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hIszeroGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         s5.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hPushDestGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         s6.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hJumpiGas :
      (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
       let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
       let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
       let s3 := Ethereum.EVM.mstoreNextState s2
        (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
       let s4 := Ethereum.EVM.callvalueNextState s3
       let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
       let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
       let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
       s7.machineState.gasAvailable.toNat < GasConstants.Ghigh)) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
  let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
  let s3 := Ethereum.EVM.mstoreNextState s2
    (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
  let s4 := Ethereum.EVM.callvalueNextState s3
  let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
  let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
  let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
  have hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 7 s0 s7 := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7] using
      truthEVM_push_dest_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas hMemGas hVerylowGas hCallvalueGas hDupGas
        hIszeroGas hPushDestGas
  have hJumpiStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s7 = .error .OutOfGass := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7] using
      truthEVM_jumpi_oog_step
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hJumpiGas
  have hFuel : 7 ≤ g.toNat := by
    have hg15 : 15 ≤ g.toNat :=
      truthGas_ge_fifteen_of_mstore_memory_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hFirstGas hSecondGas hMemGas
    omega
  exact EVM_Xi_of_initial_continue_trace_error_of_le
    (n := 7)
    hFuel
    (by simpa [s0] using hTrace)
    hJumpiStep

lemma truthEVM_jumpi_continue
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hValidJump :
      (Ethereum.EVM.D_J I.code ⟨0⟩).contains (⟨0x0e⟩ : Ethereum.UInt256) = true)
    (hJumpiGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
         s7.machineState.gasAvailable.toNat < GasConstants.Ghigh)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
      (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s7 = .ok (s8, none) := by
  intro s0 s1 s2 s3 s4 s5 s6 s7 s8
  have hDecode :
      Ethereum.EVM.decode I.code s7.machineState.pc = some (.JUMPI, .none) := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7] using
      truthEVM_jumpi_decode
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode
  have hStack :
      s7.machineState.stack =
        (⟨0x0e⟩ : Ethereum.UInt256) :: Ethereum.UInt256.isZero I.weiValue :: I.weiValue :: [] := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7] using
      (truthEVM_jumpi_stack
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I))
  exact Ethereum.EVM.Xstep_jumpi_continue_of_decode hDecode hStack
    (by simpa [s0, s1, s2, s3, s4, s5, s6, s7] using hJumpiGas)
    (by
      intro _hCond
      exact hValidJump)
    (by simp)

lemma truthEVM_jumpi_fallthrough_continue
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hValue : I.weiValue ≠ (⟨0⟩ : Ethereum.UInt256))
    (hJumpiGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
         s7.machineState.gasAvailable.toNat < GasConstants.Ghigh)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
      (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s7 = .ok (s8, none) := by
  intro s0 s1 s2 s3 s4 s5 s6 s7 s8
  have hDecode :
      Ethereum.EVM.decode I.code s7.machineState.pc = some (.JUMPI, .none) := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7] using
      truthEVM_jumpi_decode
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode
  have hStack :
      s7.machineState.stack =
        (⟨0x0e⟩ : Ethereum.UInt256) :: Ethereum.UInt256.isZero I.weiValue :: I.weiValue :: [] := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7] using
      (truthEVM_jumpi_stack
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I))
  exact Ethereum.EVM.Xstep_jumpi_fallthrough_continue_of_decode hDecode hStack
    (by simpa [s0, s1, s2, s3, s4, s5, s6, s7] using hJumpiGas)
    (Ethereum.UInt256.isZero_bne_zero_eq_false_of_ne_zero hValue)
    (by simp)

lemma truthEVM_jumpi_trace
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hValidJump :
      (Ethereum.EVM.D_J I.code ⟨0⟩).contains (⟨0x0e⟩ : Ethereum.UInt256) = true)
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow))
    (hCallvalueGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         s3.machineState.gasAvailable.toNat < GasConstants.Gbase))
    (hDupGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         s4.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hIszeroGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         s5.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hPushDestGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         s6.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hJumpiGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
         s7.machineState.gasAvailable.toNat < GasConstants.Ghigh)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
      (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
    Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 8 s0 s8 := by
  intro s0 s1 s2 s3 s4 s5 s6 s7 s8
  have hTrace7 :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 7 s0 s7 := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7] using
      truthEVM_push_dest_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas hMemGas hVerylowGas hCallvalueGas hDupGas
        hIszeroGas hPushDestGas
  have hJumpiStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s7 = .ok (s8, none) := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8] using
      truthEVM_jumpi_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hValidJump hJumpiGas
  simpa using Ethereum.EVM.ContinueTrace.snoc hTrace7 hJumpiStep

lemma truthEVM_jumpi_fallthrough_trace
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hValue : I.weiValue ≠ (⟨0⟩ : Ethereum.UInt256))
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow))
    (hCallvalueGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         s3.machineState.gasAvailable.toNat < GasConstants.Gbase))
    (hDupGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         s4.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hIszeroGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         s5.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hPushDestGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         s6.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hJumpiGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
         s7.machineState.gasAvailable.toNat < GasConstants.Ghigh)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
      (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
    Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 8 s0 s8 := by
  intro s0 s1 s2 s3 s4 s5 s6 s7 s8
  have hTrace7 :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 7 s0 s7 := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7] using
      truthEVM_push_dest_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas hMemGas hVerylowGas hCallvalueGas hDupGas
        hIszeroGas hPushDestGas
  have hJumpiStep :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s7 = .ok (s8, none) := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8] using
      truthEVM_jumpi_fallthrough_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hValue hJumpiGas
  simpa using Ethereum.EVM.ContinueTrace.snoc hTrace7 hJumpiStep

lemma truthEVM_jumpdest_decode_of_callvalue_zero
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hValue : I.weiValue = (⟨0⟩ : Ethereum.UInt256)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
      (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
    Ethereum.EVM.decode I.code s8.machineState.pc = some (.JUMPDEST, .none) := by
  rw [hValue]
  simp [Ethereum.EVM.jumpiNextState, Ethereum.EVM.push1NextState, Ethereum.EVM.mstoreNextState,
    Ethereum.EVM.callvalueNextState, Ethereum.EVM.dup1NextState, Ethereum.EVM.iszeroNextState,
    hCode, Ethereum.UInt256.ofNat, Id.run]
  exact truthBytecode_decode_14

lemma truthEVM_push0_decode_of_callvalue_nonzero
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hValue : I.weiValue ≠ (⟨0⟩ : Ethereum.UInt256)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
      (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
    Ethereum.EVM.decode I.code s8.machineState.pc = some (.PUSH0, .none) := by
  have hCond := Ethereum.UInt256.isZero_bne_zero_eq_false_of_ne_zero hValue
  simp [Ethereum.EVM.jumpiNextState, hCond, Ethereum.EVM.push1NextState,
    Ethereum.EVM.mstoreNextState, Ethereum.EVM.callvalueNextState, Ethereum.EVM.dup1NextState,
    Ethereum.EVM.iszeroNextState, hCode, Ethereum.UInt256.ofNat, Id.run]
  exact truthBytecode_decode_11

lemma truthEVM_fallthrough_first_push0_oog
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hValue : I.weiValue ≠ (⟨0⟩ : Ethereum.UInt256))
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow))
    (hCallvalueGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         s3.machineState.gasAvailable.toNat < GasConstants.Gbase))
    (hDupGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         s4.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hIszeroGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         s5.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hPushDestGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         s6.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hJumpiGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
         s7.machineState.gasAvailable.toNat < GasConstants.Ghigh))
    (hPush0Gas :
      (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
       let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
       let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
       let s3 := Ethereum.EVM.mstoreNextState s2
        (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
       let s4 := Ethereum.EVM.callvalueNextState s3
       let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
       let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
       let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
       let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
        (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
       s8.machineState.gasAvailable.toNat < GasConstants.Gbase)) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
  let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
  let s3 := Ethereum.EVM.mstoreNextState s2
    (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
  let s4 := Ethereum.EVM.callvalueNextState s3
  let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
  let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
  let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
  let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
    (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
  have hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 8 s0 s8 := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8] using
      truthEVM_jumpi_fallthrough_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hValue hFirstGas hSecondGas hMemGas hVerylowGas hCallvalueGas
        hDupGas hIszeroGas hPushDestGas hJumpiGas
  have hDecode :
      Ethereum.EVM.decode I.code s8.machineState.pc = some (.PUSH0, .none) := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8] using
      truthEVM_push0_decode_of_callvalue_nonzero
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hValue
  have hPush0Gas' : s8.machineState.gasAvailable.toNat < GasConstants.Gbase := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8] using hPush0Gas
  have hPush0Step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s8 = .error .OutOfGass :=
    Ethereum.EVM.Xstep_push0_oog_of_decode hDecode hPush0Gas'
  have hFuel : 8 ≤ g.toNat := by
    have hg15 : 15 ≤ g.toNat :=
      truthGas_ge_fifteen_of_mstore_memory_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hFirstGas hSecondGas hMemGas
    omega
  exact EVM_Xi_of_initial_continue_trace_error_of_le
    (n := 8)
    hFuel
    (by simpa [s0] using hTrace)
    hPush0Step

lemma truthEVM_fallthrough_first_push0_continue
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hValue : I.weiValue ≠ (⟨0⟩ : Ethereum.UInt256))
    (hPush0Gas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
         let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
          (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
         s8.machineState.gasAvailable.toNat < GasConstants.Gbase)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
      (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
    let s9 := Ethereum.EVM.push0NextState s8
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s8 = .ok (s9, none) := by
  intro s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
  have hDecode :
      Ethereum.EVM.decode I.code s8.machineState.pc = some (.PUSH0, .none) := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8] using
      truthEVM_push0_decode_of_callvalue_nonzero
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hValue
  exact Ethereum.EVM.Xstep_push0_continue_of_decode hDecode
    (by simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8] using hPush0Gas)
    (by simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, Ethereum.EVM.jumpiNextState,
      Ethereum.EVM.push1NextState, Ethereum.EVM.mstoreNextState, Ethereum.EVM.callvalueNextState,
      Ethereum.EVM.dup1NextState, Ethereum.EVM.iszeroNextState])

lemma truthEVM_fallthrough_first_push0_trace
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hValue : I.weiValue ≠ (⟨0⟩ : Ethereum.UInt256))
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow))
    (hCallvalueGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         s3.machineState.gasAvailable.toNat < GasConstants.Gbase))
    (hDupGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         s4.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hIszeroGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         s5.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hPushDestGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         s6.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hJumpiGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
         s7.machineState.gasAvailable.toNat < GasConstants.Ghigh))
    (hPush0Gas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
         let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
          (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
         s8.machineState.gasAvailable.toNat < GasConstants.Gbase)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
      (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
    let s9 := Ethereum.EVM.push0NextState s8
    Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 9 s0 s9 := by
  intro s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
  have hTrace8 :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 8 s0 s8 := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8] using
      truthEVM_jumpi_fallthrough_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hValue hFirstGas hSecondGas hMemGas hVerylowGas hCallvalueGas
        hDupGas hIszeroGas hPushDestGas hJumpiGas
  have hPush0Step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s8 = .ok (s9, none) := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9] using
      truthEVM_fallthrough_first_push0_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hValue hPush0Gas
  simpa using Ethereum.EVM.ContinueTrace.snoc hTrace8 hPush0Step

lemma truthEVM_second_push0_decode_of_callvalue_nonzero
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hValue : I.weiValue ≠ (⟨0⟩ : Ethereum.UInt256)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
      (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
    let s9 := Ethereum.EVM.push0NextState s8
    Ethereum.EVM.decode I.code s9.machineState.pc = some (.PUSH0, .none) := by
  have hCond := Ethereum.UInt256.isZero_bne_zero_eq_false_of_ne_zero hValue
  simp [Ethereum.EVM.jumpiNextState, hCond, Ethereum.EVM.push1NextState,
    Ethereum.EVM.mstoreNextState, Ethereum.EVM.callvalueNextState, Ethereum.EVM.dup1NextState,
    Ethereum.EVM.iszeroNextState, Ethereum.EVM.push0NextState, hCode, Ethereum.UInt256.ofNat,
    Id.run]
  exact truthBytecode_decode_12

lemma truthEVM_fallthrough_second_push0_oog
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hValue : I.weiValue ≠ (⟨0⟩ : Ethereum.UInt256))
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow))
    (hCallvalueGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         s3.machineState.gasAvailable.toNat < GasConstants.Gbase))
    (hDupGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         s4.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hIszeroGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         s5.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hPushDestGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         s6.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hJumpiGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
         s7.machineState.gasAvailable.toNat < GasConstants.Ghigh))
    (hPush0Gas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
         let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
          (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
         s8.machineState.gasAvailable.toNat < GasConstants.Gbase))
    (hSecondPush0Gas :
      (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
       let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
       let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
       let s3 := Ethereum.EVM.mstoreNextState s2
        (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
       let s4 := Ethereum.EVM.callvalueNextState s3
       let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
       let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
       let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
       let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
        (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
       let s9 := Ethereum.EVM.push0NextState s8
       s9.machineState.gasAvailable.toNat < GasConstants.Gbase)) :
    Ethereum.EVM.Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .error .OutOfGass := by
  let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
  let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
  let s3 := Ethereum.EVM.mstoreNextState s2
    (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
  let s4 := Ethereum.EVM.callvalueNextState s3
  let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
  let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
  let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
  let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
    (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
  let s9 := Ethereum.EVM.push0NextState s8
  have hTrace :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 9 s0 s9 := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9] using
      truthEVM_fallthrough_first_push0_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hValue hFirstGas hSecondGas hMemGas hVerylowGas hCallvalueGas
        hDupGas hIszeroGas hPushDestGas hJumpiGas hPush0Gas
  have hDecode :
      Ethereum.EVM.decode I.code s9.machineState.pc = some (.PUSH0, .none) := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9] using
      truthEVM_second_push0_decode_of_callvalue_nonzero
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hValue
  have hSecondPush0Gas' : s9.machineState.gasAvailable.toNat < GasConstants.Gbase := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9] using hSecondPush0Gas
  have hPush0Step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s9 = .error .OutOfGass :=
    Ethereum.EVM.Xstep_push0_oog_of_decode hDecode hSecondPush0Gas'
  have hFuel : 9 ≤ g.toNat := by
    have hg15 : 15 ≤ g.toNat :=
      truthGas_ge_fifteen_of_mstore_memory_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hFirstGas hSecondGas hMemGas
    omega
  exact EVM_Xi_of_initial_continue_trace_error_of_le
    (n := 9)
    hFuel
    (by simpa [s0] using hTrace)
    hPush0Step

lemma truthEVM_fallthrough_second_push0_continue
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hValue : I.weiValue ≠ (⟨0⟩ : Ethereum.UInt256))
    (hSecondPush0Gas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
         let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
          (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
         let s9 := Ethereum.EVM.push0NextState s8
         s9.machineState.gasAvailable.toNat < GasConstants.Gbase)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
      (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
    let s9 := Ethereum.EVM.push0NextState s8
    let s10 := Ethereum.EVM.push0NextState s9
    Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s9 = .ok (s10, none) := by
  intro s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
  have hDecode :
      Ethereum.EVM.decode I.code s9.machineState.pc = some (.PUSH0, .none) := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9] using
      truthEVM_second_push0_decode_of_callvalue_nonzero
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hValue
  exact Ethereum.EVM.Xstep_push0_continue_of_decode hDecode
    (by simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9] using hSecondPush0Gas)
    (by simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, Ethereum.EVM.jumpiNextState,
      Ethereum.EVM.push1NextState, Ethereum.EVM.mstoreNextState, Ethereum.EVM.callvalueNextState,
      Ethereum.EVM.dup1NextState, Ethereum.EVM.iszeroNextState, Ethereum.EVM.push0NextState])

lemma truthEVM_fallthrough_second_push0_trace
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hValue : I.weiValue ≠ (⟨0⟩ : Ethereum.UInt256))
    (hFirstGas : ¬ g.toNat < GasConstants.Gverylow)
    (hSecondGas :
      ¬ (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow)
    (hMemGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE))
    (hVerylowGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         (s2.machineState.gasAvailable -
            Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
            GasConstants.Gverylow))
    (hCallvalueGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         s3.machineState.gasAvailable.toNat < GasConstants.Gbase))
    (hDupGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         s4.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hIszeroGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         s5.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hPushDestGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         s6.machineState.gasAvailable.toNat < GasConstants.Gverylow))
    (hJumpiGas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
         s7.machineState.gasAvailable.toNat < GasConstants.Ghigh))
    (hPush0Gas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
         let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
          (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
         s8.machineState.gasAvailable.toNat < GasConstants.Gbase))
    (hSecondPush0Gas :
      ¬ (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         let s3 := Ethereum.EVM.mstoreNextState s2
          (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
         let s4 := Ethereum.EVM.callvalueNextState s3
         let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
         let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
         let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
         let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
          (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
         let s9 := Ethereum.EVM.push0NextState s8
         s9.machineState.gasAvailable.toNat < GasConstants.Gbase)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
      (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
    let s9 := Ethereum.EVM.push0NextState s8
    let s10 := Ethereum.EVM.push0NextState s9
    Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 10 s0 s10 := by
  intro s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
  have hTrace9 :
      Ethereum.EVM.ContinueTrace (Ethereum.EVM.D_J I.code ⟨0⟩) 9 s0 s9 := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9] using
      truthEVM_fallthrough_first_push0_trace
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hValue hFirstGas hSecondGas hMemGas hVerylowGas hCallvalueGas
        hDupGas hIszeroGas hPushDestGas hJumpiGas hPush0Gas
  have hPush0Step :
      Ethereum.EVM.Xstep (Ethereum.EVM.D_J I.code ⟨0⟩) s9 = .ok (s10, none) := by
    simpa [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10] using
      truthEVM_fallthrough_second_push0_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hValue hSecondPush0Gas
  simpa using Ethereum.EVM.ContinueTrace.snoc hTrace9 hPush0Step

lemma truthEVM_revert_decode_of_callvalue_nonzero
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv}
    (hCode : I.code = truthBytecode)
    (hValue : I.weiValue ≠ (⟨0⟩ : Ethereum.UInt256)) :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
      (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
    let s9 := Ethereum.EVM.push0NextState s8
    let s10 := Ethereum.EVM.push0NextState s9
    Ethereum.EVM.decode I.code s10.machineState.pc = some (.REVERT, .none) := by
  have hCond := Ethereum.UInt256.isZero_bne_zero_eq_false_of_ne_zero hValue
  simp [Ethereum.EVM.jumpiNextState, hCond, Ethereum.EVM.push1NextState,
    Ethereum.EVM.mstoreNextState, Ethereum.EVM.callvalueNextState, Ethereum.EVM.dup1NextState,
    Ethereum.EVM.iszeroNextState, Ethereum.EVM.push0NextState, hCode, Ethereum.UInt256.ofNat,
    Id.run]
  exact truthBytecode_decode_13

lemma truthEVM_revert_stack_of_callvalue_nonzero
    {createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare}
    {genesisBlockHeader : Ethereum.BlockHeader}
    {blocks : Ethereum.ProcessedBlocks}
    {σ σ₀ : Ethereum.AccountMap}
    {g : Ethereum.UInt256}
    {A : Ethereum.Substate}
    {I : Ethereum.ExecutionEnv} :
    let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
    let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
    let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
    let s3 := Ethereum.EVM.mstoreNextState s2
      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
    let s4 := Ethereum.EVM.callvalueNextState s3
    let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
    let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
    let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
    let s8 := Ethereum.EVM.jumpiNextState s7 (⟨0x0e⟩ : Ethereum.UInt256)
      (Ethereum.UInt256.isZero I.weiValue) [I.weiValue]
    let s9 := Ethereum.EVM.push0NextState s8
    let s10 := Ethereum.EVM.push0NextState s9
    s10.machineState.stack =
      (⟨0⟩ : Ethereum.UInt256) :: (⟨0⟩ : Ethereum.UInt256) :: I.weiValue :: [] := by
  intro s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
  simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10,
    Ethereum.EVM.jumpiNextState, Ethereum.EVM.push1NextState, Ethereum.EVM.mstoreNextState,
    Ethereum.EVM.callvalueNextState, Ethereum.EVM.dup1NextState, Ethereum.EVM.iszeroNextState,
    Ethereum.EVM.push0NextState]

/-- The runtime bytecode refines the Act specification, for every initial state.
    Proof deferred. -/
theorem truthCorrect :
    runtimeEquivalence!?! truthConfig truthBytecode truthContract := by
  apply runtimeEquivalence_intro
  intro createdAccounts genesisBlockHeader blocks σ σ₀ g A I hCode hCalldataSize
  by_cases hFirstGas : g.toNat < GasConstants.Gverylow
  · exact truthRuntime_outOfGas_of_evm
      (truthEVM_first_push_oog
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas)
  · -- Remaining core obligation: characterize `Ethereum.EVM.Ξ` after the first
    -- `PUSH1` step, for symbolic gas and all calldata/callvalue cases.
    have hFirstStep := truthEVM_first_push_continue
      (createdAccounts := createdAccounts)
      (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks)
      (σ := σ)
      (σ₀ := σ₀)
      (g := g)
      (A := A)
      (I := I)
      hCode hFirstGas
    by_cases hSecondGas :
      (g - Ethereum.UInt256.ofNat GasConstants.Gverylow).toNat < GasConstants.Gverylow
    · exact truthRuntime_outOfGas_of_evm
        (truthEVM_second_push_oog
          (createdAccounts := createdAccounts)
          (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks)
          (σ := σ)
          (σ₀ := σ₀)
          (g := g)
          (A := A)
          (I := I)
          hCode hFirstGas hSecondGas)
    · have hSecondStep := truthEVM_second_push_continue
        (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks)
        (σ := σ)
        (σ₀ := σ₀)
        (g := g)
        (A := A)
        (I := I)
        hCode hFirstGas hSecondGas
      by_cases hMstoreMemGas :
        (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
         let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
         let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
         s2.machineState.gasAvailable.toNat < Ethereum.EVM.memoryExpansionCost s2 .MSTORE)
      · exact truthRuntime_outOfGas_of_evm
          (truthEVM_mstore_memory_oog
            (createdAccounts := createdAccounts)
            (genesisBlockHeader := genesisBlockHeader)
            (blocks := blocks)
            (σ := σ)
            (σ₀ := σ₀)
            (g := g)
            (A := A)
            (I := I)
            hCode hFirstGas hSecondGas hMstoreMemGas)
      · by_cases hMstoreVerylowGas :
          (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
           let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
           let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
           (s2.machineState.gasAvailable -
              Ethereum.UInt256.ofNat (Ethereum.EVM.memoryExpansionCost s2 .MSTORE)).toNat <
              GasConstants.Gverylow)
        · exact truthRuntime_outOfGas_of_evm
            (truthEVM_mstore_verylow_oog
              (createdAccounts := createdAccounts)
              (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks)
              (σ := σ)
              (σ₀ := σ₀)
              (g := g)
              (A := A)
              (I := I)
              hCode hFirstGas hSecondGas hMstoreMemGas hMstoreVerylowGas)
        · have hMstoreStep := truthEVM_mstore_continue
            (createdAccounts := createdAccounts)
            (genesisBlockHeader := genesisBlockHeader)
            (blocks := blocks)
            (σ := σ)
            (σ₀ := σ₀)
            (g := g)
            (A := A)
            (I := I)
            hCode hMstoreMemGas hMstoreVerylowGas
          by_cases hCallvalueGas :
            (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
             let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
             let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
             let s3 := Ethereum.EVM.mstoreNextState s2
              (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
             s3.machineState.gasAvailable.toNat < GasConstants.Gbase)
          · exact truthRuntime_outOfGas_of_evm
              (truthEVM_callvalue_oog
                (createdAccounts := createdAccounts)
                (genesisBlockHeader := genesisBlockHeader)
                (blocks := blocks)
                (σ := σ)
                (σ₀ := σ₀)
                (g := g)
                (A := A)
                (I := I)
                hCode hFirstGas hSecondGas hMstoreMemGas hMstoreVerylowGas hCallvalueGas)
          · have hCallvalueStep := truthEVM_callvalue_continue
              (createdAccounts := createdAccounts)
              (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks)
              (σ := σ)
              (σ₀ := σ₀)
              (g := g)
              (A := A)
              (I := I)
              hCode hCallvalueGas
            by_cases hDupGas :
              (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
               let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
               let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
               let s3 := Ethereum.EVM.mstoreNextState s2
                (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
               let s4 := Ethereum.EVM.callvalueNextState s3
               s4.machineState.gasAvailable.toNat < GasConstants.Gverylow)
            · exact truthRuntime_outOfGas_of_evm
                (truthEVM_dup1_oog
                  (createdAccounts := createdAccounts)
                  (genesisBlockHeader := genesisBlockHeader)
                  (blocks := blocks)
                  (σ := σ)
                  (σ₀ := σ₀)
                  (g := g)
                  (A := A)
                  (I := I)
                  hCode hFirstGas hSecondGas hMstoreMemGas hMstoreVerylowGas
                  hCallvalueGas hDupGas)
            · have hDupStep := truthEVM_dup1_continue
                (createdAccounts := createdAccounts)
                (genesisBlockHeader := genesisBlockHeader)
                (blocks := blocks)
                (σ := σ)
                (σ₀ := σ₀)
                (g := g)
                (A := A)
                (I := I)
                hCode hDupGas
              by_cases hIszeroGas :
                (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
                 let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
                 let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
                 let s3 := Ethereum.EVM.mstoreNextState s2
                  (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
                 let s4 := Ethereum.EVM.callvalueNextState s3
                 let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
                 s5.machineState.gasAvailable.toNat < GasConstants.Gverylow)
              · exact truthRuntime_outOfGas_of_evm
                  (truthEVM_iszero_oog
                    (createdAccounts := createdAccounts)
                    (genesisBlockHeader := genesisBlockHeader)
                    (blocks := blocks)
                    (σ := σ)
                    (σ₀ := σ₀)
                    (g := g)
                    (A := A)
                    (I := I)
                    hCode hFirstGas hSecondGas hMstoreMemGas hMstoreVerylowGas
                    hCallvalueGas hDupGas hIszeroGas)
              · have hIszeroStep := truthEVM_iszero_continue
                  (createdAccounts := createdAccounts)
                  (genesisBlockHeader := genesisBlockHeader)
                  (blocks := blocks)
                  (σ := σ)
                  (σ₀ := σ₀)
                  (g := g)
                  (A := A)
                  (I := I)
                  hCode hIszeroGas
                by_cases hPushDestGas :
                  (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
                   let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
                   let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
                   let s3 := Ethereum.EVM.mstoreNextState s2
                    (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
                   let s4 := Ethereum.EVM.callvalueNextState s3
                   let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
                   let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
                   s6.machineState.gasAvailable.toNat < GasConstants.Gverylow)
                · exact truthRuntime_outOfGas_of_evm
                    (truthEVM_push_dest_oog
                      (createdAccounts := createdAccounts)
                      (genesisBlockHeader := genesisBlockHeader)
                      (blocks := blocks)
                      (σ := σ)
                      (σ₀ := σ₀)
                      (g := g)
                      (A := A)
                      (I := I)
                      hCode hFirstGas hSecondGas hMstoreMemGas hMstoreVerylowGas
                      hCallvalueGas hDupGas hIszeroGas hPushDestGas)
                · have hPushDestStep := truthEVM_push_dest_continue
                    (createdAccounts := createdAccounts)
                    (genesisBlockHeader := genesisBlockHeader)
                    (blocks := blocks)
                    (σ := σ)
                    (σ₀ := σ₀)
                    (g := g)
                    (A := A)
                    (I := I)
                    hCode hPushDestGas
                  by_cases hJumpiGas :
                    (let s0 := initialEVMState createdAccounts genesisBlockHeader blocks σ σ₀ g A I
                     let s1 := Ethereum.EVM.push1NextState s0 (⟨0x80⟩ : Ethereum.UInt256)
                     let s2 := Ethereum.EVM.push1NextState s1 (⟨0x40⟩ : Ethereum.UInt256)
                     let s3 := Ethereum.EVM.mstoreNextState s2
                      (⟨0x40⟩ : Ethereum.UInt256) (⟨0x80⟩ : Ethereum.UInt256) []
                     let s4 := Ethereum.EVM.callvalueNextState s3
                     let s5 := Ethereum.EVM.dup1NextState s4 I.weiValue []
                     let s6 := Ethereum.EVM.iszeroNextState s5 I.weiValue [I.weiValue]
                     let s7 := Ethereum.EVM.push1NextState s6 (⟨0x0e⟩ : Ethereum.UInt256)
                     s7.machineState.gasAvailable.toNat < GasConstants.Ghigh)
                  · exact truthRuntime_outOfGas_of_evm
                      (truthEVM_jumpi_oog
                        (createdAccounts := createdAccounts)
                        (genesisBlockHeader := genesisBlockHeader)
                        (blocks := blocks)
                        (σ := σ)
                        (σ₀ := σ₀)
                        (g := g)
                        (A := A)
                        (I := I)
                        hCode hFirstGas hSecondGas hMstoreMemGas hMstoreVerylowGas
                        hCallvalueGas hDupGas hIszeroGas hPushDestGas hJumpiGas)
                  · -- Remaining core obligation: split on callvalue after the
                    -- successful non-payable-guard `JUMPI`; the zero-callvalue
                    -- branch also needs a kernel-checked valid-jump-table fact
                    -- for bytecode offset `0x0e`.
                    sorry
