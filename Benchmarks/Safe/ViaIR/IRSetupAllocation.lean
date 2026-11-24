import Benchmarks.Safe.ViaIR.SetupCalldataFacts
import Benchmarks.Safe.ViaIR.SetupModulesSource
import Benchmarks.Safe.ViaIR.IRMemoryAllocation
import Benchmarks.Safe.ViaIR.SetupSource

variable {fork : Ethereum.Fork}

/-! Boundary evidence for the setup data allocation. The calldata tail is symbolic;
only its finite ABI prefix is evaluated. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

def safeIRSetupAllocationLength : Nat := 2 ^ 64 - 255

def safeIRSetupAllocationPrefix : ByteArray :=
  ⟨#[0xb6, 0x3e, 0x80, 0x0d]⟩ ++
    (⟨256⟩ : UInt256).toByteArray ++ (⟨1⟩ : UInt256).toByteArray ++
    (⟨0⟩ : UInt256).toByteArray ++ (⟨320⟩ : UInt256).toByteArray ++
    (⟨0⟩ : UInt256).toByteArray ++ (⟨0⟩ : UInt256).toByteArray ++
    (⟨0⟩ : UInt256).toByteArray ++ (⟨0⟩ : UInt256).toByteArray ++
    (⟨1⟩ : UInt256).toByteArray ++ (⟨8192⟩ : UInt256).toByteArray ++
    (UInt256.ofNat safeIRSetupAllocationLength).toByteArray

def safeIRSetupAllocationCalldata : ByteArray :=
  safeIRSetupAllocationPrefix ++ ByteArray.zeroes safeIRSetupAllocationLength

theorem safeIRSetupAllocationPrefix_size : safeIRSetupAllocationPrefix.size = 356 := by
  native_decide

theorem safeIRSetupAllocationCalldata_size :
    safeIRSetupAllocationCalldata.size = 2 ^ 64 + 101 := by
  rw [safeIRSetupAllocationCalldata, ByteArray.size_append,
    safeIRSetupAllocationPrefix_size, ByteArray_zeroes_size]
  decide +kernel

private theorem dispatchSamePrefix (c : ContractDecl) (a b : ByteArray)
    (h : a.extract 0 4 = b.extract 0 4) :
    selectorDispatchMsg c a = selectorDispatchMsg c b := by
  rw [selectorDispatchMsg_eq_dispatchList, selectorDispatchMsg_eq_dispatchList]
  generalize c.transitions = ts
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [dispatchList_cons, h, ih]

theorem safeIRSetupAllocationDispatch :
    selectorDispatchMsg contract safeIRSetupAllocationCalldata = some setupTransition := by
  rw [dispatchSamePrefix contract safeIRSetupAllocationCalldata safeIRSetupAllocationPrefix
    (extract_append_left _ _ _ _ (by rw [safeIRSetupAllocationPrefix_size]; decide))]
  native_decide

theorem safeIRSetupAllocationWord (off : Nat) (h : off + 32 ≤ 356) :
    calldataWord safeIRSetupAllocationCalldata off =
      calldataWord safeIRSetupAllocationPrefix off := by
  have hb : (calldataWord safeIRSetupAllocationCalldata off).toByteArray =
      (calldataWord safeIRSetupAllocationPrefix off).toByteArray := by
    rw [calldataWord_bytes_at (by rw [safeIRSetupAllocationCalldata_size]; omega),
      calldataWord_bytes_at (by rw [safeIRSetupAllocationPrefix_size]; exact h)]
    exact extract_append_left _ _ _ _ (by rw [safeIRSetupAllocationPrefix_size]; exact h)
  have hw := congrArg (fun b ↦ UInt256.ofNat (fromByteArrayBigEndian b)) hb
  simpa only [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat] using hw

theorem safeIRSetupAllocationBounds :
    SetupCalldataBounds safeIRSetupAllocationCalldata 1 safeIRSetupAllocationLength := by
  have h4 : calldataWord safeIRSetupAllocationCalldata 4 = ⟨256⟩ := by
    rw [safeIRSetupAllocationWord 4 (by decide)]; native_decide
  have h100 : calldataWord safeIRSetupAllocationCalldata 100 = ⟨320⟩ := by
    rw [safeIRSetupAllocationWord 100 (by decide)]; native_decide
  constructor
  · rw [safeIRSetupAllocationCalldata_size]; decide
  · rw [safeIRSetupAllocationCalldata_size]; decide
  · rw [h4]; decide
  · rw [h4]; change calldataWord _ 260 = _
    rw [safeIRSetupAllocationWord 260 (by decide)]; native_decide
  · decide
  · rw [setupOwnersStart, h4, safeIRSetupAllocationCalldata_size]; decide
  · rw [safeIRSetupAllocationWord 68 (by decide)]; native_decide
  · rw [h100]; decide
  · rw [h100]; change calldataWord _ 324 = _
    rw [safeIRSetupAllocationWord 324 (by decide)]; native_decide
  · decide
  · rw [setupDataStart, h100, safeIRSetupAllocationCalldata_size]; decide
  · rw [safeIRSetupAllocationWord 132 (by decide)]; native_decide
  · rw [safeIRSetupAllocationWord 164 (by decide)]; native_decide
  · rw [safeIRSetupAllocationWord 228 (by decide)]; native_decide

theorem safeIRSetupAllocationOwners :
    calldataWords safeIRSetupAllocationCalldata
      (setupOwnersStart safeIRSetupAllocationCalldata) 1 = [⟨8192⟩] := by
  have h4 : calldataWord safeIRSetupAllocationCalldata 4 = ⟨256⟩ := by
    rw [safeIRSetupAllocationWord 4 (by decide)]; native_decide
  rw [setupOwnersStart, h4]
  change [calldataWord safeIRSetupAllocationCalldata 292] = _
  rw [safeIRSetupAllocationWord 292 (by decide)]; native_decide

private theorem setupAccepted {cd : ByteArray} {n len : Nat}
    (hb : SetupCalldataBounds cd n len)
    (hc : ∀ w ∈ calldataWords cd (setupOwnersStart cd) n,
      w.toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? (setupTransition.params.map Param.name)
      (transitionSignature setupTransition).paramTypes cd =
      some (setupCalldataInput cd n len).args := by
  change decodeCalldata setupNames setupTypes cd = _
  exact (decodeSetupBounded hb).trans (if_pos hc)

theorem safeIRSetupAllocationDecoding :
    config.externalABI.decodeCalldata? (setupTransition.params.map Param.name)
      (transitionSignature setupTransition).paramTypes safeIRSetupAllocationCalldata =
      some (setupCalldataInput safeIRSetupAllocationCalldata 1
        safeIRSetupAllocationLength).args := by
  apply setupAccepted safeIRSetupAllocationBounds
  rw [safeIRSetupAllocationOwners]
  simp only [List.mem_singleton]
  intro w hw
  subst w
  decide

theorem safeIRSetupAllocationPayload :
    (setupCalldataInput safeIRSetupAllocationCalldata 1 safeIRSetupAllocationLength).payload =
      ByteArray.zeroes safeIRSetupAllocationLength := by
  have h100 : calldataWord safeIRSetupAllocationCalldata 100 = ⟨320⟩ := by
    rw [safeIRSetupAllocationWord 100 (by decide)]; native_decide
  change safeIRSetupAllocationCalldata.extract (setupDataStart safeIRSetupAllocationCalldata)
    (setupDataStart safeIRSetupAllocationCalldata + safeIRSetupAllocationLength) = _
  rw [setupDataStart, h100]
  exact extract_append_right' _ _ _ _ safeIRSetupAllocationPrefix_size.symm
    (by rw [safeIRSetupAllocationPrefix_size, ByteArray_zeroes_size]; rfl)

theorem safeIRSetupAllocationNoCalls :
    let p := setupCalldataInput safeIRSetupAllocationCalldata 1 safeIRSetupAllocationLength
    p.threshold = ⟨1⟩ ∧ p.target = ⟨0⟩ ∧ p.fallbackHandler = ⟨0⟩ ∧ p.payment = ⟨0⟩ := by
  change calldataWord safeIRSetupAllocationCalldata 36 = ⟨1⟩ ∧
    calldataWord safeIRSetupAllocationCalldata 68 = ⟨0⟩ ∧
    calldataWord safeIRSetupAllocationCalldata 132 = ⟨0⟩ ∧
    calldataWord safeIRSetupAllocationCalldata 196 = ⟨0⟩
  rw [safeIRSetupAllocationWord 36 (by decide), safeIRSetupAllocationWord 68 (by decide),
    safeIRSetupAllocationWord 132 (by decide), safeIRSetupAllocationWord 196 (by decide)]
  native_decide

theorem safeIRSetupAllocationPointer :
    192 + 32 + ABI.paddedSize safeIRSetupAllocationLength = 2 ^ 64 := by
  decide +kernel

def safeIRSetupAllocationCursor : State :=
  { (default : State) with
    executionEnv := { (default : ExecutionEnv) with code := safeBytecode }
    machineState := { (default : MachineState) with
      pc := ⟨7208⟩
      stack := [⟨356⟩, UInt256.ofNat safeIRSetupAllocationLength,
        UInt256.ofNat (2 ^ 64 + 101), ⟨3409⟩]
      memory := writeWord ByteArray.empty 64 ⟨192⟩
      activeWords := ⟨3⟩
      gasAvailable := .ofUInt256 ⟨100000⟩ } }

theorem safeIRSetupAllocationExecution :
    (match X .cancun 100001 (D_J safeBytecode 0) safeIRSetupAllocationCursor with
      | .ok (.revert gas out) => gas.toNat > 99000 &&
          out == (⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ ++ (⟨0x41⟩ : UInt256).toByteArray)
      | _ => false) = true := by native_decide

theorem safeIRSetupAllocationSourceReturns (evm : State)
    (he : moduleLink evm ⟨1⟩ = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    let p : SetupModulesInput := ⟨⟨0⟩, ByteArray.zeroes safeIRSetupAllocationLength⟩
    ExecFuncBody fork config p.frame evm setupModulesFunction.body
      (.returned p.frame (p.state evm) none) := by
  exact safeSetupModulesZero (hperm := by assumption) _ evm he rfl

theorem safeIRSetupAllocationSourceCannotRevert (evm : State)
    (he : moduleLink evm ⟨1⟩ = ⟨0⟩) :
    let p : SetupModulesInput := ⟨⟨0⟩, ByteArray.zeroes safeIRSetupAllocationLength⟩
    ¬ExecFuncBody fork config p.frame evm setupModulesFunction.body .reverted := by
  let p : SetupModulesInput := ⟨⟨0⟩, ByteArray.zeroes safeIRSetupAllocationLength⟩
  have hg : evalExpr? config p.frame evm
      (eqE (.storage (modulesRef sentinelAddr)) zeroAddr) = .ok (.bool true) := by
    simpa only [he, decide_true] using safeSetupModulesEmpty p evm
  have hv := safeEvalModuleSentinel evm p.args
  have hs := safeAssignModuleLink evm p.args sentinelAddr ⟨1⟩ ⟨1⟩
    (by simp [SetupModulesInput.args])
    (by decide) (by decide) hv
  have hc : evalExpr? config p.frame (p.state evm)
      (neE (.var "to") zeroAddr) = .ok (.bool false) := by
    simpa only [p, ne_self_iff_false, decide_false] using
      safeSetupModulesCondition p (p.state evm) (by decide)
  change ¬ExecFuncBody fork config p.frame evm setupModulesFunction.body .reverted
  intro h
  cases h with
  | execBlockRevert h =>
    cases h with
    | consRevert h => cases h <;> simp_all
    | consNormal h ht =>
      cases h
      cases ht with
      | consRevert h => cases h <;> simp_all [SetupModulesInput.frame]
      | consNormal h ht =>
        cases h with
        | assign _ hv' hs' =>
          have heq := hv.symm.trans hv'
          cases heq
          have heq := hs.symm.trans hs'
          cases heq
          cases ht with
          | consNormal _ hn => cases hn
          | consRevert h =>
            cases h <;> simp_all [SetupModulesInput.frame, SetupModulesInput.state]
            rename_i hn
            cases hn

theorem safeIRSetupDataAllocationBound (owners data : Nat) :
    160 + 32 * owners + 32 + ABI.paddedSize data < 2 ^ 64 ↔
      32 * owners + data ≤ 2 ^ 64 - 224 := by
  unfold ABI.paddedSize
  omega

theorem safeIRSetupDataAllocationBound_covers_owners (owners data : Nat)
    (h : 32 * owners + data ≤ 2 ^ 64 - 224) : 160 + 32 * owners < 2 ^ 64 := by
  omega

theorem safeIRSetupAllocationFirstRejected :
    32 + (safeIRSetupAllocationLength - 1) ≤ 2 ^ 64 - 224 ∧
      ¬32 + safeIRSetupAllocationLength ≤ 2 ^ 64 - 224 := by
  decide +kernel

/-- The approved local guard rejects the allocation-boundary input in the source semantics. -/
theorem safeIRSetupAllocationGuardReverts (evm : State)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    let p := setupCalldataInput safeIRSetupAllocationCalldata 1 safeIRSetupAllocationLength
    ExecBlock fork config p.frame evm setupTransition.body .reverted := by
  apply safeSetupAllocationRevert (hperm := hperm) _ evm hv
  have hp := safeIRSetupAllocationNoCalls.2.2.2
  rw [SetupInput.allocationLimit, hp]
  simp only [ne_self_iff_false, false_and, ite_false]
  rw [safeIRSetupAllocationPayload, ByteArray_zeroes_size]
  change ¬32 * (calldataWords safeIRSetupAllocationCalldata
    (setupOwnersStart safeIRSetupAllocationCalldata) 1).length +
      safeIRSetupAllocationLength ≤ 2 ^ 64 - 224
  rw [safeIRSetupAllocationOwners]
  decide +kernel

/-- The setup token-payment encoder reserves another 128 bytes after the data buffer. -/
theorem safeIRSetupTokenAllocationBound (owners data : Nat) :
    160 + 32 * owners + 32 + ABI.paddedSize data + 128 < 2 ^ 64 ↔
      32 * owners + data ≤ 2 ^ 64 - 352 := by
  unfold ABI.paddedSize
  omega

theorem safeIRSetupTokenAllocationBoundary :
    32 + (2 ^ 64 - 256) ≤ 2 ^ 64 - 224 ∧
      192 + 32 + ABI.paddedSize (2 ^ 64 - 256) = 2 ^ 64 - 32 ∧
      (2 ^ 64 - 32) + ABI.paddedSize 100 = 2 ^ 64 + 96 := by
  decide +kernel

def safeIRSetupTokenAllocationCursor : State :=
  { (default : State) with
    executionEnv := { (default : ExecutionEnv) with code := safeBytecode }
    machineState := { (default : MachineState) with
      pc := ⟨7128⟩
      stack := [UInt256.ofNat (2 ^ 64 - 32), ⟨100⟩, ⟨10618⟩]
      memory := ByteArray.empty
      gasAvailable := .ofUInt256 ⟨100000⟩ } }

/-- A segment certificate for the later token allocation, not a complete setup execution. -/
theorem safeIRSetupTokenAllocationExecution :
    (match X .cancun 100001 (D_J safeBytecode 0) safeIRSetupTokenAllocationCursor with
      | .ok (.revert gas out) => gas.toNat > 99000 &&
          out == (⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ ++ (⟨0x41⟩ : UInt256).toByteArray)
      | _ => false) = true := by native_decide

/-- The conditional guard rejects the additional token-encoder allocation boundary. -/
theorem safeIRSetupTokenAllocationGuardReverts (evm : State) (payload : ByteArray)
    (hlen : payload.size = 2 ^ 64 - 256)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    let p : SetupInput :=
      ⟨[⟨8192⟩], ⟨1⟩, ⟨0⟩, payload, ⟨0⟩, ⟨8193⟩, ⟨1⟩, ⟨0⟩⟩
    ExecBlock fork config p.frame evm setupTransition.body .reverted := by
  apply safeSetupAllocationRevert (hperm := hperm) _ evm hv
  rw [safeSetupAllocationLimit_token _ (by change (⟨1⟩ : UInt256) ≠ ⟨0⟩; decide)
    (by change AccountAddress.ofNat 8193 ≠ EVM.address 0; decide)]
  simp only [List.length_cons, List.length_nil, hlen]
  decide +kernel

end Benchmarks.Safe.ViaIR
