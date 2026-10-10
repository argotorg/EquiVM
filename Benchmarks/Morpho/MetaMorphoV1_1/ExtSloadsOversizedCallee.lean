import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsAllocationRegression

/-! A concrete callee that returns the oversized buffer from the allocation regression.
The trace is symbolic; no executable test attempts to allocate the returned byte array. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsAllocationRegression

set_option autoImplicit false

-- PUSH1 32; PUSH0; MSTORE; PUSH1 1; PUSH1 32; MSTORE;
-- PUSH9 2^64; PUSH0; RETURN.
def oversizedCalleeCode : ByteArray :=
  ⟨#[0x60, 0x20, 0x5f, 0x52, 0x60, 0x01, 0x60, 0x20, 0x52,
    0x68, 0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0x5f, 0xf3]⟩

def oversizedCalleePrefix : ByteArray :=
  (⟨32⟩ : UInt256).toByteArray ++ (⟨1⟩ : UInt256).toByteArray

theorem oversizedCalleePrefix_size : oversizedCalleePrefix.size = 64 := by
  simp only [oversizedCalleePrefix, ByteArray.size_append, toByteArray_size]

theorem oversizedCalleePrefix_output :
    oversizedCalleePrefix.readWithPadding 0 (2 ^ 64) = oversizedReturn := by
  have hread : oversizedCalleePrefix.readWithoutPadding 0 (2 ^ 64) =
      oversizedCalleePrefix := by
    unfold ByteArray.readWithoutPadding
    rw [if_neg (by rw [oversizedCalleePrefix_size]; decide), oversizedCalleePrefix_size]
    rw [Nat.min_eq_right (by norm_num)]
    simpa only [oversizedCalleePrefix_size, Nat.zero_add] using
      byteArray_extract_self oversizedCalleePrefix
  rw [ByteArray.readWithPadding, hread, oversizedCalleePrefix_size]
  exact ByteArray.append_assoc

set_option maxRecDepth 2000 in
theorem oversizedCalleeXi (σ σ₀ : AccountMap) (A : Substate) (I : ExecutionEnv)
    (hcode : I.code = oversizedCalleeCode) :
    ∃ gasOut, Ξ σ σ₀ (UInt256.ofNat (2 ^ 120)) A I =
      .ok (.success (σ, gasOut, A) oversizedReturn) := by
  let gas := Sat256.ofUInt256 (UInt256.ofNat (2 ^ 120))
  let s0 := initState σ σ₀ gas A I
  let s1 := stPush1 s0 ⟨32⟩
  let s2 := stPush0 s1
  let s3 := stMStore s2 ⟨0⟩ ⟨32⟩ []
  let s4 := stPush1 s3 ⟨1⟩
  let s5 := stPush1 s4 ⟨32⟩
  let s6 := stMStore s5 ⟨32⟩ ⟨1⟩ []
  let s7 := stPushConst s6 (UInt256.ofNat (2 ^ 64)) 9
  let s8 := stPush0 s7
  have h0 := push1_xstep (s := s0) (rest := []) hcode rfl
    (by decide +kernel : decode oversizedCalleeCode ⟨0⟩ =
      some (.Push .PUSH1, some (⟨32⟩, 1))) rfl (by decide)
  have h1 := push0_xstep (s := s1) (rest := [⟨32⟩]) hcode rfl
    (by decide +kernel : decode oversizedCalleeCode ⟨2⟩ = some (.PUSH0, none)) rfl (by decide)
  have h2 := mstore_xstep (s := s2) (t := []) hcode rfl
    (by decide +kernel : decode oversizedCalleeCode ⟨3⟩ = some (.MSTORE, none)) rfl (by decide)
  have h3 := push1_xstep (s := s3) (rest := []) hcode rfl
    (by decide +kernel : decode oversizedCalleeCode ⟨4⟩ =
      some (.Push .PUSH1, some (⟨1⟩, 1))) rfl (by decide)
  have h4 := push1_xstep (s := s4) (rest := [⟨1⟩]) hcode rfl
    (by decide +kernel : decode oversizedCalleeCode ⟨6⟩ =
      some (.Push .PUSH1, some (⟨32⟩, 1))) rfl (by decide)
  have h5 := mstore_xstep (s := s5) (t := []) hcode rfl
    (by decide +kernel : decode oversizedCalleeCode ⟨8⟩ = some (.MSTORE, none)) rfl (by decide)
  have h6 := pushConst_xstep (s := s6) (rest := []) hcode rfl (by decide)
    (by decide +kernel : decode oversizedCalleeCode ⟨9⟩ =
      some (.Push .PUSH9, some (UInt256.ofNat (2 ^ 64), 9))) rfl (by decide)
  have h7 := push0_xstep (s := s7) (rest := [UInt256.ofNat (2 ^ 64)]) hcode rfl
    (by decide +kernel : decode oversizedCalleeCode ⟨19⟩ = some (.PUSH0, none)) rfl (by decide)
  have h8 := return_xstep (s := s8) (t := []) hcode rfl
    (by decide +kernel : decode oversizedCalleeCode ⟨20⟩ = some (.RETURN, none)) rfl (by decide)
  have mc2 : memoryExpansionCost s2 .MSTORE = 3 := by
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', s2, s1, s0,
      stPush0, stPush1, initState]
    rfl
  have mc5 : memoryExpansionCost s5 .MSTORE = 3 := by
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', s5, s4, s3, s2, s1, s0,
      stPush0, stPush1, stMStore, initState]
    rfl
  have mc8 : memoryExpansionCost s8 .RETURN =
      memExpansionCost ⟨2⟩ ⟨0⟩ (UInt256.ofNat (2 ^ 64)) := by
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', s8, s7, s6, s5, s4, s3,
      s2, s1, s0, stPush0, stPush1, stPushConst, stMStore, initState]
    rfl
  have hg3 : s3.machineState.gasAvailable = gas.subNat 11 := by
    change (((gas.subNat 3).subNat 2).subNat (memoryExpansionCost s2 .MSTORE)).subNat 3 = _
    rw [mc2]
    rfl
  have hg4 : s4.machineState.gasAvailable = gas.subNat 14 := by
    change s3.machineState.gasAvailable.subNat 3 = _
    rw [hg3]
    rfl
  have hg5 : s5.machineState.gasAvailable = gas.subNat 17 := by
    change s4.machineState.gasAvailable.subNat 3 = _
    rw [hg4]
    rfl
  have hg6 : s6.machineState.gasAvailable = gas.subNat 23 := by
    change (s5.machineState.gasAvailable.subNat (memoryExpansionCost s5 .MSTORE)).subNat 3 = _
    rw [hg5, mc5]
    rfl
  have hg7 : s7.machineState.gasAvailable = gas.subNat 26 := by
    change s6.machineState.gasAvailable.subNat 3 = _
    rw [hg6]
    rfl
  have hg8 : s8.machineState.gasAvailable = gas.subNat 28 := by
    change s7.machineState.gasAvailable.subNat 2 = _
    rw [hg7]
    rfl
  have r0 := stepContinue (g := gas) (k := 0) (C := 0) rfl h0 (by decide) (by decide)
  have r1 := stepContinue (g := gas) (k := 1) (C := 3) rfl h1 (by decide) (by decide)
  have r2 := stepContinue (g := gas) (k := 2) (C := 5) rfl h2 (by decide)
    (by rw [mc2]; decide)
  have r3 := stepContinue (g := gas) (k := 3) (C := 11) hg3 h3 (by decide) (by decide)
  have r4 := stepContinue (g := gas) (k := 4) (C := 14) hg4 h4 (by decide) (by decide)
  have r5 := stepContinue (g := gas) (k := 5) (C := 17) hg5 h5 (by decide)
    (by rw [mc5]; decide)
  have r6 := stepContinue (g := gas) (k := 6) (C := 23) hg6 h6 (by decide) (by decide)
  have r7 := stepContinue (g := gas) (k := 7) (C := 26) hg7 h7 (by decide) (by decide)
  have r8 := stepHaltSuccess (g := gas) (k := 8) (C := 28) hg8 h8 (by decide)
    (by rw [mc8]; decide +kernel)
  have hm : s8.machineState.memory = oversizedCalleePrefix := by
    change (⟨1⟩ : UInt256).toByteArray.write 0
      ((⟨32⟩ : UInt256).toByteArray.write 0 ByteArray.empty 0 32) 32 32 = _
    decide +kernel
  have hout : s8.machineState.memory.readWithPadding (⟨0⟩ : UInt256).toNat
      (UInt256.ofNat (2 ^ 64)).toNat = oversizedReturn := by
    rw [hm]
    exact oversizedCalleePrefix_output
  rw [hout] at r8
  have hrun : X ((UInt256.ofNat (2 ^ 120)).toNat + 1) (D_J I.code 0) s0 =
      .ok (.success (stReturn s8 ⟨0⟩ (UInt256.ofNat (2 ^ 64)) []) oversizedReturn) := by
    change X (gas.toNat + 1 - 0) (D_J I.code 0) s0 = _
    rw [hcode, r0, r1, r2, r3, r4, r5, r6, r7]
    exact r8
  exact ⟨_, Xi_success_of_X hrun⟩

def oversizedCalleeAddress : AccountAddress := AccountAddress.ofNat 0x6000

def oversizedCallerAddress : AccountAddress := AccountAddress.ofNat 0x6001

def oversizedCalleeAccounts : AccountMap :=
  (∅ : AccountMap).insert oversizedCalleeAddress
    { (default : Account) with code := oversizedCalleeCode }

theorem oversizedCalleeToExecute :
    toExecute oversizedCalleeAccounts oversizedCalleeAddress =
      .Code oversizedCalleeCode := by
  rfl

set_option maxRecDepth 2000 in
theorem oversizedCalleeTheta (σ₀ : AccountMap) (A : Substate) (I : ExecutionEnv)
    (input : ByteArray) :
    ∃ gasOut, Θ oversizedCalleeAccounts σ₀ A oversizedCallerAddress I.sender
      oversizedCalleeAddress (toExecute oversizedCalleeAccounts oversizedCalleeAddress)
      (UInt256.ofNat (2 ^ 120)) (.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩ input (I.depth + 1)
      I.header I.blobVersionedHashes I.blocks false =
      (oversizedCalleeAccounts, gasOut, A, true, oversizedReturn) := by
  let calleeEnv : ExecutionEnv :=
    { codeOwner := oversizedCalleeAddress, sender := I.sender,
      gasPrice := (UInt256.ofNat I.gasPrice).toNat, calldata := input,
      source := oversizedCallerAddress, weiValue := ⟨0⟩, depth := I.depth + 1,
      perm := false, code := oversizedCalleeCode, header := I.header,
      blobVersionedHashes := I.blobVersionedHashes, blocks := I.blocks }
  obtain ⟨gasOut, hrun⟩ := oversizedCalleeXi oversizedCalleeAccounts σ₀ A calleeEnv rfl
  refine ⟨gasOut, ?_⟩
  rw [oversizedCalleeToExecute]
  unfold Θ
  change (let result : AccountMap × UInt256 × Substate × ByteArray :=
      match Ξ oversizedCalleeAccounts σ₀ (UInt256.ofNat (2 ^ 120)) A calleeEnv with
      | .error _ => (∅, ⟨0⟩, A, ByteArray.empty)
      | .ok (.revert g out) => (∅, g, A, out)
      | .ok (.success (accounts, g, substate) out) => (accounts, g, substate, out)
    (if result.1 == ∅ then oversizedCalleeAccounts else result.1,
      result.2.1, if result.1 == ∅ then A else result.2.2.1,
      if result.1 == ∅ then false else true, result.2.2.2)) = _
  rw [hrun]
  rfl

def oversizedCallerState : State :=
  initState oversizedCalleeAccounts oversizedCalleeAccounts
    (Sat256.ofUInt256 (UInt256.ofNat (2 ^ 122))) default
    { (default : ExecutionEnv) with codeOwner := oversizedCallerAddress }

theorem oversizedCalleeTypedCall (slot : UInt256) :
    typedCallViaEVM config oversizedCallerState oversizedCalleeAddress "extSloads" 0
      [.array [wordBytes32Value slot]] (true, oversizedCallerState, oversizedReturn) false := by
  refine ⟨extSloadsCalldata slot, extSloadsEncode slot, ?_⟩
  obtain ⟨gasOut, hcall⟩ := oversizedCalleeTheta oversizedCalleeAccounts default
    oversizedCallerState.executionEnv (extSloadsCalldata slot)
  refine callViaEVM.callMade (σ' := oversizedCalleeAccounts) (g' := gasOut)
    (A' := default) (valueWord := ⟨0⟩) rfl ?_ rfl (by decide +kernel) (by decide +kernel)
  exact ⟨UInt256.ofNat (2 ^ 120), default, hcall.symm⟩

/-- A real typed call can return an accepted array beyond solc's allocation limit. -/
theorem oversizedCalleeCallAccepted (slot : UInt256) :
    ∃ values,
      typedCallViaEVM config oversizedCallerState oversizedCalleeAddress "extSloads" 0
        [.array [wordBytes32Value slot]] (true, oversizedCallerState, oversizedReturn) false ∧
      config.externalABI.decode? "extSloads" oversizedReturn = some [.array values] ∧
      values.length = 1 ∧ oversizedReturn.size = 2 ^ 64 := by
  obtain ⟨values, hdecode, hlen⟩ := oversizedReturn_sourceAccepts
  exact ⟨values, oversizedCalleeTypedCall slot, hdecode, hlen, oversizedReturn_size⟩

/-- Successful calls and valid ABI decoding do not imply the missing allocation bound. -/
theorem acceptedCallDoesNotBoundReturnSize :
    ¬ (∀ (evm evm' : State) (target : AccountAddress) (args values : List Value)
        (out : ByteArray),
      typedCallViaEVM config evm target "extSloads" 0 args (true, evm', out) false →
      config.externalABI.decode? "extSloads" out = some [.array values] →
      out.size < 2 ^ 64) := by
  intro hbound
  obtain ⟨values, hcall, hdecode, _, hsize⟩ := oversizedCalleeCallAccepted ⟨0⟩
  have hlt := hbound oversizedCallerState oversizedCallerState oversizedCalleeAddress
    [.array [wordBytes32Value ⟨0⟩]] values oversizedReturn hcall hdecode
  rw [hsize] at hlt
  exact (Nat.lt_irrefl _) hlt

end Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsAllocationRegression
