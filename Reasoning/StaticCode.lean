import Reasoning.Storage

/-!
# Static code-size preservation

Static EVM execution preserves the code-size observation used by `EXTCODESIZE`.  This mirrors the
upstream static-storage theorem, but tracks only `(findD · default).code.size`, which is the exact
fact needed by solc external-call guards.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Theory

def accountCodeStateEq (σ τ : AccountMap) : Prop :=
  ∀ addr : AccountAddress,
    (σ.findD addr default).code.size = (τ.findD addr default).code.size

@[simp] theorem accountCodeStateEq_refl (σ : AccountMap) :
    accountCodeStateEq σ σ := by
  intro addr
  rfl

theorem accountCodeStateEq_symm {σ τ : AccountMap}
    (h : accountCodeStateEq σ τ) :
    accountCodeStateEq τ σ := by
  intro addr
  exact (h addr).symm

theorem accountCodeStateEq_trans {σ τ υ : AccountMap}
    (hστ : accountCodeStateEq σ τ)
    (hτυ : accountCodeStateEq τ υ) :
    accountCodeStateEq σ υ := by
  intro addr
  exact (hστ addr).trans (hτυ addr)

theorem accountCodeStateEq_insert_preserve
    (σ : AccountMap) (addr : AccountAddress) (acc : Account)
    (hcode : acc.code.size = (σ.findD addr default).code.size) :
    accountCodeStateEq σ (σ.insert addr acc) := by
  intro query
  by_cases hcmp : compare query addr = .eq
  · have hfind : (σ.insert addr acc).find? query = some acc := by
      exact Batteries.RBMap.find?_insert_of_eq σ hcmp
    have hcmp' : compare addr query = .eq := by
      have hswap :=
        (Std.OrientedCmp.eq_swap (cmp := compare) (a := query) (b := addr))
      rw [hcmp] at hswap
      simpa using hswap.symm
    have hquery : σ.find? addr = σ.find? query := by
      exact Batteries.RBMap.find?_congr σ hcmp'
    have hcode' : acc.code.size = (σ.findD query default).code.size := by
      simpa [Batteries.RBMap.findD, hquery] using hcode
    simp [Batteries.RBMap.findD, hfind, hcode']
  · have hfind : (σ.insert addr acc).find? query = σ.find? query := by
      exact Batteries.RBMap.find?_insert_of_ne σ hcmp
    simp [Batteries.RBMap.findD, hfind]

theorem accountCodeStateEq_debit_if_present
    (σ : AccountMap) (addr : AccountAddress) (value : UInt256) :
    accountCodeStateEq σ
      (match σ.find? addr with
      | none => σ
      | some acc => σ.insert addr { acc with balance := acc.balance - value }) := by
  cases hfind : σ.find? addr with
  | none =>
      simp
  | some acc =>
      simp
      exact accountCodeStateEq_insert_preserve σ addr { acc with balance := acc.balance - value }
        (by simp [Batteries.RBMap.findD, hfind])

theorem sendEth_accountCodeStateEq
    (r s : AccountAddress) (v : UInt256) (z : Bool) (σ : AccountMap) :
    accountCodeStateEq σ (sendEth r s v z σ) := by
  unfold sendEth
  by_cases hz : z
  · simp [hz]
    let σ₁ : AccountMap :=
      match σ.find? r with
      | none =>
          if (v != UInt256.ofNat 0) = true then
            σ.insert r
              (let __src := (default : Account)
              { nonce := __src.nonce, balance := v, storage := __src.storage, code := __src.code,
                tstorage := __src.tstorage })
          else σ
      | some acc =>
          σ.insert r
            { nonce := acc.nonce, balance := acc.balance + v, storage := acc.storage, code := acc.code,
              tstorage := acc.tstorage }
    have hσ₁ : accountCodeStateEq σ σ₁ := by
      dsimp [σ₁]
      cases hr : σ.find? r with
      | none =>
          by_cases hv : (v != UInt256.ofNat 0) = true
          · simp [hv]
            apply accountCodeStateEq_insert_preserve
            simp [Batteries.RBMap.findD, hr]
          · simp [hv]
      | some acc =>
          simp
          apply accountCodeStateEq_insert_preserve
          simp [Batteries.RBMap.findD, hr]
    simpa [σ₁] using accountCodeStateEq_trans hσ₁
      (accountCodeStateEq_debit_if_present σ₁ s v)
  · simp [hz]

theorem accountCodeStateEq_final_of_empty_or_self {σ τ ρ : AccountMap}
    (hστ : accountCodeStateEq σ τ) (hρ : ρ = ∅ ∨ ρ = τ) :
    accountCodeStateEq σ (if ρ == ∅ then σ else ρ) := by
  rcases hρ with rfl | rfl
  · simp [rbMap_empty_beq_empty]
  · by_cases hempty : (ρ == ∅) = true
    · simp [hempty]
    · simp [hempty, hστ]

theorem accountCodeStateEq_of_precompiled_Theta
    {blobVersionedHashes : List ByteArray}
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap} {A A' : Substate}
    {s o r pc : AccountAddress} {g g' p v v' : UInt256}
    {d out : ByteArray} {e : Fin 1025} {H : BlockHeader} {w z : Bool}
    (hTheta : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (.Precompiled pc) g p v v' d e H w =
      (createdAccounts', σ', g', A', z, out)) :
    accountCodeStateEq σ σ' := by
  let σ₁ := sendEth r s v true σ
  let I : ExecutionEnv :=
    { codeOwner := r, sender := o, source := s, weiValue := v', calldata := d,
      code := default, gasPrice := p.toNat, header := H, depth := e, perm := w,
      blobVersionedHashes := blobVersionedHashes }
  have hproj :
      (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
        (.Precompiled pc) g p v v' d e H w).2.1 = σ' := by
    simpa using congrArg (fun x => x.2.1) hTheta
  rw [← hproj]
  rw [precompiled_Theta_accountMap_eq blobVersionedHashes createdAccounts
    genesisBlockHeader blocks σ σ₀ A s o r pc g p v v' d e H w]
  exact accountCodeStateEq_final_of_empty_or_self
    (sendEth_accountCodeStateEq r s v true σ)
    (by simpa [σ₁, I] using precompiled_result_accountMap_empty_or_self pc σ₁ g A I)

def stateCodeStateEq (state₁ state₂ : State) : Prop :=
  accountCodeStateEq state₁.accountMap state₂.accountMap

@[simp] theorem stateCodeStateEq_refl (state : State) :
    stateCodeStateEq state state := by
  simp [stateCodeStateEq]

theorem stateCodeStateEq_trans {state₁ state₂ state₃ : State}
    (h₁₂ : stateCodeStateEq state₁ state₂)
    (h₂₃ : stateCodeStateEq state₂ state₃) :
    stateCodeStateEq state₁ state₃ := by
  exact accountCodeStateEq_trans h₁₂ h₂₃

theorem stateCodeStateEq_with_executionEnv_depth {state₁ state₂ : State}
    (h : stateCodeStateEq state₁ state₂) (depth : Fin 1025) :
    stateCodeStateEq state₁ ({state₂ with executionEnv.depth := depth} : State) := by
  simpa [stateCodeStateEq] using h

theorem stateCodeStateEq_with_executionEnv {state₁ state₂ : State}
    (h : stateCodeStateEq state₁ state₂) (executionEnv : ExecutionEnv) :
    stateCodeStateEq state₁ ({state₂ with executionEnv := executionEnv} : State) := by
  simpa [stateCodeStateEq] using h

theorem stateCodeStateEq_of_accountMap_eq {state state' : State}
    (h : state'.accountMap = state.accountMap) :
    stateCodeStateEq state state' := by
  simp [stateCodeStateEq, h]

theorem Z_static_stateCodeStateEq
    {validJumps : Array UInt256} {op : Operation} {state stateZ : State}
    {cost : Nat} :
    Z validJumps op state = .ok (stateZ, cost) →
    stateCodeStateEq state stateZ := by
  intro hZ
  rcases Z_ok_eq_charged_cost hZ with ⟨hstate, _hcost⟩
  subst stateZ
  simp [stateCodeStateEq]
lemma static_step_stackmemflow_static_stateCodeStateEq_of_Z
    {validJumps : Array UInt256} {op : Operation.SMSFOp} {gasCost : Nat}
    {arg : Option (UInt256 × Nat)} {state stateZ stepped : State}
    (hperm : state.executionEnv.perm = false)
    (hZ : Z validJumps (.StackMemFlow op) state = .ok (stateZ, gasCost))
    (hstep :
      step gasCost (.StackMemFlow op, arg)
        {stateZ with executionEnv.depth := state.executionEnv.depth} = .ok stepped) :
    stateCodeStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  let stepState : State := {stateZ with executionEnv.depth := state.executionEnv.depth}
  cases op <;> simp [step] at hstep
  · split at hstep <;> try contradiction
    injection hstep with hstate
    rw [← hstate]
    exact stateCodeStateEq_refl _
  · split at hstep <;> try contradiction
    injection hstep with hstate
    rw [← hstate]
    exact stateCodeStateEq_refl _
  · have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateCodeStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · have hm := static_unaryStateOp_accountMap_eq
      (f := Ethereum.State.sload)
      (by
        intro s v
        simp [Ethereum.State.sload, Ethereum.State.addAccessedStorageKey,
          Ethereum.State.lookupAccount])
      hstep
    exact stateCodeStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateCodeStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · split at hstep <;> try contradiction
    injection hstep with hstate
    rw [← hstate]
    exact stateCodeStateEq_refl _
  · split at hstep <;> try contradiction
    injection hstep with hstate
    rw [← hstate]
    exact stateCodeStateEq_refl _
  · rw [← hstep]
    simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC, stateCodeStateEq]
  · have hm := static_machineStateOp_accountMap_eq hstep
    exact stateCodeStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · have hm := static_machineStateOp_accountMap_eq hstep
    exact stateCodeStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · rw [← hstep]
    simp [Ethereum.State.incrPC, stateCodeStateEq]
  · have hm := static_unaryStateOp_accountMap_eq
      (f := Ethereum.State.tload)
      (by intro s v; simp [Ethereum.State.tload])
      hstep
    exact stateCodeStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · have hm := static_ternaryMachineStateOp_accountMap_eq hstep
    exact stateCodeStateEq_of_accountMap_eq (by simpa [stepState] using hm)

lemma call_static_stateCodeStateEq_at_depth
    {n gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState state' : State}
    (hdepth : 1024 - evmState.executionEnv.depth.val = n + 1)
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountCodeStateEq σ σ')
    (hperm : permission = false)
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    stateCodeStateEq evmState state' := by
  unfold call at h
  simp at h
  split at h
  · rename_i hcall
    rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp [stateCodeStateEq]
    let θ :=
      Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
        evmState.blocks evmState.accountMap evmState.σ₀
        (evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (evmState.executionEnv.depth + 1) evmState.executionEnv.header false
    have hθ :
        Θ blobVersionedHashes evmState.createdAccounts evmState.genesisBlockHeader
          evmState.blocks evmState.accountMap evmState.σ₀
          (evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate
          (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
          (AccountAddress.ofUInt256 recipient)
          (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
          (UInt256.ofNat
            (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
              value gas evmState.accountMap evmState.machineState evmState.substate))
          (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
          (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
          (evmState.executionEnv.depth + 1) evmState.executionEnv.header false =
        (θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1, θ.2.2.2.2.1, θ.2.2.2.2.2) := by
      rfl
    have hpres : accountCodeStateEq evmState.accountMap θ.2.1 :=
      ihTheta blobVersionedHashes evmState.genesisBlockHeader evmState.blocks
        evmState.createdAccounts (evmState.executionEnv.depth + 1)
        evmState.accountMap evmState.σ₀
        ((evmState.addAccessedAccount (AccountAddress.ofUInt256 t)).substate)
        (AccountAddress.ofUInt256 source) evmState.executionEnv.sender
        (AccountAddress.ofUInt256 recipient)
        (toExecute evmState.accountMap (AccountAddress.ofUInt256 t))
        (UInt256.ofNat
          (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
            value gas evmState.accountMap evmState.machineState evmState.substate))
        (UInt256.ofNat evmState.executionEnv.gasPrice) value value'
        (evmState.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        evmState.executionEnv.header
        θ.1 θ.2.1 θ.2.2.1 θ.2.2.2.1 θ.2.2.2.2.1 θ.2.2.2.2.2
        (static_depth_succ_measure hdepth hcall.2)
        hθ
    simpa [θ, hperm] using hpres
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp [stateCodeStateEq]

lemma call_static_stateCodeStateEq_max_depth
    {gasCost : Nat}
    {blobVersionedHashes : List ByteArray}
    {gas source recipient t value value' inOffset inSize outOffset outSize x : UInt256}
    {permission : Bool} {evmState state' : State}
    (hdepth : evmState.executionEnv.depth = 1024)
    (h : call gasCost blobVersionedHashes gas source recipient t value value'
        inOffset inSize outOffset outSize permission evmState = .ok (x, state')) :
    stateCodeStateEq evmState state' := by
  unfold call at h
  simp at h
  split at h
  · rename_i hcall
    exact False.elim (by
      have hlt := hcall.2
      omega)
  · rcases h with ⟨_, hstate⟩
    rw [← hstate]
    simp [stateCodeStateEq]

lemma step_system_call_static_stateCodeStateEq_of_Z_at_depth
    {n : Nat} {validJumps : Array UInt256} {op : Operation.SOp}
    {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat}
    (hcallkind : op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL)
    (hdepth : 1024 - state.executionEnv.depth.val = n + 1)
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountCodeStateEq σ σ')
    (hperm : state.executionEnv.perm = false)
    (hZ : Z validJumps (.System op) state = .ok (stateZ, cost))
    (hstep :
      step cost (.System op, arg)
        {stateZ with executionEnv.depth := state.executionEnv.depth} = .ok stepped) :
    stateCodeStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  let stepState : State := {stateZ with executionEnv.depth := state.executionEnv.depth}
  have hZEnv : stateZ.executionEnv = state.executionEnv :=
    Z_executionEnv_eq (validJumps := validJumps) (state := state) (op := .System op) hZ
  cases op
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateCodeStateEq_at_depth
      (n := n)
      (hdepth := by simp [hdepth])
      ihTheta
      (by simpa [stepState, hZEnv] using hperm)
      hcall
    simpa [stepState, stateCodeStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateCodeStateEq_at_depth
      (n := n)
      (hdepth := by simp [hdepth])
      ihTheta
      (by simpa [stepState, hZEnv] using hperm)
      hcall
    simpa [stepState, stateCodeStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateCodeStateEq_at_depth
      (n := n)
      (hdepth := by simp [hdepth])
      ihTheta
      (by simpa [stepState, hZEnv] using hperm)
      hcall
    simpa [stepState, stateCodeStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateCodeStateEq_at_depth
      (n := n)
      (hdepth := by simp [hdepth])
      ihTheta
      rfl
      hcall
    simpa [stepState, stateCodeStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse

lemma step_system_call_static_stateCodeStateEq_of_Z_max_depth
    {validJumps : Array UInt256} {op : Operation.SOp} {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat}
    (hcallkind : op = .CALL ∨ op = .CALLCODE ∨ op = .DELEGATECALL ∨ op = .STATICCALL)
    (hdepth : state.executionEnv.depth = 1024)
    (hZ : Z validJumps (.System op) state = .ok (stateZ, cost))
    (hstep :
      step cost (.System op, arg)
        {stateZ with executionEnv.depth := state.executionEnv.depth} = .ok stepped) :
    stateCodeStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  let stepState : State := {stateZ with executionEnv.depth := state.executionEnv.depth}
  cases op
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateCodeStateEq_max_depth
      (hdepth := by simp [hdepth])
      hcall
    simpa [stepState, stateCodeStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateCodeStateEq_max_depth
      (hdepth := by simp [hdepth])
      hcall
    simpa [stepState, stateCodeStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateCodeStateEq_max_depth
      (hdepth := by simp [hdepth])
      hcall
    simpa [stepState, stateCodeStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · simp [step, bind, Except.bind] at hstep
    split at hstep <;> try contradiction
    rename_i popped hpop
    rcases popped with ⟨stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩
    split at hstep <;> try contradiction
    rename_i callResult hcall
    rcases callResult with ⟨x, callState⟩
    injection hstep with hstate
    rw [← hstate]
    have hcallPres := call_static_stateCodeStateEq_max_depth
      (hdepth := by simp [hdepth])
      hcall
    simpa [stepState, stateCodeStateEq, Ethereum.State.replaceStackAndIncrPC,
      Ethereum.State.incrPC] using hcallPres
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse
  · have hfalse : False := by
      rcases hcallkind with h | h | h | h <;> cases h
    exact False.elim hfalse

theorem step_system_static_stateCodeStateEq_of_Z_max_depth
    {validJumps : Array UInt256} {op : Operation.SOp} {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat} :
    state.executionEnv.perm = false →
    state.executionEnv.depth = 1024 →
    Z validJumps (.System op) state = .ok (stateZ, cost) →
    step cost (.System op, arg) {stateZ with executionEnv.depth := state.executionEnv.depth} =
      .ok stepped →
    stateCodeStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  intro hperm hdepth hZ hstep
  let stepState : State := {stateZ with executionEnv.depth := state.executionEnv.depth}
  cases op
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · exact step_system_call_static_stateCodeStateEq_of_Z_max_depth (by simp) hdepth hZ hstep
  · exact step_system_call_static_stateCodeStateEq_of_Z_max_depth (by simp) hdepth hZ hstep
  · simp [step] at hstep
    have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateCodeStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · exact step_system_call_static_stateCodeStateEq_of_Z_max_depth (by simp) hdepth hZ hstep
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · exact step_system_call_static_stateCodeStateEq_of_Z_max_depth (by simp) hdepth hZ hstep
  · simp [step] at hstep
    have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateCodeStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · simp [step] at hstep
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)

theorem step_system_static_stateCodeStateEq_of_Z_succ_depth
    {n : Nat} {validJumps : Array UInt256} {op : Operation.SOp}
    {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat} :
    state.executionEnv.perm = false →
    1024 - state.executionEnv.depth.val = n + 1 →
    (∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountCodeStateEq σ σ') →
    Z validJumps (.System op) state = .ok (stateZ, cost) →
    step cost (.System op, arg) {stateZ with executionEnv.depth := state.executionEnv.depth} =
      .ok stepped →
    stateCodeStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  intro hperm hdepth ihTheta hZ hstep
  let stepState : State := {stateZ with executionEnv.depth := state.executionEnv.depth}
  cases op
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · exact step_system_call_static_stateCodeStateEq_of_Z_at_depth (by simp)
      hdepth ihTheta hperm hZ hstep
  · exact step_system_call_static_stateCodeStateEq_of_Z_at_depth (by simp)
      hdepth ihTheta hperm hZ hstep
  · simp [step] at hstep
    have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateCodeStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · exact step_system_call_static_stateCodeStateEq_of_Z_at_depth (by simp)
      hdepth ihTheta hperm hZ hstep
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)
  · exact step_system_call_static_stateCodeStateEq_of_Z_at_depth (by simp)
      hdepth ihTheta hperm hZ hstep
  · simp [step] at hstep
    have hm := static_binaryMachineStateOp_accountMap_eq hstep
    exact stateCodeStateEq_of_accountMap_eq (by simpa [stepState] using hm)
  · simp [step] at hstep
  · exact False.elim (Z_static_forbidden_mem_false hperm (by simp) hZ)

theorem step_static_stateCodeStateEq_of_Z_max_depth
    {validJumps : Array UInt256} {op : Operation} {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat} :
    state.executionEnv.perm = false →
    state.executionEnv.depth = 1024 →
    Z validJumps op state = .ok (stateZ, cost) →
    step cost (op, arg) {stateZ with executionEnv.depth := state.executionEnv.depth} =
      .ok stepped →
    stateCodeStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  intro hperm hdepth hZ hstep
  rcases op with op | op | op | op | op | op | op | op | op | op
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_stoparith_accountMap_eq hstep)
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_compbit_accountMap_eq hstep)
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_keccak_accountMap_eq hstep)
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_env_accountMap_eq hstep)
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_block_accountMap_eq hstep)
  · exact static_step_stackmemflow_static_stateCodeStateEq_of_Z hperm hZ hstep
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_push_accountMap_eq hstep)
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_dup_accountMap_eq hstep)
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_exchange_accountMap_eq hstep)
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_log_accountMap_eq hstep)
  · exact step_system_static_stateCodeStateEq_of_Z_max_depth hperm hdepth hZ hstep

theorem step_static_stateCodeStateEq_of_Z_succ_depth
    {n : Nat} {validJumps : Array UInt256} {op : Operation}
    {arg : Option (UInt256 × Nat)}
    {state stateZ stepped : State} {cost : Nat} :
    state.executionEnv.perm = false →
    1024 - state.executionEnv.depth.val = n + 1 →
    (∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountCodeStateEq σ σ') →
    Z validJumps op state = .ok (stateZ, cost) →
    step cost (op, arg) {stateZ with executionEnv.depth := state.executionEnv.depth} =
      .ok stepped →
    stateCodeStateEq
      ({stateZ with executionEnv.depth := state.executionEnv.depth} : State) stepped := by
  intro hperm hdepth ihTheta hZ hstep
  rcases op with op | op | op | op | op | op | op | op | op | op
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_stoparith_accountMap_eq hstep)
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_compbit_accountMap_eq hstep)
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_keccak_accountMap_eq hstep)
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_env_accountMap_eq hstep)
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_block_accountMap_eq hstep)
  · exact static_step_stackmemflow_static_stateCodeStateEq_of_Z hperm hZ hstep
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_push_accountMap_eq hstep)
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_dup_accountMap_eq hstep)
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_exchange_accountMap_eq hstep)
  · exact stateCodeStateEq_of_accountMap_eq
      (static_step_log_accountMap_eq hstep)
  · exact step_system_static_stateCodeStateEq_of_Z_succ_depth
      hperm hdepth ihTheta hZ hstep

theorem Xstep_static_stateCodeStateEq_max_depth
    {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)} :
    state.executionEnv.perm = false →
    state.executionEnv.depth = 1024 →
    Xstep validJumps state = .ok (state', ret) →
    stateCodeStateEq state state' := by
  intro hperm hdepth hstep
  set instr : Operation × Option (UInt256 × Nat) :=
    decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none) with hinstr
  rcases instr with ⟨op, arg⟩
  unfold Xstep at hstep
  simp only [bind, Except.bind] at hstep
  split at hstep
  · simp at hstep
  · rename_i stateZ cost hZ
    have hZ' : Z validJumps op state = .ok (stateZ, cost) := by
      simpa [← hinstr] using hZ
    cases hstep' :
        step cost (op, arg)
          {stateZ with executionEnv.depth := state.executionEnv.depth} with
    | error e =>
        simp [← hinstr, hstep'] at hstep
    | ok stepped =>
        have hstep'' :
            step cost (op, arg)
              {stateZ with executionEnv.depth := state.executionEnv.depth} =
            .ok stepped := hstep'
        have hZpres : stateCodeStateEq state stateZ :=
          Z_static_stateCodeStateEq hZ'
        have hstepPres :
            stateCodeStateEq
              ({stateZ with executionEnv.depth := state.executionEnv.depth} : State)
              stepped :=
          step_static_stateCodeStateEq_of_Z_max_depth hperm hdepth hZ' hstep''
        have hprefix : stateCodeStateEq state stepped :=
          stateCodeStateEq_trans
            (stateCodeStateEq_with_executionEnv_depth hZpres state.executionEnv.depth)
            hstepPres
        simp [← hinstr, hstep'] at hstep
        split at hstep
        · injection hstep with hstate
          have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
            congrArg Prod.fst hstate
          subst state'
          exact stateCodeStateEq_with_executionEnv hprefix state.executionEnv
        · split at hstep
          · injection hstep with hstate
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hstate
            subst state'
            exact stateCodeStateEq_with_executionEnv hprefix state.executionEnv
          · injection hstep with hstate
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hstate
            subst state'
            exact stateCodeStateEq_with_executionEnv hprefix state.executionEnv

theorem Xstep_static_stateCodeStateEq_succ_depth
    {n : Nat} {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)} :
    state.executionEnv.perm = false →
    1024 - state.executionEnv.depth.val = n + 1 →
    (∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountCodeStateEq σ σ') →
    Xstep validJumps state = .ok (state', ret) →
    stateCodeStateEq state state' := by
  intro hperm hdepth ihTheta hstep
  set instr : Operation × Option (UInt256 × Nat) :=
    decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none) with hinstr
  rcases instr with ⟨op, arg⟩
  unfold Xstep at hstep
  simp only [bind, Except.bind] at hstep
  split at hstep
  · simp at hstep
  · rename_i stateZ cost hZ
    have hZ' : Z validJumps op state = .ok (stateZ, cost) := by
      simpa [← hinstr] using hZ
    cases hstep' :
        step cost (op, arg)
          {stateZ with executionEnv.depth := state.executionEnv.depth} with
    | error e =>
        simp [← hinstr, hstep'] at hstep
    | ok stepped =>
        have hstep'' :
            step cost (op, arg)
              {stateZ with executionEnv.depth := state.executionEnv.depth} =
            .ok stepped := hstep'
        have hZpres : stateCodeStateEq state stateZ :=
          Z_static_stateCodeStateEq hZ'
        have hstepPres :
            stateCodeStateEq
              ({stateZ with executionEnv.depth := state.executionEnv.depth} : State)
              stepped :=
          step_static_stateCodeStateEq_of_Z_succ_depth
            hperm hdepth ihTheta hZ' hstep''
        have hprefix : stateCodeStateEq state stepped :=
          stateCodeStateEq_trans
            (stateCodeStateEq_with_executionEnv_depth hZpres state.executionEnv.depth)
            hstepPres
        simp [← hinstr, hstep'] at hstep
        split at hstep
        · injection hstep with hstate
          have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
            congrArg Prod.fst hstate
          subst state'
          exact stateCodeStateEq_with_executionEnv hprefix state.executionEnv
        · split at hstep
          · injection hstep with hstate
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hstate
            subst state'
            exact stateCodeStateEq_with_executionEnv hprefix state.executionEnv
          · injection hstep with hstate
            have hstateEq : { stepped with executionEnv := state.executionEnv } = state' :=
              congrArg Prod.fst hstate
            subst state'
            exact stateCodeStateEq_with_executionEnv hprefix state.executionEnv

theorem Xstep_static_preserves_perm
    {validJumps : Array UInt256} {state state' : State}
    {ret : Option (HaltCause × ByteArray)} :
    state.executionEnv.perm = false →
    Xstep validJumps state = .ok (state', ret) →
    state'.executionEnv.perm = false := by
  intro hperm hstep
  unfold Xstep at hstep
  simp only [bind, Except.bind] at hstep
  split at hstep
  · simp at hstep
  · rename_i stateZ cost hZ
    cases hstep' :
        step cost
          (decode state.executionEnv.code state.machineState.pc |>.getD (.STOP, .none))
          {stateZ with executionEnv.depth := state.executionEnv.depth} with
    | error e =>
        simp [hstep'] at hstep
    | ok stepped =>
        simp [hstep'] at hstep
        split at hstep
        · injection hstep with hstate
          have hstateEq := congrArg Prod.fst hstate
          simp at hstateEq
          subst state'
          simpa using hperm
        · split at hstep
          · injection hstep with hstate
            have hstateEq := congrArg Prod.fst hstate
            simp at hstateEq
            subst state'
            simpa using hperm
          · injection hstep with hstate
            have hstateEq := congrArg Prod.fst hstate
            simp at hstateEq
            subst state'
            simpa using hperm

theorem X_static_stateCodeStateEq_max_depth
    {validJumps : Array UInt256} {state state' : State} {out : ByteArray}
    (fuel : Nat)
    (hperm : state.executionEnv.perm = false)
    (hdepth : state.executionEnv.depth = 1024)
    (hX : X fuel validJumps state = .ok (.success state' out)) :
    stateCodeStateEq state state' := by
  induction fuel generalizing state with
  | zero =>
      simp [X] at hX
  | succ fuel ih =>
      simp [X] at hX
      cases hstep : Xstep validJumps state with
      | error e =>
          simp [hstep, bind, Except.bind] at hX
      | ok stepResult =>
          rcases stepResult with ⟨next, ret⟩
          have hnext : stateCodeStateEq state next :=
            Xstep_static_stateCodeStateEq_max_depth
              (validJumps := validJumps) hperm hdepth hstep
          cases ret with
          | none =>
              have htailPerm :
                  ({next with executionEnv.depth := state.executionEnv.depth} : State).executionEnv.perm =
                    false := by
                simpa using Xstep_static_preserves_perm
                  (validJumps := validJumps) (ret := none) hperm hstep
              have htail :
                  stateCodeStateEq
                    ({next with executionEnv.depth := state.executionEnv.depth} : State) state' :=
                ih htailPerm (by simp [hdepth])
                  (by simpa [hstep, bind, Except.bind] using hX)
              exact stateCodeStateEq_trans
                (stateCodeStateEq_with_executionEnv_depth hnext state.executionEnv.depth)
                htail
          | some ret =>
              rcases ret with ⟨cause, out'⟩
              cases cause with
              | revert =>
                  simp [hstep, bind, Except.bind] at hX
              | success =>
                  simp [hstep, bind, Except.bind] at hX
                  rcases hX with ⟨hstate, _hout⟩
                  subst state'
                  exact hnext

theorem X_static_stateCodeStateEq_succ_depth
    {n : Nat} {validJumps : Array UInt256} {state state' : State} {out : ByteArray}
    (fuel : Nat)
    (hperm : state.executionEnv.perm = false)
    (hdepth : 1024 - state.executionEnv.depth.val = n + 1)
    (ihTheta : ∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountCodeStateEq σ σ')
    (hX : X fuel validJumps state = .ok (.success state' out)) :
    stateCodeStateEq state state' := by
  induction fuel generalizing state with
  | zero =>
      simp [X] at hX
  | succ fuel ih =>
      simp [X] at hX
      cases hstep : Xstep validJumps state with
      | error e =>
          simp [hstep, bind, Except.bind] at hX
      | ok stepResult =>
          rcases stepResult with ⟨next, ret⟩
          have hnext : stateCodeStateEq state next :=
            Xstep_static_stateCodeStateEq_succ_depth
              (validJumps := validJumps) hperm hdepth ihTheta hstep
          cases ret with
          | none =>
              have htailPerm :
                  ({next with executionEnv.depth := state.executionEnv.depth} : State).executionEnv.perm =
                    false := by
                simpa using Xstep_static_preserves_perm
                  (validJumps := validJumps) (ret := none) hperm hstep
              have htail :
                  stateCodeStateEq
                    ({next with executionEnv.depth := state.executionEnv.depth} : State) state' :=
                ih htailPerm (by simp [hdepth])
                  (by simpa [hstep, bind, Except.bind] using hX)
              exact stateCodeStateEq_trans
                (stateCodeStateEq_with_executionEnv_depth hnext state.executionEnv.depth)
                htail
          | some ret =>
              rcases ret with ⟨cause, out'⟩
              cases cause with
              | revert =>
                  simp [hstep, bind, Except.bind] at hX
              | success =>
                  simp [hstep, bind, Except.bind] at hX
                  rcases hX with ⟨hstate, _hout⟩
                  subst state'
                  exact hnext

theorem Xi_static_accountCodeStateEq_max_depth
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {out : ByteArray} :
    I.perm = false →
    I.depth = 1024 →
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success (createdAccounts', σ', g', A') out) →
    accountCodeStateEq σ σ' := by
  intro hperm hdepth hXi
  let freshEvmState : State :=
    { (default : State) with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      machineState.gasAvailable := .ofUInt256 g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader
    }
  unfold Ξ at hXi
  simp only [bind, Except.bind] at hXi
  cases hX :
      X (UInt256.toNat g + 1) (D_J I.code 0) freshEvmState with
  | error e =>
      rw [hX] at hXi
      simp at hXi
  | ok result =>
      cases result with
      | revert gRevert outRevert =>
          rw [hX] at hXi
          simp at hXi
      | success stateSuccess outSuccess =>
          have hstate :
              stateCodeStateEq freshEvmState stateSuccess :=
            X_static_stateCodeStateEq_max_depth (UInt256.toNat g + 1)
              (by simpa [freshEvmState] using hperm)
              (by simpa [freshEvmState] using hdepth)
              hX
          rw [hX] at hXi
          simp at hXi
          rcases hXi with ⟨hcomponents, _hout⟩
          rcases hcomponents with ⟨_hcreated, hσ, _hg, _hA⟩
          subst σ'
          simpa [stateCodeStateEq, freshEvmState] using hstate

theorem Xi_static_accountCodeStateEq_succ_depth
    {n : Nat}
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap} {g g' : UInt256} {A A' : Substate}
    {I : ExecutionEnv} {out : ByteArray} :
    I.perm = false →
    1024 - I.depth.val = n + 1 →
    (∀ (blobVersionedHashesᵢ : List ByteArray)
        (genesisBlockHeaderᵢ : BlockHeader) (blocksᵢ : ProcessedBlocks)
        createdAccountsᵢ (e : Fin 1025) σ σ₀ A s o r c g p v v' d H
        createdAccounts' σ' g' A' z out,
        1024 - e.val = n →
          Θ blobVersionedHashesᵢ createdAccountsᵢ genesisBlockHeaderᵢ blocksᵢ
              σ σ₀ A s o r c g p v v' d e H false =
            (createdAccounts', σ', g', A', z, out) →
          accountCodeStateEq σ σ') →
    Ξ createdAccounts genesisBlockHeader blocks σ σ₀ g A I =
      .ok (.success (createdAccounts', σ', g', A') out) →
    accountCodeStateEq σ σ' := by
  intro hperm hdepth ihTheta hXi
  let freshEvmState : State :=
    { (default : State) with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      createdAccounts := createdAccounts
      machineState.gasAvailable := .ofUInt256 g
      blocks := blocks
      genesisBlockHeader := genesisBlockHeader
    }
  unfold Ξ at hXi
  simp only [bind, Except.bind] at hXi
  cases hX :
      X (UInt256.toNat g + 1) (D_J I.code 0) freshEvmState with
  | error e =>
      rw [hX] at hXi
      simp at hXi
  | ok result =>
      cases result with
      | revert gRevert outRevert =>
          rw [hX] at hXi
          simp at hXi
      | success stateSuccess outSuccess =>
          have hstate :
              stateCodeStateEq freshEvmState stateSuccess :=
            X_static_stateCodeStateEq_succ_depth (UInt256.toNat g + 1)
              (by simpa [freshEvmState] using hperm)
              (by simpa [freshEvmState] using hdepth)
              ihTheta
              hX
          rw [hX] at hXi
          simp at hXi
          rcases hXi with ⟨hcomponents, _hout⟩
          rcases hcomponents with ⟨_hcreated, hσ, _hg, _hA⟩
          subst σ'
          simpa [stateCodeStateEq, freshEvmState] using hstate

theorem thetaXiAccountMap_static_accountCodeStateEq
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {σ σPre : AccountMap} {A : Substate}
    {xi : Except EVM.ExecutionException
      (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate))}
    (hpre : accountCodeStateEq σ σPre)
    (hxi : ∀ {createdAccounts' σ' g' A' out},
      xi = .ok (.success (createdAccounts', σ', g', A') out) →
      accountCodeStateEq σPre σ') :
    accountCodeStateEq σ (thetaXiAccountMap σ createdAccounts A xi) := by
  cases h : xi with
  | error e =>
      simp [thetaXiAccountMap, thetaXiResult]
  | ok result =>
      cases result with
      | revert g' out =>
          simp [thetaXiAccountMap, thetaXiResult]
      | success result out =>
          rcases result with ⟨createdAccounts', σ', g', A'⟩
          by_cases hempty : (σ' == (∅ : AccountMap)) = true
          · simp [thetaXiAccountMap, thetaXiResult, hempty]
          · simpa [thetaXiAccountMap, thetaXiResult, hempty] using
              accountCodeStateEq_trans hpre (hxi h)
theorem Theta_static_accountCodeStateEq
    {blobVersionedHashes : List ByteArray}
    {createdAccounts createdAccounts' : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σ' : AccountMap} {A A' : Substate}
    {s o r : AccountAddress} {c : ToExecute}
    {g g' p v v' : UInt256} {d out : ByteArray} {e : Fin 1025}
    {H : BlockHeader} {z : Bool}
    (hTheta : Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r c
        g p v v' d e H false =
      (createdAccounts', σ', g', A', z, out)) :
    accountCodeStateEq σ σ' := by
  generalize hn : 1024 - e.val = n
  induction n generalizing blobVersionedHashes createdAccounts genesisBlockHeader blocks
      createdAccounts' σ σ₀ σ' A A' s o r c g g' p v v' d out e H z with
  | zero =>
      have he : e = 1024 := by omega
      subst e
      cases hc : c with
      | Precompiled pc =>
          exact accountCodeStateEq_of_precompiled_Theta
            (createdAccounts' := createdAccounts') (pc := pc) (by simpa [hc] using hTheta)
      | Code code =>
          let σ₁ := sendEth r s v true σ
          let I : ExecutionEnv :=
            { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
              source := s, weiValue := v', depth := (1024 : Fin 1025), perm := false,
              code := code, header := H, blobVersionedHashes := blobVersionedHashes }
          let xi := Ξ createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I
          have hproj :
              (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
                (.Code code) g p v v' d (1024 : Fin 1025) H false).2.1 = σ' := by
            simpa [hc] using congrArg (fun x => x.2.1) hTheta
          rw [← hproj]
          rw [code_Theta_accountMap_eq blobVersionedHashes createdAccounts
            genesisBlockHeader blocks σ σ₀ A s o r code g p v v' d (1024 : Fin 1025) H]
          exact thetaXiAccountMap_static_accountCodeStateEq
            (sendEth_accountCodeStateEq r s v true σ)
            (by
              intro createdAccounts' σ' g' A' out hsuccess
              exact Xi_static_accountCodeStateEq_max_depth (I := I)
                rfl rfl (by simpa [σ₁, I, xi] using hsuccess))
  | succ n ih =>
      cases hc : c with
      | Precompiled pc =>
          exact accountCodeStateEq_of_precompiled_Theta
            (createdAccounts' := createdAccounts') (pc := pc) (by simpa [hc] using hTheta)
      | Code code =>
          let σ₁ := sendEth r s v true σ
          let I : ExecutionEnv :=
            { codeOwner := r, sender := o, gasPrice := p.toNat, calldata := d,
              source := s, weiValue := v', depth := e, perm := false,
              code := code, header := H, blobVersionedHashes := blobVersionedHashes }
          let xi := Ξ createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I
          have hproj :
              (Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r
                (.Code code) g p v v' d e H false).2.1 = σ' := by
            simpa [hc] using congrArg (fun x => x.2.1) hTheta
          rw [← hproj]
          rw [code_Theta_accountMap_eq blobVersionedHashes createdAccounts
            genesisBlockHeader blocks σ σ₀ A s o r code g p v v' d e H]
          exact thetaXiAccountMap_static_accountCodeStateEq
            (sendEth_accountCodeStateEq r s v true σ)
            (by
              intro createdAccounts' σ' g' A' out hsuccess
              exact Xi_static_accountCodeStateEq_succ_depth (n := n) (I := I)
                rfl (by simpa [I] using hn)
                (by
                  intro blobVersionedHashesᵢ genesisBlockHeaderᵢ blocksᵢ
                    createdAccountsᵢ eᵢ σᵢ σ₀ᵢ Aᵢ sᵢ oᵢ rᵢ cᵢ gᵢ pᵢ vᵢ v'ᵢ dᵢ Hᵢ
                    createdAccounts'ᵢ σ'ᵢ g'ᵢ A'ᵢ zᵢ outᵢ heᵢ hThetaᵢ
                  exact ih (blobVersionedHashes := blobVersionedHashesᵢ)
                    (createdAccounts := createdAccountsᵢ)
                    (genesisBlockHeader := genesisBlockHeaderᵢ) (blocks := blocksᵢ)
                    (σ := σᵢ) (σ₀ := σ₀ᵢ) (σ' := σ'ᵢ) (A := Aᵢ) (A' := A'ᵢ)
                    (s := sᵢ) (o := oᵢ) (r := rᵢ) (c := cᵢ) (g := gᵢ) (g' := g'ᵢ)
                    (p := pᵢ) (v := vᵢ) (v' := v'ᵢ) (d := dᵢ) (out := outᵢ)
                    (e := eᵢ) (H := Hᵢ) (z := zᵢ) hThetaᵢ heᵢ)
                (by simpa [σ₁, I, xi] using hsuccess))


end Reasoning.Theory
