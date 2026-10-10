import Benchmarks.UniswapV4PoolManager.OperationPotentialMemory

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES Ccallgas_lt_Ccall to retain the warm access charge.
theorem Ccallgas_add_100_le (t r : AccountAddress) (value gas : UInt256)
    (σ : AccountMap) (μ : MachineState) (A : Substate) :
    Ccallgas t r value gas σ μ A+100 ≤ Ccall t r value gas σ μ A := by
  by_cases hv : value = (⟨0⟩ : UInt256)
  · subst value
    unfold Ccall Ccallgas Cextra Cxfer Cnew Caccess
    simp [bne, GasConstants.Gwarmaccess, GasConstants.Gcoldaccountaccess]
    split
    · split <;> omega
    · rename_i hn
      exact False.elim (hn rfl)
  · have hb : (value != (⟨0⟩ : UInt256)) = true := by simpa using hv
    unfold Ccall Ccallgas Cextra Cxfer Cnew Caccess
    simp [hb, GasConstants.Gwarmaccess, GasConstants.Gcoldaccountaccess,
      GasConstants.Gcallvalue, GasConstants.Gcallstipend, GasConstants.Gnewaccount]
    split <;> omega

-- GENERALIZES call_gas_decreases to retain any charge above the forwarded gas.
theorem gas_sub_refund_minimum {available cost refund minimum : Nat}
    (hpaid : cost ≤ available) (hnet : refund+minimum ≤ cost) :
    available-(cost-refund)+minimum ≤ available := by omega

theorem call_gas_minimum {cost minimum : Nat}
    {gas source recipient target value value' inOff inSize outOff outSize : UInt256}
    {permission : Bool} {s s' : State} {x : UInt256}
    (hpaid : cost ≤ s.machineState.gasAvailable.toNat)
    (hnet : Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 recipient)
      value gas s.accountMap s.machineState s.substate+minimum ≤ cost)
    (h : call cost gas source recipient target value value' inOff inSize outOff outSize permission s = .ok (x, s')) :
    s'.machineState.gasAvailable.toNat+minimum ≤ s.machineState.gasAvailable.toNat := by
  have ht := Theta_gas_le
    (σ := s.accountMap) (σ₀ := s.σ₀)
    (A := s.substate.addAccessedAccount (AccountAddress.ofUInt256 target))
    (s := AccountAddress.ofUInt256 source) (o := s.executionEnv.sender)
    (r := AccountAddress.ofUInt256 recipient) (c := toExecute s.accountMap (AccountAddress.ofUInt256 target))
    (g := UInt256.ofNat (Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 recipient)
      value gas s.accountMap s.machineState s.substate))
    (p := UInt256.ofNat s.executionEnv.gasPrice) (v := value) (v' := value')
    (d := s.machineState.memory.readWithPadding inOff.toNat inSize.toNat)
    (e := s.executionEnv.depth+1) (H := s.executionEnv.header)
    (blobVersionedHashes := s.executionEnv.blobVersionedHashes)
    (blocks := s.executionEnv.blocks) (w := permission)
  have hf := UInt256.toNat_ofNat_le (Ccallgas (AccountAddress.ofUInt256 target)
    (AccountAddress.ofUInt256 recipient) value gas s.accountMap s.machineState s.substate)
  unfold call at h
  simp [Ethereum.State.addAccessedAccount] at h
  repeat' (split at h)
  all_goals
    rcases h with ⟨_, hs⟩
    rw [← hs]
    simp only [Sat256.subNat_toNat]
    first
    | exact gas_sub_refund_minimum hpaid ((Nat.add_le_add_right (ht.trans hf) _).trans hnet)
    | exact gas_sub_refund_minimum hpaid ((Nat.add_le_add_right hf _).trans hnet)

theorem step_create_gas_cost {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (h : step gasCost (.CREATE, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat+gasCost ≤ s.machineState.gasAvailable.toNat := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ _ _ _ result hc
  rcases result with ⟨_, _⟩
  have hg := create_gas_le hc
  rw [← h]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at hg ⊢
  omega

theorem step_create2_gas_cost {gasCost : Nat} {arg : Option (UInt256 × Nat)} {s s' : State}
    (hle : gasCost ≤ s.machineState.gasAvailable.toNat)
    (h : step gasCost (.CREATE2, arg) s = .ok s') :
    s'.machineState.gasAvailable.toNat+gasCost ≤ s.machineState.gasAvailable.toNat := by
  rw [step.eq_1] at h
  simp [bind, Except.bind, pure, Except.pure,
    Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at h
  repeat (first | simp at h | split at h)
  rename_i _ _ _ _ result hc
  rcases result with ⟨_, _⟩
  have hg := create_gas_le hc
  rw [← h]
  simp [Ethereum.State.replaceStackAndIncrPC, Ethereum.State.incrPC] at hg ⊢
  omega

end Benchmarks.UniswapV4PoolManager
