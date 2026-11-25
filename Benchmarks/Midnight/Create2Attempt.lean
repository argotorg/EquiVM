import Benchmarks.Midnight.Common
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

/-! The creation attempt inside CREATE2 and its source-level counterpart. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def zeroCreate2Attempt (fork : Ethereum.Fork) (s : State) (initCode : ByteArray) (salt : UInt256) :
    AccountAddress × State × UInt256 × Bool × ByteArray :=
  let creator := s.accountMap.get? s.executionEnv.codeOwner |>.getD default
  let gas := UInt256.ofNat (L s.machineState.gasAvailable.toNat)
  if creator.nonce.toNat ≥ 2^64 - 1 then (0, s, gas, false, ByteArray.empty)
  else if hc : (⟨0⟩ : UInt256) ≤
      (s.accountMap.get? s.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      s.executionEnv.depth.val < 1024 ∧ initCode.size ≤ 49152 then
    let (addr, σ', gas', A', z, out) := Lambda fork
      (s.accountMap.insert s.executionEnv.codeOwner {creator with nonce := creator.nonce + ⟨1⟩})
      s.σ₀ s.substate s.executionEnv.codeOwner s.executionEnv.sender gas
      (UInt256.ofNat s.executionEnv.gasPrice) ⟨0⟩ initCode
      ⟨s.executionEnv.depth.val + 1, Nat.succ_lt_succ hc.2.1⟩
      (some (Ethereum.UInt256.toByteArray salt)) s.executionEnv.header
      s.executionEnv.blobVersionedHashes s.executionEnv.blocks s.executionEnv.perm
    (addr, {s with accountMap := σ', substate := A'}, gas', z, out)
  else (0, s, gas, false, ByteArray.empty)

theorem zeroCreate2Attempt_source {cfg : Config} {name : Ident} {args : List Value}
    {s evm : State} {initCode : ByteArray} (salt : UInt256)
    (hs : SourceState s s.executionEnv s.accountMap evm)
    (hcode : cfg.creationCode name args = some initCode) :
    ∃ addr mid gas z out evm',
      zeroCreate2Attempt fork s initCode salt = (addr, mid, gas, z, out) ∧
      newViaEVM fork cfg evm name 0 args (some (Ethereum.UInt256.toByteArray salt))
        (addr, evm', z) ∧
      mid.σ₀ = s.σ₀ ∧ mid.machineState.memory = s.machineState.memory ∧
      SourceState s s.executionEnv mid.accountMap evm' ∧
      (z = true → s.executionEnv.depth ≠ 1024 ∧ initCode.size ≤ 49152) := by
  let creator : Account := s.accountMap.get? s.executionEnv.codeOwner |>.getD default
  by_cases hn : creator.nonce.toNat ≥ 2^64 - 1
  · have ha : zeroCreate2Attempt fork s initCode salt =
        (0, s, UInt256.ofNat (L s.machineState.gasAvailable.toNat), false, ByteArray.empty) := by
      unfold zeroCreate2Attempt
      exact if_pos hn
    refine ⟨0, s, _, false, ByteArray.empty, evm, ha, ?_, rfl, rfl, hs, by simp⟩
    apply newViaEVM.notCreated hcode
    intro hc
    have hb := hc.2.2.1
    rw [← hs.accounts, hs.env] at hb
    exact Nat.not_lt_of_ge hn hb
  · have hbal : (⟨0⟩ : UInt256) ≤
        (s.accountMap.get? s.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) := Fin.zero_le _
    by_cases hc : s.executionEnv.depth.val < 1024 ∧ initCode.size ≤ 49152
    · have hc' : (⟨0⟩ : UInt256) ≤
          (s.accountMap.get? s.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
          s.executionEnv.depth.val < 1024 ∧ initCode.size ≤ 49152 := ⟨hbal, hc⟩
      have hdepth : s.executionEnv.depth ≠ 1024 := by
        intro h
        have hb := hc.1
        rw [h] at hb
        exact Nat.not_lt.mpr (by decide) hb
      have hdepthNext : (⟨s.executionEnv.depth.val + 1, Nat.succ_lt_succ hc.1⟩ : Fin 1025)
          = s.executionEnv.depth + 1 := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one]
        exact (Nat.mod_eq_of_lt (by omega)).symm
      let result := Lambda fork
        (s.accountMap.insert s.executionEnv.codeOwner {creator with nonce := creator.nonce + ⟨1⟩})
        s.σ₀ s.substate s.executionEnv.codeOwner s.executionEnv.sender
        (UInt256.ofNat (L s.machineState.gasAvailable.toNat))
        (UInt256.ofNat s.executionEnv.gasPrice) ⟨0⟩ initCode (s.executionEnv.depth + 1)
        (some (Ethereum.UInt256.toByteArray salt)) s.executionEnv.header
        s.executionEnv.blobVersionedHashes s.executionEnv.blocks s.executionEnv.perm
      rcases hr : result with ⟨addr, σ', gas', A', z, out⟩
      refine ⟨addr, {s with accountMap := σ', substate := A'}, gas', z, out,
        {evm with accountMap := σ', substate := A'}, ?_, ?_, rfl, rfl,
        ⟨hs.world, hs.env, rfl⟩, fun _ ↦ ⟨hdepth, hc.2⟩⟩
      · unfold zeroCreate2Attempt
        rw [if_neg hn, dif_pos hc', hdepthNext]
        change (match result with
          | (a, σ, g, A, z, o) => (a, {s with accountMap := σ, substate := A}, g, z, o)) = _
        rw [hr]
      · refine @newViaEVM.created fork cfg evm name 0 args _ (fun _ _ ↦ gas') (fun _ _ ↦ out)
          initCode ⟨0⟩ addr σ' A' z _ hcode ?_ wordOfInt_zero.symm ?_ rfl
        · unfold newCanCreate
          rw [← hs.accounts, hs.env, wordOfInt_zero]
          exact ⟨Fin.zero_le _, hdepth, Nat.lt_of_not_ge hn, hc.2⟩
        · refine ⟨UInt256.ofNat (L s.machineState.gasAvailable.toNat), s.substate, ?_⟩
          simpa only [← hs.accounts, hs.env, hs.world] using hr.symm
    · have hc' : ¬ ((⟨0⟩ : UInt256) ≤
          (s.accountMap.get? s.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
          s.executionEnv.depth.val < 1024 ∧ initCode.size ≤ 49152) := fun h ↦ hc h.2
      have ha : zeroCreate2Attempt fork s initCode salt =
          (0, s, UInt256.ofNat (L s.machineState.gasAvailable.toNat), false, ByteArray.empty) := by
        unfold zeroCreate2Attempt
        rw [if_neg hn, dif_neg hc']
      refine ⟨0, s, _, false, ByteArray.empty, evm, ha, ?_, rfl, rfl, hs, by simp⟩
      apply newViaEVM.notCreated hcode
      intro hcan
      apply hc
      have hdep := hcan.2.1
      rw [hs.env] at hdep
      refine ⟨?_, hcan.2.2.2⟩
      have hb := s.executionEnv.depth.isLt
      have hnval : s.executionEnv.depth.val ≠ 1024 := fun h ↦ hdep (Fin.ext h)
      omega

end Benchmarks.Midnight
