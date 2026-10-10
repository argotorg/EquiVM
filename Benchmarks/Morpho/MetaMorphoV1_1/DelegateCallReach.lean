import Reasoning.ExternalCall

/-! Generic delegate-call reachability, including the call-depth limit. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: the DELEGATECALL counterpart of RD.solcStaticcall.
def delegateCallResult (σ σ₀ : AccountMap) (I : ExecutionEnv) (A : Substate)
    (target : AccountAddress) (gas : UInt256) (data : ByteArray) :
    AccountMap × UInt256 × Substate × Bool × ByteArray :=
  if I.depth < 1024 then
    Θ σ σ₀ A I.source I.sender I.codeOwner (toExecute σ target) gas
      (UInt256.ofNat I.gasPrice) ⟨0⟩ I.weiValue data (I.depth + 1) I.header
      I.blobVersionedHashes I.blocks I.perm
  else (σ, gas, A, false, ByteArray.empty)

theorem delegateCallResult_gas (σ σ₀ : AccountMap) (I : ExecutionEnv) (A : Substate)
    (target : AccountAddress) (gas : UInt256) (data : ByteArray) :
    (delegateCallResult σ σ₀ I A target gas data).2.1.toNat ≤ gas.toNat := by
  unfold delegateCallResult
  split
  · exact Theta_returnedGas_le ..
  · exact le_rfl

theorem delegateCallResult_status (σ σ₀ : AccountMap) (I : ExecutionEnv) (A : Substate)
    (target : AccountAddress) (gas : UInt256) (data : ByteArray) :
    let ok := (delegateCallResult σ σ₀ I A target gas data).2.2.2.1
    (if (!ok) || I.depth == 1024 then (⟨0⟩ : UInt256) else ⟨1⟩) =
      if ok then ⟨1⟩ else ⟨0⟩ := by
  dsimp only
  by_cases hd : I.depth < 1024
  · have hn : (I.depth == 1024) = false := by
      rw [beq_eq_false_iff_ne]
      exact ne_of_lt hd
    rw [hn, Bool.or_false]
    cases (delegateCallResult σ σ₀ I A target gas data).2.2.2.1 <;> rfl
  · simp [delegateCallResult, hd]

theorem delegateCallReach {code : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {gasArg target inOffset inSize outOffset outSize : UInt256} {R : List UInt256}
    (rd : RD code I g s0 pc
      (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata σ k C)
    (hdec : decode code pc = some (.DELEGATECALL, none)) (hstack : R.length + 1 ≤ 1024) :
    ∃ (A : Substate) (callGas : UInt256) (k' C' : Nat),
      let result := delegateCallResult σ s0.σ₀ I A (AccountAddress.ofUInt256 target)
        callGas (mem.readWithPadding inOffset.toNat inSize.toNat)
      RD code I g s0 (pc + ⟨1⟩) ((if result.2.2.2.1 then ⟨1⟩ else ⟨0⟩) :: R)
        (callOutputMem mem result.2.2.2.2 outOffset outSize)
        (callActiveWords aw inOffset inSize outOffset outSize) result.2.2.2.2 result.1 k' C' := by
  rcases rd with hoog |
    ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, henv, hworld⟩
  · exact ⟨default, ⟨0⟩, k, C, Or.inl hoog⟩
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.DELEGATECALL, none) := by
      rw [hcode, hpc]
      exact hdec
    have st := step_delegatecall s hd
    rw [hstk] at st
    have hov : (R.length + 1 + 1 + 1 + 1 + 1 + 1 - 6 + 1 > 1024) = False :=
      eq_false (by omega)
    have hbal : ∀ y : UInt256, ((⟨0⟩ : UInt256) ≤ y) = True :=
      fun _ ↦ eq_true (Fin.zero_le _)
    have hgt : ∀ y : UInt256, ((⟨0⟩ : UInt256) > y) = False :=
      fun _ ↦ eq_false (Fin.not_lt_zero _)
    simp only [List.length_cons, hov, hbal, hgt, true_and, if_false, decide_false,
      Bool.or_false, accountAddress_roundtrip] at st
    rw [collapse_two_stage, hcode] at st
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    split at hXP
    · exact ⟨default, ⟨0⟩, k, C, Or.inl hXP⟩
    · rename_i hP
      let mc := memoryExpansionCost s .DELEGATECALL
      let gasState := { s.machineState with gasAvailable := s.machineState.gasAvailable.subNat mc }
      let gc := Ccall (AccountAddress.ofUInt256 target) s.executionEnv.codeOwner ⟨0⟩ gasArg
        s.accountMap gasState s.substate
      let G := Ccallgas (AccountAddress.ofUInt256 target) s.executionEnv.codeOwner ⟨0⟩ gasArg
        s.accountMap { gasState with execLength := s.machineState.execLength + 1 } s.substate
      let cg := UInt256.ofNat G
      let A := (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
      let result := delegateCallResult s.accountMap s.σ₀ s.executionEnv A
        (AccountAddress.ofUInt256 target) cg
        (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hret : result.2.1.toNat ≤ cg.toNat := delegateCallResult_gas ..
      have hcg : cg.toNat ≤ G := Nat.mod_le _ _
      have hcost : G < gc := Ccallgas_lt_Ccall _ _ _ _ _
        { gasState with execLength := s.machineState.execLength + 1 } _
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      let charge := mc + (gc - result.2.1.toNat)
      have hcharge : 1 ≤ charge := by dsimp only [charge]; omega
      have hle : charge ≤ s.machineState.gasAvailable.toNat := by
        dsimp only [charge]
        have := Nat.sub_le gc result.2.1.toNat
        omega
      have hCle : C + charge ≤ g.toNat := by omega
      have hgas' : (s.machineState.gasAvailable.subNat mc).subNat
          (gc - result.2.1.toNat) = g.subNat (C + charge) := by
        rw [hgas]
        simp only [Sat256.subNat_sub_add_of_sub_sub, charge, Nat.add_assoc]
      have hstatus := delegateCallResult_status s.accountMap s.σ₀ s.executionEnv A
        (AccountAddress.ofUInt256 target) cg
        (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
      change (if (!result.2.2.2.1) || s.executionEnv.depth == 1024 then (⟨0⟩ : UInt256)
        else ⟨1⟩) = (if result.2.2.2.1 then ⟨1⟩ else ⟨0⟩) at hstatus
      rw [show g.toNat - k = g.toNat + 1 - (k + 1) from by omega] at hXP
      refine ⟨A, cg, k + 1, C + charge, Or.inr ⟨_, hXP, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · exact hcode
      · rw [hpc]
      · change (if (!result.2.2.2.1) || s.executionEnv.depth == 1024 then (⟨0⟩ : UInt256)
          else ⟨1⟩) :: R = _
        rw [hstatus]
        simp only [result, hacc, hworld, henv, hmem]
      · exact hgas'
      · omega
      · exact hCle
      · change result.2.2.2.2.write 0 s.machineState.memory outOffset.toNat
          (min outSize (UInt256.ofNat result.2.2.2.2.size)).toNat = _
        simp only [callOutputMem, result, hacc, hworld, henv, hmem]
      · simp only [callActiveWords, haw]
      · change result.2.2.2.2 = _
        simp only [result, hacc, hworld, henv, hmem]
      · change result.1 = _
        simp only [result, hacc, hworld, henv, hmem]
      · exact henv
      · exact hworld

end Benchmarks.Morpho.MetaMorphoV1_1
