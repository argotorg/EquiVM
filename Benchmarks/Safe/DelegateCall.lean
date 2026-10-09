import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- GENERALIZES Reasoning.Reach.RD.call to the DELEGATECALL context and value rules.
set_option maxHeartbeats 1000000 in
theorem delegateCallReach {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    {k C : ℕ} {gasArg target inOffset inSize outOffset outSize : UInt256}
    {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata σ k C)
    (hdec : decode code pc = some (.DELEGATECALL, .none))
    (hdepth : ee.depth.val < 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (σ', g'', A', z, o) = Ethereum.EVM.Θ σ s0.σ₀ A_in
          ee.source ee.sender
          ee.codeOwner (toExecute σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat ee.gasPrice) ⟨0⟩ ee.weiValue
          (mem.readWithPadding inOffset.toNat inSize.toNat) (ee.depth + 1) ee.header
          ee.blobVersionedHashes ee.blocks ee.perm)
      ∧ RD code ee g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: t)
          (o.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat o.size)).toNat)
          (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
            outOffset.toNat outSize.toNat))
          o σ' k' C'
      ∧ o.size < UInt256.size := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact ⟨_, _, _, default, ⟨0⟩, k, C, ⟨_, _, rfl⟩,
      (by unfold RD; exact Or.inl hoog),
      (by
        exact Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (Reasoning.Reach.readWithPadding_size_lt_uint256_of_word _ inOffset inSize))⟩
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.DELEGATECALL, .none) := by
      rw [hcode, hpc]; exact hdec
    have hdepth' : s.executionEnv.depth.val < 1024 := by rw [hee]; exact hdepth
    have st := step_delegatecall s hd
    rw [hstk] at st
    simp only [accountAddress_roundtrip] at st
    have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 - 6 + 1 > 1024) = False :=
      eq_false (by omega)
    have hdepthLt : s.executionEnv.depth < 1024 := by rw [Fin.lt_def]; exact hdepth'
    have hbal : ∀ y : UInt256, ((⟨0⟩ : UInt256) ≤ y) = True :=
      fun _ ↦ eq_true (Fin.zero_le _)
    have hgtF : ∀ y : UInt256, ((⟨0⟩ : UInt256) > y) = False :=
      fun _ ↦ eq_false (Fin.not_lt_zero _)
    have hdeqF : (s.executionEnv.depth == 1024) = false := by
      rw [beq_eq_false_iff_ne]; intro hh; rw [hh] at hdepth'; exact absurd hdepth' (by decide)
    simp only [List.length_cons, hovF, hdepthLt, hbal, hgtF, hdeqF, and_true, if_true,
      Bool.or_false] at st
    rw [collapse_two_stage, hcode] at st
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    split at hXP
    · exact ⟨_, _, _, default, ⟨0⟩, k, C, ⟨_, _, rfl⟩,
        (by unfold RD; exact Or.inl hXP),
        (by
          exact Theta_returnData_size_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (Reasoning.Reach.readWithPadding_size_lt_uint256_of_word _ inOffset inSize))⟩
    · rename_i hP
      set mc := memoryExpansionCost s Operation.DELEGATECALL with hmc
      set gc := Ccall (AccountAddress.ofUInt256 target) s.executionEnv.codeOwner
        (⟨0⟩ : UInt256) gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack,
          execLength := s.machineState.execLength,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return }
        s.substate with hgc
      set G := Ccallgas (AccountAddress.ofUInt256 target) s.executionEnv.codeOwner
        (⟨0⟩ : UInt256) gasArg s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack,
          execLength := s.machineState.execLength + 1,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return }
        s.substate with hG
      set cg := UInt256.ofNat G with hcg
      set ce := Cextra (AccountAddress.ofUInt256 target) s.executionEnv.codeOwner
        (⟨0⟩ : UInt256) s.accountMap s.substate with hce
      set θs := Θ s.accountMap s.σ₀
        (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
        s.executionEnv.source
        s.executionEnv.sender s.executionEnv.codeOwner
        (toExecute s.accountMap (AccountAddress.ofUInt256 target)) cg
        (UInt256.ofNat s.executionEnv.gasPrice) (⟨0⟩ : UInt256) s.executionEnv.weiValue
        (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
        (s.executionEnv.depth + 1) s.executionEnv.header s.executionEnv.blobVersionedHashes
        s.executionEnv.blocks s.executionEnv.perm with hθs
      set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - θs.2.1.toNat)
        with hgv
      have hσ : s.accountMap = σ := hacc
      have hw1 : s.σ₀ = s0.σ₀ := hworld
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hmcle : mc ≤ s.machineState.gasAvailable.toNat := by omega
      have hretle : θs.2.1.toNat ≤ cg.toNat := by
        rw [hθs]
        exact Theta_returnedGas_le s.accountMap s.σ₀
          (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
          s.executionEnv.source
          s.executionEnv.sender s.executionEnv.codeOwner
          (toExecute s.accountMap (AccountAddress.ofUInt256 target)) cg
          (UInt256.ofNat s.executionEnv.gasPrice) (⟨0⟩ : UInt256) s.executionEnv.weiValue
          (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
          (s.executionEnv.depth + 1) s.executionEnv.header s.executionEnv.blobVersionedHashes
          s.executionEnv.blocks s.executionEnv.perm
      have hcgle : cg.toNat ≤ G := by
        have h : cg.toNat = G % UInt256.size := by rw [hcg]; rfl
        rw [h]; exact Nat.mod_le _ _
      have hgcG : gc = G + ce := by rw [hgc, hG, hce]; rfl
      have hce1 : 1 ≤ ce := by
        rw [hce]
        have hcacc : 1 ≤ Caccess (AccountAddress.ofUInt256 target) s.substate := by
          unfold Caccess; split <;> decide
        unfold Cextra; omega
      have hg''le : θs.2.1.toNat + 1 ≤ gc := by omega
      have hgcle' : gc ≤ (s.machineState.gasAvailable.subNat mc).toNat := by
        rw [toNat_sub_ofNat hmcle]; omega
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      have hrefundCostPos : 1 ≤ gc - θs.2.1.toNat := by omega
      set callCharge := mc + (gc - θs.2.1.toNat) with hcallCharge
      have hcallChargeLeGas : callCharge ≤ s.machineState.gasAvailable.toNat := by
        rw [hcallCharge]
        have hdeltaLe : gc - θs.2.1.toNat ≤ gc := Nat.sub_le _ _
        omega
      have hCcallCharge : C + callCharge ≤ g.toNat := by
        rw [hgasN] at hcallChargeLeGas
        omega
      have hgvGas : gv = g.subNat (C + callCharge) := by
        rw [hgv, hgas, hcallCharge]
        rw [Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      rw [show g.toNat - k = g.toNat + 1 - (k + 1) from by omega] at hXP
      refine ⟨θs.1, θs.2.2.2.1, θs.2.2.2.2,
        (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate, cg, k + 1,
        C + callCharge, ⟨θs.2.1, θs.2.2.1, ?_⟩, ?_, ?_⟩
      · rw [← hee, ← hσ, ← hmem, ← hw1, ← hθs]
      · unfold RD
        refine Or.inr ⟨_, hXP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact hcode
        · rw [hpc]
        · cases θs.2.2.2.1 <;> rfl
        · show gv = g.subNat (C + callCharge)
          exact hgvGas
        · show k + 1 ≤ C + callCharge
          rw [hcallCharge]
          omega
        · exact hCcallCharge
        · rw [hmem]
        · rw [haw]
        · rfl
        · rfl
        · exact hee
        · exact hworld
      · rw [hθs]
        exact Ethereum.EVM.theta_projection_output_size_lt_uint256
          s.accountMap s.σ₀
          (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
          s.executionEnv.source
          s.executionEnv.sender s.executionEnv.codeOwner
          (toExecute s.accountMap (AccountAddress.ofUInt256 target))
          (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
          cg (UInt256.ofNat s.executionEnv.gasPrice) (⟨0⟩ : UInt256) s.executionEnv.weiValue
          (s.executionEnv.depth + 1) s.executionEnv.header s.executionEnv.blobVersionedHashes
          s.executionEnv.blocks s.executionEnv.perm
          (Reasoning.Reach.readWithPadding_size_lt_uint256_of_word _ inOffset inSize)

-- GENERALIZES Reasoning.Reach.RD.solcStaticcallDepthLimit to DELEGATECALL.
theorem delegateCallDepthLimitReach {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    {k C : ℕ} {gasArg target inOffset inSize outOffset outSize : UInt256}
    {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata σ k C)
    (hdec : decode code pc = some (.DELEGATECALL, .none))
    (hdepth : ee.depth = 1024)
    (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) (⟨0⟩ :: t)
        (ByteArray.empty.write 0 mem outOffset.toNat
          (min outSize (UInt256.ofNat ByteArray.empty.size)).toNat)
        (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat))
        ByteArray.empty σ k' C' := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee,
    hworld⟩
  · exact ⟨k, C, by unfold RD; exact Or.inl hoog⟩
  · have hd : decode s.executionEnv.code s.machineState.pc = some (.DELEGATECALL, .none) := by
      rw [hcode, hpc]; exact hdec
    have hdepth1024 : s.executionEnv.depth = 1024 := by rw [hee]; exact hdepth
    have st := step_delegatecall s hd
    rw [hstk] at st
    simp only [accountAddress_roundtrip] at st
    have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 - 6 + 1 > 1024) = False :=
      eq_false (by omega)
    have hdepthF : (s.executionEnv.depth < 1024) = False :=
      eq_false (by rw [hdepth1024]; exact lt_irrefl _)
    have hbal : ∀ y : UInt256, ((⟨0⟩ : UInt256) ≤ y) = True :=
      fun _ ↦ eq_true (Fin.zero_le _)
    have hgtF : ∀ y : UInt256, ((⟨0⟩ : UInt256) > y) = False :=
      fun _ ↦ eq_false (Fin.not_lt_zero _)
    have hdeqT : (s.executionEnv.depth == 1024) = true := by
      rw [beq_iff_eq]; exact hdepth1024
    simp only [List.length_cons, hovF, hdepthF, hbal, hgtF, hdeqT, and_false,
      Bool.or_true, if_true] at st
    rw [collapse_two_stage, hcode] at st
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    set mc := memoryExpansionCost s Operation.DELEGATECALL with hmc
    set gc := Ccall (AccountAddress.ofUInt256 target) s.executionEnv.codeOwner
      (⟨0⟩ : UInt256) gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack,
        execLength := s.machineState.execLength,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return }
      s.substate with hgc
    set G := Ccallgas (AccountAddress.ofUInt256 target) s.executionEnv.codeOwner
      (⟨0⟩ : UInt256) gasArg s.accountMap
      { pc := s.machineState.pc, stack := s.machineState.stack,
        execLength := s.machineState.execLength + 1,
        gasAvailable := s.machineState.gasAvailable.subNat mc,
        activeWords := s.machineState.activeWords, memory := s.machineState.memory,
        returnData := s.machineState.returnData, H_return := s.machineState.H_return }
      s.substate with hG
    set ce := Cextra (AccountAddress.ofUInt256 target) s.executionEnv.codeOwner
      (⟨0⟩ : UInt256) s.accountMap s.substate with hce
    set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - (UInt256.ofNat G).toNat)
      with hgv
    have hσ : s.accountMap = σ := hacc
    split at hXP
    · exact ⟨k, C, by unfold RD; exact Or.inl hXP⟩
    · rename_i hP
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hmcle : mc ≤ s.machineState.gasAvailable.toNat := by omega
      have hcgle : (UInt256.ofNat G).toNat ≤ G := by
        show G % UInt256.size ≤ G
        exact Nat.mod_le _ _
      have hgcG : gc = G + ce := by
        rw [hgc, hG, hce]
        rfl
      have hce1 : 1 ≤ ce := by
        rw [hce]
        have hcacc : 1 ≤ Caccess (AccountAddress.ofUInt256 target) s.substate := by
          unfold Caccess; split <;> decide
        unfold Cextra
        omega
      have hgcle' : gc ≤ (s.machineState.gasAvailable.subNat mc).toNat := by
        rw [toNat_sub_ofNat hmcle]
        omega
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      set callCharge := mc + (gc - (UInt256.ofNat G).toNat) with hcallCharge
      have hcallChargeLeGas : callCharge ≤ s.machineState.gasAvailable.toNat := by
        rw [hcallCharge]
        have hdeltaLe : gc - (UInt256.ofNat G).toNat ≤ gc := Nat.sub_le _ _
        omega
      have hCcallCharge : C + callCharge ≤ g.toNat := by
        rw [hgasN] at hcallChargeLeGas
        omega
      have hgvGas : gv = g.subNat (C + callCharge) := by
        rw [hgv, hgas, hcallCharge]
        rw [Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      rw [show g.toNat - k = g.toNat + 1 - (k + 1) from by omega] at hXP
      refine ⟨k + 1, C + callCharge, ?_⟩
      unfold RD
      refine Or.inr ⟨_, hXP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hcode
      · rw [hpc]
      · rfl
      · show gv = g.subNat (C + callCharge)
        exact hgvGas
      · show k + 1 ≤ C + callCharge
        rw [hcallCharge]
        omega
      · exact hCcallCharge
      · simp [hmem]
      · rw [haw]
      · rfl
      · simp [hσ]
      · exact hee
      · exact hworld

end Benchmarks.Safe
