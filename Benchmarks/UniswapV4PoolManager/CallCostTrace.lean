import Benchmarks.UniswapV4PoolManager.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Reasoning.Reach

-- GENERALIZES Reasoning.Reach.RD.call to retain gas spent by the same opaque callee invocation.
theorem RD.callWithCost {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : ℕ}
    {gasArg target inOffset inSize outOffset outSize : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
          (gasArg :: target :: ⟨0⟩ :: inOffset :: inSize :: outOffset :: outSize :: t)
          mem aw rdata σ k C)
    (hdec : decode code pc = some (.CALL, .none))
    (hdepth : ee.depth.val < 1024)
    (hov : t.length + 1 ≤ 1024) :
    X (g.toNat+1) (D_J code 0) s0 = .error .OutOfGass ∨
    ∃ (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas g'' : UInt256) (A' : Substate) (k' C' : ℕ),
      (
        (σ', g'', A', z, o) = Ethereum.EVM.Θ σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat ee.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOffset.toNat inSize.toNat) (ee.depth + 1) ee.header ee.blobVersionedHashes ee.blocks ee.perm)
      ∧ RD code ee g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: t)
          (o.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat o.size)).toNat)
          (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
            outOffset.toNat outSize.toNat))
          o σ' k' C'
      ∧ C + (Cₘ (callActiveWords aw inOffset inSize outOffset outSize) - Cₘ aw) +
          100 + (callGas.toNat-g''.toNat) ≤ C'
      ∧ o.size < UInt256.size := by
  unfold RD at h
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hσ₀⟩
  · exact .inl hoog
  · -- reach the CALL cursor `s`; reduce `step_call` (value 0, depth < 1024)
    have hd : decode s.executionEnv.code s.machineState.pc = some (.CALL, .none) := by
      rw [hcode, hpc]; exact hdec
    have hdepth' : s.executionEnv.depth.val < 1024 := by rw [hee]; exact hdepth
    have st := step_call s hd
    rw [hstk] at st
    have hovF : (t.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 + 1 > 1024) = False := eq_false (by omega)
    have hstaticF : (¬ s.executionEnv.perm = true ∧ ({val := 0} : UInt256) ≠ {val := 0}) = False :=
      eq_false (by rintro ⟨_, h2⟩; exact h2 rfl)
    have hdepthLt : s.executionEnv.depth < 1024 := by rw [Fin.lt_def]; exact hdepth'
    have hbal : ∀ y : UInt256, (({val := 0} : UInt256) ≤ y) = True := fun y => eq_true (Fin.zero_le _)
    have hgtF : ∀ y : UInt256, (({val := 0} : UInt256) > y) = False := fun y => eq_false (Fin.not_lt_zero _)
    have hdeqF : (s.executionEnv.depth == 1024) = false := by
      rw [beq_eq_false_iff_ne]; intro hh; rw [hh] at hdepth'; exact absurd hdepth' (by decide)
    simp only [List.length_cons, hovF, hstaticF, if_false, hdepthLt, hbal, hgtF, hdeqF,
      and_true, if_true, Bool.or_false] at st
    rw [collapse_two_stage, hcode] at st
    -- st : Xstep (D_J code 0) s = if (gas < memCost+gasCost) then OOG else .ok (SUCC, none)
    -- Step the cursor with `X_peel`, then `split` on the (unnamed) gas guard so SUCC stays concrete.
    have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
    have hXP := hX.trans (hfuel.symm ▸ X_peel (f := g.toNat - k) st)
    -- hXP : X (g+1) s0 = if (gas < memCost+gasCost) then OOG else X (g-k) SUCC
    split at hXP
    · exact .inl hXP
    · -- success: SUCC is concrete in hXP.  Emit `Or.inr ⟨SUCC, …⟩` with field projections,
      -- the gas-refund arithmetic (`C' = g - SUCC.gas`), and the Θ-link by tuple-eta.
      rename_i hP
      set mc := memoryExpansionCost s Operation.CALL with hmc
      set gc := Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) { val := 0 } gasArg
        s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hgc
      set G := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) { val := 0 } gasArg
        s.accountMap
        { pc := s.machineState.pc, stack := s.machineState.stack, execLength := s.machineState.execLength + 1,
          gasAvailable := s.machineState.gasAvailable.subNat mc,
          activeWords := s.machineState.activeWords, memory := s.machineState.memory,
          returnData := s.machineState.returnData, H_return := s.machineState.H_return } s.substate with hG
      set cg := UInt256.ofNat G with hcg
      set ce := Cextra (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target) { val := 0 }
        s.accountMap s.substate with hce
      set θs := Θ s.accountMap s.σ₀ (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
        (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner)) s.executionEnv.sender
        (AccountAddress.ofUInt256 target) (toExecute s.accountMap (AccountAddress.ofUInt256 target))
        cg (UInt256.ofNat s.executionEnv.gasPrice) { val := 0 } { val := 0 }
        (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat) (s.executionEnv.depth + 1)
        s.executionEnv.header s.executionEnv.blobVersionedHashes s.executionEnv.blocks
        s.executionEnv.perm with hθs
      set gv := (s.machineState.gasAvailable.subNat mc).subNat (gc - θs.2.1.toNat) with hgv
      have hσ : s.accountMap = σ := hacc
      have hw1 : s.σ₀ = s0.σ₀ := hσ₀
      -- gas arithmetic
      have haN : s.machineState.gasAvailable.toNat < UInt256.size := s.machineState.gasAvailable.isLt
      have hPle : mc + gc ≤ s.machineState.gasAvailable.toNat := Nat.le_of_not_lt hP
      have hmcle : mc ≤ s.machineState.gasAvailable.toNat := by omega
      have hretle : θs.2.1.toNat ≤ cg.toNat := by
        rw [hθs]
        exact Theta_returnedGas_le s.accountMap s.σ₀ (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
          (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner)) s.executionEnv.sender
          (AccountAddress.ofUInt256 target) (toExecute s.accountMap (AccountAddress.ofUInt256 target))
          cg (UInt256.ofNat s.executionEnv.gasPrice) { val := 0 } { val := 0 }
          (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat) (s.executionEnv.depth + 1)
          s.executionEnv.header s.executionEnv.blobVersionedHashes s.executionEnv.blocks s.executionEnv.perm
      have hcgle : cg.toNat ≤ G := by
        have h : cg.toNat = G % UInt256.size := by rw [hcg]; rfl
        rw [h]; exact Nat.mod_le _ _
      have hgcG : gc = G + ce := by rw [hgc, hG, hce]; rfl
      have hce100 : 100 ≤ ce := by
        rw [hce]
        have hcacc : 100 ≤ Caccess (AccountAddress.ofUInt256 target) s.substate := by
          unfold Caccess; split <;> decide
        unfold Cextra; omega
      have hg''le : θs.2.1.toNat + 1 ≤ gc := by omega
      have hgcle' : gc ≤ (s.machineState.gasAvailable.subNat mc).toNat := by
        rw [toNat_sub_ofNat hmcle]; omega
      have hgvN : gv = (s.machineState.gasAvailable.subNat mc).subNat (gc - θs.2.1.toNat) := by
        rw [hgv]
      have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
        rw [hgas, Sat256.subNat_toNat]
      have hrefundCostPos : 1 ≤ gc - θs.2.1.toNat := by omega
      set callCharge := mc + (gc - θs.2.1.toNat) with hcallCharge
      have hcallChargePos : 1 ≤ callCharge := by
        rw [hcallCharge]
        omega
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
      have hgkey : gv.toNat + k + 1 ≤ g.toNat := by
        rw [hgvGas, Sat256.subNat_toNat]
        omega
      rw [show g.toNat - k = g.toNat + 1 - (k + 1) from by omega] at hXP
      -- assemble the conclusion
      refine .inr ⟨θs.1, θs.2.2.2.1, θs.2.2.2.2,
        (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate, cg, θs.2.1, θs.2.2.1, k + 1,
        C + callCharge, ?_, ?_, ?_, ?_⟩
      · -- Θ-link: rewrite cursor fields to the world/ee/acc form, then tuple-eta
        rw [← hee, ← hσ, ← hmem, ← hw1, ← hθs]
      · -- RD on the successor `SUCC` (inferred from `hXP`'s `X` equation)
        unfold RD
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
        · exact hσ₀
      · have hmceq : mc = Cₘ (callActiveWords aw inOffset inSize outOffset outSize) - Cₘ aw := by
          simp only [hmc, memoryExpansionCost, memoryExpansionCost.μᵢ', hstk, haw, callActiveWords]
          rfl
        rw [← hmceq, hcallCharge]
        omega
      · rw [hθs]
        exact Ethereum.EVM.theta_projection_output_size_lt_uint256
          s.accountMap s.σ₀ (s.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
          (AccountAddress.ofUInt256 (UInt256.ofNat ↑s.executionEnv.codeOwner))
          s.executionEnv.sender (AccountAddress.ofUInt256 target)
          (toExecute s.accountMap (AccountAddress.ofUInt256 target))
          (s.machineState.memory.readWithPadding inOffset.toNat inSize.toNat)
          cg (UInt256.ofNat s.executionEnv.gasPrice) { val := 0 } { val := 0 }
          (s.executionEnv.depth + 1) s.executionEnv.header s.executionEnv.blobVersionedHashes s.executionEnv.blocks s.executionEnv.perm
          (Reasoning.Reach.readWithPadding_size_lt_uint256_of_word _ inOffset inSize)

end Reasoning.Reach
