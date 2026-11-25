import Benchmarks.Midnight.Create2Step

variable {fork : Ethereum.Fork}

/-! Reachability and source execution advance together across CREATE2. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: the CREATE2 analogue of the external-call bridge.
theorem zeroValueCreate2Bridge {cfg : Config} {name : Ident} {args : List Value}
    {code I g s0 pc R mem aw rdata σ k C evm} {offset size salt : UInt256}
    {initCode : ByteArray}
    (rd : RD fork code I g s0 pc (⟨0⟩ :: offset :: size :: salt :: R) mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm)
    (hdec : decode code pc = some (.CREATE2, .none))
    (hperm : I.perm = true)
    (hcode : cfg.creationCode name args = some initCode)
    (hinit : mem.readWithPadding offset.toNat size.toNat = initCode)
    (hstack : R.length + 1 ≤ 1024) :
    X fork (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
    ∃ (evm' : State) (σ' : AccountMap) (addr : AccountAddress) (z : Bool)
      (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      newViaEVM fork cfg evm name 0 args (some (Ethereum.UInt256.toByteArray salt)) (addr, evm', z) ∧
      SourceState s0 I σ' evm' ∧
      RD fork code I g s0 (pc + ⟨1⟩) ((if z then UInt256.ofNat addr.val else ⟨0⟩) :: R)
        mem aw' out σ' k' C' := by
  rcases rd with hoog | ⟨s, hX, hc, hp, hstk, hg, hk, hC, hm, ha, hr, hσ, hI, hσ₀⟩
  · exact Or.inl hoog
  have hsc : SourceState s s.executionEnv s.accountMap evm :=
    ⟨hs.world.trans hσ₀.symm, hs.env.trans hI.symm, hσ.trans hs.accounts⟩
  have hd : decode s.executionEnv.code s.machineState.pc = some (.CREATE2, .none) := by
    rw [hc, hp]; exact hdec
  have hcode' : cfg.creationCode name args =
      some (s.machineState.memory.readWithPadding offset.toNat size.toNat) := by
    rw [hm, hinit]; exact hcode
  have hfuel : g.toNat + 1 - k = (g.toNat - k) + 1 := by omega
  rcases zeroValueCreate2Step hsc hd hstk (hI ▸ hperm) hcode' hstack with
    hoog | ⟨addr, evm', z, s', hnew, hstep, henv, hworld, hpc, hstk', hmem, hs'⟩
  · have hpeel := X_peel (P := True) (s' := s) (f := g.toNat - k)
      (by simpa only [if_true] using hoog)
    rw [hc] at hpeel
    exact Or.inl (hX.trans (hfuel.symm ▸ (by simpa only [if_true] using hpeel)))
  · have hdrop := Xstep_gas_decreases_of_continues hstep
    have hgasN : s.machineState.gasAvailable.toNat = g.toNat - C := by
      rw [hg, Sat256.subNat_toNat]
    let C' := g.toNat - s'.machineState.gasAvailable.toNat
    have hC' : C' ≤ g.toNat := Nat.sub_le _ _
    have hk' : k + 1 ≤ C' := by dsimp only [C']; omega
    have hgas' : s'.machineState.gasAvailable = g.subNat C' := by
      apply Sat256.ext
      rw [Sat256.subNat_toNat]
      dsimp only [C']
      omega
    have hpeel := X_peel (P := False) (f := g.toNat - k)
      (by simpa only [if_false] using hstep)
    rw [hc] at hpeel
    have hX' : X fork (g.toNat + 1) (D_J code 0) s0 =
        X fork (g.toNat + 1 - (k + 1)) (D_J code 0) s' := by
      have hn : g.toNat + 1 - (k + 1) = g.toNat - k := by omega
      rw [hn]
      exact hX.trans (hfuel.symm ▸ (by simpa only [if_false] using hpeel))
    refine Or.inr ⟨evm', s'.accountMap, addr, z, s'.machineState.returnData,
      s'.machineState.activeWords, k + 1, C', hnew,
      ⟨hs'.world.trans hσ₀, hs'.env.trans hI, hs'.accounts⟩, ?_⟩
    exact Or.inr ⟨s', hX', (congrArg ExecutionEnv.code henv).trans hc,
      hpc.trans (congrArg (· + ⟨1⟩) hp), hstk', hgas', hk', hC', hmem.trans hm,
      rfl, rfl, rfl, henv.trans hI, hworld.trans hσ₀⟩

end Benchmarks.Midnight
