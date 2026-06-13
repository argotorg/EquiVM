import TruthClaude.PowCorrect

/-! Scratch: develop Pow decode/encode segment lemmas, then move into PowCorrect. -/

open Act ABI Ethereum Ethereum.EVM TruthClaude.Theory

set_option maxRecDepth 10000

/-- solc routine `0x9c` (`cleanup_t_uint256`-style identity): entry at pc 156 with stack
    `[v, ret, …R]`, returns `v` to the dynamic address `ret`, leaving `[v, …R]`.  9 instructions,
    gas 27; memory and active words untouched. -/
theorem powRoutine_9c {g : UInt256} {s0 s : State} {k C : ℕ} {v ret : UInt256} {R : List UInt256}
    (hcode : s.executionEnv.code = powBytecode) (hpc : s.machineState.pc = ⟨156⟩)
    (hstk : s.machineState.stack = v :: ret :: R)
    (hret : (D_J powBytecode ⟨0⟩).contains ret = true) (hov : R.length + 4 ≤ 1024)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ (k' C' : ℕ) (s' : State),
          X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k') (D_J powBytecode ⟨0⟩) s'
        ∧ s'.executionEnv.code = powBytecode ∧ s'.machineState.pc = ret
        ∧ s'.machineState.stack = v :: R
        ∧ s'.machineState.gasAvailable.toNat = g.toNat - C' ∧ k' ≤ C' ∧ C' ≤ g.toNat
        ∧ s'.machineState.memory = s.machineState.memory
        ∧ s'.machineState.activeWords = s.machineState.activeWords := by
  -- 0: JUMPDEST
  have st0 := jumpdest_xstep hcode hpc (by decide) (by rw [hstk]; simp only [List.length_cons]; omega)
  by_cases g0 : g.toNat < C + 1
  · exact Or.inl (hX.trans (stepOOG hgas st0 hk hC (by omega)))
  · set s1 := stJumpdest s with hs1
    have hX1 := hX.trans (stepContinue (k := k) (C := C) hgas st0 hk (by omega))
    have hc1 : s1.executionEnv.code = powBytecode := by rw [hs1]; simp only [stJumpdest]; exact hcode
    have hp1 : s1.machineState.pc = ⟨157⟩ := by rw [hs1]; simp only [stJumpdest]; rw [hpc]; rfl
    have hg1 : s1.machineState.gasAvailable.toNat = g.toNat - (C + 1) := by
      rw [hs1]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
    have hk1 : s1.machineState.stack = v :: ret :: R := by rw [hs1]; simp only [stJumpdest]; exact hstk
    have st1 := push0_xstep hc1 hp1 (by decide) hk1 (by first | (simp only [List.length_cons]; omega) | omega)
    by_cases g1 : g.toNat < C + 3
    · exact Or.inl (hX1.trans (stepOOG (k := k+1) (C := C+1) hg1 st1 (by omega) (by omega) (by omega)))
    · set s2 := stPush0 s1 with hs2
      have hX2 := hX1.trans (stepContinue (k := k+1) (C := C+1) hg1 st1 (by omega) (by omega))
      have hc2 : s2.executionEnv.code = powBytecode := by rw [hs2]; simp only [stPush0]; exact hc1
      have hp2 : s2.machineState.pc = ⟨158⟩ := by rw [hs2]; simp only [stPush0]; rw [hp1]; rfl
      have hg2 : s2.machineState.gasAvailable.toNat = g.toNat - (C + 3) := by
        rw [hs2]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
      have hk2 : s2.machineState.stack = ⟨0⟩ :: v :: ret :: R := by rw [hs2]; simp only [stPush0, hk1]
      have st2 := dup2_xstep hc2 hp2 (by decide) hk2 (by first | (simp only [List.length_cons]; omega) | omega)
      by_cases g2 : g.toNat < C + 6
      · exact Or.inl (hX2.trans (stepOOG (k := k+2) (C := C+3) hg2 st2 (by omega) (by omega) (by omega)))
      · set s3 := stSwap s2 (v :: ⟨0⟩ :: v :: ret :: R) with hs3
        have hX3 := hX2.trans (stepContinue (k := k+2) (C := C+3) hg2 st2 (by omega) (by omega))
        have hc3 : s3.executionEnv.code = powBytecode := by rw [hs3]; simp only [stSwap]; exact hc2
        have hp3 : s3.machineState.pc = ⟨159⟩ := by rw [hs3]; simp only [stSwap]; rw [hp2]; rfl
        have hg3 : s3.machineState.gasAvailable.toNat = g.toNat - (C + 6) := by
          rw [hs3]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
        have hk3 : s3.machineState.stack = v :: ⟨0⟩ :: v :: ret :: R := by rw [hs3]; simp only [stSwap]
        have st3 := swap1_xstep hc3 hp3 (by decide) hk3 (by first | (simp only [List.length_cons]; omega) | omega)
        by_cases g3 : g.toNat < C + 9
        · exact Or.inl (hX3.trans (stepOOG (k := k+3) (C := C+6) hg3 st3 (by omega) (by omega) (by omega)))
        · set s4 := stSwap s3 (⟨0⟩ :: v :: v :: ret :: R) with hs4
          have hX4 := hX3.trans (stepContinue (k := k+3) (C := C+6) hg3 st3 (by omega) (by omega))
          have hc4 : s4.executionEnv.code = powBytecode := by rw [hs4]; simp only [stSwap]; exact hc3
          have hp4 : s4.machineState.pc = ⟨160⟩ := by rw [hs4]; simp only [stSwap]; rw [hp3]; rfl
          have hg4 : s4.machineState.gasAvailable.toNat = g.toNat - (C + 9) := by
            rw [hs4]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
          have hk4 : s4.machineState.stack = ⟨0⟩ :: v :: v :: ret :: R := by rw [hs4]; simp only [stSwap]
          have st4 := pop_xstep hc4 hp4 (by decide) hk4 (by first | (simp only [List.length_cons]; omega) | omega)
          by_cases g4 : g.toNat < C + 11
          · exact Or.inl (hX4.trans (stepOOG (k := k+4) (C := C+9) hg4 st4 (by omega) (by omega) (by omega)))
          · set s5 := stPop s4 (v :: v :: ret :: R) with hs5
            have hX5 := hX4.trans (stepContinue (k := k+4) (C := C+9) hg4 st4 (by omega) (by omega))
            have hc5 : s5.executionEnv.code = powBytecode := by rw [hs5]; simp only [stPop]; exact hc4
            have hp5 : s5.machineState.pc = ⟨161⟩ := by rw [hs5]; simp only [stPop]; rw [hp4]; rfl
            have hg5 : s5.machineState.gasAvailable.toNat = g.toNat - (C + 11) := by
              rw [hs5]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
            have hk5 : s5.machineState.stack = v :: v :: ret :: R := by rw [hs5]; simp only [stPop]
            have st5 := swap2_xstep hc5 hp5 (by decide) hk5 (by omega)
            by_cases g5 : g.toNat < C + 14
            · exact Or.inl (hX5.trans (stepOOG (k := k+5) (C := C+11) hg5 st5 (by omega) (by omega) (by omega)))
            · set s6 := stSwap s5 (ret :: v :: v :: R) with hs6
              have hX6 := hX5.trans (stepContinue (k := k+5) (C := C+11) hg5 st5 (by omega) (by omega))
              have hc6 : s6.executionEnv.code = powBytecode := by rw [hs6]; simp only [stSwap]; exact hc5
              have hp6 : s6.machineState.pc = ⟨162⟩ := by rw [hs6]; simp only [stSwap]; rw [hp5]; rfl
              have hg6 : s6.machineState.gasAvailable.toNat = g.toNat - (C + 14) := by
                rw [hs6]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
              have hk6 : s6.machineState.stack = ret :: v :: v :: R := by rw [hs6]; simp only [stSwap]
              have st6 := swap1_xstep hc6 hp6 (by decide) hk6 (by first | (simp only [List.length_cons]; omega) | omega)
              by_cases g6 : g.toNat < C + 17
              · exact Or.inl (hX6.trans (stepOOG (k := k+6) (C := C+14) hg6 st6 (by omega) (by omega) (by omega)))
              · set s7 := stSwap s6 (v :: ret :: v :: R) with hs7
                have hX7 := hX6.trans (stepContinue (k := k+6) (C := C+14) hg6 st6 (by omega) (by omega))
                have hc7 : s7.executionEnv.code = powBytecode := by rw [hs7]; simp only [stSwap]; exact hc6
                have hp7 : s7.machineState.pc = ⟨163⟩ := by rw [hs7]; simp only [stSwap]; rw [hp6]; rfl
                have hg7 : s7.machineState.gasAvailable.toNat = g.toNat - (C + 17) := by
                  rw [hs7]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                have hk7 : s7.machineState.stack = v :: ret :: v :: R := by rw [hs7]; simp only [stSwap]
                have st7 := pop_xstep hc7 hp7 (by decide) hk7 (by first | (simp only [List.length_cons]; omega) | omega)
                by_cases g7 : g.toNat < C + 19
                · exact Or.inl (hX7.trans (stepOOG (k := k+7) (C := C+17) hg7 st7 (by omega) (by omega) (by omega)))
                · set s8 := stPop s7 (ret :: v :: R) with hs8
                  have hX8 := hX7.trans (stepContinue (k := k+7) (C := C+17) hg7 st7 (by omega) (by omega))
                  have hc8 : s8.executionEnv.code = powBytecode := by rw [hs8]; simp only [stPop]; exact hc7
                  have hp8 : s8.machineState.pc = ⟨164⟩ := by rw [hs8]; simp only [stPop]; rw [hp7]; rfl
                  have hg8 : s8.machineState.gasAvailable.toNat = g.toNat - (C + 19) := by
                    rw [hs8]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                  have hk8 : s8.machineState.stack = ret :: v :: R := by rw [hs8]; simp only [stPop]
                  have st8 := jump_xstep hc8 hp8 (by decide) hk8 hret (by first | (simp only [List.length_cons]; omega) | omega)
                  by_cases g8 : g.toNat < C + 27
                  · exact Or.inl (hX8.trans (stepOOG (k := k+8) (C := C+19) (cost := 8) hg8 st8 (by omega) (by omega) (by omega)))
                  · set s9 := stJump s8 ret (v :: R) with hs9
                    have hX9 := hX8.trans (stepContinue (k := k+8) (C := C+19) (cost := 8) hg8 st8 (by omega) (by omega))
                    refine Or.inr ⟨k+9, C+27, s9, ?_, ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_⟩
                    · have he : g.toNat + 1 - (k + 8 + 1) = g.toNat + 1 - (k + 9) := by omega
                      rw [← he]; exact hX9
                    · rw [hs9]; simp only [stJump]; exact hc8
                    · rw [hs9]; simp only [stJump]
                    · rw [hs9]; simp only [stJump]
                    · rw [hs9]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                    · rw [hs9]; simp only [stJump]
                      rw [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
                      simp only [stPop, stSwap, stPush0, stJumpdest]
                    · rw [hs9]; simp only [stJump]
                      rw [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
                      simp only [stPop, stSwap, stPush0, stJumpdest]

/-- solc routine `0xa5` (`abi_decode`'s validator): entry at pc 165 with `[arg, ret, …R]`, calls
    `0x9c` to clean `arg`, checks `arg == cleanup(arg)` (always true for uint256, so no revert),
    and returns to `ret` leaving `[…R]` (the caller keeps its own copy of the value).  Calls
    `powRoutine_9c` internally; gas is symbolic across the call. -/
theorem powRoutine_a5 {g : UInt256} {s0 s : State} {k C : ℕ} {arg ret : UInt256} {R : List UInt256}
    (hcode : s.executionEnv.code = powBytecode) (hpc : s.machineState.pc = ⟨165⟩)
    (hstk : s.machineState.stack = arg :: ret :: R)
    (hret : (D_J powBytecode ⟨0⟩).contains ret = true) (hov : R.length + 6 ≤ 1024)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ (k' C' : ℕ) (s' : State),
          X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k') (D_J powBytecode ⟨0⟩) s'
        ∧ s'.executionEnv.code = powBytecode ∧ s'.machineState.pc = ret
        ∧ s'.machineState.stack = R
        ∧ s'.machineState.gasAvailable.toNat = g.toNat - C' ∧ k' ≤ C' ∧ C' ≤ g.toNat
        ∧ s'.machineState.memory = s.machineState.memory
        ∧ s'.machineState.activeWords = s.machineState.activeWords := by
  -- 0xa5..0xad: set up the call to 0x9c (target 156, return 174)
  have st0 := jumpdest_xstep hcode hpc (by decide) (by rw [hstk]; simp only [List.length_cons]; omega)
  by_cases g0 : g.toNat < C + 1
  · exact Or.inl (hX.trans (stepOOG hgas st0 hk hC (by omega)))
  · set s1 := stJumpdest s with hs1
    have hX1 := hX.trans (stepContinue (k := k) (C := C) hgas st0 hk (by omega))
    have hc1 : s1.executionEnv.code = powBytecode := by rw [hs1]; simp only [stJumpdest]; exact hcode
    have hp1 : s1.machineState.pc = ⟨166⟩ := by rw [hs1]; simp only [stJumpdest]; rw [hpc]; rfl
    have hg1 : s1.machineState.gasAvailable.toNat = g.toNat - (C + 1) := by
      rw [hs1]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
    have hk1 : s1.machineState.stack = arg :: ret :: R := by rw [hs1]; simp only [stJumpdest]; exact hstk
    have st1 := push2_xstep (argv := ⟨174⟩) hc1 hp1 (by decide) hk1 (by first | (simp only [List.length_cons]; omega) | omega)
    by_cases g1 : g.toNat < C + 4
    · exact Or.inl (hX1.trans (stepOOG (k := k+1) (C := C+1) hg1 st1 (by omega) (by omega) (by omega)))
    · set s2 := stPush2 s1 ⟨174⟩ with hs2
      have hX2 := hX1.trans (stepContinue (k := k+1) (C := C+1) hg1 st1 (by omega) (by omega))
      have hc2 : s2.executionEnv.code = powBytecode := by rw [hs2]; simp only [stPush2]; exact hc1
      have hp2 : s2.machineState.pc = ⟨169⟩ := by rw [hs2]; simp only [stPush2]; rw [hp1]; rfl
      have hg2 : s2.machineState.gasAvailable.toNat = g.toNat - (C + 4) := by
        rw [hs2]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
      have hk2 : s2.machineState.stack = ⟨174⟩ :: arg :: ret :: R := by rw [hs2]; simp only [stPush2, hk1]
      have st2 := dup2_xstep hc2 hp2 (by decide) hk2 (by first | (simp only [List.length_cons]; omega) | omega)
      by_cases g2 : g.toNat < C + 7
      · exact Or.inl (hX2.trans (stepOOG (k := k+2) (C := C+4) hg2 st2 (by omega) (by omega) (by omega)))
      · set s3 := stSwap s2 (arg :: ⟨174⟩ :: arg :: ret :: R) with hs3
        have hX3 := hX2.trans (stepContinue (k := k+2) (C := C+4) hg2 st2 (by omega) (by omega))
        have hc3 : s3.executionEnv.code = powBytecode := by rw [hs3]; simp only [stSwap]; exact hc2
        have hp3 : s3.machineState.pc = ⟨170⟩ := by rw [hs3]; simp only [stSwap]; rw [hp2]; rfl
        have hg3 : s3.machineState.gasAvailable.toNat = g.toNat - (C + 7) := by
          rw [hs3]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
        have hk3 : s3.machineState.stack = arg :: ⟨174⟩ :: arg :: ret :: R := by rw [hs3]; simp only [stSwap]
        have st3 := push2_xstep (argv := ⟨156⟩) hc3 hp3 (by decide) hk3 (by first | (simp only [List.length_cons]; omega) | omega)
        by_cases g3 : g.toNat < C + 10
        · exact Or.inl (hX3.trans (stepOOG (k := k+3) (C := C+7) hg3 st3 (by omega) (by omega) (by omega)))
        · set s4 := stPush2 s3 ⟨156⟩ with hs4
          have hX4 := hX3.trans (stepContinue (k := k+3) (C := C+7) hg3 st3 (by omega) (by omega))
          have hc4 : s4.executionEnv.code = powBytecode := by rw [hs4]; simp only [stPush2]; exact hc3
          have hp4 : s4.machineState.pc = ⟨173⟩ := by rw [hs4]; simp only [stPush2]; rw [hp3]; rfl
          have hg4 : s4.machineState.gasAvailable.toNat = g.toNat - (C + 10) := by
            rw [hs4]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
          have hk4 : s4.machineState.stack = ⟨156⟩ :: arg :: ⟨174⟩ :: arg :: ret :: R := by
            rw [hs4]; simp only [stPush2, hk3]
          have st4 := jump_xstep hc4 hp4 (by decide) hk4
            (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by first | (simp only [List.length_cons]; omega) | omega)
          by_cases g4 : g.toNat < C + 18
          · exact Or.inl (hX4.trans (stepOOG (k := k+4) (C := C+10) (cost := 8) hg4 st4 (by omega) (by omega) (by omega)))
          · set s5 := stJump s4 ⟨156⟩ (arg :: ⟨174⟩ :: arg :: ret :: R) with hs5
            have hX5 := hX4.trans (stepContinue (k := k+4) (C := C+10) (cost := 8) hg4 st4 (by omega) (by omega))
            have hc5 : s5.executionEnv.code = powBytecode := by rw [hs5]; simp only [stJump]; exact hc4
            have hp5 : s5.machineState.pc = ⟨156⟩ := by rw [hs5]; simp only [stJump]
            have hg5 : s5.machineState.gasAvailable.toNat = g.toNat - (C + 18) := by
              rw [hs5]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
            have hk5 : s5.machineState.stack = arg :: ⟨174⟩ :: arg :: ret :: R := by rw [hs5]; simp only [stJump]
            have hmem5 : s5.machineState.memory = s.machineState.memory := by
              rw [hs5]; simp only [stJump]; rw [hs4, hs3, hs2, hs1]; simp only [stPush2, stSwap, stJumpdest]
            have haw5 : s5.machineState.activeWords = s.machineState.activeWords := by
              rw [hs5]; simp only [stJump]; rw [hs4, hs3, hs2, hs1]; simp only [stPush2, stSwap, stJumpdest]
            -- call 0x9c: cleans `arg`, returns to 174 with [arg, arg, ret, R]
            rcases powRoutine_9c (v := arg) (ret := ⟨174⟩) (R := arg :: ret :: R)
                hc5 hp5 hk5 (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
                (by first | (simp only [List.length_cons]; omega) | omega) hg5 (by omega) (by omega) hX5
              with hoog | ⟨k9, C9, s9, hX9, hc9, hp9, hk9, hg9, hkC9, hCg9, hm9, ha9⟩
            · exact Or.inl hoog
            -- 0xae..0xba: EQ check (always passes), POP, return to `ret`
            have st9 := jumpdest_xstep hc9 hp9 (by decide) (by rw [hk9]; simp only [List.length_cons]; omega)
            by_cases g9 : g.toNat < C9 + 1
            · exact Or.inl (hX9.trans (stepOOG hg9 st9 hkC9 hCg9 (by omega)))
            · set s10 := stJumpdest s9 with hs10
              have hX10 := hX9.trans (stepContinue (k := k9) (C := C9) hg9 st9 hkC9 (by omega))
              have hc10 : s10.executionEnv.code = powBytecode := by rw [hs10]; simp only [stJumpdest]; exact hc9
              have hp10 : s10.machineState.pc = ⟨175⟩ := by rw [hs10]; simp only [stJumpdest]; rw [hp9]; rfl
              have hg10 : s10.machineState.gasAvailable.toNat = g.toNat - (C9 + 1) := by
                rw [hs10]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
              have hk10 : s10.machineState.stack = arg :: arg :: ret :: R := by rw [hs10]; simp only [stJumpdest]; exact hk9
              have st10 := dup2_xstep hc10 hp10 (by decide) hk10 (by first | (simp only [List.length_cons]; omega) | omega)
              by_cases g10 : g.toNat < C9 + 4
              · exact Or.inl (hX10.trans (stepOOG (k := k9+1) (C := C9+1) hg10 st10 (by omega) (by omega) (by omega)))
              · set s11 := stSwap s10 (arg :: arg :: arg :: ret :: R) with hs11
                have hX11 := hX10.trans (stepContinue (k := k9+1) (C := C9+1) hg10 st10 (by omega) (by omega))
                have hc11 : s11.executionEnv.code = powBytecode := by rw [hs11]; simp only [stSwap]; exact hc10
                have hp11 : s11.machineState.pc = ⟨176⟩ := by rw [hs11]; simp only [stSwap]; rw [hp10]; rfl
                have hg11 : s11.machineState.gasAvailable.toNat = g.toNat - (C9 + 4) := by
                  rw [hs11]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                have hk11 : s11.machineState.stack = arg :: arg :: arg :: ret :: R := by rw [hs11]; simp only [stSwap]
                have st11 := eq_xstep hc11 hp11 (by decide) hk11 (by first | (simp only [List.length_cons]; omega) | omega)
                by_cases g11 : g.toNat < C9 + 7
                · exact Or.inl (hX11.trans (stepOOG (k := k9+2) (C := C9+4) hg11 st11 (by omega) (by omega) (by omega)))
                · set s12 := stBinop s11 (UInt256.eq arg arg) (arg :: ret :: R) with hs12
                  have hX12 := hX11.trans (stepContinue (k := k9+2) (C := C9+4) hg11 st11 (by omega) (by omega))
                  have hc12 : s12.executionEnv.code = powBytecode := by rw [hs12]; simp only [stBinop]; exact hc11
                  have hp12 : s12.machineState.pc = ⟨177⟩ := by rw [hs12]; simp only [stBinop]; rw [hp11]; rfl
                  have hg12 : s12.machineState.gasAvailable.toNat = g.toNat - (C9 + 7) := by
                    rw [hs12]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                  have hk12 : s12.machineState.stack = ⟨1⟩ :: arg :: ret :: R := by
                    rw [hs12]; simp only [stBinop]; rw [u256_eq_refl]
                  have st12 := push2_xstep (argv := ⟨184⟩) hc12 hp12 (by decide) hk12 (by first | (simp only [List.length_cons]; omega) | omega)
                  by_cases g12 : g.toNat < C9 + 10
                  · exact Or.inl (hX12.trans (stepOOG (k := k9+3) (C := C9+7) hg12 st12 (by omega) (by omega) (by omega)))
                  · set s13 := stPush2 s12 ⟨184⟩ with hs13
                    have hX13 := hX12.trans (stepContinue (k := k9+3) (C := C9+7) hg12 st12 (by omega) (by omega))
                    have hc13 : s13.executionEnv.code = powBytecode := by rw [hs13]; simp only [stPush2]; exact hc12
                    have hp13 : s13.machineState.pc = ⟨180⟩ := by rw [hs13]; simp only [stPush2]; rw [hp12]; rfl
                    have hg13 : s13.machineState.gasAvailable.toNat = g.toNat - (C9 + 10) := by
                      rw [hs13]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                    have hk13 : s13.machineState.stack = ⟨184⟩ :: ⟨1⟩ :: arg :: ret :: R := by rw [hs13]; simp only [stPush2, hk12]
                    have st13 := jumpi_t_xstep hc13 hp13 (by decide) hk13 (by decide)
                      (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by first | (simp only [List.length_cons]; omega) | omega)
                    by_cases g13 : g.toNat < C9 + 20
                    · exact Or.inl (hX13.trans (stepOOG (k := k9+4) (C := C9+10) (cost := 10) hg13 st13 (by omega) (by omega) (by omega)))
                    · set s14 := stJumpiT s13 ⟨184⟩ (arg :: ret :: R) with hs14
                      have hX14 := hX13.trans (stepContinue (k := k9+4) (C := C9+10) (cost := 10) hg13 st13 (by omega) (by omega))
                      have hc14 : s14.executionEnv.code = powBytecode := by rw [hs14]; simp only [stJumpiT]; exact hc13
                      have hp14 : s14.machineState.pc = ⟨184⟩ := by rw [hs14]; simp only [stJumpiT]
                      have hg14 : s14.machineState.gasAvailable.toNat = g.toNat - (C9 + 20) := by
                        rw [hs14]; simp only [stJumpiT]; rw [toNat_sub_ofNat (by omega)]; omega
                      have hk14 : s14.machineState.stack = arg :: ret :: R := by rw [hs14]; simp only [stJumpiT]
                      have st14 := jumpdest_xstep hc14 hp14 (by decide) (by rw [hk14]; simp only [List.length_cons]; omega)
                      by_cases g14 : g.toNat < C9 + 21
                      · exact Or.inl (hX14.trans (stepOOG (k := k9+5) (C := C9+20) hg14 st14 (by omega) (by omega) (by omega)))
                      · set s15 := stJumpdest s14 with hs15
                        have hX15 := hX14.trans (stepContinue (k := k9+5) (C := C9+20) hg14 st14 (by omega) (by omega))
                        have hc15 : s15.executionEnv.code = powBytecode := by rw [hs15]; simp only [stJumpdest]; exact hc14
                        have hp15 : s15.machineState.pc = ⟨185⟩ := by rw [hs15]; simp only [stJumpdest]; rw [hp14]; rfl
                        have hg15 : s15.machineState.gasAvailable.toNat = g.toNat - (C9 + 21) := by
                          rw [hs15]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                        have hk15 : s15.machineState.stack = arg :: ret :: R := by rw [hs15]; simp only [stJumpdest]; exact hk14
                        have st15 := pop_xstep hc15 hp15 (by decide) hk15 (by first | (simp only [List.length_cons]; omega) | omega)
                        by_cases g15 : g.toNat < C9 + 23
                        · exact Or.inl (hX15.trans (stepOOG (k := k9+6) (C := C9+21) hg15 st15 (by omega) (by omega) (by omega)))
                        · set s16 := stPop s15 (ret :: R) with hs16
                          have hX16 := hX15.trans (stepContinue (k := k9+6) (C := C9+21) hg15 st15 (by omega) (by omega))
                          have hc16 : s16.executionEnv.code = powBytecode := by rw [hs16]; simp only [stPop]; exact hc15
                          have hp16 : s16.machineState.pc = ⟨186⟩ := by rw [hs16]; simp only [stPop]; rw [hp15]; rfl
                          have hg16 : s16.machineState.gasAvailable.toNat = g.toNat - (C9 + 23) := by
                            rw [hs16]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                          have hk16 : s16.machineState.stack = ret :: R := by rw [hs16]; simp only [stPop]
                          have st16 := jump_xstep hc16 hp16 (by decide) hk16 hret (by omega)
                          by_cases g16 : g.toNat < C9 + 31
                          · exact Or.inl (hX16.trans (stepOOG (k := k9+7) (C := C9+23) (cost := 8) hg16 st16 (by omega) (by omega) (by omega)))
                          · set s17 := stJump s16 ret R with hs17
                            have hX17 := hX16.trans (stepContinue (k := k9+7) (C := C9+23) (cost := 8) hg16 st16 (by omega) (by omega))
                            refine Or.inr ⟨k9+8, C9+31, s17, ?_, ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_⟩
                            · have he : g.toNat + 1 - (k9 + 7 + 1) = g.toNat + 1 - (k9 + 8) := by omega
                              rw [← he]; exact hX17
                            · rw [hs17]; simp only [stJump]; exact hc16
                            · rw [hs17]; simp only [stJump]
                            · rw [hs17]; simp only [stJump]
                            · rw [hs17]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                            · rw [hs17]; simp only [stJump]
                              rw [hs16, hs15, hs14, hs13, hs12, hs11, hs10]
                              simp only [stPop, stJumpdest, stJumpiT, stPush2, stBinop, stSwap]
                              rw [hm9, hmem5]
                            · rw [hs17]; simp only [stJump]
                              rw [hs16, hs15, hs14, hs13, hs12, hs11, hs10]
                              simp only [stPop, stJumpdest, stJumpiT, stPush2, stBinop, stSwap]
                              rw [ha9, haw5]

/-- solc routine `0xbb` (`abi_decode_uint256`): entry at pc 187 with `[offset, end, ret, …R]`,
    loads the 32-byte word `calldata[offset]`, validates it via `0xa5`, and returns it to `ret`
    leaving `[calldata[offset], …R]`.  Needs `hee : executionEnv = I` for the load. -/
theorem powRoutine_bb {g : UInt256} {s0 s : State} {I : Ethereum.ExecutionEnv} {k C : ℕ}
    {offset ennd ret : UInt256} {R : List UInt256}
    (hcode : s.executionEnv.code = powBytecode) (hee : s.executionEnv = I)
    (hpc : s.machineState.pc = ⟨187⟩)
    (hstk : s.machineState.stack = offset :: ennd :: ret :: R)
    (hret : (D_J powBytecode ⟨0⟩).contains ret = true) (hov : R.length + 10 ≤ 1024)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ (k' C' : ℕ) (s' : State),
          X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k') (D_J powBytecode ⟨0⟩) s'
        ∧ s'.executionEnv.code = powBytecode ∧ s'.machineState.pc = ret
        ∧ s'.machineState.stack
            = uInt256OfByteArray (I.calldata.readBytes offset.toNat 32) :: R
        ∧ s'.machineState.gasAvailable.toNat = g.toNat - C' ∧ k' ≤ C' ∧ C' ≤ g.toNat
        ∧ s'.machineState.memory = s.machineState.memory
        ∧ s'.machineState.activeWords = s.machineState.activeWords := by
  have st0 := jumpdest_xstep hcode hpc (by decide) (by rw [hstk]; simp only [List.length_cons]; omega)
  by_cases g0 : g.toNat < C + 1
  · exact Or.inl (hX.trans (stepOOG hgas st0 hk hC (by omega)))
  · set s1 := stJumpdest s with hs1
    have hX1 := hX.trans (stepContinue (k := k) (C := C) hgas st0 hk (by omega))
    have hc1 : s1.executionEnv.code = powBytecode := by rw [hs1]; simp only [stJumpdest]; exact hcode
    have he1 : s1.executionEnv = I := by rw [hs1]; simp only [stJumpdest]; exact hee
    have hp1 : s1.machineState.pc = ⟨188⟩ := by rw [hs1]; simp only [stJumpdest]; rw [hpc]; rfl
    have hg1 : s1.machineState.gasAvailable.toNat = g.toNat - (C + 1) := by
      rw [hs1]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
    have hk1 : s1.machineState.stack = offset :: ennd :: ret :: R := by rw [hs1]; simp only [stJumpdest]; exact hstk
    have st1 := push0_xstep hc1 hp1 (by decide) hk1 (by first | (simp only [List.length_cons]; omega) | omega)
    by_cases g1 : g.toNat < C + 3
    · exact Or.inl (hX1.trans (stepOOG (k := k+1) (C := C+1) hg1 st1 (by omega) (by omega) (by omega)))
    · set s2 := stPush0 s1 with hs2
      have hX2 := hX1.trans (stepContinue (k := k+1) (C := C+1) hg1 st1 (by omega) (by omega))
      have hc2 : s2.executionEnv.code = powBytecode := by rw [hs2]; simp only [stPush0]; exact hc1
      have he2 : s2.executionEnv = I := by rw [hs2]; simp only [stPush0]; exact he1
      have hp2 : s2.machineState.pc = ⟨189⟩ := by rw [hs2]; simp only [stPush0]; rw [hp1]; rfl
      have hg2 : s2.machineState.gasAvailable.toNat = g.toNat - (C + 3) := by
        rw [hs2]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
      have hk2 : s2.machineState.stack = ⟨0⟩ :: offset :: ennd :: ret :: R := by rw [hs2]; simp only [stPush0, hk1]
      have st2 := dup2_xstep hc2 hp2 (by decide) hk2 (by first | (simp only [List.length_cons]; omega) | omega)
      by_cases g2 : g.toNat < C + 6
      · exact Or.inl (hX2.trans (stepOOG (k := k+2) (C := C+3) hg2 st2 (by omega) (by omega) (by omega)))
      · set s3 := stSwap s2 (offset :: ⟨0⟩ :: offset :: ennd :: ret :: R) with hs3
        have hX3 := hX2.trans (stepContinue (k := k+2) (C := C+3) hg2 st2 (by omega) (by omega))
        have hc3 : s3.executionEnv.code = powBytecode := by rw [hs3]; simp only [stSwap]; exact hc2
        have he3 : s3.executionEnv = I := by rw [hs3]; simp only [stSwap]; exact he2
        have hp3 : s3.machineState.pc = ⟨190⟩ := by rw [hs3]; simp only [stSwap]; rw [hp2]; rfl
        have hg3 : s3.machineState.gasAvailable.toNat = g.toNat - (C + 6) := by
          rw [hs3]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
        have hk3 : s3.machineState.stack = offset :: ⟨0⟩ :: offset :: ennd :: ret :: R := by rw [hs3]; simp only [stSwap]
        have st3 := calldataload_xstep hc3 hp3 (by decide) hk3 (by first | (simp only [List.length_cons]; omega) | omega)
        by_cases g3 : g.toNat < C + 9
        · exact Or.inl (hX3.trans (stepOOG (k := k+3) (C := C+6) hg3 st3 (by omega) (by omega) (by omega)))
        · set s4 := stCalldataload s3 offset (⟨0⟩ :: offset :: ennd :: ret :: R) with hs4
          have hX4 := hX3.trans (stepContinue (k := k+3) (C := C+6) hg3 st3 (by omega) (by omega))
          have hc4 : s4.executionEnv.code = powBytecode := by rw [hs4]; simp only [stCalldataload]; exact hc3
          have hp4 : s4.machineState.pc = ⟨191⟩ := by rw [hs4]; simp only [stCalldataload]; rw [hp3]; rfl
          have hg4 : s4.machineState.gasAvailable.toNat = g.toNat - (C + 9) := by
            rw [hs4]; simp only [stCalldataload]; rw [toNat_sub_ofNat (by omega)]; omega
          have hk4 : s4.machineState.stack
              = uInt256OfByteArray (I.calldata.readBytes offset.toNat 32) :: ⟨0⟩ :: offset :: ennd :: ret :: R := by
            rw [hs4]; simp only [stCalldataload, he3]
          set val := uInt256OfByteArray (I.calldata.readBytes offset.toNat 32) with hvaldef
          have st4 := swap1_xstep hc4 hp4 (by decide) hk4 (by first | (simp only [List.length_cons]; omega) | omega)
          by_cases g4 : g.toNat < C + 12
          · exact Or.inl (hX4.trans (stepOOG (k := k+4) (C := C+9) hg4 st4 (by omega) (by omega) (by omega)))
          · set s5 := stSwap s4 (⟨0⟩ :: val :: offset :: ennd :: ret :: R) with hs5
            have hX5 := hX4.trans (stepContinue (k := k+4) (C := C+9) hg4 st4 (by omega) (by omega))
            have hc5 : s5.executionEnv.code = powBytecode := by rw [hs5]; simp only [stSwap]; exact hc4
            have hp5 : s5.machineState.pc = ⟨192⟩ := by rw [hs5]; simp only [stSwap]; rw [hp4]; rfl
            have hg5 : s5.machineState.gasAvailable.toNat = g.toNat - (C + 12) := by
              rw [hs5]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
            have hk5 : s5.machineState.stack = ⟨0⟩ :: val :: offset :: ennd :: ret :: R := by rw [hs5]; simp only [stSwap]
            have st5 := pop_xstep hc5 hp5 (by decide) hk5 (by first | (simp only [List.length_cons]; omega) | omega)
            by_cases g5 : g.toNat < C + 14
            · exact Or.inl (hX5.trans (stepOOG (k := k+5) (C := C+12) hg5 st5 (by omega) (by omega) (by omega)))
            · set s6 := stPop s5 (val :: offset :: ennd :: ret :: R) with hs6
              have hX6 := hX5.trans (stepContinue (k := k+5) (C := C+12) hg5 st5 (by omega) (by omega))
              have hc6 : s6.executionEnv.code = powBytecode := by rw [hs6]; simp only [stPop]; exact hc5
              have hp6 : s6.machineState.pc = ⟨193⟩ := by rw [hs6]; simp only [stPop]; rw [hp5]; rfl
              have hg6 : s6.machineState.gasAvailable.toNat = g.toNat - (C + 14) := by
                rw [hs6]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
              have hk6 : s6.machineState.stack = val :: offset :: ennd :: ret :: R := by rw [hs6]; simp only [stPop]
              have st6 := push2_xstep (argv := ⟨201⟩) hc6 hp6 (by decide) hk6 (by first | (simp only [List.length_cons]; omega) | omega)
              by_cases g6 : g.toNat < C + 17
              · exact Or.inl (hX6.trans (stepOOG (k := k+6) (C := C+14) hg6 st6 (by omega) (by omega) (by omega)))
              · set s7 := stPush2 s6 ⟨201⟩ with hs7
                have hX7 := hX6.trans (stepContinue (k := k+6) (C := C+14) hg6 st6 (by omega) (by omega))
                have hc7 : s7.executionEnv.code = powBytecode := by rw [hs7]; simp only [stPush2]; exact hc6
                have hp7 : s7.machineState.pc = ⟨196⟩ := by rw [hs7]; simp only [stPush2]; rw [hp6]; rfl
                have hg7 : s7.machineState.gasAvailable.toNat = g.toNat - (C + 17) := by
                  rw [hs7]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                have hk7 : s7.machineState.stack = ⟨201⟩ :: val :: offset :: ennd :: ret :: R := by rw [hs7]; simp only [stPush2, hk6]
                have st7 := dup2_xstep hc7 hp7 (by decide) hk7 (by first | (simp only [List.length_cons]; omega) | omega)
                by_cases g7 : g.toNat < C + 20
                · exact Or.inl (hX7.trans (stepOOG (k := k+7) (C := C+17) hg7 st7 (by omega) (by omega) (by omega)))
                · set s8 := stSwap s7 (val :: ⟨201⟩ :: val :: offset :: ennd :: ret :: R) with hs8
                  have hX8 := hX7.trans (stepContinue (k := k+7) (C := C+17) hg7 st7 (by omega) (by omega))
                  have hc8 : s8.executionEnv.code = powBytecode := by rw [hs8]; simp only [stSwap]; exact hc7
                  have hp8 : s8.machineState.pc = ⟨197⟩ := by rw [hs8]; simp only [stSwap]; rw [hp7]; rfl
                  have hg8 : s8.machineState.gasAvailable.toNat = g.toNat - (C + 20) := by
                    rw [hs8]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                  have hk8 : s8.machineState.stack = val :: ⟨201⟩ :: val :: offset :: ennd :: ret :: R := by rw [hs8]; simp only [stSwap]
                  have st8 := push2_xstep (argv := ⟨165⟩) hc8 hp8 (by decide) hk8 (by first | (simp only [List.length_cons]; omega) | omega)
                  by_cases g8 : g.toNat < C + 23
                  · exact Or.inl (hX8.trans (stepOOG (k := k+8) (C := C+20) hg8 st8 (by omega) (by omega) (by omega)))
                  · set s9 := stPush2 s8 ⟨165⟩ with hs9
                    have hX9 := hX8.trans (stepContinue (k := k+8) (C := C+20) hg8 st8 (by omega) (by omega))
                    have hc9 : s9.executionEnv.code = powBytecode := by rw [hs9]; simp only [stPush2]; exact hc8
                    have hp9 : s9.machineState.pc = ⟨200⟩ := by rw [hs9]; simp only [stPush2]; rw [hp8]; rfl
                    have hg9 : s9.machineState.gasAvailable.toNat = g.toNat - (C + 23) := by
                      rw [hs9]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                    have hk9 : s9.machineState.stack = ⟨165⟩ :: val :: ⟨201⟩ :: val :: offset :: ennd :: ret :: R := by rw [hs9]; simp only [stPush2, hk8]
                    have st9 := jump_xstep hc9 hp9 (by decide) hk9
                      (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by first | (simp only [List.length_cons]; omega) | omega)
                    by_cases g9 : g.toNat < C + 31
                    · exact Or.inl (hX9.trans (stepOOG (k := k+9) (C := C+23) (cost := 8) hg9 st9 (by omega) (by omega) (by omega)))
                    · set s10 := stJump s9 ⟨165⟩ (val :: ⟨201⟩ :: val :: offset :: ennd :: ret :: R) with hs10
                      have hX10 := hX9.trans (stepContinue (k := k+9) (C := C+23) (cost := 8) hg9 st9 (by omega) (by omega))
                      have hc10 : s10.executionEnv.code = powBytecode := by rw [hs10]; simp only [stJump]; exact hc9
                      have hp10 : s10.machineState.pc = ⟨165⟩ := by rw [hs10]; simp only [stJump]
                      have hg10 : s10.machineState.gasAvailable.toNat = g.toNat - (C + 31) := by
                        rw [hs10]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                      have hk10 : s10.machineState.stack = val :: ⟨201⟩ :: val :: offset :: ennd :: ret :: R := by rw [hs10]; simp only [stJump]
                      have hmem10 : s10.machineState.memory = s.machineState.memory := by
                        rw [hs10]; simp only [stJump]; rw [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
                        simp only [stPush2, stSwap, stPop, stCalldataload, stPush0, stJumpdest]
                      have haw10 : s10.machineState.activeWords = s.machineState.activeWords := by
                        rw [hs10]; simp only [stJump]; rw [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
                        simp only [stPush2, stSwap, stPop, stCalldataload, stPush0, stJumpdest]
                      -- call 0xa5 (validator); returns to 201 with [val, offset, ennd, ret, R]
                      rcases powRoutine_a5 (arg := val) (ret := ⟨201⟩) (R := val :: offset :: ennd :: ret :: R)
                          hc10 hp10 hk10 (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
                          (by first | (simp only [List.length_cons]; omega) | omega) hg10 (by omega) (by omega) hX10
                        with hoog | ⟨ka, Ca, sa, hXa, hca, hpa, hka, hga, hkCa, hCga, hma, haa⟩
                      · exact Or.inl hoog
                      -- 0xc9..0xce: rearrange and return to `ret`
                      have sta := jumpdest_xstep hca hpa (by decide) (by rw [hka]; simp only [List.length_cons]; omega)
                      by_cases ga : g.toNat < Ca + 1
                      · exact Or.inl (hXa.trans (stepOOG hga sta hkCa hCga (by omega)))
                      · set s11 := stJumpdest sa with hs11
                        have hX11 := hXa.trans (stepContinue (k := ka) (C := Ca) hga sta hkCa (by omega))
                        have hc11 : s11.executionEnv.code = powBytecode := by rw [hs11]; simp only [stJumpdest]; exact hca
                        have hp11 : s11.machineState.pc = ⟨202⟩ := by rw [hs11]; simp only [stJumpdest]; rw [hpa]; rfl
                        have hg11 : s11.machineState.gasAvailable.toNat = g.toNat - (Ca + 1) := by
                          rw [hs11]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                        have hk11 : s11.machineState.stack = val :: offset :: ennd :: ret :: R := by
                          rw [hs11]; simp only [stJumpdest]; exact hka
                        have st11 := swap3_xstep hc11 hp11 (by decide) hk11 (by omega)
                        by_cases g11 : g.toNat < Ca + 4
                        · exact Or.inl (hX11.trans (stepOOG (k := ka+1) (C := Ca+1) hg11 st11 (by omega) (by omega) (by omega)))
                        · set s12 := stSwap s11 (ret :: offset :: ennd :: val :: R) with hs12
                          have hX12 := hX11.trans (stepContinue (k := ka+1) (C := Ca+1) hg11 st11 (by omega) (by omega))
                          have hc12 : s12.executionEnv.code = powBytecode := by rw [hs12]; simp only [stSwap]; exact hc11
                          have hp12 : s12.machineState.pc = ⟨203⟩ := by rw [hs12]; simp only [stSwap]; rw [hp11]; rfl
                          have hg12 : s12.machineState.gasAvailable.toNat = g.toNat - (Ca + 4) := by
                            rw [hs12]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                          have hk12 : s12.machineState.stack = ret :: offset :: ennd :: val :: R := by rw [hs12]; simp only [stSwap]
                          have st12 := swap2_xstep hc12 hp12 (by decide) hk12 (by first | (simp only [List.length_cons]; omega) | omega)
                          by_cases g12 : g.toNat < Ca + 7
                          · exact Or.inl (hX12.trans (stepOOG (k := ka+2) (C := Ca+4) hg12 st12 (by omega) (by omega) (by omega)))
                          · set s13 := stSwap s12 (ennd :: offset :: ret :: val :: R) with hs13
                            have hX13 := hX12.trans (stepContinue (k := ka+2) (C := Ca+4) hg12 st12 (by omega) (by omega))
                            have hc13 : s13.executionEnv.code = powBytecode := by rw [hs13]; simp only [stSwap]; exact hc12
                            have hp13 : s13.machineState.pc = ⟨204⟩ := by rw [hs13]; simp only [stSwap]; rw [hp12]; rfl
                            have hg13 : s13.machineState.gasAvailable.toNat = g.toNat - (Ca + 7) := by
                              rw [hs13]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                            have hk13 : s13.machineState.stack = ennd :: offset :: ret :: val :: R := by rw [hs13]; simp only [stSwap]
                            have st13 := pop_xstep hc13 hp13 (by decide) hk13 (by first | (simp only [List.length_cons]; omega) | omega)
                            by_cases g13 : g.toNat < Ca + 9
                            · exact Or.inl (hX13.trans (stepOOG (k := ka+3) (C := Ca+7) hg13 st13 (by omega) (by omega) (by omega)))
                            · set s14 := stPop s13 (offset :: ret :: val :: R) with hs14
                              have hX14 := hX13.trans (stepContinue (k := ka+3) (C := Ca+7) hg13 st13 (by omega) (by omega))
                              have hc14 : s14.executionEnv.code = powBytecode := by rw [hs14]; simp only [stPop]; exact hc13
                              have hp14 : s14.machineState.pc = ⟨205⟩ := by rw [hs14]; simp only [stPop]; rw [hp13]; rfl
                              have hg14 : s14.machineState.gasAvailable.toNat = g.toNat - (Ca + 9) := by
                                rw [hs14]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                              have hk14 : s14.machineState.stack = offset :: ret :: val :: R := by rw [hs14]; simp only [stPop]
                              have st14 := pop_xstep hc14 hp14 (by decide) hk14 (by first | (simp only [List.length_cons]; omega) | omega)
                              by_cases g14 : g.toNat < Ca + 11
                              · exact Or.inl (hX14.trans (stepOOG (k := ka+4) (C := Ca+9) hg14 st14 (by omega) (by omega) (by omega)))
                              · set s15 := stPop s14 (ret :: val :: R) with hs15
                                have hX15 := hX14.trans (stepContinue (k := ka+4) (C := Ca+9) hg14 st14 (by omega) (by omega))
                                have hc15 : s15.executionEnv.code = powBytecode := by rw [hs15]; simp only [stPop]; exact hc14
                                have hp15 : s15.machineState.pc = ⟨206⟩ := by rw [hs15]; simp only [stPop]; rw [hp14]; rfl
                                have hg15 : s15.machineState.gasAvailable.toNat = g.toNat - (Ca + 11) := by
                                  rw [hs15]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                have hk15 : s15.machineState.stack = ret :: val :: R := by rw [hs15]; simp only [stPop]
                                have st15 := jump_xstep hc15 hp15 (by decide) hk15 hret (by first | (simp only [List.length_cons]; omega) | omega)
                                by_cases g15 : g.toNat < Ca + 19
                                · exact Or.inl (hX15.trans (stepOOG (k := ka+5) (C := Ca+11) (cost := 8) hg15 st15 (by omega) (by omega) (by omega)))
                                · set s16 := stJump s15 ret (val :: R) with hs16
                                  have hX16 := hX15.trans (stepContinue (k := ka+5) (C := Ca+11) (cost := 8) hg15 st15 (by omega) (by omega))
                                  refine Or.inr ⟨ka+6, Ca+19, s16, ?_, ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_⟩
                                  · have he : g.toNat + 1 - (ka + 5 + 1) = g.toNat + 1 - (ka + 6) := by omega
                                    rw [← he]; exact hX16
                                  · rw [hs16]; simp only [stJump]; exact hc15
                                  · rw [hs16]; simp only [stJump]
                                  · rw [hs16]; simp only [stJump]
                                  · rw [hs16]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                  · rw [hs16]; simp only [stJump]
                                    rw [hs15, hs14, hs13, hs12, hs11]
                                    simp only [stPop, stSwap, stJumpdest]
                                    rw [hma, hmem10]
                                  · rw [hs16]; simp only [stJump]
                                    rw [hs15, hs14, hs13, hs12, hs11]
                                    simp only [stPop, stSwap, stJumpdest]
                                    rw [haa, haw10]

/-- `SUB` of `ofNat sz` and `4` is `sz - 4` (no wrap), for `4 ≤ sz < size`. -/
theorem sub4_toNat {sz : ℕ} (h4 : 4 ≤ sz) (hsz : sz < UInt256.size) :
    (UInt256.sub (UInt256.ofNat sz) ⟨4⟩).toNat = sz - 4 := by
  have h1 : (UInt256.ofNat sz).toNat = sz := by
    show (Fin.ofNat _ sz).val = sz; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hsz
  have hrw : UInt256.sub (UInt256.ofNat sz) ⟨4⟩ = UInt256.ofNat sz - UInt256.ofNat 4 := rfl
  rw [hrw, toNat_sub_ofNat (by rw [h1]; exact h4), h1]

/-- `SLT a 32 = 0` (signed) when `32 ≤ a < 2^255`. -/
theorem slt32_zero {a : UInt256} (hlo : 32 ≤ a.toNat) (hhi : a.toNat < 2 ^ 255) :
    UInt256.slt a ⟨32⟩ = ⟨0⟩ := by
  have h32 : (⟨32⟩ : UInt256).toNat = 32 := by
    show (Fin.ofNat _ 32).val = 32; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))
  have hbool : UInt256.sltBool a ⟨32⟩ = false := by
    unfold UInt256.sltBool
    rw [if_neg (show ¬ a.toNat ≥ 2 ^ 255 by omega),
        if_neg (show ¬ (⟨32⟩ : UInt256).toNat ≥ 2 ^ 255 by rw [h32]; norm_num)]
    exact decide_eq_false (show ¬ a < ⟨32⟩ by
      show ¬ a.toNat < (⟨32⟩ : UInt256).toNat; rw [h32]; omega)
  show UInt256.fromBool (UInt256.sltBool a ⟨32⟩) = ⟨0⟩
  rw [hbool]; rfl

/-- `ADD` of two in-range literals does not wrap. -/
theorem add_lit_toNat {a b : ℕ} (ha : a < UInt256.size) (hb : b < UInt256.size)
    (h : a + b < UInt256.size) :
    (UInt256.add (UInt256.ofNat a) (UInt256.ofNat b)).toNat = a + b := by
  have hav : (UInt256.ofNat a).toNat = a := by
    show (Fin.ofNat _ a).val = a; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt ha
  have hbv : (UInt256.ofNat b).toNat = b := by
    show (Fin.ofNat _ b).val = b; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hb
  show ((UInt256.ofNat a).val + (UInt256.ofNat b).val).val = a + b
  rw [Fin.add_def]
  show ((UInt256.ofNat a).toNat + (UInt256.ofNat b).toNat) % UInt256.size = a + b
  rw [hav, hbv, Nat.mod_eq_of_lt h]

/-- `(⟨4⟩ + ⟨0⟩).toNat = 4`. -/
theorem add40_toNat : ((⟨4⟩ : UInt256) + ⟨0⟩).toNat = 4 := by
  have : (⟨4⟩ : UInt256) + ⟨0⟩ = UInt256.add (UInt256.ofNat 4) (UInt256.ofNat 0) := rfl
  rw [this, add_lit_toNat (lt_size_of_lt256 (by norm_num)) (lt_size_of_lt256 (by norm_num))
    (lt_size_of_lt256 (by norm_num))]

/-- solc routine `0xcf` (`abi_decode_tuple_t_uint256`): entry at pc 207 with
    `[⟨4⟩, ofNat size, ret, …R']`, checks the calldata is long enough (`size ≥ 36`, so the signed
    bounds-check passes — no revert), loads the argument via `0xbb`, and returns it to `ret`
    leaving `[calldata[4:36], …R']`. -/
theorem powRoutine_cf {g : UInt256} {s0 s : State} {I : Ethereum.ExecutionEnv} {k C : ℕ}
    {ret : UInt256} {R' : List UInt256}
    (hcode : s.executionEnv.code = powBytecode) (hee : s.executionEnv = I)
    (hpc : s.machineState.pc = ⟨207⟩)
    (hstk : s.machineState.stack = ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R')
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255)
    (hret : (D_J powBytecode ⟨0⟩).contains ret = true) (hov : R'.length + 15 ≤ 1024)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ (k' C' : ℕ) (s' : State),
          X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k') (D_J powBytecode ⟨0⟩) s'
        ∧ s'.executionEnv.code = powBytecode ∧ s'.machineState.pc = ret
        ∧ s'.machineState.stack = uInt256OfByteArray (I.calldata.readBytes 4 32) :: R'
        ∧ s'.machineState.gasAvailable.toNat = g.toNat - C' ∧ k' ≤ C' ∧ C' ≤ g.toNat
        ∧ s'.machineState.memory = s.machineState.memory
        ∧ s'.machineState.activeWords = s.machineState.activeWords := by
  have hszsize : I.calldata.size < UInt256.size := by
    have hp : (2:ℕ)^255 < UInt256.size := by
      have : (2:ℕ)^255 < 2^256 := by norm_num
      simpa [UInt256.size] using this
    omega
  set de := UInt256.ofNat I.calldata.size with hde
  have hsltval : UInt256.slt (UInt256.sub de ⟨4⟩) ⟨32⟩ = ⟨0⟩ := by
    apply slt32_zero
    · rw [hde, sub4_toNat (by omega) hszsize]; omega
    · rw [hde, sub4_toNat (by omega) hszsize]; omega
  have st0 := jumpdest_xstep hcode hpc (by decide) (by rw [hstk]; simp only [List.length_cons]; omega)
  by_cases g0 : g.toNat < C + 1
  · exact Or.inl (hX.trans (stepOOG hgas st0 hk hC (by omega)))
  · set s1 := stJumpdest s with hs1
    have hX1 := hX.trans (stepContinue (k := k) (C := C) hgas st0 hk (by omega))
    have hc1 : s1.executionEnv.code = powBytecode := by rw [hs1]; simp only [stJumpdest]; exact hcode
    have hp1 : s1.machineState.pc = ⟨208⟩ := by rw [hs1]; simp only [stJumpdest]; rw [hpc]; rfl
    have hg1 : s1.machineState.gasAvailable.toNat = g.toNat - (C + 1) := by
      rw [hs1]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
    have hk1 : s1.machineState.stack = ⟨4⟩ :: de :: ret :: R' := by rw [hs1]; simp only [stJumpdest]; exact hstk
    have st1 := push0_xstep hc1 hp1 (by decide) hk1 (by first | (simp only [List.length_cons]; omega) | omega)
    by_cases g1 : g.toNat < C + 3
    · exact Or.inl (hX1.trans (stepOOG (k := k+1) (C := C+1) hg1 st1 (by omega) (by omega) (by omega)))
    · set s2 := stPush0 s1 with hs2
      have hX2 := hX1.trans (stepContinue (k := k+1) (C := C+1) hg1 st1 (by omega) (by omega))
      have hc2 : s2.executionEnv.code = powBytecode := by rw [hs2]; simp only [stPush0]; exact hc1
      have hp2 : s2.machineState.pc = ⟨209⟩ := by rw [hs2]; simp only [stPush0]; rw [hp1]; rfl
      have hg2 : s2.machineState.gasAvailable.toNat = g.toNat - (C + 3) := by
        rw [hs2]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
      have hk2 : s2.machineState.stack = ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs2]; simp only [stPush0, hk1]
      have st2 := push1_xstep (argv := ⟨32⟩) hc2 hp2 (by decide) hk2 (by first | (simp only [List.length_cons]; omega) | omega)
      by_cases g2 : g.toNat < C + 6
      · exact Or.inl (hX2.trans (stepOOG (k := k+2) (C := C+3) hg2 st2 (by omega) (by omega) (by omega)))
      · set s3 := stPush1 s2 ⟨32⟩ with hs3
        have hX3 := hX2.trans (stepContinue (k := k+2) (C := C+3) hg2 st2 (by omega) (by omega))
        have hc3 : s3.executionEnv.code = powBytecode := by rw [hs3]; simp only [stPush1]; exact hc2
        have hp3 : s3.machineState.pc = ⟨211⟩ := by rw [hs3]; simp only [stPush1]; rw [hp2]; rfl
        have hg3 : s3.machineState.gasAvailable.toNat = g.toNat - (C + 6) := by
          rw [hs3]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
        have hk3 : s3.machineState.stack = ⟨32⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs3]; simp only [stPush1, hk2]
        have st3 := dup3_xstep hc3 hp3 (by decide) hk3 (by first | (simp only [List.length_cons]; omega) | omega)
        by_cases g3 : g.toNat < C + 9
        · exact Or.inl (hX3.trans (stepOOG (k := k+3) (C := C+6) hg3 st3 (by omega) (by omega) (by omega)))
        · set s4 := stSwap s3 (⟨4⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R') with hs4
          have hX4 := hX3.trans (stepContinue (k := k+3) (C := C+6) hg3 st3 (by omega) (by omega))
          have hc4 : s4.executionEnv.code = powBytecode := by rw [hs4]; simp only [stSwap]; exact hc3
          have hp4 : s4.machineState.pc = ⟨212⟩ := by rw [hs4]; simp only [stSwap]; rw [hp3]; rfl
          have hg4 : s4.machineState.gasAvailable.toNat = g.toNat - (C + 9) := by
            rw [hs4]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
          have hk4 : s4.machineState.stack = ⟨4⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs4]; simp only [stSwap]
          have st4 := dup5_xstep hc4 hp4 (by decide) hk4 (by first | (simp only [List.length_cons]; omega) | omega)
          by_cases g4 : g.toNat < C + 12
          · exact Or.inl (hX4.trans (stepOOG (k := k+4) (C := C+9) hg4 st4 (by omega) (by omega) (by omega)))
          · set s5 := stSwap s4 (de :: ⟨4⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R') with hs5
            have hX5 := hX4.trans (stepContinue (k := k+4) (C := C+9) hg4 st4 (by omega) (by omega))
            have hc5 : s5.executionEnv.code = powBytecode := by rw [hs5]; simp only [stSwap]; exact hc4
            have hp5 : s5.machineState.pc = ⟨213⟩ := by rw [hs5]; simp only [stSwap]; rw [hp4]; rfl
            have hg5 : s5.machineState.gasAvailable.toNat = g.toNat - (C + 12) := by
              rw [hs5]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
            have hk5 : s5.machineState.stack = de :: ⟨4⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs5]; simp only [stSwap]
            have st5 := sub_xstep hc5 hp5 (by decide) hk5 (by first | (simp only [List.length_cons]; omega) | omega)
            by_cases g5 : g.toNat < C + 15
            · exact Or.inl (hX5.trans (stepOOG (k := k+5) (C := C+12) hg5 st5 (by omega) (by omega) (by omega)))
            · set s6 := stBinop s5 (UInt256.sub de ⟨4⟩) (⟨32⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R') with hs6
              have hX6 := hX5.trans (stepContinue (k := k+5) (C := C+12) hg5 st5 (by omega) (by omega))
              have hc6 : s6.executionEnv.code = powBytecode := by rw [hs6]; simp only [stBinop]; exact hc5
              have hp6 : s6.machineState.pc = ⟨214⟩ := by rw [hs6]; simp only [stBinop]; rw [hp5]; rfl
              have hg6 : s6.machineState.gasAvailable.toNat = g.toNat - (C + 15) := by
                rw [hs6]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
              have hk6 : s6.machineState.stack = UInt256.sub de ⟨4⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs6]; simp only [stBinop]
              have st6 := slt_xstep hc6 hp6 (by decide) hk6 (by first | (simp only [List.length_cons]; omega) | omega)
              by_cases g6 : g.toNat < C + 18
              · exact Or.inl (hX6.trans (stepOOG (k := k+6) (C := C+15) hg6 st6 (by omega) (by omega) (by omega)))
              · set s7 := stBinop s6 (UInt256.slt (UInt256.sub de ⟨4⟩) ⟨32⟩) (⟨0⟩ :: ⟨4⟩ :: de :: ret :: R') with hs7
                have hX7 := hX6.trans (stepContinue (k := k+6) (C := C+15) hg6 st6 (by omega) (by omega))
                have hc7 : s7.executionEnv.code = powBytecode := by rw [hs7]; simp only [stBinop]; exact hc6
                have hp7 : s7.machineState.pc = ⟨215⟩ := by rw [hs7]; simp only [stBinop]; rw [hp6]; rfl
                have hg7 : s7.machineState.gasAvailable.toNat = g.toNat - (C + 18) := by
                  rw [hs7]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                have hk7 : s7.machineState.stack = ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by
                  rw [hs7]; simp only [stBinop]; rw [hsltval]
                have st7 := iszero_xstep hc7 hp7 (by decide) hk7 (by first | (simp only [List.length_cons]; omega) | omega)
                by_cases g7 : g.toNat < C + 21
                · exact Or.inl (hX7.trans (stepOOG (k := k+7) (C := C+18) hg7 st7 (by omega) (by omega) (by omega)))
                · set s8 := stIsZero s7 ⟨0⟩ (⟨0⟩ :: ⟨4⟩ :: de :: ret :: R') with hs8
                  have hX8 := hX7.trans (stepContinue (k := k+7) (C := C+18) hg7 st7 (by omega) (by omega))
                  have hc8 : s8.executionEnv.code = powBytecode := by rw [hs8]; simp only [stIsZero]; exact hc7
                  have hp8 : s8.machineState.pc = ⟨216⟩ := by rw [hs8]; simp only [stIsZero]; rw [hp7]; rfl
                  have hg8 : s8.machineState.gasAvailable.toNat = g.toNat - (C + 21) := by
                    rw [hs8]; simp only [stIsZero]; rw [toNat_sub_ofNat (by omega)]; omega
                  have hk8 : s8.machineState.stack = ⟨1⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by
                    rw [hs8]; simp only [stIsZero]; rw [show UInt256.isZero ⟨0⟩ = ⟨1⟩ from by decide]
                  have st8 := push2_xstep (argv := ⟨228⟩) hc8 hp8 (by decide) hk8 (by first | (simp only [List.length_cons]; omega) | omega)
                  by_cases g8 : g.toNat < C + 24
                  · exact Or.inl (hX8.trans (stepOOG (k := k+8) (C := C+21) hg8 st8 (by omega) (by omega) (by omega)))
                  · set s9 := stPush2 s8 ⟨228⟩ with hs9
                    have hX9 := hX8.trans (stepContinue (k := k+8) (C := C+21) hg8 st8 (by omega) (by omega))
                    have hc9 : s9.executionEnv.code = powBytecode := by rw [hs9]; simp only [stPush2]; exact hc8
                    have hp9 : s9.machineState.pc = ⟨219⟩ := by rw [hs9]; simp only [stPush2]; rw [hp8]; rfl
                    have hg9 : s9.machineState.gasAvailable.toNat = g.toNat - (C + 24) := by
                      rw [hs9]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                    have hk9 : s9.machineState.stack = ⟨228⟩ :: ⟨1⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs9]; simp only [stPush2, hk8]
                    have st9 := jumpi_t_xstep hc9 hp9 (by decide) hk9 (by decide)
                      (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by first | (simp only [List.length_cons]; omega) | omega)
                    by_cases g9 : g.toNat < C + 34
                    · exact Or.inl (hX9.trans (stepOOG (k := k+9) (C := C+24) (cost := 10) hg9 st9 (by omega) (by omega) (by omega)))
                    · set s10 := stJumpiT s9 ⟨228⟩ (⟨0⟩ :: ⟨4⟩ :: de :: ret :: R') with hs10
                      have hX10 := hX9.trans (stepContinue (k := k+9) (C := C+24) (cost := 10) hg9 st9 (by omega) (by omega))
                      have hc10 : s10.executionEnv.code = powBytecode := by rw [hs10]; simp only [stJumpiT]; exact hc9
                      have hp10 : s10.machineState.pc = ⟨228⟩ := by rw [hs10]; simp only [stJumpiT]
                      have hg10 : s10.machineState.gasAvailable.toNat = g.toNat - (C + 34) := by
                        rw [hs10]; simp only [stJumpiT]; rw [toNat_sub_ofNat (by omega)]; omega
                      have hk10 : s10.machineState.stack = ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs10]; simp only [stJumpiT]
                      have st10 := jumpdest_xstep hc10 hp10 (by decide) (by rw [hk10]; simp only [List.length_cons]; omega)
                      by_cases g10 : g.toNat < C + 35
                      · exact Or.inl (hX10.trans (stepOOG (k := k+10) (C := C+34) hg10 st10 (by omega) (by omega) (by omega)))
                      · set s11 := stJumpdest s10 with hs11
                        have hX11 := hX10.trans (stepContinue (k := k+10) (C := C+34) hg10 st10 (by omega) (by omega))
                        have hc11 : s11.executionEnv.code = powBytecode := by rw [hs11]; simp only [stJumpdest]; exact hc10
                        have hp11 : s11.machineState.pc = ⟨229⟩ := by rw [hs11]; simp only [stJumpdest]; rw [hp10]; rfl
                        have hg11 : s11.machineState.gasAvailable.toNat = g.toNat - (C + 35) := by
                          rw [hs11]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                        have hk11 : s11.machineState.stack = ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs11]; simp only [stJumpdest]; exact hk10
                        have st11 := push0_xstep hc11 hp11 (by decide) hk11 (by first | (simp only [List.length_cons]; omega) | omega)
                        by_cases g11 : g.toNat < C + 37
                        · exact Or.inl (hX11.trans (stepOOG (k := k+11) (C := C+35) hg11 st11 (by omega) (by omega) (by omega)))
                        · set s12 := stPush0 s11 with hs12
                          have hX12 := hX11.trans (stepContinue (k := k+11) (C := C+35) hg11 st11 (by omega) (by omega))
                          have hc12 : s12.executionEnv.code = powBytecode := by rw [hs12]; simp only [stPush0]; exact hc11
                          have hp12 : s12.machineState.pc = ⟨230⟩ := by rw [hs12]; simp only [stPush0]; rw [hp11]; rfl
                          have hg12 : s12.machineState.gasAvailable.toNat = g.toNat - (C + 37) := by
                            rw [hs12]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                          have hk12 : s12.machineState.stack = ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs12]; simp only [stPush0, hk11]
                          have st12 := push2_xstep (argv := ⟨241⟩) hc12 hp12 (by decide) hk12 (by first | (simp only [List.length_cons]; omega) | omega)
                          by_cases g12 : g.toNat < C + 40
                          · exact Or.inl (hX12.trans (stepOOG (k := k+12) (C := C+37) hg12 st12 (by omega) (by omega) (by omega)))
                          · set s13 := stPush2 s12 ⟨241⟩ with hs13
                            have hX13 := hX12.trans (stepContinue (k := k+12) (C := C+37) hg12 st12 (by omega) (by omega))
                            have hc13 : s13.executionEnv.code = powBytecode := by rw [hs13]; simp only [stPush2]; exact hc12
                            have hp13 : s13.machineState.pc = ⟨233⟩ := by rw [hs13]; simp only [stPush2]; rw [hp12]; rfl
                            have hg13 : s13.machineState.gasAvailable.toNat = g.toNat - (C + 40) := by
                              rw [hs13]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                            have hk13 : s13.machineState.stack = ⟨241⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs13]; simp only [stPush2, hk12]
                            have st13 := dup5_xstep hc13 hp13 (by decide) hk13 (by first | (simp only [List.length_cons]; omega) | omega)
                            by_cases g13 : g.toNat < C + 43
                            · exact Or.inl (hX13.trans (stepOOG (k := k+13) (C := C+40) hg13 st13 (by omega) (by omega) (by omega)))
                            · set s14 := stSwap s13 (de :: ⟨241⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R') with hs14
                              have hX14 := hX13.trans (stepContinue (k := k+13) (C := C+40) hg13 st13 (by omega) (by omega))
                              have hc14 : s14.executionEnv.code = powBytecode := by rw [hs14]; simp only [stSwap]; exact hc13
                              have hp14 : s14.machineState.pc = ⟨234⟩ := by rw [hs14]; simp only [stSwap]; rw [hp13]; rfl
                              have hg14 : s14.machineState.gasAvailable.toNat = g.toNat - (C + 43) := by
                                rw [hs14]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                              have hk14 : s14.machineState.stack = de :: ⟨241⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs14]; simp only [stSwap]
                              have st14 := dup3_xstep hc14 hp14 (by decide) hk14 (by first | (simp only [List.length_cons]; omega) | omega)
                              by_cases g14 : g.toNat < C + 46
                              · exact Or.inl (hX14.trans (stepOOG (k := k+14) (C := C+43) hg14 st14 (by omega) (by omega) (by omega)))
                              · set s15 := stSwap s14 (⟨0⟩ :: de :: ⟨241⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R') with hs15
                                have hX15 := hX14.trans (stepContinue (k := k+14) (C := C+43) hg14 st14 (by omega) (by omega))
                                have hc15 : s15.executionEnv.code = powBytecode := by rw [hs15]; simp only [stSwap]; exact hc14
                                have hp15 : s15.machineState.pc = ⟨235⟩ := by rw [hs15]; simp only [stSwap]; rw [hp14]; rfl
                                have hg15 : s15.machineState.gasAvailable.toNat = g.toNat - (C + 46) := by
                                  rw [hs15]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                have hk15 : s15.machineState.stack = ⟨0⟩ :: de :: ⟨241⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs15]; simp only [stSwap]
                                have st15 := dup6_xstep hc15 hp15 (by decide) hk15 (by first | (simp only [List.length_cons]; omega) | omega)
                                by_cases g15 : g.toNat < C + 49
                                · exact Or.inl (hX15.trans (stepOOG (k := k+15) (C := C+46) hg15 st15 (by omega) (by omega) (by omega)))
                                · set s16 := stSwap s15 (⟨4⟩ :: ⟨0⟩ :: de :: ⟨241⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R') with hs16
                                  have hX16 := hX15.trans (stepContinue (k := k+15) (C := C+46) hg15 st15 (by omega) (by omega))
                                  have hc16 : s16.executionEnv.code = powBytecode := by rw [hs16]; simp only [stSwap]; exact hc15
                                  have hp16 : s16.machineState.pc = ⟨236⟩ := by rw [hs16]; simp only [stSwap]; rw [hp15]; rfl
                                  have hg16 : s16.machineState.gasAvailable.toNat = g.toNat - (C + 49) := by
                                    rw [hs16]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                  have hk16 : s16.machineState.stack = ⟨4⟩ :: ⟨0⟩ :: de :: ⟨241⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs16]; simp only [stSwap]
                                  have st16 := add_xstep hc16 hp16 (by decide) hk16 (by first | (simp only [List.length_cons]; omega) | omega)
                                  by_cases g16 : g.toNat < C + 52
                                  · exact Or.inl (hX16.trans (stepOOG (k := k+16) (C := C+49) hg16 st16 (by omega) (by omega) (by omega)))
                                  · set s17 := stBinop s16 ((⟨4⟩ : UInt256) + ⟨0⟩) (de :: ⟨241⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R') with hs17
                                    have hX17 := hX16.trans (stepContinue (k := k+16) (C := C+49) hg16 st16 (by omega) (by omega))
                                    have hc17 : s17.executionEnv.code = powBytecode := by rw [hs17]; simp only [stBinop]; exact hc16
                                    have hp17 : s17.machineState.pc = ⟨237⟩ := by rw [hs17]; simp only [stBinop]; rw [hp16]; rfl
                                    have hg17 : s17.machineState.gasAvailable.toNat = g.toNat - (C + 52) := by
                                      rw [hs17]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                                    have hk17 : s17.machineState.stack = ((⟨4⟩ : UInt256) + ⟨0⟩) :: de :: ⟨241⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs17]; simp only [stBinop]
                                    have st17 := push2_xstep (argv := ⟨187⟩) hc17 hp17 (by decide) hk17 (by first | (simp only [List.length_cons]; omega) | omega)
                                    by_cases g17 : g.toNat < C + 55
                                    · exact Or.inl (hX17.trans (stepOOG (k := k+17) (C := C+52) hg17 st17 (by omega) (by omega) (by omega)))
                                    · set s18 := stPush2 s17 ⟨187⟩ with hs18
                                      have hX18 := hX17.trans (stepContinue (k := k+17) (C := C+52) hg17 st17 (by omega) (by omega))
                                      have hc18 : s18.executionEnv.code = powBytecode := by rw [hs18]; simp only [stPush2]; exact hc17
                                      have hp18 : s18.machineState.pc = ⟨240⟩ := by rw [hs18]; simp only [stPush2]; rw [hp17]; rfl
                                      have hg18 : s18.machineState.gasAvailable.toNat = g.toNat - (C + 55) := by
                                        rw [hs18]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                                      have hk18 : s18.machineState.stack = ⟨187⟩ :: ((⟨4⟩ : UInt256) + ⟨0⟩) :: de :: ⟨241⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs18]; simp only [stPush2, hk17]
                                      have st18 := jump_xstep hc18 hp18 (by decide) hk18
                                        (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by first | (simp only [List.length_cons]; omega) | omega)
                                      by_cases g18 : g.toNat < C + 63
                                      · exact Or.inl (hX18.trans (stepOOG (k := k+18) (C := C+55) (cost := 8) hg18 st18 (by omega) (by omega) (by omega)))
                                      · set s19 := stJump s18 ⟨187⟩ (((⟨4⟩ : UInt256) + ⟨0⟩) :: de :: ⟨241⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R') with hs19
                                        have hX19 := hX18.trans (stepContinue (k := k+18) (C := C+55) (cost := 8) hg18 st18 (by omega) (by omega))
                                        have hc19 : s19.executionEnv.code = powBytecode := by rw [hs19]; simp only [stJump]; exact hc18
                                        have he19 : s19.executionEnv = I := by
                                          rw [hs19]; simp only [stJump]
                                          rw [hs18, hs17, hs16, hs15, hs14, hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
                                          simp only [stPush2, stBinop, stSwap, stJumpiT, stJumpdest, stPush0, stIsZero, stPush1]
                                          exact hee
                                        have hp19 : s19.machineState.pc = ⟨187⟩ := by rw [hs19]; simp only [stJump]
                                        have hg19 : s19.machineState.gasAvailable.toNat = g.toNat - (C + 63) := by
                                          rw [hs19]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                        have hk19 : s19.machineState.stack = ((⟨4⟩ : UInt256) + ⟨0⟩) :: de :: ⟨241⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs19]; simp only [stJump]
                                        have hmem19 : s19.machineState.memory = s.machineState.memory := by
                                          rw [hs19]; simp only [stJump]
                                          rw [hs18, hs17, hs16, hs15, hs14, hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
                                          simp only [stPush2, stBinop, stSwap, stJumpiT, stJumpdest, stPush0, stIsZero, stPush1]
                                        have haw19 : s19.machineState.activeWords = s.machineState.activeWords := by
                                          rw [hs19]; simp only [stJump]
                                          rw [hs18, hs17, hs16, hs15, hs14, hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
                                          simp only [stPush2, stBinop, stSwap, stJumpiT, stJumpdest, stPush0, stIsZero, stPush1]
                                        -- call 0xbb: loads the argument, returns to 241
                                        rcases powRoutine_bb (I := I) (offset := (⟨4⟩ : UInt256) + ⟨0⟩) (ennd := de)
                                            (ret := ⟨241⟩) (R := ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R')
                                            hc19 he19 hp19 hk19 (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
                                            (by first | (simp only [List.length_cons]; omega) | omega) hg19 (by omega) (by omega) hX19
                                          with hoog | ⟨kb, Cb, sb, hXb, hcb, hpb, hkb, hgb, hkCb, hCgb, hmb, hab⟩
                                        · exact Or.inl hoog
                                        rw [add40_toNat] at hkb
                                        set val := uInt256OfByteArray (I.calldata.readBytes 4 32) with hvaldef
                                        -- 0xf1..0xf9: rearrange decoded value, return to `ret`
                                        have stb := jumpdest_xstep hcb hpb (by decide) (by rw [hkb]; simp only [List.length_cons]; omega)
                                        by_cases gb : g.toNat < Cb + 1
                                        · exact Or.inl (hXb.trans (stepOOG hgb stb hkCb hCgb (by omega)))
                                        · set s20 := stJumpdest sb with hs20
                                          have hX20 := hXb.trans (stepContinue (k := kb) (C := Cb) hgb stb hkCb (by omega))
                                          have hc20 : s20.executionEnv.code = powBytecode := by rw [hs20]; simp only [stJumpdest]; exact hcb
                                          have hp20 : s20.machineState.pc = ⟨242⟩ := by rw [hs20]; simp only [stJumpdest]; rw [hpb]; rfl
                                          have hg20 : s20.machineState.gasAvailable.toNat = g.toNat - (Cb + 1) := by
                                            rw [hs20]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                                          have hk20 : s20.machineState.stack = val :: ⟨0⟩ :: ⟨0⟩ :: ⟨4⟩ :: de :: ret :: R' := by rw [hs20]; simp only [stJumpdest]; exact hkb
                                          have st20 := swap2_xstep hc20 hp20 (by decide) hk20 (by first | (simp only [List.length_cons]; omega) | omega)
                                          by_cases g20 : g.toNat < Cb + 4
                                          · exact Or.inl (hX20.trans (stepOOG (k := kb+1) (C := Cb+1) hg20 st20 (by omega) (by omega) (by omega)))
                                          · set s21 := stSwap s20 (⟨0⟩ :: ⟨0⟩ :: val :: ⟨4⟩ :: de :: ret :: R') with hs21
                                            have hX21 := hX20.trans (stepContinue (k := kb+1) (C := Cb+1) hg20 st20 (by omega) (by omega))
                                            have hc21 : s21.executionEnv.code = powBytecode := by rw [hs21]; simp only [stSwap]; exact hc20
                                            have hp21 : s21.machineState.pc = ⟨243⟩ := by rw [hs21]; simp only [stSwap]; rw [hp20]; rfl
                                            have hg21 : s21.machineState.gasAvailable.toNat = g.toNat - (Cb + 4) := by
                                              rw [hs21]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                            have hk21 : s21.machineState.stack = ⟨0⟩ :: ⟨0⟩ :: val :: ⟨4⟩ :: de :: ret :: R' := by rw [hs21]; simp only [stSwap]
                                            have st21 := pop_xstep hc21 hp21 (by decide) hk21 (by first | (simp only [List.length_cons]; omega) | omega)
                                            by_cases g21 : g.toNat < Cb + 6
                                            · exact Or.inl (hX21.trans (stepOOG (k := kb+2) (C := Cb+4) hg21 st21 (by omega) (by omega) (by omega)))
                                            · set s22 := stPop s21 (⟨0⟩ :: val :: ⟨4⟩ :: de :: ret :: R') with hs22
                                              have hX22 := hX21.trans (stepContinue (k := kb+2) (C := Cb+4) hg21 st21 (by omega) (by omega))
                                              have hc22 : s22.executionEnv.code = powBytecode := by rw [hs22]; simp only [stPop]; exact hc21
                                              have hp22 : s22.machineState.pc = ⟨244⟩ := by rw [hs22]; simp only [stPop]; rw [hp21]; rfl
                                              have hg22 : s22.machineState.gasAvailable.toNat = g.toNat - (Cb + 6) := by
                                                rw [hs22]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                              have hk22 : s22.machineState.stack = ⟨0⟩ :: val :: ⟨4⟩ :: de :: ret :: R' := by rw [hs22]; simp only [stPop]
                                              have st22 := pop_xstep hc22 hp22 (by decide) hk22 (by first | (simp only [List.length_cons]; omega) | omega)
                                              by_cases g22 : g.toNat < Cb + 8
                                              · exact Or.inl (hX22.trans (stepOOG (k := kb+3) (C := Cb+6) hg22 st22 (by omega) (by omega) (by omega)))
                                              · set s23 := stPop s22 (val :: ⟨4⟩ :: de :: ret :: R') with hs23
                                                have hX23 := hX22.trans (stepContinue (k := kb+3) (C := Cb+6) hg22 st22 (by omega) (by omega))
                                                have hc23 : s23.executionEnv.code = powBytecode := by rw [hs23]; simp only [stPop]; exact hc22
                                                have hp23 : s23.machineState.pc = ⟨245⟩ := by rw [hs23]; simp only [stPop]; rw [hp22]; rfl
                                                have hg23 : s23.machineState.gasAvailable.toNat = g.toNat - (Cb + 8) := by
                                                  rw [hs23]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                have hk23 : s23.machineState.stack = val :: ⟨4⟩ :: de :: ret :: R' := by rw [hs23]; simp only [stPop]
                                                have st23 := swap3_xstep hc23 hp23 (by decide) hk23 (by omega)
                                                by_cases g23 : g.toNat < Cb + 11
                                                · exact Or.inl (hX23.trans (stepOOG (k := kb+4) (C := Cb+8) hg23 st23 (by omega) (by omega) (by omega)))
                                                · set s24 := stSwap s23 (ret :: ⟨4⟩ :: de :: val :: R') with hs24
                                                  have hX24 := hX23.trans (stepContinue (k := kb+4) (C := Cb+8) hg23 st23 (by omega) (by omega))
                                                  have hc24 : s24.executionEnv.code = powBytecode := by rw [hs24]; simp only [stSwap]; exact hc23
                                                  have hp24 : s24.machineState.pc = ⟨246⟩ := by rw [hs24]; simp only [stSwap]; rw [hp23]; rfl
                                                  have hg24 : s24.machineState.gasAvailable.toNat = g.toNat - (Cb + 11) := by
                                                    rw [hs24]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                  have hk24 : s24.machineState.stack = ret :: ⟨4⟩ :: de :: val :: R' := by rw [hs24]; simp only [stSwap]
                                                  have st24 := swap2_xstep hc24 hp24 (by decide) hk24 (by first | (simp only [List.length_cons]; omega) | omega)
                                                  by_cases g24 : g.toNat < Cb + 14
                                                  · exact Or.inl (hX24.trans (stepOOG (k := kb+5) (C := Cb+11) hg24 st24 (by omega) (by omega) (by omega)))
                                                  · set s25 := stSwap s24 (de :: ⟨4⟩ :: ret :: val :: R') with hs25
                                                    have hX25 := hX24.trans (stepContinue (k := kb+5) (C := Cb+11) hg24 st24 (by omega) (by omega))
                                                    have hc25 : s25.executionEnv.code = powBytecode := by rw [hs25]; simp only [stSwap]; exact hc24
                                                    have hp25 : s25.machineState.pc = ⟨247⟩ := by rw [hs25]; simp only [stSwap]; rw [hp24]; rfl
                                                    have hg25 : s25.machineState.gasAvailable.toNat = g.toNat - (Cb + 14) := by
                                                      rw [hs25]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                    have hk25 : s25.machineState.stack = de :: ⟨4⟩ :: ret :: val :: R' := by rw [hs25]; simp only [stSwap]
                                                    have st25 := pop_xstep hc25 hp25 (by decide) hk25 (by first | (simp only [List.length_cons]; omega) | omega)
                                                    by_cases g25 : g.toNat < Cb + 16
                                                    · exact Or.inl (hX25.trans (stepOOG (k := kb+6) (C := Cb+14) hg25 st25 (by omega) (by omega) (by omega)))
                                                    · set s26 := stPop s25 (⟨4⟩ :: ret :: val :: R') with hs26
                                                      have hX26 := hX25.trans (stepContinue (k := kb+6) (C := Cb+14) hg25 st25 (by omega) (by omega))
                                                      have hc26 : s26.executionEnv.code = powBytecode := by rw [hs26]; simp only [stPop]; exact hc25
                                                      have hp26 : s26.machineState.pc = ⟨248⟩ := by rw [hs26]; simp only [stPop]; rw [hp25]; rfl
                                                      have hg26 : s26.machineState.gasAvailable.toNat = g.toNat - (Cb + 16) := by
                                                        rw [hs26]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                      have hk26 : s26.machineState.stack = ⟨4⟩ :: ret :: val :: R' := by rw [hs26]; simp only [stPop]
                                                      have st26 := pop_xstep hc26 hp26 (by decide) hk26 (by first | (simp only [List.length_cons]; omega) | omega)
                                                      by_cases g26 : g.toNat < Cb + 18
                                                      · exact Or.inl (hX26.trans (stepOOG (k := kb+7) (C := Cb+16) hg26 st26 (by omega) (by omega) (by omega)))
                                                      · set s27 := stPop s26 (ret :: val :: R') with hs27
                                                        have hX27 := hX26.trans (stepContinue (k := kb+7) (C := Cb+16) hg26 st26 (by omega) (by omega))
                                                        have hc27 : s27.executionEnv.code = powBytecode := by rw [hs27]; simp only [stPop]; exact hc26
                                                        have hp27 : s27.machineState.pc = ⟨249⟩ := by rw [hs27]; simp only [stPop]; rw [hp26]; rfl
                                                        have hg27 : s27.machineState.gasAvailable.toNat = g.toNat - (Cb + 18) := by
                                                          rw [hs27]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                        have hk27 : s27.machineState.stack = ret :: val :: R' := by rw [hs27]; simp only [stPop]
                                                        have st27 := jump_xstep hc27 hp27 (by decide) hk27 hret (by first | (simp only [List.length_cons]; omega) | omega)
                                                        by_cases g27 : g.toNat < Cb + 26
                                                        · exact Or.inl (hX27.trans (stepOOG (k := kb+8) (C := Cb+18) (cost := 8) hg27 st27 (by omega) (by omega) (by omega)))
                                                        · set s28 := stJump s27 ret (val :: R') with hs28
                                                          have hX28 := hX27.trans (stepContinue (k := kb+8) (C := Cb+18) (cost := 8) hg27 st27 (by omega) (by omega))
                                                          refine Or.inr ⟨kb+9, Cb+26, s28, ?_, ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_⟩
                                                          · have he : g.toNat + 1 - (kb + 8 + 1) = g.toNat + 1 - (kb + 9) := by omega
                                                            rw [← he]; exact hX28
                                                          · rw [hs28]; simp only [stJump]; exact hc27
                                                          · rw [hs28]; simp only [stJump]
                                                          · rw [hs28]; simp only [stJump]
                                                          · rw [hs28]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                                          · rw [hs28]; simp only [stJump]
                                                            rw [hs27, hs26, hs25, hs24, hs23, hs22, hs21, hs20]
                                                            simp only [stPop, stSwap, stJumpdest]
                                                            rw [hmb, hmem19]
                                                          · rw [hs28]; simp only [stJump]
                                                            rw [hs27, hs26, hs25, hs24, hs23, hs22, hs21, hs20]
                                                            simp only [stPop, stSwap, stJumpdest]
                                                            rw [hab, haw19]

/-- General `ADD` toNat (mod size). -/
theorem uadd_toNat (a b : UInt256) : (a + b).toNat = (a.toNat + b.toNat) % UInt256.size := by
  show (a.val + b.val).val = (a.val.val + b.val.val) % UInt256.size
  rw [Fin.add_def]

/-- solc recomputes `dataEnd = headStart + (calldatasize − headStart) = calldatasize`. -/
theorem add_sub4 {sz : ℕ} (h4 : 4 ≤ sz) (hsz : sz < UInt256.size) :
    (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat sz) ⟨4⟩ = UInt256.ofNat sz := by
  apply u256_inj
  have h4t : (⟨4⟩ : UInt256).toNat = 4 := by
    show (Fin.ofNat _ 4).val = 4; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))
  have hsz' : (UInt256.ofNat sz).toNat = sz := by
    show (Fin.ofNat _ sz).val = sz; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hsz
  rw [uadd_toNat, h4t, sub4_toNat h4 hsz, hsz',
      show 4 + (sz - 4) = sz from by omega, Nat.mod_eq_of_lt hsz]

/-- Function body `0x2d`: set up and call the ABI decoder, returning at `0x42 = 66` with the
    decoded argument `n = calldata[4:36]` on the stack (`[n, ⟨71⟩, sel]`).  `sel` is the leftover
    selector word from dispatch; `⟨71⟩` is the post-function return address. -/
theorem powX_decode {g : UInt256} {s0 s : State} {I : Ethereum.ExecutionEnv} {k C : ℕ}
    {sel : UInt256}
    (hcode : s.executionEnv.code = powBytecode) (hee : s.executionEnv = I)
    (hpc : s.machineState.pc = ⟨45⟩) (hstk : s.machineState.stack = [sel])
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ (k' C' : ℕ) (s' : State),
          X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k') (D_J powBytecode ⟨0⟩) s'
        ∧ s'.executionEnv.code = powBytecode ∧ s'.machineState.pc = ⟨66⟩
        ∧ s'.machineState.stack = uInt256OfByteArray (I.calldata.readBytes 4 32) :: ⟨71⟩ :: [sel]
        ∧ s'.machineState.gasAvailable.toNat = g.toNat - C' ∧ k' ≤ C' ∧ C' ≤ g.toNat
        ∧ s'.machineState.memory = s.machineState.memory
        ∧ s'.machineState.activeWords = s.machineState.activeWords := by
  have hszsize : I.calldata.size < UInt256.size := by
    have hp : (2:ℕ)^255 < UInt256.size := by
      have : (2:ℕ)^255 < 2^256 := by norm_num
      simpa [UInt256.size] using this
    omega
  have st0 := jumpdest_xstep hcode hpc (by decide) (by rw [hstk]; simp only [List.length_cons, List.length_nil]; omega)
  by_cases g0 : g.toNat < C + 1
  · exact Or.inl (hX.trans (stepOOG hgas st0 hk hC (by omega)))
  · set s1 := stJumpdest s with hs1
    have hX1 := hX.trans (stepContinue (k := k) (C := C) hgas st0 hk (by omega))
    have hc1 : s1.executionEnv.code = powBytecode := by rw [hs1]; simp only [stJumpdest]; exact hcode
    have he1 : s1.executionEnv = I := by rw [hs1]; simp only [stJumpdest]; exact hee
    have hp1 : s1.machineState.pc = ⟨46⟩ := by rw [hs1]; simp only [stJumpdest]; rw [hpc]; rfl
    have hg1 : s1.machineState.gasAvailable.toNat = g.toNat - (C + 1) := by
      rw [hs1]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
    have hk1 : s1.machineState.stack = [sel] := by rw [hs1]; simp only [stJumpdest]; exact hstk
    have st1 := push2_xstep (argv := ⟨71⟩) hc1 hp1 (by decide) hk1 (by simp only [List.length_cons, List.length_nil]; omega)
    by_cases g1 : g.toNat < C + 4
    · exact Or.inl (hX1.trans (stepOOG (k := k+1) (C := C+1) hg1 st1 (by omega) (by omega) (by omega)))
    · set s2 := stPush2 s1 ⟨71⟩ with hs2
      have hX2 := hX1.trans (stepContinue (k := k+1) (C := C+1) hg1 st1 (by omega) (by omega))
      have hc2 : s2.executionEnv.code = powBytecode := by rw [hs2]; simp only [stPush2]; exact hc1
      have he2 : s2.executionEnv = I := by rw [hs2]; simp only [stPush2]; exact he1
      have hp2 : s2.machineState.pc = ⟨49⟩ := by rw [hs2]; simp only [stPush2]; rw [hp1]; rfl
      have hg2 : s2.machineState.gasAvailable.toNat = g.toNat - (C + 4) := by
        rw [hs2]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
      have hk2 : s2.machineState.stack = ⟨71⟩ :: [sel] := by rw [hs2]; simp only [stPush2, hk1]
      have st2 := push1_xstep (argv := ⟨4⟩) hc2 hp2 (by decide) hk2 (by simp only [List.length_cons, List.length_nil]; omega)
      by_cases g2 : g.toNat < C + 7
      · exact Or.inl (hX2.trans (stepOOG (k := k+2) (C := C+4) hg2 st2 (by omega) (by omega) (by omega)))
      · set s3 := stPush1 s2 ⟨4⟩ with hs3
        have hX3 := hX2.trans (stepContinue (k := k+2) (C := C+4) hg2 st2 (by omega) (by omega))
        have hc3 : s3.executionEnv.code = powBytecode := by rw [hs3]; simp only [stPush1]; exact hc2
        have he3 : s3.executionEnv = I := by rw [hs3]; simp only [stPush1]; exact he2
        have hp3 : s3.machineState.pc = ⟨51⟩ := by rw [hs3]; simp only [stPush1]; rw [hp2]; rfl
        have hg3 : s3.machineState.gasAvailable.toNat = g.toNat - (C + 7) := by
          rw [hs3]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
        have hk3 : s3.machineState.stack = ⟨4⟩ :: ⟨71⟩ :: [sel] := by rw [hs3]; simp only [stPush1, hk2]
        have st3 := dup1_xstep hc3 hp3 (by decide) hk3 (by simp only [List.length_cons, List.length_nil]; omega)
        by_cases g3 : g.toNat < C + 10
        · exact Or.inl (hX3.trans (stepOOG (k := k+3) (C := C+7) hg3 st3 (by omega) (by omega) (by omega)))
        · set s4 := stDup1 s3 ⟨4⟩ (⟨71⟩ :: [sel]) with hs4
          have hX4 := hX3.trans (stepContinue (k := k+3) (C := C+7) hg3 st3 (by omega) (by omega))
          have hc4 : s4.executionEnv.code = powBytecode := by rw [hs4]; simp only [stDup1]; exact hc3
          have he4 : s4.executionEnv = I := by rw [hs4]; simp only [stDup1]; exact he3
          have hp4 : s4.machineState.pc = ⟨52⟩ := by rw [hs4]; simp only [stDup1]; rw [hp3]; rfl
          have hg4 : s4.machineState.gasAvailable.toNat = g.toNat - (C + 10) := by
            rw [hs4]; simp only [stDup1]; rw [toNat_sub_ofNat (by omega)]; omega
          have hk4 : s4.machineState.stack = ⟨4⟩ :: ⟨4⟩ :: ⟨71⟩ :: [sel] := by rw [hs4]; simp only [stDup1]
          have st4 := calldatasize_xstep hc4 hp4 (by decide) hk4 (by simp only [List.length_cons, List.length_nil]; omega)
          by_cases g4 : g.toNat < C + 12
          · exact Or.inl (hX4.trans (stepOOG (k := k+4) (C := C+10) hg4 st4 (by omega) (by omega) (by omega)))
          · set s5 := stCalldatasize s4 with hs5
            have hX5 := hX4.trans (stepContinue (k := k+4) (C := C+10) hg4 st4 (by omega) (by omega))
            have hc5 : s5.executionEnv.code = powBytecode := by rw [hs5]; simp only [stCalldatasize]; exact hc4
            have he5 : s5.executionEnv = I := by rw [hs5]; simp only [stCalldatasize]; exact he4
            have hp5 : s5.machineState.pc = ⟨53⟩ := by rw [hs5]; simp only [stCalldatasize]; rw [hp4]; rfl
            have hg5 : s5.machineState.gasAvailable.toNat = g.toNat - (C + 12) := by
              rw [hs5]; simp only [stCalldatasize]; rw [toNat_sub_ofNat (by omega)]; omega
            have hk5 : s5.machineState.stack = UInt256.ofNat I.calldata.size :: ⟨4⟩ :: ⟨4⟩ :: ⟨71⟩ :: [sel] := by
              rw [hs5]; simp only [stCalldatasize, hk4, he4]
            have st5 := sub_xstep hc5 hp5 (by decide) hk5 (by simp only [List.length_cons, List.length_nil]; omega)
            by_cases g5 : g.toNat < C + 15
            · exact Or.inl (hX5.trans (stepOOG (k := k+5) (C := C+12) hg5 st5 (by omega) (by omega) (by omega)))
            · set s6 := stBinop s5 (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (⟨4⟩ :: ⟨71⟩ :: [sel]) with hs6
              have hX6 := hX5.trans (stepContinue (k := k+5) (C := C+12) hg5 st5 (by omega) (by omega))
              have hc6 : s6.executionEnv.code = powBytecode := by rw [hs6]; simp only [stBinop]; exact hc5
              have he6 : s6.executionEnv = I := by rw [hs6]; simp only [stBinop]; exact he5
              have hp6 : s6.machineState.pc = ⟨54⟩ := by rw [hs6]; simp only [stBinop]; rw [hp5]; rfl
              have hg6 : s6.machineState.gasAvailable.toNat = g.toNat - (C + 15) := by
                rw [hs6]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
              have hk6 : s6.machineState.stack = UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨71⟩ :: [sel] := by
                rw [hs6]; simp only [stBinop]
              have st6 := dup2_xstep hc6 hp6 (by decide) hk6 (by simp only [List.length_cons, List.length_nil]; omega)
              by_cases g6 : g.toNat < C + 18
              · exact Or.inl (hX6.trans (stepOOG (k := k+6) (C := C+15) hg6 st6 (by omega) (by omega) (by omega)))
              · set s7 := stSwap s6 (⟨4⟩ :: UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨71⟩ :: [sel]) with hs7
                have hX7 := hX6.trans (stepContinue (k := k+6) (C := C+15) hg6 st6 (by omega) (by omega))
                have hc7 : s7.executionEnv.code = powBytecode := by rw [hs7]; simp only [stSwap]; exact hc6
                have hp7 : s7.machineState.pc = ⟨55⟩ := by rw [hs7]; simp only [stSwap]; rw [hp6]; rfl
                have hg7 : s7.machineState.gasAvailable.toNat = g.toNat - (C + 18) := by
                  rw [hs7]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                have hk7 : s7.machineState.stack = ⟨4⟩ :: UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨71⟩ :: [sel] := by
                  rw [hs7]; simp only [stSwap]
                have st7 := add_xstep hc7 hp7 (by decide) hk7 (by simp only [List.length_cons, List.length_nil]; omega)
                by_cases g7 : g.toNat < C + 21
                · exact Or.inl (hX7.trans (stepOOG (k := k+7) (C := C+18) hg7 st7 (by omega) (by omega) (by omega)))
                · set s8 := stBinop s7 ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (⟨4⟩ :: ⟨71⟩ :: [sel]) with hs8
                  have hX8 := hX7.trans (stepContinue (k := k+7) (C := C+18) hg7 st7 (by omega) (by omega))
                  have hc8 : s8.executionEnv.code = powBytecode := by rw [hs8]; simp only [stBinop]; exact hc7
                  have he8 : s8.executionEnv = I := by rw [hs8]; simp only [stBinop]; exact he6
                  have hp8 : s8.machineState.pc = ⟨56⟩ := by rw [hs8]; simp only [stBinop]; rw [hp7]; rfl
                  have hg8 : s8.machineState.gasAvailable.toNat = g.toNat - (C + 21) := by
                    rw [hs8]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                  have hk8 : s8.machineState.stack = ((⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) :: ⟨4⟩ :: ⟨71⟩ :: [sel] := by
                    rw [hs8]; simp only [stBinop]
                  rw [add_sub4 (by omega) hszsize] at hk8
                  have st8 := swap1_xstep hc8 hp8 (by decide) hk8 (by simp only [List.length_cons, List.length_nil]; omega)
                  by_cases g8 : g.toNat < C + 24
                  · exact Or.inl (hX8.trans (stepOOG (k := k+8) (C := C+21) hg8 st8 (by omega) (by omega) (by omega)))
                  · set s9 := stSwap s8 (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ⟨71⟩ :: [sel]) with hs9
                    have hX9 := hX8.trans (stepContinue (k := k+8) (C := C+21) hg8 st8 (by omega) (by omega))
                    have hc9 : s9.executionEnv.code = powBytecode := by rw [hs9]; simp only [stSwap]; exact hc8
                    have he9 : s9.executionEnv = I := by rw [hs9]; simp only [stSwap]; exact he8
                    have hp9 : s9.machineState.pc = ⟨57⟩ := by rw [hs9]; simp only [stSwap]; rw [hp8]; rfl
                    have hg9 : s9.machineState.gasAvailable.toNat = g.toNat - (C + 24) := by
                      rw [hs9]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                    have hk9 : s9.machineState.stack = ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ⟨71⟩ :: [sel] := by rw [hs9]; simp only [stSwap]
                    have st9 := push2_xstep (argv := ⟨66⟩) hc9 hp9 (by decide) hk9 (by simp only [List.length_cons, List.length_nil]; omega)
                    by_cases g9 : g.toNat < C + 27
                    · exact Or.inl (hX9.trans (stepOOG (k := k+9) (C := C+24) hg9 st9 (by omega) (by omega) (by omega)))
                    · set s10 := stPush2 s9 ⟨66⟩ with hs10
                      have hX10 := hX9.trans (stepContinue (k := k+9) (C := C+24) hg9 st9 (by omega) (by omega))
                      have hc10 : s10.executionEnv.code = powBytecode := by rw [hs10]; simp only [stPush2]; exact hc9
                      have he10 : s10.executionEnv = I := by rw [hs10]; simp only [stPush2]; exact he9
                      have hp10 : s10.machineState.pc = ⟨60⟩ := by rw [hs10]; simp only [stPush2]; rw [hp9]; rfl
                      have hg10 : s10.machineState.gasAvailable.toNat = g.toNat - (C + 27) := by
                        rw [hs10]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                      have hk10 : s10.machineState.stack = ⟨66⟩ :: ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ⟨71⟩ :: [sel] := by rw [hs10]; simp only [stPush2, hk9]
                      have st10 := swap2_xstep hc10 hp10 (by decide) hk10 (by simp only [List.length_cons, List.length_nil]; omega)
                      by_cases g10 : g.toNat < C + 30
                      · exact Or.inl (hX10.trans (stepOOG (k := k+10) (C := C+27) hg10 st10 (by omega) (by omega) (by omega)))
                      · set s11 := stSwap s10 (UInt256.ofNat I.calldata.size :: ⟨4⟩ :: ⟨66⟩ :: ⟨71⟩ :: [sel]) with hs11
                        have hX11 := hX10.trans (stepContinue (k := k+10) (C := C+27) hg10 st10 (by omega) (by omega))
                        have hc11 : s11.executionEnv.code = powBytecode := by rw [hs11]; simp only [stSwap]; exact hc10
                        have he11 : s11.executionEnv = I := by rw [hs11]; simp only [stSwap]; exact he10
                        have hp11 : s11.machineState.pc = ⟨61⟩ := by rw [hs11]; simp only [stSwap]; rw [hp10]; rfl
                        have hg11 : s11.machineState.gasAvailable.toNat = g.toNat - (C + 30) := by
                          rw [hs11]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                        have hk11 : s11.machineState.stack = UInt256.ofNat I.calldata.size :: ⟨4⟩ :: ⟨66⟩ :: ⟨71⟩ :: [sel] := by rw [hs11]; simp only [stSwap]
                        have st11 := swap1_xstep hc11 hp11 (by decide) hk11 (by simp only [List.length_cons, List.length_nil]; omega)
                        by_cases g11 : g.toNat < C + 33
                        · exact Or.inl (hX11.trans (stepOOG (k := k+11) (C := C+30) hg11 st11 (by omega) (by omega) (by omega)))
                        · set s12 := stSwap s11 (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ⟨66⟩ :: ⟨71⟩ :: [sel]) with hs12
                          have hX12 := hX11.trans (stepContinue (k := k+11) (C := C+30) hg11 st11 (by omega) (by omega))
                          have hc12 : s12.executionEnv.code = powBytecode := by rw [hs12]; simp only [stSwap]; exact hc11
                          have he12 : s12.executionEnv = I := by rw [hs12]; simp only [stSwap]; exact he11
                          have hp12 : s12.machineState.pc = ⟨62⟩ := by rw [hs12]; simp only [stSwap]; rw [hp11]; rfl
                          have hg12 : s12.machineState.gasAvailable.toNat = g.toNat - (C + 33) := by
                            rw [hs12]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                          have hk12 : s12.machineState.stack = ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ⟨66⟩ :: ⟨71⟩ :: [sel] := by rw [hs12]; simp only [stSwap]
                          have st12 := push2_xstep (argv := ⟨207⟩) hc12 hp12 (by decide) hk12 (by simp only [List.length_cons, List.length_nil]; omega)
                          by_cases g12 : g.toNat < C + 36
                          · exact Or.inl (hX12.trans (stepOOG (k := k+12) (C := C+33) hg12 st12 (by omega) (by omega) (by omega)))
                          · set s13 := stPush2 s12 ⟨207⟩ with hs13
                            have hX13 := hX12.trans (stepContinue (k := k+12) (C := C+33) hg12 st12 (by omega) (by omega))
                            have hc13 : s13.executionEnv.code = powBytecode := by rw [hs13]; simp only [stPush2]; exact hc12
                            have he13 : s13.executionEnv = I := by rw [hs13]; simp only [stPush2]; exact he12
                            have hp13 : s13.machineState.pc = ⟨65⟩ := by rw [hs13]; simp only [stPush2]; rw [hp12]; rfl
                            have hg13 : s13.machineState.gasAvailable.toNat = g.toNat - (C + 36) := by
                              rw [hs13]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                            have hk13 : s13.machineState.stack = ⟨207⟩ :: ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ⟨66⟩ :: ⟨71⟩ :: [sel] := by rw [hs13]; simp only [stPush2, hk12]
                            have st13 := jump_xstep hc13 hp13 (by decide) hk13
                              (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by simp only [List.length_cons, List.length_nil]; omega)
                            by_cases g13 : g.toNat < C + 44
                            · exact Or.inl (hX13.trans (stepOOG (k := k+13) (C := C+36) (cost := 8) hg13 st13 (by omega) (by omega) (by omega)))
                            · set s14 := stJump s13 ⟨207⟩ (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ⟨66⟩ :: ⟨71⟩ :: [sel]) with hs14
                              have hX14 := hX13.trans (stepContinue (k := k+13) (C := C+36) (cost := 8) hg13 st13 (by omega) (by omega))
                              have hc14 : s14.executionEnv.code = powBytecode := by rw [hs14]; simp only [stJump]; exact hc13
                              have he14 : s14.executionEnv = I := by rw [hs14]; simp only [stJump]; exact he13
                              have hp14 : s14.machineState.pc = ⟨207⟩ := by rw [hs14]; simp only [stJump]
                              have hg14 : s14.machineState.gasAvailable.toNat = g.toNat - (C + 44) := by
                                rw [hs14]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                              have hk14 : s14.machineState.stack = ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ⟨66⟩ :: ⟨71⟩ :: [sel] := by rw [hs14]; simp only [stJump]
                              have hmem14 : s14.machineState.memory = s.machineState.memory := by
                                rw [hs14]; simp only [stJump]
                                rw [hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
                                simp only [stPush2, stSwap, stBinop, stCalldatasize, stDup1, stPush1, stJumpdest]
                              have haw14 : s14.machineState.activeWords = s.machineState.activeWords := by
                                rw [hs14]; simp only [stJump]
                                rw [hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
                                simp only [stPush2, stSwap, stBinop, stCalldatasize, stDup1, stPush1, stJumpdest]
                              -- call 0xcf (decoder)
                              rcases powRoutine_cf (I := I) (ret := ⟨66⟩) (R' := ⟨71⟩ :: [sel])
                                  hc14 he14 hp14 hk14 hsz36 hsz255
                                  (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
                                  (by simp only [List.length_cons, List.length_nil]; omega) hg14 (by omega) (by omega) hX14
                                with hoog | ⟨kc, Cc, sc, hXc, hcc, hpc', hkc, hgc, hkCc, hCgc, hmc, hac⟩
                              · exact Or.inl hoog
                              refine Or.inr ⟨kc, Cc, sc, hXc, hcc, hpc', hkc, hgc, hkCc, hCgc, ?_, ?_⟩
                              · rw [hmc, hmem14]
                              · rw [hac, haw14]

/-- `0x42 → 0x75`: jump to the `require(n < 256)` check (passes, since `n < 256`), initialise
    `r = 1, i = 0`, and reach the loop header `0x75` with stack `[0, 1, 0, n, 71, sel]`. -/
theorem powX_require {g : UInt256} {s0 s : State} {k C : ℕ} {n sel : UInt256} {R : List UInt256}
    (hcode : s.executionEnv.code = powBytecode) (hpc : s.machineState.pc = ⟨66⟩)
    (hstk : s.machineState.stack = n :: ⟨71⟩ :: sel :: R) (hn : n.toNat < 256)
    (hov : R.length + 10 ≤ 1024)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ (k' C' : ℕ) (s' : State),
          X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k') (D_J powBytecode ⟨0⟩) s'
        ∧ s'.executionEnv.code = powBytecode ∧ s'.machineState.pc = ⟨117⟩
        ∧ s'.machineState.stack = ⟨0⟩ :: ⟨1⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R
        ∧ s'.machineState.gasAvailable.toNat = g.toNat - C' ∧ k' ≤ C' ∧ C' ≤ g.toNat
        ∧ s'.machineState.memory = s.machineState.memory
        ∧ s'.machineState.activeWords = s.machineState.activeWords := by
  have h256 : (⟨256⟩ : UInt256).toNat = 256 := by
    show (Fin.ofNat _ 256).val = 256; simp only [Fin.ofNat]
    have : (256:ℕ) < UInt256.size := by
      have := pow_lt_size (show (8:ℕ) < 256 by norm_num); norm_num at this; exact this
    exact Nat.mod_eq_of_lt this
  have hltval : UInt256.lt n ⟨256⟩ = ⟨1⟩ := ult_one (by rw [h256]; exact hn)
  have st0 := jumpdest_xstep hcode hpc (by decide) (by rw [hstk]; simp only [List.length_cons]; omega)
  by_cases g0 : g.toNat < C + 1
  · exact Or.inl (hX.trans (stepOOG hgas st0 hk hC (by omega)))
  · set s1 := stJumpdest s with hs1
    have hX1 := hX.trans (stepContinue (k := k) (C := C) hgas st0 hk (by omega))
    have hc1 : s1.executionEnv.code = powBytecode := by rw [hs1]; simp only [stJumpdest]; exact hcode
    have hp1 : s1.machineState.pc = ⟨67⟩ := by rw [hs1]; simp only [stJumpdest]; rw [hpc]; rfl
    have hg1 : s1.machineState.gasAvailable.toNat = g.toNat - (C + 1) := by
      rw [hs1]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
    have hk1 : s1.machineState.stack = n :: ⟨71⟩ :: sel :: R := by rw [hs1]; simp only [stJumpdest]; exact hstk
    have st1 := push2_xstep (argv := ⟨93⟩) hc1 hp1 (by decide) hk1 (by first | (simp only [List.length_cons]; omega) | omega)
    by_cases g1 : g.toNat < C + 4
    · exact Or.inl (hX1.trans (stepOOG (k := k+1) (C := C+1) hg1 st1 (by omega) (by omega) (by omega)))
    · set s2 := stPush2 s1 ⟨93⟩ with hs2
      have hX2 := hX1.trans (stepContinue (k := k+1) (C := C+1) hg1 st1 (by omega) (by omega))
      have hc2 : s2.executionEnv.code = powBytecode := by rw [hs2]; simp only [stPush2]; exact hc1
      have hp2 : s2.machineState.pc = ⟨70⟩ := by rw [hs2]; simp only [stPush2]; rw [hp1]; rfl
      have hg2 : s2.machineState.gasAvailable.toNat = g.toNat - (C + 4) := by
        rw [hs2]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
      have hk2 : s2.machineState.stack = ⟨93⟩ :: n :: ⟨71⟩ :: sel :: R := by rw [hs2]; simp only [stPush2, hk1]
      have st2 := jump_xstep hc2 hp2 (by decide) hk2
        (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by first | (simp only [List.length_cons]; omega) | omega)
      by_cases g2 : g.toNat < C + 12
      · exact Or.inl (hX2.trans (stepOOG (k := k+2) (C := C+4) (cost := 8) hg2 st2 (by omega) (by omega) (by omega)))
      · set s3 := stJump s2 ⟨93⟩ (n :: ⟨71⟩ :: sel :: R) with hs3
        have hX3 := hX2.trans (stepContinue (k := k+2) (C := C+4) (cost := 8) hg2 st2 (by omega) (by omega))
        have hc3 : s3.executionEnv.code = powBytecode := by rw [hs3]; simp only [stJump]; exact hc2
        have hp3 : s3.machineState.pc = ⟨93⟩ := by rw [hs3]; simp only [stJump]
        have hg3 : s3.machineState.gasAvailable.toNat = g.toNat - (C + 12) := by
          rw [hs3]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
        have hk3 : s3.machineState.stack = n :: ⟨71⟩ :: sel :: R := by rw [hs3]; simp only [stJump]
        have st3 := jumpdest_xstep hc3 hp3 (by decide) (by rw [hk3]; simp only [List.length_cons]; omega)
        by_cases g3 : g.toNat < C + 13
        · exact Or.inl (hX3.trans (stepOOG (k := k+3) (C := C+12) hg3 st3 (by omega) (by omega) (by omega)))
        · set s4 := stJumpdest s3 with hs4
          have hX4 := hX3.trans (stepContinue (k := k+3) (C := C+12) hg3 st3 (by omega) (by omega))
          have hc4 : s4.executionEnv.code = powBytecode := by rw [hs4]; simp only [stJumpdest]; exact hc3
          have hp4 : s4.machineState.pc = ⟨94⟩ := by rw [hs4]; simp only [stJumpdest]; rw [hp3]; rfl
          have hg4 : s4.machineState.gasAvailable.toNat = g.toNat - (C + 13) := by
            rw [hs4]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
          have hk4 : s4.machineState.stack = n :: ⟨71⟩ :: sel :: R := by rw [hs4]; simp only [stJumpdest]; exact hk3
          have st4 := push0_xstep hc4 hp4 (by decide) hk4 (by first | (simp only [List.length_cons]; omega) | omega)
          by_cases g4 : g.toNat < C + 15
          · exact Or.inl (hX4.trans (stepOOG (k := k+4) (C := C+13) hg4 st4 (by omega) (by omega) (by omega)))
          · set s5 := stPush0 s4 with hs5
            have hX5 := hX4.trans (stepContinue (k := k+4) (C := C+13) hg4 st4 (by omega) (by omega))
            have hc5 : s5.executionEnv.code = powBytecode := by rw [hs5]; simp only [stPush0]; exact hc4
            have hp5 : s5.machineState.pc = ⟨95⟩ := by rw [hs5]; simp only [stPush0]; rw [hp4]; rfl
            have hg5 : s5.machineState.gasAvailable.toNat = g.toNat - (C + 15) := by
              rw [hs5]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
            have hk5 : s5.machineState.stack = ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R := by rw [hs5]; simp only [stPush0, hk4]
            have st5 := push2_xstep (argv := ⟨256⟩) hc5 hp5 (by decide) hk5 (by first | (simp only [List.length_cons]; omega) | omega)
            by_cases g5 : g.toNat < C + 18
            · exact Or.inl (hX5.trans (stepOOG (k := k+5) (C := C+15) hg5 st5 (by omega) (by omega) (by omega)))
            · set s6 := stPush2 s5 ⟨256⟩ with hs6
              have hX6 := hX5.trans (stepContinue (k := k+5) (C := C+15) hg5 st5 (by omega) (by omega))
              have hc6 : s6.executionEnv.code = powBytecode := by rw [hs6]; simp only [stPush2]; exact hc5
              have hp6 : s6.machineState.pc = ⟨98⟩ := by rw [hs6]; simp only [stPush2]; rw [hp5]; rfl
              have hg6 : s6.machineState.gasAvailable.toNat = g.toNat - (C + 18) := by
                rw [hs6]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
              have hk6 : s6.machineState.stack = ⟨256⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R := by rw [hs6]; simp only [stPush2, hk5]
              have st6 := dup3_xstep hc6 hp6 (by decide) hk6 (by first | (simp only [List.length_cons]; omega) | omega)
              by_cases g6 : g.toNat < C + 21
              · exact Or.inl (hX6.trans (stepOOG (k := k+6) (C := C+18) hg6 st6 (by omega) (by omega) (by omega)))
              · set s7 := stSwap s6 (n :: ⟨256⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R) with hs7
                have hX7 := hX6.trans (stepContinue (k := k+6) (C := C+18) hg6 st6 (by omega) (by omega))
                have hc7 : s7.executionEnv.code = powBytecode := by rw [hs7]; simp only [stSwap]; exact hc6
                have hp7 : s7.machineState.pc = ⟨99⟩ := by rw [hs7]; simp only [stSwap]; rw [hp6]; rfl
                have hg7 : s7.machineState.gasAvailable.toNat = g.toNat - (C + 21) := by
                  rw [hs7]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                have hk7 : s7.machineState.stack = n :: ⟨256⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R := by rw [hs7]; simp only [stSwap]
                have st7 := lt_xstep hc7 hp7 (by decide) hk7 (by first | (simp only [List.length_cons]; omega) | omega)
                by_cases g7 : g.toNat < C + 24
                · exact Or.inl (hX7.trans (stepOOG (k := k+7) (C := C+21) hg7 st7 (by omega) (by omega) (by omega)))
                · set s8 := stBinop s7 (UInt256.lt n ⟨256⟩) (⟨0⟩ :: n :: ⟨71⟩ :: sel :: R) with hs8
                  have hX8 := hX7.trans (stepContinue (k := k+7) (C := C+21) hg7 st7 (by omega) (by omega))
                  have hc8 : s8.executionEnv.code = powBytecode := by rw [hs8]; simp only [stBinop]; exact hc7
                  have hp8 : s8.machineState.pc = ⟨100⟩ := by rw [hs8]; simp only [stBinop]; rw [hp7]; rfl
                  have hg8 : s8.machineState.gasAvailable.toNat = g.toNat - (C + 24) := by
                    rw [hs8]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                  have hk8 : s8.machineState.stack = ⟨1⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R := by
                    rw [hs8]; simp only [stBinop]; rw [hltval]
                  have st8 := push2_xstep (argv := ⟨107⟩) hc8 hp8 (by decide) hk8 (by first | (simp only [List.length_cons]; omega) | omega)
                  by_cases g8 : g.toNat < C + 27
                  · exact Or.inl (hX8.trans (stepOOG (k := k+8) (C := C+24) hg8 st8 (by omega) (by omega) (by omega)))
                  · set s9 := stPush2 s8 ⟨107⟩ with hs9
                    have hX9 := hX8.trans (stepContinue (k := k+8) (C := C+24) hg8 st8 (by omega) (by omega))
                    have hc9 : s9.executionEnv.code = powBytecode := by rw [hs9]; simp only [stPush2]; exact hc8
                    have hp9 : s9.machineState.pc = ⟨103⟩ := by rw [hs9]; simp only [stPush2]; rw [hp8]; rfl
                    have hg9 : s9.machineState.gasAvailable.toNat = g.toNat - (C + 27) := by
                      rw [hs9]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                    have hk9 : s9.machineState.stack = ⟨107⟩ :: ⟨1⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R := by rw [hs9]; simp only [stPush2, hk8]
                    have st9 := jumpi_t_xstep hc9 hp9 (by decide) hk9 (by decide)
                      (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by first | (simp only [List.length_cons]; omega) | omega)
                    by_cases g9 : g.toNat < C + 37
                    · exact Or.inl (hX9.trans (stepOOG (k := k+9) (C := C+27) (cost := 10) hg9 st9 (by omega) (by omega) (by omega)))
                    · set s10 := stJumpiT s9 ⟨107⟩ (⟨0⟩ :: n :: ⟨71⟩ :: sel :: R) with hs10
                      have hX10 := hX9.trans (stepContinue (k := k+9) (C := C+27) (cost := 10) hg9 st9 (by omega) (by omega))
                      have hc10 : s10.executionEnv.code = powBytecode := by rw [hs10]; simp only [stJumpiT]; exact hc9
                      have hp10 : s10.machineState.pc = ⟨107⟩ := by rw [hs10]; simp only [stJumpiT]
                      have hg10 : s10.machineState.gasAvailable.toNat = g.toNat - (C + 37) := by
                        rw [hs10]; simp only [stJumpiT]; rw [toNat_sub_ofNat (by omega)]; omega
                      have hk10 : s10.machineState.stack = ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R := by rw [hs10]; simp only [stJumpiT]
                      have st10 := jumpdest_xstep hc10 hp10 (by decide) (by rw [hk10]; simp only [List.length_cons]; omega)
                      by_cases g10 : g.toNat < C + 38
                      · exact Or.inl (hX10.trans (stepOOG (k := k+10) (C := C+37) hg10 st10 (by omega) (by omega) (by omega)))
                      · set s11 := stJumpdest s10 with hs11
                        have hX11 := hX10.trans (stepContinue (k := k+10) (C := C+37) hg10 st10 (by omega) (by omega))
                        have hc11 : s11.executionEnv.code = powBytecode := by rw [hs11]; simp only [stJumpdest]; exact hc10
                        have hp11 : s11.machineState.pc = ⟨108⟩ := by rw [hs11]; simp only [stJumpdest]; rw [hp10]; rfl
                        have hg11 : s11.machineState.gasAvailable.toNat = g.toNat - (C + 38) := by
                          rw [hs11]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                        have hk11 : s11.machineState.stack = ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R := by rw [hs11]; simp only [stJumpdest]; exact hk10
                        have st11 := push0_xstep hc11 hp11 (by decide) hk11 (by first | (simp only [List.length_cons]; omega) | omega)
                        by_cases g11 : g.toNat < C + 40
                        · exact Or.inl (hX11.trans (stepOOG (k := k+11) (C := C+38) hg11 st11 (by omega) (by omega) (by omega)))
                        · set s12 := stPush0 s11 with hs12
                          have hX12 := hX11.trans (stepContinue (k := k+11) (C := C+38) hg11 st11 (by omega) (by omega))
                          have hc12 : s12.executionEnv.code = powBytecode := by rw [hs12]; simp only [stPush0]; exact hc11
                          have hp12 : s12.machineState.pc = ⟨109⟩ := by rw [hs12]; simp only [stPush0]; rw [hp11]; rfl
                          have hg12 : s12.machineState.gasAvailable.toNat = g.toNat - (C + 40) := by
                            rw [hs12]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                          have hk12 : s12.machineState.stack = ⟨0⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R := by rw [hs12]; simp only [stPush0, hk11]
                          have st12 := push1_xstep (argv := ⟨1⟩) hc12 hp12 (by decide) hk12 (by first | (simp only [List.length_cons]; omega) | omega)
                          by_cases g12 : g.toNat < C + 43
                          · exact Or.inl (hX12.trans (stepOOG (k := k+12) (C := C+40) hg12 st12 (by omega) (by omega) (by omega)))
                          · set s13 := stPush1 s12 ⟨1⟩ with hs13
                            have hX13 := hX12.trans (stepContinue (k := k+12) (C := C+40) hg12 st12 (by omega) (by omega))
                            have hc13 : s13.executionEnv.code = powBytecode := by rw [hs13]; simp only [stPush1]; exact hc12
                            have hp13 : s13.machineState.pc = ⟨111⟩ := by rw [hs13]; simp only [stPush1]; rw [hp12]; rfl
                            have hg13 : s13.machineState.gasAvailable.toNat = g.toNat - (C + 43) := by
                              rw [hs13]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                            have hk13 : s13.machineState.stack = ⟨1⟩ :: ⟨0⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R := by rw [hs13]; simp only [stPush1, hk12]
                            have st13 := swap1_xstep hc13 hp13 (by decide) hk13 (by first | (simp only [List.length_cons]; omega) | omega)
                            by_cases g13 : g.toNat < C + 46
                            · exact Or.inl (hX13.trans (stepOOG (k := k+13) (C := C+43) hg13 st13 (by omega) (by omega) (by omega)))
                            · set s14 := stSwap s13 (⟨0⟩ :: ⟨1⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R) with hs14
                              have hX14 := hX13.trans (stepContinue (k := k+13) (C := C+43) hg13 st13 (by omega) (by omega))
                              have hc14 : s14.executionEnv.code = powBytecode := by rw [hs14]; simp only [stSwap]; exact hc13
                              have hp14 : s14.machineState.pc = ⟨112⟩ := by rw [hs14]; simp only [stSwap]; rw [hp13]; rfl
                              have hg14 : s14.machineState.gasAvailable.toNat = g.toNat - (C + 46) := by
                                rw [hs14]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                              have hk14 : s14.machineState.stack = ⟨0⟩ :: ⟨1⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R := by rw [hs14]; simp only [stSwap]
                              have st14 := pop_xstep hc14 hp14 (by decide) hk14 (by first | (simp only [List.length_cons]; omega) | omega)
                              by_cases g14 : g.toNat < C + 48
                              · exact Or.inl (hX14.trans (stepOOG (k := k+14) (C := C+46) hg14 st14 (by omega) (by omega) (by omega)))
                              · set s15 := stPop s14 (⟨1⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R) with hs15
                                have hX15 := hX14.trans (stepContinue (k := k+14) (C := C+46) hg14 st14 (by omega) (by omega))
                                have hc15 : s15.executionEnv.code = powBytecode := by rw [hs15]; simp only [stPop]; exact hc14
                                have hp15 : s15.machineState.pc = ⟨113⟩ := by rw [hs15]; simp only [stPop]; rw [hp14]; rfl
                                have hg15 : s15.machineState.gasAvailable.toNat = g.toNat - (C + 48) := by
                                  rw [hs15]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                have hk15 : s15.machineState.stack = ⟨1⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R := by rw [hs15]; simp only [stPop]
                                have st15 := push0_xstep hc15 hp15 (by decide) hk15 (by first | (simp only [List.length_cons]; omega) | omega)
                                by_cases g15 : g.toNat < C + 50
                                · exact Or.inl (hX15.trans (stepOOG (k := k+15) (C := C+48) hg15 st15 (by omega) (by omega) (by omega)))
                                · set s16 := stPush0 s15 with hs16
                                  have hX16 := hX15.trans (stepContinue (k := k+15) (C := C+48) hg15 st15 (by omega) (by omega))
                                  have hc16 : s16.executionEnv.code = powBytecode := by rw [hs16]; simp only [stPush0]; exact hc15
                                  have hp16 : s16.machineState.pc = ⟨114⟩ := by rw [hs16]; simp only [stPush0]; rw [hp15]; rfl
                                  have hg16 : s16.machineState.gasAvailable.toNat = g.toNat - (C + 50) := by
                                    rw [hs16]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                                  have hk16 : s16.machineState.stack = ⟨0⟩ :: ⟨1⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R := by rw [hs16]; simp only [stPush0, hk15]
                                  have st16 := push0_xstep hc16 hp16 (by decide) hk16 (by first | (simp only [List.length_cons]; omega) | omega)
                                  by_cases g16 : g.toNat < C + 52
                                  · exact Or.inl (hX16.trans (stepOOG (k := k+16) (C := C+50) hg16 st16 (by omega) (by omega) (by omega)))
                                  · set s17 := stPush0 s16 with hs17
                                    have hX17 := hX16.trans (stepContinue (k := k+16) (C := C+50) hg16 st16 (by omega) (by omega))
                                    have hc17 : s17.executionEnv.code = powBytecode := by rw [hs17]; simp only [stPush0]; exact hc16
                                    have hp17 : s17.machineState.pc = ⟨115⟩ := by rw [hs17]; simp only [stPush0]; rw [hp16]; rfl
                                    have hg17 : s17.machineState.gasAvailable.toNat = g.toNat - (C + 52) := by
                                      rw [hs17]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                                    have hk17 : s17.machineState.stack = ⟨0⟩ :: ⟨0⟩ :: ⟨1⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R := by rw [hs17]; simp only [stPush0, hk16]
                                    have st17 := swap1_xstep hc17 hp17 (by decide) hk17 (by first | (simp only [List.length_cons]; omega) | omega)
                                    by_cases g17 : g.toNat < C + 55
                                    · exact Or.inl (hX17.trans (stepOOG (k := k+17) (C := C+52) hg17 st17 (by omega) (by omega) (by omega)))
                                    · set s18 := stSwap s17 (⟨0⟩ :: ⟨0⟩ :: ⟨1⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R) with hs18
                                      have hX18 := hX17.trans (stepContinue (k := k+17) (C := C+52) hg17 st17 (by omega) (by omega))
                                      have hc18 : s18.executionEnv.code = powBytecode := by rw [hs18]; simp only [stSwap]; exact hc17
                                      have hp18 : s18.machineState.pc = ⟨116⟩ := by rw [hs18]; simp only [stSwap]; rw [hp17]; rfl
                                      have hg18 : s18.machineState.gasAvailable.toNat = g.toNat - (C + 55) := by
                                        rw [hs18]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                      have hk18 : s18.machineState.stack = ⟨0⟩ :: ⟨0⟩ :: ⟨1⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R := by rw [hs18]; simp only [stSwap]
                                      have st18 := pop_xstep hc18 hp18 (by decide) hk18 (by first | (simp only [List.length_cons]; omega) | omega)
                                      by_cases g18 : g.toNat < C + 57
                                      · exact Or.inl (hX18.trans (stepOOG (k := k+18) (C := C+55) hg18 st18 (by omega) (by omega) (by omega)))
                                      · set s19 := stPop s18 (⟨0⟩ :: ⟨1⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R) with hs19
                                        have hX19 := hX18.trans (stepContinue (k := k+18) (C := C+55) hg18 st18 (by omega) (by omega))
                                        refine Or.inr ⟨k+19, C+57, s19, ?_, ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_⟩
                                        · have he : g.toNat + 1 - (k + 18 + 1) = g.toNat + 1 - (k + 19) := by omega
                                          rw [← he]; exact hX19
                                        · rw [hs19]; simp only [stPop]; exact hc18
                                        · rw [hs19]; simp only [stPop]; rw [hp18]; rfl
                                        · rw [hs19]; simp only [stPop]
                                        · rw [hs19]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                        · rw [hs19]; simp only [stPop]
                                          rw [hs18, hs17, hs16, hs15, hs14, hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
                                          simp only [stPop, stSwap, stPush0, stPush1, stPush2, stBinop, stJumpiT, stJumpdest, stJump]
                                        · rw [hs19]; simp only [stPop]
                                          rw [hs18, hs17, hs16, hs15, hs14, hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
                                          simp only [stPop, stSwap, stPush0, stPush1, stPush2, stBinop, stJumpiT, stJumpdest, stJump]

/-- Loop exit `0x8e → 0x47`: drop the loop scratch, keep the result `val = 2^n`, and jump to the
    encoder at the saved return address `ret`.  `[a, val, c, d, ret] ++ Rt → at ret, val :: Rt`. -/
theorem powX_exit {g : UInt256} {s0 s : State} {k C : ℕ} {a val c d ret : UInt256} {Rt : List UInt256}
    (hcode : s.executionEnv.code = powBytecode) (hpc : s.machineState.pc = ⟨142⟩)
    (hstk : s.machineState.stack = a :: val :: c :: d :: ret :: Rt)
    (hret : (D_J powBytecode ⟨0⟩).contains ret = true) (hov : Rt.length + 7 ≤ 1024)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ (k' C' : ℕ) (s' : State),
          X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k') (D_J powBytecode ⟨0⟩) s'
        ∧ s'.executionEnv.code = powBytecode ∧ s'.machineState.pc = ret
        ∧ s'.machineState.stack = val :: Rt
        ∧ s'.machineState.gasAvailable.toNat = g.toNat - C' ∧ k' ≤ C' ∧ C' ≤ g.toNat
        ∧ s'.machineState.memory = s.machineState.memory
        ∧ s'.machineState.activeWords = s.machineState.activeWords := by
  have st0 := jumpdest_xstep hcode hpc (by decide) (by rw [hstk]; simp only [List.length_cons]; omega)
  by_cases g0 : g.toNat < C + 1
  · exact Or.inl (hX.trans (stepOOG hgas st0 hk hC (by omega)))
  · set s1 := stJumpdest s with hs1
    have hX1 := hX.trans (stepContinue (k := k) (C := C) hgas st0 hk (by omega))
    have hc1 : s1.executionEnv.code = powBytecode := by rw [hs1]; simp only [stJumpdest]; exact hcode
    have hp1 : s1.machineState.pc = ⟨143⟩ := by rw [hs1]; simp only [stJumpdest]; rw [hpc]; rfl
    have hg1 : s1.machineState.gasAvailable.toNat = g.toNat - (C + 1) := by
      rw [hs1]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
    have hk1 : s1.machineState.stack = a :: val :: c :: d :: ret :: Rt := by rw [hs1]; simp only [stJumpdest]; exact hstk
    have st1 := dup2_xstep hc1 hp1 (by decide) hk1 (by first | (simp only [List.length_cons]; omega) | omega)
    by_cases g1 : g.toNat < C + 4
    · exact Or.inl (hX1.trans (stepOOG (k := k+1) (C := C+1) hg1 st1 (by omega) (by omega) (by omega)))
    · set s2 := stSwap s1 (val :: a :: val :: c :: d :: ret :: Rt) with hs2
      have hX2 := hX1.trans (stepContinue (k := k+1) (C := C+1) hg1 st1 (by omega) (by omega))
      have hc2 : s2.executionEnv.code = powBytecode := by rw [hs2]; simp only [stSwap]; exact hc1
      have hp2 : s2.machineState.pc = ⟨144⟩ := by rw [hs2]; simp only [stSwap]; rw [hp1]; rfl
      have hg2 : s2.machineState.gasAvailable.toNat = g.toNat - (C + 4) := by
        rw [hs2]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
      have hk2 : s2.machineState.stack = val :: a :: val :: c :: d :: ret :: Rt := by rw [hs2]; simp only [stSwap]
      have st2 := swap3_xstep hc2 hp2 (by decide) hk2 (by first | (simp only [List.length_cons]; omega) | omega)
      by_cases g2 : g.toNat < C + 7
      · exact Or.inl (hX2.trans (stepOOG (k := k+2) (C := C+4) hg2 st2 (by omega) (by omega) (by omega)))
      · set s3 := stSwap s2 (c :: a :: val :: val :: d :: ret :: Rt) with hs3
        have hX3 := hX2.trans (stepContinue (k := k+2) (C := C+4) hg2 st2 (by omega) (by omega))
        have hc3 : s3.executionEnv.code = powBytecode := by rw [hs3]; simp only [stSwap]; exact hc2
        have hp3 : s3.machineState.pc = ⟨145⟩ := by rw [hs3]; simp only [stSwap]; rw [hp2]; rfl
        have hg3 : s3.machineState.gasAvailable.toNat = g.toNat - (C + 7) := by
          rw [hs3]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
        have hk3 : s3.machineState.stack = c :: a :: val :: val :: d :: ret :: Rt := by rw [hs3]; simp only [stSwap]
        have st3 := pop_xstep hc3 hp3 (by decide) hk3 (by first | (simp only [List.length_cons]; omega) | omega)
        by_cases g3 : g.toNat < C + 9
        · exact Or.inl (hX3.trans (stepOOG (k := k+3) (C := C+7) hg3 st3 (by omega) (by omega) (by omega)))
        · set s4 := stPop s3 (a :: val :: val :: d :: ret :: Rt) with hs4
          have hX4 := hX3.trans (stepContinue (k := k+3) (C := C+7) hg3 st3 (by omega) (by omega))
          have hc4 : s4.executionEnv.code = powBytecode := by rw [hs4]; simp only [stPop]; exact hc3
          have hp4 : s4.machineState.pc = ⟨146⟩ := by rw [hs4]; simp only [stPop]; rw [hp3]; rfl
          have hg4 : s4.machineState.gasAvailable.toNat = g.toNat - (C + 9) := by
            rw [hs4]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
          have hk4 : s4.machineState.stack = a :: val :: val :: d :: ret :: Rt := by rw [hs4]; simp only [stPop]
          have st4 := pop_xstep hc4 hp4 (by decide) hk4 (by first | (simp only [List.length_cons]; omega) | omega)
          by_cases g4 : g.toNat < C + 11
          · exact Or.inl (hX4.trans (stepOOG (k := k+4) (C := C+9) hg4 st4 (by omega) (by omega) (by omega)))
          · set s5 := stPop s4 (val :: val :: d :: ret :: Rt) with hs5
            have hX5 := hX4.trans (stepContinue (k := k+4) (C := C+9) hg4 st4 (by omega) (by omega))
            have hc5 : s5.executionEnv.code = powBytecode := by rw [hs5]; simp only [stPop]; exact hc4
            have hp5 : s5.machineState.pc = ⟨147⟩ := by rw [hs5]; simp only [stPop]; rw [hp4]; rfl
            have hg5 : s5.machineState.gasAvailable.toNat = g.toNat - (C + 11) := by
              rw [hs5]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
            have hk5 : s5.machineState.stack = val :: val :: d :: ret :: Rt := by rw [hs5]; simp only [stPop]
            have st5 := pop_xstep hc5 hp5 (by decide) hk5 (by first | (simp only [List.length_cons]; omega) | omega)
            by_cases g5 : g.toNat < C + 13
            · exact Or.inl (hX5.trans (stepOOG (k := k+5) (C := C+11) hg5 st5 (by omega) (by omega) (by omega)))
            · set s6 := stPop s5 (val :: d :: ret :: Rt) with hs6
              have hX6 := hX5.trans (stepContinue (k := k+5) (C := C+11) hg5 st5 (by omega) (by omega))
              have hc6 : s6.executionEnv.code = powBytecode := by rw [hs6]; simp only [stPop]; exact hc5
              have hp6 : s6.machineState.pc = ⟨148⟩ := by rw [hs6]; simp only [stPop]; rw [hp5]; rfl
              have hg6 : s6.machineState.gasAvailable.toNat = g.toNat - (C + 13) := by
                rw [hs6]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
              have hk6 : s6.machineState.stack = val :: d :: ret :: Rt := by rw [hs6]; simp only [stPop]
              have st6 := swap2_xstep hc6 hp6 (by decide) hk6 (by omega)
              by_cases g6 : g.toNat < C + 16
              · exact Or.inl (hX6.trans (stepOOG (k := k+6) (C := C+13) hg6 st6 (by omega) (by omega) (by omega)))
              · set s7 := stSwap s6 (ret :: d :: val :: Rt) with hs7
                have hX7 := hX6.trans (stepContinue (k := k+6) (C := C+13) hg6 st6 (by omega) (by omega))
                have hc7 : s7.executionEnv.code = powBytecode := by rw [hs7]; simp only [stSwap]; exact hc6
                have hp7 : s7.machineState.pc = ⟨149⟩ := by rw [hs7]; simp only [stSwap]; rw [hp6]; rfl
                have hg7 : s7.machineState.gasAvailable.toNat = g.toNat - (C + 16) := by
                  rw [hs7]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                have hk7 : s7.machineState.stack = ret :: d :: val :: Rt := by rw [hs7]; simp only [stSwap]
                have st7 := swap1_xstep hc7 hp7 (by decide) hk7 (by first | (simp only [List.length_cons]; omega) | omega)
                by_cases g7 : g.toNat < C + 19
                · exact Or.inl (hX7.trans (stepOOG (k := k+7) (C := C+16) hg7 st7 (by omega) (by omega) (by omega)))
                · set s8 := stSwap s7 (d :: ret :: val :: Rt) with hs8
                  have hX8 := hX7.trans (stepContinue (k := k+7) (C := C+16) hg7 st7 (by omega) (by omega))
                  have hc8 : s8.executionEnv.code = powBytecode := by rw [hs8]; simp only [stSwap]; exact hc7
                  have hp8 : s8.machineState.pc = ⟨150⟩ := by rw [hs8]; simp only [stSwap]; rw [hp7]; rfl
                  have hg8 : s8.machineState.gasAvailable.toNat = g.toNat - (C + 19) := by
                    rw [hs8]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                  have hk8 : s8.machineState.stack = d :: ret :: val :: Rt := by rw [hs8]; simp only [stSwap]
                  have st8 := pop_xstep hc8 hp8 (by decide) hk8 (by first | (simp only [List.length_cons]; omega) | omega)
                  by_cases g8 : g.toNat < C + 21
                  · exact Or.inl (hX8.trans (stepOOG (k := k+8) (C := C+19) hg8 st8 (by omega) (by omega) (by omega)))
                  · set s9 := stPop s8 (ret :: val :: Rt) with hs9
                    have hX9 := hX8.trans (stepContinue (k := k+8) (C := C+19) hg8 st8 (by omega) (by omega))
                    have hc9 : s9.executionEnv.code = powBytecode := by rw [hs9]; simp only [stPop]; exact hc8
                    have hp9 : s9.machineState.pc = ⟨151⟩ := by rw [hs9]; simp only [stPop]; rw [hp8]; rfl
                    have hg9 : s9.machineState.gasAvailable.toNat = g.toNat - (C + 21) := by
                      rw [hs9]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                    have hk9 : s9.machineState.stack = ret :: val :: Rt := by rw [hs9]; simp only [stPop]
                    have st9 := jump_xstep hc9 hp9 (by decide) hk9 hret (by first | (simp only [List.length_cons]; omega) | omega)
                    by_cases g9 : g.toNat < C + 29
                    · exact Or.inl (hX9.trans (stepOOG (k := k+9) (C := C+21) (cost := 8) hg9 st9 (by omega) (by omega) (by omega)))
                    · set s10 := stJump s9 ret (val :: Rt) with hs10
                      have hX10 := hX9.trans (stepContinue (k := k+9) (C := C+21) (cost := 8) hg9 st9 (by omega) (by omega))
                      refine Or.inr ⟨k+10, C+29, s10, ?_, ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_⟩
                      · have he : g.toNat + 1 - (k + 9 + 1) = g.toNat + 1 - (k + 10) := by omega
                        rw [← he]; exact hX10
                      · rw [hs10]; simp only [stJump]; exact hc9
                      · rw [hs10]; simp only [stJump]
                      · rw [hs10]; simp only [stJump]
                      · rw [hs10]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                      · rw [hs10]; simp only [stJump]
                        rw [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
                        simp only [stPop, stSwap, stJumpdest]
                      · rw [hs10]; simp only [stJump]
                        rw [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
                        simp only [stPop, stSwap, stJumpdest]

/-! ## Encoder memory: the result word stored at `0x80` -/

/-- Memory after solc stores the return word `val` at `0x80` (over the free-pointer memory). -/
noncomputable def powMem2 (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 solcFreePtrMem 128 32

theorem powMem2_eq (val : UInt256) :
    powMem2 val = (solcFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat 32)) ++ UInt256.toByteArray val := by
  rw [powMem2, toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; omega)
        (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))]
  norm_num [solcFreePtrMem_size]

theorem powMem2_size (val : UInt256) : (powMem2 val).size = 160 := by
  rw [powMem2_eq, ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
      zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem solcFreePtrMem_pad_size :
    (solcFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat 32)).size = 128 := by
  rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size _ (by norm_num)]

theorem powMem2_read64 (val : UInt256) :
    (powMem2 val).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := powMem2_size val; omega), powMem2_eq,
      extract_append_left _ _ _ _ (by have := solcFreePtrMem_pad_size; omega),
      extract_append_left _ _ _ _ (by have := solcFreePtrMem_size; omega),
      ← readWithPadding_eq_extract _ _ (by have := solcFreePtrMem_size; omega), solcFreePtrMem_read64]

theorem powMem2_read128 (val : UInt256) :
    (powMem2 val).readWithPadding 128 32 = UInt256.toByteArray val := by
  rw [readWithPadding_eq_extract _ _ (by have := powMem2_size val; omega), powMem2_eq,
      extract_append_right' _ _ _ _ (by have := solcFreePtrMem_pad_size; omega)
        (by have := solcFreePtrMem_pad_size; have := toByteArray_size val; omega)]

/-- `(ofNat c).toNat = c` for in-range `c`. -/
theorem ulit_toNat' (c : ℕ) (h : c < UInt256.size) : (UInt256.ofNat c).toNat = c := by
  show (Fin.ofNat _ c).val = c; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt h

theorem u0 : (⟨0⟩ : UInt256).toNat = 0 := by
  show (Fin.ofNat _ 0).val = 0; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))
theorem u32 : (⟨32⟩ : UInt256).toNat = 32 := by
  show (Fin.ofNat _ 32).val = 32; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))
theorem u128 : (⟨128⟩ : UInt256).toNat = 128 := by
  show (Fin.ofNat _ 128).val = 128; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))

/-- `ADD` of two literals (toNat). -/
theorem add128_0_toNat : ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 := by
  rw [uadd_toNat, u128, u0, Nat.add_zero, Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))]
theorem add128_32_toNat : ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 := by
  rw [uadd_toNat, u128, u32]; show (160:ℕ) % UInt256.size = 160; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))

/-- General `SUB` toNat (no wrap). -/
theorem usub_toNat {a b : UInt256} (h : b.toNat ≤ a.toNat) :
    (UInt256.sub a b).toNat = a.toNat - b.toNat := by
  show (a.val - b.val).val = a.toNat - b.toNat
  rw [Fin.coe_sub_iff_le.mpr (by rw [Fin.le_def]; exact h)]; rfl

theorem sub_ret32_toNat : (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 := by
  rw [usub_toNat (by rw [add128_32_toNat, u128]; omega), add128_32_toNat, u128]

theorem u160 : (⟨160⟩ : UInt256).toNat = 160 := by
  show (Fin.ofNat _ 160).val = 160; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))
theorem add128_0 : ((⟨128⟩ : UInt256) + ⟨0⟩) = ⟨128⟩ := u256_inj (by rw [add128_0_toNat, u128])
theorem add128_32 : ((⟨128⟩ : UInt256) + ⟨32⟩) = ⟨160⟩ := u256_inj (by rw [add128_32_toNat, u160])
theorem sub_160_128 : UInt256.sub (⟨160⟩ : UInt256) ⟨128⟩ = ⟨32⟩ :=
  u256_inj (by rw [usub_toNat (by rw [u160, u128]; omega), u160, u128, u32])

theorem ofNat128 : UInt256.ofNat 128 = ⟨128⟩ :=
  u256_inj (by rw [ulit_toNat' 128 (lt_size_of_lt256 (by norm_num)), u128])

/-! ## Encoder `0x47 → RETURN` — the ABI-encode-and-return tail (**proved**)

`pc 71` ABI-encodes the return word `val = 2^n` into `mem[0x80 .. 0xa0]` (via the internal
`abi_encode` routines at `0x109`/`0xfa`/`0x9c`) and `RETURN`s those 32 bytes.  47 instructions
plus one nested `powRoutine_9c` call.  Concludes the success result `toByteArray val`. -/
set_option maxHeartbeats 4000000 in
theorem powX_encode {g : UInt256} {s0 s : State} {k C : ℕ} {val : UInt256} {Rt : List UInt256}
    (hcode : s.executionEnv.code = powBytecode) (hpc : s.machineState.pc = ⟨71⟩)
    (hstk : s.machineState.stack = val :: Rt)
    (hmem : s.machineState.memory = solcFreePtrMem)
    (haw : s.machineState.activeWords = UInt256.ofNat 3)
    (hov : Rt.length + 11 ≤ 1024)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ s', X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0
                = .ok (.success s' (UInt256.toByteArray val)) := by
  -- step 1: JUMPDEST @71
  have st1 := jumpdest_xstep hcode hpc (by decide) (by rw [hstk]; simp only [List.length_cons]; omega)
  by_cases g1 : g.toNat < C + 1
  · exact Or.inl (hX.trans (stepOOG (k := k) (C := C) hgas st1 hk hC (by omega)))
  · set s1 := stJumpdest s with hs1
    have hX1 := hX.trans (stepContinue (k := k) (C := C) hgas st1 hk (by omega))
    have hc1 : s1.executionEnv.code = powBytecode := by rw [hs1]; simp only [stJumpdest]; exact hcode
    have hp1 : s1.machineState.pc = ⟨72⟩ := by rw [hs1]; simp only [stJumpdest]; rw [hpc]; rfl
    have hg1 : s1.machineState.gasAvailable.toNat = g.toNat - (C + 1) := by
      rw [hs1]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
    have hk1 : s1.machineState.stack = val :: Rt := by rw [hs1]; simp only [stJumpdest]; exact hstk
    have hmem1 : s1.machineState.memory = solcFreePtrMem := by rw [hs1]; simp only [stJumpdest]; exact hmem
    have haw1 : s1.machineState.activeWords = UInt256.ofNat 3 := by rw [hs1]; simp only [stJumpdest]; exact haw
    -- step 2: PUSH1 64 @72
    have st2 := push1_xstep (argv := ⟨64⟩) hc1 hp1 (by decide) hk1 (by first | (simp only [List.length_cons]; omega) | omega)
    by_cases g2 : g.toNat < C + 4
    · exact Or.inl (hX1.trans (stepOOG (k := k+1) (C := C+1) hg1 st2 (by omega) (by omega) (by omega)))
    · set s2 := stPush1 s1 ⟨64⟩ with hs2
      have hX2 := hX1.trans (stepContinue (k := k+1) (C := C+1) hg1 st2 (by omega) (by omega))
      have hc2 : s2.executionEnv.code = powBytecode := by rw [hs2]; simp only [stPush1]; exact hc1
      have hp2 : s2.machineState.pc = ⟨74⟩ := by rw [hs2]; simp only [stPush1]; rw [hp1]; rfl
      have hg2 : s2.machineState.gasAvailable.toNat = g.toNat - (C + 4) := by
        rw [hs2]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
      have hk2 : s2.machineState.stack = ⟨64⟩ :: val :: Rt := by rw [hs2]; simp only [stPush1, hk1]
      have hmem2 : s2.machineState.memory = solcFreePtrMem := by rw [hs2]; simp only [stPush1]; exact hmem1
      have haw2 : s2.machineState.activeWords = UInt256.ofNat 3 := by rw [hs2]; simp only [stPush1]; exact haw1
      -- step 3: MLOAD @74  (reads free-pointer mem[64] = 128)
      have h0₃ : s2.machineState.stack[0]! = (⟨64⟩:UInt256) := by rw [hk2]; rfl
      have hmc3 : memoryExpansionCost s2 .MLOAD = 0 := by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw2, h0₃]; decide
      have st3 := mload_xstep hc2 hp2 (by decide) hk2 (by first | (simp only [List.length_cons]; omega) | omega)
      rw [hmc3] at st3
      by_cases g3 : g.toNat < C + 7
      · exact Or.inl (hX2.trans (stepOOG (k := k+2) (C := C+4) (cost := 0+3) hg2 st3 (by omega) (by omega) (by omega)))
      · set s3 := stMLoad s2 ⟨64⟩ (val :: Rt) with hs3
        have hX3 := hX2.trans (stepContinue (k := k+2) (C := C+4) (cost := 0+3) hg2 st3 (by omega) (by omega))
        have hc3 : s3.executionEnv.code = powBytecode := by rw [hs3]; simp only [stMLoad]; exact hc2
        have hp3 : s3.machineState.pc = ⟨75⟩ := by rw [hs3]; simp only [stMLoad]; rw [hp2]; rfl
        have hg3 : s3.machineState.gasAvailable.toNat = g.toNat - (C + 7) := by
          rw [hs3]; simp only [stMLoad, hmc3]; rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]; omega
        have hk3 : s3.machineState.stack = ⟨128⟩ :: val :: Rt := by
          rw [hs3]; simp only [stMLoad]; rw [if_neg (by rw [hmem2, solcFreePtrMem_size, haw2]; decide)]
          rw [hmem2, show (⟨64⟩:UInt256).toNat = 64 from by decide, solcFreePtrMem_read64,
            fromByteArrayBigEndian_toByteArray, show UInt256.ofNat ((⟨128⟩:UInt256).toNat) = ⟨128⟩ from by decide]
        have hmem3 : s3.machineState.memory = solcFreePtrMem := by rw [hs3]; simp only [stMLoad]; exact hmem2
        have haw3 : s3.machineState.activeWords = UInt256.ofNat 3 := by rw [hs3]; simp only [stMLoad, haw2]; decide
        -- step 4: PUSH2 84 @75
        have st4 := push2_xstep (argv := ⟨84⟩) hc3 hp3 (by decide) hk3 (by first | (simp only [List.length_cons]; omega) | omega)
        by_cases g4 : g.toNat < C + 10
        · exact Or.inl (hX3.trans (stepOOG (k := k+3) (C := C+7) hg3 st4 (by omega) (by omega) (by omega)))
        · set s4 := stPush2 s3 ⟨84⟩ with hs4
          have hX4 := hX3.trans (stepContinue (k := k+3) (C := C+7) hg3 st4 (by omega) (by omega))
          have hc4 : s4.executionEnv.code = powBytecode := by rw [hs4]; simp only [stPush2]; exact hc3
          have hp4 : s4.machineState.pc = ⟨78⟩ := by rw [hs4]; simp only [stPush2]; rw [hp3]; rfl
          have hg4 : s4.machineState.gasAvailable.toNat = g.toNat - (C + 10) := by
            rw [hs4]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
          have hk4 : s4.machineState.stack = ⟨84⟩ :: ⟨128⟩ :: val :: Rt := by rw [hs4]; simp only [stPush2, hk3]
          have hmem4 : s4.machineState.memory = solcFreePtrMem := by rw [hs4]; simp only [stPush2]; exact hmem3
          have haw4 : s4.machineState.activeWords = UInt256.ofNat 3 := by rw [hs4]; simp only [stPush2]; exact haw3
          -- step 5: SWAP2 @78
          have st5 := swap2_xstep hc4 hp4 (by decide) hk4 (by first | (simp only [List.length_cons]; omega) | omega)
          by_cases g5 : g.toNat < C + 13
          · exact Or.inl (hX4.trans (stepOOG (k := k+4) (C := C+10) hg4 st5 (by omega) (by omega) (by omega)))
          · set s5 := stSwap s4 (val :: ⟨128⟩ :: ⟨84⟩ :: Rt) with hs5
            have hX5 := hX4.trans (stepContinue (k := k+4) (C := C+10) hg4 st5 (by omega) (by omega))
            have hc5 : s5.executionEnv.code = powBytecode := by rw [hs5]; simp only [stSwap]; exact hc4
            have hp5 : s5.machineState.pc = ⟨79⟩ := by rw [hs5]; simp only [stSwap]; rw [hp4]; rfl
            have hg5 : s5.machineState.gasAvailable.toNat = g.toNat - (C + 13) := by
              rw [hs5]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
            have hk5 : s5.machineState.stack = val :: ⟨128⟩ :: ⟨84⟩ :: Rt := by rw [hs5]; simp only [stSwap]
            have hmem5 : s5.machineState.memory = solcFreePtrMem := by rw [hs5]; simp only [stSwap]; exact hmem4
            have haw5 : s5.machineState.activeWords = UInt256.ofNat 3 := by rw [hs5]; simp only [stSwap]; exact haw4
            -- step 6: SWAP1 @79
            have st6 := swap1_xstep hc5 hp5 (by decide) hk5 (by first | (simp only [List.length_cons]; omega) | omega)
            by_cases g6 : g.toNat < C + 16
            · exact Or.inl (hX5.trans (stepOOG (k := k+5) (C := C+13) hg5 st6 (by omega) (by omega) (by omega)))
            · set s6 := stSwap s5 (⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs6
              have hX6 := hX5.trans (stepContinue (k := k+5) (C := C+13) hg5 st6 (by omega) (by omega))
              have hc6 : s6.executionEnv.code = powBytecode := by rw [hs6]; simp only [stSwap]; exact hc5
              have hp6 : s6.machineState.pc = ⟨80⟩ := by rw [hs6]; simp only [stSwap]; rw [hp5]; rfl
              have hg6 : s6.machineState.gasAvailable.toNat = g.toNat - (C + 16) := by
                rw [hs6]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
              have hk6 : s6.machineState.stack = ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs6]; simp only [stSwap]
              have hmem6 : s6.machineState.memory = solcFreePtrMem := by rw [hs6]; simp only [stSwap]; exact hmem5
              have haw6 : s6.machineState.activeWords = UInt256.ofNat 3 := by rw [hs6]; simp only [stSwap]; exact haw5
              -- step 7: PUSH2 265 @80
              have st7 := push2_xstep (argv := ⟨265⟩) hc6 hp6 (by decide) hk6 (by first | (simp only [List.length_cons]; omega) | omega)
              by_cases g7 : g.toNat < C + 19
              · exact Or.inl (hX6.trans (stepOOG (k := k+6) (C := C+16) hg6 st7 (by omega) (by omega) (by omega)))
              · set s7 := stPush2 s6 ⟨265⟩ with hs7
                have hX7 := hX6.trans (stepContinue (k := k+6) (C := C+16) hg6 st7 (by omega) (by omega))
                have hc7 : s7.executionEnv.code = powBytecode := by rw [hs7]; simp only [stPush2]; exact hc6
                have hp7 : s7.machineState.pc = ⟨83⟩ := by rw [hs7]; simp only [stPush2]; rw [hp6]; rfl
                have hg7 : s7.machineState.gasAvailable.toNat = g.toNat - (C + 19) := by
                  rw [hs7]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                have hk7 : s7.machineState.stack = ⟨265⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs7]; simp only [stPush2, hk6]
                have hmem7 : s7.machineState.memory = solcFreePtrMem := by rw [hs7]; simp only [stPush2]; exact hmem6
                have haw7 : s7.machineState.activeWords = UInt256.ofNat 3 := by rw [hs7]; simp only [stPush2]; exact haw6
                -- step 8: JUMP @83 → 265
                have st8 := jump_xstep hc7 hp7 (by decide) hk7 (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by first | (simp only [List.length_cons]; omega) | omega)
                by_cases g8 : g.toNat < C + 27
                · exact Or.inl (hX7.trans (stepOOG (k := k+7) (C := C+19) (cost := 8) hg7 st8 (by omega) (by omega) (by omega)))
                · set s8 := stJump s7 ⟨265⟩ (⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs8
                  have hX8 := hX7.trans (stepContinue (k := k+7) (C := C+19) (cost := 8) hg7 st8 (by omega) (by omega))
                  have hc8 : s8.executionEnv.code = powBytecode := by rw [hs8]; simp only [stJump]; exact hc7
                  have hp8 : s8.machineState.pc = ⟨265⟩ := by rw [hs8]; simp only [stJump]
                  have hg8 : s8.machineState.gasAvailable.toNat = g.toNat - (C + 27) := by
                    rw [hs8]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                  have hk8 : s8.machineState.stack = ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs8]; simp only [stJump]
                  have hmem8 : s8.machineState.memory = solcFreePtrMem := by rw [hs8]; simp only [stJump]; exact hmem7
                  have haw8 : s8.machineState.activeWords = UInt256.ofNat 3 := by rw [hs8]; simp only [stJump]; exact haw7
                  -- step 9: JUMPDEST @265
                  have st9 := jumpdest_xstep hc8 hp8 (by decide) (by rw [hk8]; simp only [List.length_cons]; omega)
                  by_cases g9 : g.toNat < C + 28
                  · exact Or.inl (hX8.trans (stepOOG (k := k+8) (C := C+27) hg8 st9 (by omega) (by omega) (by omega)))
                  · set s9 := stJumpdest s8 with hs9
                    have hX9 := hX8.trans (stepContinue (k := k+8) (C := C+27) hg8 st9 (by omega) (by omega))
                    have hc9 : s9.executionEnv.code = powBytecode := by rw [hs9]; simp only [stJumpdest]; exact hc8
                    have hp9 : s9.machineState.pc = ⟨266⟩ := by rw [hs9]; simp only [stJumpdest]; rw [hp8]; rfl
                    have hg9 : s9.machineState.gasAvailable.toNat = g.toNat - (C + 28) := by
                      rw [hs9]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                    have hk9 : s9.machineState.stack = ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs9]; simp only [stJumpdest]; exact hk8
                    have hmem9 : s9.machineState.memory = solcFreePtrMem := by rw [hs9]; simp only [stJumpdest]; exact hmem8
                    have haw9 : s9.machineState.activeWords = UInt256.ofNat 3 := by rw [hs9]; simp only [stJumpdest]; exact haw8
                    -- step 10: PUSH0 @266
                    have st10 := push0_xstep hc9 hp9 (by decide) hk9 (by first | (simp only [List.length_cons]; omega) | omega)
                    by_cases g10 : g.toNat < C + 30
                    · exact Or.inl (hX9.trans (stepOOG (k := k+9) (C := C+28) hg9 st10 (by omega) (by omega) (by omega)))
                    · set s10 := stPush0 s9 with hs10
                      have hX10 := hX9.trans (stepContinue (k := k+9) (C := C+28) hg9 st10 (by omega) (by omega))
                      have hc10 : s10.executionEnv.code = powBytecode := by rw [hs10]; simp only [stPush0]; exact hc9
                      have hp10 : s10.machineState.pc = ⟨267⟩ := by rw [hs10]; simp only [stPush0]; rw [hp9]; rfl
                      have hg10 : s10.machineState.gasAvailable.toNat = g.toNat - (C + 30) := by
                        rw [hs10]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                      have hk10 : s10.machineState.stack = ⟨0⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs10]; simp only [stPush0, hk9]
                      have hmem10 : s10.machineState.memory = solcFreePtrMem := by rw [hs10]; simp only [stPush0]; exact hmem9
                      have haw10 : s10.machineState.activeWords = UInt256.ofNat 3 := by rw [hs10]; simp only [stPush0]; exact haw9
                      -- step 11: PUSH1 32 @267
                      have st11 := push1_xstep (argv := ⟨32⟩) hc10 hp10 (by decide) hk10 (by first | (simp only [List.length_cons]; omega) | omega)
                      by_cases g11 : g.toNat < C + 33
                      · exact Or.inl (hX10.trans (stepOOG (k := k+10) (C := C+30) hg10 st11 (by omega) (by omega) (by omega)))
                      · set s11 := stPush1 s10 ⟨32⟩ with hs11
                        have hX11 := hX10.trans (stepContinue (k := k+10) (C := C+30) hg10 st11 (by omega) (by omega))
                        have hc11 : s11.executionEnv.code = powBytecode := by rw [hs11]; simp only [stPush1]; exact hc10
                        have hp11 : s11.machineState.pc = ⟨269⟩ := by rw [hs11]; simp only [stPush1]; rw [hp10]; rfl
                        have hg11 : s11.machineState.gasAvailable.toNat = g.toNat - (C + 33) := by
                          rw [hs11]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                        have hk11 : s11.machineState.stack = ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs11]; simp only [stPush1, hk10]
                        have hmem11 : s11.machineState.memory = solcFreePtrMem := by rw [hs11]; simp only [stPush1]; exact hmem10
                        have haw11 : s11.machineState.activeWords = UInt256.ofNat 3 := by rw [hs11]; simp only [stPush1]; exact haw10
                        -- step 12: DUP3 @269
                        have st12 := dup3_xstep hc11 hp11 (by decide) hk11 (by first | (simp only [List.length_cons]; omega) | omega)
                        by_cases g12 : g.toNat < C + 36
                        · exact Or.inl (hX11.trans (stepOOG (k := k+11) (C := C+33) hg11 st12 (by omega) (by omega) (by omega)))
                        · set s12 := stSwap s11 (⟨128⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs12
                          have hX12 := hX11.trans (stepContinue (k := k+11) (C := C+33) hg11 st12 (by omega) (by omega))
                          have hc12 : s12.executionEnv.code = powBytecode := by rw [hs12]; simp only [stSwap]; exact hc11
                          have hp12 : s12.machineState.pc = ⟨270⟩ := by rw [hs12]; simp only [stSwap]; rw [hp11]; rfl
                          have hg12 : s12.machineState.gasAvailable.toNat = g.toNat - (C + 36) := by
                            rw [hs12]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                          have hk12 : s12.machineState.stack = ⟨128⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs12]; simp only [stSwap]
                          have hmem12 : s12.machineState.memory = solcFreePtrMem := by rw [hs12]; simp only [stSwap]; exact hmem11
                          have haw12 : s12.machineState.activeWords = UInt256.ofNat 3 := by rw [hs12]; simp only [stSwap]; exact haw11
                          -- step 13: ADD @270  (128 + 32 = 160)
                          have st13 := add_xstep hc12 hp12 (by decide) hk12 (by first | (simp only [List.length_cons]; omega) | omega)
                          by_cases g13 : g.toNat < C + 39
                          · exact Or.inl (hX12.trans (stepOOG (k := k+12) (C := C+36) hg12 st13 (by omega) (by omega) (by omega)))
                          · set s13 := stBinop s12 ((⟨128⟩:UInt256) + ⟨32⟩) (⟨0⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs13
                            have hX13 := hX12.trans (stepContinue (k := k+12) (C := C+36) hg12 st13 (by omega) (by omega))
                            have hc13 : s13.executionEnv.code = powBytecode := by rw [hs13]; simp only [stBinop]; exact hc12
                            have hp13 : s13.machineState.pc = ⟨271⟩ := by rw [hs13]; simp only [stBinop]; rw [hp12]; rfl
                            have hg13 : s13.machineState.gasAvailable.toNat = g.toNat - (C + 39) := by
                              rw [hs13]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                            have hk13 : s13.machineState.stack = ⟨160⟩ :: ⟨0⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs13]; simp only [stBinop]; rw [add128_32]
                            have hmem13 : s13.machineState.memory = solcFreePtrMem := by rw [hs13]; simp only [stBinop]; exact hmem12
                            have haw13 : s13.machineState.activeWords = UInt256.ofNat 3 := by rw [hs13]; simp only [stBinop]; exact haw12
                            -- step 14: SWAP1 @271
                            have st14 := swap1_xstep hc13 hp13 (by decide) hk13 (by first | (simp only [List.length_cons]; omega) | omega)
                            by_cases g14 : g.toNat < C + 42
                            · exact Or.inl (hX13.trans (stepOOG (k := k+13) (C := C+39) hg13 st14 (by omega) (by omega) (by omega)))
                            · set s14 := stSwap s13 (⟨0⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs14
                              have hX14 := hX13.trans (stepContinue (k := k+13) (C := C+39) hg13 st14 (by omega) (by omega))
                              have hc14 : s14.executionEnv.code = powBytecode := by rw [hs14]; simp only [stSwap]; exact hc13
                              have hp14 : s14.machineState.pc = ⟨272⟩ := by rw [hs14]; simp only [stSwap]; rw [hp13]; rfl
                              have hg14 : s14.machineState.gasAvailable.toNat = g.toNat - (C + 42) := by
                                rw [hs14]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                              have hk14 : s14.machineState.stack = ⟨0⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs14]; simp only [stSwap]
                              have hmem14 : s14.machineState.memory = solcFreePtrMem := by rw [hs14]; simp only [stSwap]; exact hmem13
                              have haw14 : s14.machineState.activeWords = UInt256.ofNat 3 := by rw [hs14]; simp only [stSwap]; exact haw13
                              -- step 15: POP @272
                              have st15 := pop_xstep hc14 hp14 (by decide) hk14 (by first | (simp only [List.length_cons]; omega) | omega)
                              by_cases g15 : g.toNat < C + 44
                              · exact Or.inl (hX14.trans (stepOOG (k := k+14) (C := C+42) hg14 st15 (by omega) (by omega) (by omega)))
                              · set s15 := stPop s14 (⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs15
                                have hX15 := hX14.trans (stepContinue (k := k+14) (C := C+42) hg14 st15 (by omega) (by omega))
                                have hc15 : s15.executionEnv.code = powBytecode := by rw [hs15]; simp only [stPop]; exact hc14
                                have hp15 : s15.machineState.pc = ⟨273⟩ := by rw [hs15]; simp only [stPop]; rw [hp14]; rfl
                                have hg15 : s15.machineState.gasAvailable.toNat = g.toNat - (C + 44) := by
                                  rw [hs15]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                have hk15 : s15.machineState.stack = ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs15]; simp only [stPop]
                                have hmem15 : s15.machineState.memory = solcFreePtrMem := by rw [hs15]; simp only [stPop]; exact hmem14
                                have haw15 : s15.machineState.activeWords = UInt256.ofNat 3 := by rw [hs15]; simp only [stPop]; exact haw14
                                -- step 16: PUSH2 284 @273
                                have st16 := push2_xstep (argv := ⟨284⟩) hc15 hp15 (by decide) hk15 (by first | (simp only [List.length_cons]; omega) | omega)
                                by_cases g16 : g.toNat < C + 47
                                · exact Or.inl (hX15.trans (stepOOG (k := k+15) (C := C+44) hg15 st16 (by omega) (by omega) (by omega)))
                                · set s16 := stPush2 s15 ⟨284⟩ with hs16
                                  have hX16 := hX15.trans (stepContinue (k := k+15) (C := C+44) hg15 st16 (by omega) (by omega))
                                  have hc16 : s16.executionEnv.code = powBytecode := by rw [hs16]; simp only [stPush2]; exact hc15
                                  have hp16 : s16.machineState.pc = ⟨276⟩ := by rw [hs16]; simp only [stPush2]; rw [hp15]; rfl
                                  have hg16 : s16.machineState.gasAvailable.toNat = g.toNat - (C + 47) := by
                                    rw [hs16]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                                  have hk16 : s16.machineState.stack = ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs16]; simp only [stPush2, hk15]
                                  have hmem16 : s16.machineState.memory = solcFreePtrMem := by rw [hs16]; simp only [stPush2]; exact hmem15
                                  have haw16 : s16.machineState.activeWords = UInt256.ofNat 3 := by rw [hs16]; simp only [stPush2]; exact haw15
                                  -- step 17: PUSH0 @276
                                  have st17 := push0_xstep hc16 hp16 (by decide) hk16 (by first | (simp only [List.length_cons]; omega) | omega)
                                  by_cases g17 : g.toNat < C + 49
                                  · exact Or.inl (hX16.trans (stepOOG (k := k+16) (C := C+47) hg16 st17 (by omega) (by omega) (by omega)))
                                  · set s17 := stPush0 s16 with hs17
                                    have hX17 := hX16.trans (stepContinue (k := k+16) (C := C+47) hg16 st17 (by omega) (by omega))
                                    have hc17 : s17.executionEnv.code = powBytecode := by rw [hs17]; simp only [stPush0]; exact hc16
                                    have hp17 : s17.machineState.pc = ⟨277⟩ := by rw [hs17]; simp only [stPush0]; rw [hp16]; rfl
                                    have hg17 : s17.machineState.gasAvailable.toNat = g.toNat - (C + 49) := by
                                      rw [hs17]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                                    have hk17 : s17.machineState.stack = ⟨0⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs17]; simp only [stPush0, hk16]
                                    have hmem17 : s17.machineState.memory = solcFreePtrMem := by rw [hs17]; simp only [stPush0]; exact hmem16
                                    have haw17 : s17.machineState.activeWords = UInt256.ofNat 3 := by rw [hs17]; simp only [stPush0]; exact haw16
                                    -- step 18: DUP4 @277  (dup the 4th = 128)
                                    have st18 := dup4_xstep hc17 hp17 (by decide) hk17 (by first | (simp only [List.length_cons]; omega) | omega)
                                    by_cases g18 : g.toNat < C + 52
                                    · exact Or.inl (hX17.trans (stepOOG (k := k+17) (C := C+49) hg17 st18 (by omega) (by omega) (by omega)))
                                    · set s18 := stSwap s17 (⟨128⟩ :: ⟨0⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs18
                                      have hX18 := hX17.trans (stepContinue (k := k+17) (C := C+49) hg17 st18 (by omega) (by omega))
                                      have hc18 : s18.executionEnv.code = powBytecode := by rw [hs18]; simp only [stSwap]; exact hc17
                                      have hp18 : s18.machineState.pc = ⟨278⟩ := by rw [hs18]; simp only [stSwap]; rw [hp17]; rfl
                                      have hg18 : s18.machineState.gasAvailable.toNat = g.toNat - (C + 52) := by
                                        rw [hs18]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                      have hk18 : s18.machineState.stack = ⟨128⟩ :: ⟨0⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs18]; simp only [stSwap]
                                      have hmem18 : s18.machineState.memory = solcFreePtrMem := by rw [hs18]; simp only [stSwap]; exact hmem17
                                      have haw18 : s18.machineState.activeWords = UInt256.ofNat 3 := by rw [hs18]; simp only [stSwap]; exact haw17
                                      -- step 19: ADD @278  (128 + 0 = 128)
                                      have st19 := add_xstep hc18 hp18 (by decide) hk18 (by first | (simp only [List.length_cons]; omega) | omega)
                                      by_cases g19 : g.toNat < C + 55
                                      · exact Or.inl (hX18.trans (stepOOG (k := k+18) (C := C+52) hg18 st19 (by omega) (by omega) (by omega)))
                                      · set s19 := stBinop s18 ((⟨128⟩:UInt256) + ⟨0⟩) (⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs19
                                        have hX19 := hX18.trans (stepContinue (k := k+18) (C := C+52) hg18 st19 (by omega) (by omega))
                                        have hc19 : s19.executionEnv.code = powBytecode := by rw [hs19]; simp only [stBinop]; exact hc18
                                        have hp19 : s19.machineState.pc = ⟨279⟩ := by rw [hs19]; simp only [stBinop]; rw [hp18]; rfl
                                        have hg19 : s19.machineState.gasAvailable.toNat = g.toNat - (C + 55) := by
                                          rw [hs19]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                                        have hk19 : s19.machineState.stack = ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs19]; simp only [stBinop]; rw [add128_0]
                                        have hmem19 : s19.machineState.memory = solcFreePtrMem := by rw [hs19]; simp only [stBinop]; exact hmem18
                                        have haw19 : s19.machineState.activeWords = UInt256.ofNat 3 := by rw [hs19]; simp only [stBinop]; exact haw18
                                        -- step 20: DUP5 @279  (dup the 5th = val)
                                        have st20 := dup5_xstep hc19 hp19 (by decide) hk19 (by first | (simp only [List.length_cons]; omega) | omega)
                                        by_cases g20 : g.toNat < C + 58
                                        · exact Or.inl (hX19.trans (stepOOG (k := k+19) (C := C+55) hg19 st20 (by omega) (by omega) (by omega)))
                                        · set s20 := stSwap s19 (val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs20
                                          have hX20 := hX19.trans (stepContinue (k := k+19) (C := C+55) hg19 st20 (by omega) (by omega))
                                          have hc20 : s20.executionEnv.code = powBytecode := by rw [hs20]; simp only [stSwap]; exact hc19
                                          have hp20 : s20.machineState.pc = ⟨280⟩ := by rw [hs20]; simp only [stSwap]; rw [hp19]; rfl
                                          have hg20 : s20.machineState.gasAvailable.toNat = g.toNat - (C + 58) := by
                                            rw [hs20]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                          have hk20 : s20.machineState.stack = val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs20]; simp only [stSwap]
                                          have hmem20 : s20.machineState.memory = solcFreePtrMem := by rw [hs20]; simp only [stSwap]; exact hmem19
                                          have haw20 : s20.machineState.activeWords = UInt256.ofNat 3 := by rw [hs20]; simp only [stSwap]; exact haw19
                                          -- step 21: PUSH2 250 @280
                                          have st21 := push2_xstep (argv := ⟨250⟩) hc20 hp20 (by decide) hk20 (by first | (simp only [List.length_cons]; omega) | omega)
                                          by_cases g21 : g.toNat < C + 61
                                          · exact Or.inl (hX20.trans (stepOOG (k := k+20) (C := C+58) hg20 st21 (by omega) (by omega) (by omega)))
                                          · set s21 := stPush2 s20 ⟨250⟩ with hs21
                                            have hX21 := hX20.trans (stepContinue (k := k+20) (C := C+58) hg20 st21 (by omega) (by omega))
                                            have hc21 : s21.executionEnv.code = powBytecode := by rw [hs21]; simp only [stPush2]; exact hc20
                                            have hp21 : s21.machineState.pc = ⟨283⟩ := by rw [hs21]; simp only [stPush2]; rw [hp20]; rfl
                                            have hg21 : s21.machineState.gasAvailable.toNat = g.toNat - (C + 61) := by
                                              rw [hs21]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                                            have hk21 : s21.machineState.stack = ⟨250⟩ :: val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs21]; simp only [stPush2, hk20]
                                            have hmem21 : s21.machineState.memory = solcFreePtrMem := by rw [hs21]; simp only [stPush2]; exact hmem20
                                            have haw21 : s21.machineState.activeWords = UInt256.ofNat 3 := by rw [hs21]; simp only [stPush2]; exact haw20
                                            -- step 22: JUMP @283 → 250
                                            have st22 := jump_xstep hc21 hp21 (by decide) hk21 (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by first | (simp only [List.length_cons]; omega) | omega)
                                            by_cases g22 : g.toNat < C + 69
                                            · exact Or.inl (hX21.trans (stepOOG (k := k+21) (C := C+61) (cost := 8) hg21 st22 (by omega) (by omega) (by omega)))
                                            · set s22 := stJump s21 ⟨250⟩ (val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs22
                                              have hX22 := hX21.trans (stepContinue (k := k+21) (C := C+61) (cost := 8) hg21 st22 (by omega) (by omega))
                                              have hc22 : s22.executionEnv.code = powBytecode := by rw [hs22]; simp only [stJump]; exact hc21
                                              have hp22 : s22.machineState.pc = ⟨250⟩ := by rw [hs22]; simp only [stJump]
                                              have hg22 : s22.machineState.gasAvailable.toNat = g.toNat - (C + 69) := by
                                                rw [hs22]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                              have hk22 : s22.machineState.stack = val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs22]; simp only [stJump]
                                              have hmem22 : s22.machineState.memory = solcFreePtrMem := by rw [hs22]; simp only [stJump]; exact hmem21
                                              have haw22 : s22.machineState.activeWords = UInt256.ofNat 3 := by rw [hs22]; simp only [stJump]; exact haw21
                                              -- step 23: JUMPDEST @250
                                              have st23 := jumpdest_xstep hc22 hp22 (by decide) (by rw [hk22]; simp only [List.length_cons]; omega)
                                              by_cases g23 : g.toNat < C + 70
                                              · exact Or.inl (hX22.trans (stepOOG (k := k+22) (C := C+69) hg22 st23 (by omega) (by omega) (by omega)))
                                              · set s23 := stJumpdest s22 with hs23
                                                have hX23 := hX22.trans (stepContinue (k := k+22) (C := C+69) hg22 st23 (by omega) (by omega))
                                                have hc23 : s23.executionEnv.code = powBytecode := by rw [hs23]; simp only [stJumpdest]; exact hc22
                                                have hp23 : s23.machineState.pc = ⟨251⟩ := by rw [hs23]; simp only [stJumpdest]; rw [hp22]; rfl
                                                have hg23 : s23.machineState.gasAvailable.toNat = g.toNat - (C + 70) := by
                                                  rw [hs23]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                                                have hk23 : s23.machineState.stack = val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs23]; simp only [stJumpdest]; exact hk22
                                                have hmem23 : s23.machineState.memory = solcFreePtrMem := by rw [hs23]; simp only [stJumpdest]; exact hmem22
                                                have haw23 : s23.machineState.activeWords = UInt256.ofNat 3 := by rw [hs23]; simp only [stJumpdest]; exact haw22
                                                -- step 24: PUSH2 259 @251
                                                have st24 := push2_xstep (argv := ⟨259⟩) hc23 hp23 (by decide) hk23 (by first | (simp only [List.length_cons]; omega) | omega)
                                                by_cases g24 : g.toNat < C + 73
                                                · exact Or.inl (hX23.trans (stepOOG (k := k+23) (C := C+70) hg23 st24 (by omega) (by omega) (by omega)))
                                                · set s24 := stPush2 s23 ⟨259⟩ with hs24
                                                  have hX24 := hX23.trans (stepContinue (k := k+23) (C := C+70) hg23 st24 (by omega) (by omega))
                                                  have hc24 : s24.executionEnv.code = powBytecode := by rw [hs24]; simp only [stPush2]; exact hc23
                                                  have hp24 : s24.machineState.pc = ⟨254⟩ := by rw [hs24]; simp only [stPush2]; rw [hp23]; rfl
                                                  have hg24 : s24.machineState.gasAvailable.toNat = g.toNat - (C + 73) := by
                                                    rw [hs24]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                                                  have hk24 : s24.machineState.stack = ⟨259⟩ :: val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs24]; simp only [stPush2, hk23]
                                                  have hmem24 : s24.machineState.memory = solcFreePtrMem := by rw [hs24]; simp only [stPush2]; exact hmem23
                                                  have haw24 : s24.machineState.activeWords = UInt256.ofNat 3 := by rw [hs24]; simp only [stPush2]; exact haw23
                                                  -- step 25: DUP2 @254  (dup the 2nd = val)
                                                  have st25 := dup2_xstep hc24 hp24 (by decide) hk24 (by first | (simp only [List.length_cons]; omega) | omega)
                                                  by_cases g25 : g.toNat < C + 76
                                                  · exact Or.inl (hX24.trans (stepOOG (k := k+24) (C := C+73) hg24 st25 (by omega) (by omega) (by omega)))
                                                  · set s25 := stSwap s24 (val :: ⟨259⟩ :: val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs25
                                                    have hX25 := hX24.trans (stepContinue (k := k+24) (C := C+73) hg24 st25 (by omega) (by omega))
                                                    have hc25 : s25.executionEnv.code = powBytecode := by rw [hs25]; simp only [stSwap]; exact hc24
                                                    have hp25 : s25.machineState.pc = ⟨255⟩ := by rw [hs25]; simp only [stSwap]; rw [hp24]; rfl
                                                    have hg25 : s25.machineState.gasAvailable.toNat = g.toNat - (C + 76) := by
                                                      rw [hs25]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                    have hk25 : s25.machineState.stack = val :: ⟨259⟩ :: val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs25]; simp only [stSwap]
                                                    have hmem25 : s25.machineState.memory = solcFreePtrMem := by rw [hs25]; simp only [stSwap]; exact hmem24
                                                    have haw25 : s25.machineState.activeWords = UInt256.ofNat 3 := by rw [hs25]; simp only [stSwap]; exact haw24
                                                    -- step 26: PUSH2 156 @255
                                                    have st26 := push2_xstep (argv := ⟨156⟩) hc25 hp25 (by decide) hk25 (by first | (simp only [List.length_cons]; omega) | omega)
                                                    by_cases g26 : g.toNat < C + 79
                                                    · exact Or.inl (hX25.trans (stepOOG (k := k+25) (C := C+76) hg25 st26 (by omega) (by omega) (by omega)))
                                                    · set s26 := stPush2 s25 ⟨156⟩ with hs26
                                                      have hX26 := hX25.trans (stepContinue (k := k+25) (C := C+76) hg25 st26 (by omega) (by omega))
                                                      have hc26 : s26.executionEnv.code = powBytecode := by rw [hs26]; simp only [stPush2]; exact hc25
                                                      have hp26 : s26.machineState.pc = ⟨258⟩ := by rw [hs26]; simp only [stPush2]; rw [hp25]; rfl
                                                      have hg26 : s26.machineState.gasAvailable.toNat = g.toNat - (C + 79) := by
                                                        rw [hs26]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                                                      have hk26 : s26.machineState.stack = ⟨156⟩ :: val :: ⟨259⟩ :: val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs26]; simp only [stPush2, hk25]
                                                      have hmem26 : s26.machineState.memory = solcFreePtrMem := by rw [hs26]; simp only [stPush2]; exact hmem25
                                                      have haw26 : s26.machineState.activeWords = UInt256.ofNat 3 := by rw [hs26]; simp only [stPush2]; exact haw25
                                                      -- step 27: JUMP @258 → 156
                                                      have st27 := jump_xstep hc26 hp26 (by decide) hk26 (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by first | (simp only [List.length_cons]; omega) | omega)
                                                      by_cases g27 : g.toNat < C + 87
                                                      · exact Or.inl (hX26.trans (stepOOG (k := k+26) (C := C+79) (cost := 8) hg26 st27 (by omega) (by omega) (by omega)))
                                                      · set s27 := stJump s26 ⟨156⟩ (val :: ⟨259⟩ :: val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs27
                                                        have hX27 := hX26.trans (stepContinue (k := k+26) (C := C+79) (cost := 8) hg26 st27 (by omega) (by omega))
                                                        have hc27 : s27.executionEnv.code = powBytecode := by rw [hs27]; simp only [stJump]; exact hc26
                                                        have hp27 : s27.machineState.pc = ⟨156⟩ := by rw [hs27]; simp only [stJump]
                                                        have hg27 : s27.machineState.gasAvailable.toNat = g.toNat - (C + 87) := by
                                                          rw [hs27]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                                        have hk27 : s27.machineState.stack = val :: ⟨259⟩ :: (val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) := by rw [hs27]; simp only [stJump]
                                                        have hmem27 : s27.machineState.memory = solcFreePtrMem := by rw [hs27]; simp only [stJump]; exact hmem26
                                                        have haw27 : s27.machineState.activeWords = UInt256.ofNat 3 := by rw [hs27]; simp only [stJump]; exact haw26
                                                        -- internal `abi_encode_uint` call: routine 9c @156 → 259
                                                        rcases powRoutine_9c hc27 hp27 hk27
                                                            (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
                                                            (by first | (simp only [List.length_cons]; omega) | omega) hg27 (by omega) (by omega) hX27 with
                                                          hoog | ⟨k28, C28, sR, hXR, hcR, hpR, hkR, hgR, hkkR, hCCR, hmemR0, hawR0⟩
                                                        · exact Or.inl hoog
                                                        · have hmemR : sR.machineState.memory = solcFreePtrMem := by rw [hmemR0]; exact hmem27
                                                          have hawR : sR.machineState.activeWords = UInt256.ofNat 3 := by rw [hawR0]; exact haw27
                                                          -- step 28: JUMPDEST @259
                                                          have st28 := jumpdest_xstep hcR hpR (by decide) (by rw [hkR]; simp only [List.length_cons]; omega)
                                                          by_cases g28 : g.toNat < C28 + 1
                                                          · exact Or.inl (hXR.trans (stepOOG (k := k28) (C := C28) hgR st28 hkkR hCCR (by omega)))
                                                          · set s28 := stJumpdest sR with hs28
                                                            have hX28 := hXR.trans (stepContinue (k := k28) (C := C28) hgR st28 hkkR (by omega))
                                                            have hc28 : s28.executionEnv.code = powBytecode := by rw [hs28]; simp only [stJumpdest]; exact hcR
                                                            have hp28 : s28.machineState.pc = ⟨260⟩ := by rw [hs28]; simp only [stJumpdest]; rw [hpR]; rfl
                                                            have hg28 : s28.machineState.gasAvailable.toNat = g.toNat - (C28 + 1) := by
                                                              rw [hs28]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                                                            have hk28 : s28.machineState.stack = val :: val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs28]; simp only [stJumpdest]; exact hkR
                                                            have hmem28 : s28.machineState.memory = solcFreePtrMem := by rw [hs28]; simp only [stJumpdest]; exact hmemR
                                                            have haw28 : s28.machineState.activeWords = UInt256.ofNat 3 := by rw [hs28]; simp only [stJumpdest]; exact hawR
                                                            -- step 29: DUP3 @260  (dup the 3rd = 128)
                                                            have st29 := dup3_xstep hc28 hp28 (by decide) hk28 (by first | (simp only [List.length_cons]; omega) | omega)
                                                            by_cases g29 : g.toNat < C28 + 4
                                                            · exact Or.inl (hX28.trans (stepOOG (k := k28+1) (C := C28+1) hg28 st29 (by omega) (by omega) (by omega)))
                                                            · set s29 := stSwap s28 (⟨128⟩ :: val :: val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs29
                                                              have hX29 := hX28.trans (stepContinue (k := k28+1) (C := C28+1) hg28 st29 (by omega) (by omega))
                                                              have hc29 : s29.executionEnv.code = powBytecode := by rw [hs29]; simp only [stSwap]; exact hc28
                                                              have hp29 : s29.machineState.pc = ⟨261⟩ := by rw [hs29]; simp only [stSwap]; rw [hp28]; rfl
                                                              have hg29 : s29.machineState.gasAvailable.toNat = g.toNat - (C28 + 4) := by
                                                                rw [hs29]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                              have hk29 : s29.machineState.stack = ⟨128⟩ :: val :: val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs29]; simp only [stSwap]
                                                              have hmem29 : s29.machineState.memory = solcFreePtrMem := by rw [hs29]; simp only [stSwap]; exact hmem28
                                                              have haw29 : s29.machineState.activeWords = UInt256.ofNat 3 := by rw [hs29]; simp only [stSwap]; exact haw28
                                                              -- step 30: MSTORE @261  (store val at 0x80; mem ↦ powMem2 val, aw 3 ↦ 5)
                                                              have h0₃₀ : s29.machineState.stack[0]! = (⟨128⟩:UInt256) := by rw [hk29]; rfl
                                                              have hmc30 : memoryExpansionCost s29 .MSTORE = 6 := by
                                                                simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw29, h0₃₀]; decide
                                                              have st30 := mstore_xstep hc29 hp29 (by decide) hk29 (by first | (simp only [List.length_cons]; omega) | omega)
                                                              rw [hmc30] at st30
                                                              by_cases g30 : g.toNat < C28 + 13
                                                              · exact Or.inl (hX29.trans (stepOOG (k := k28+2) (C := C28+4) (cost := 6+3) hg29 st30 (by omega) (by omega) (by omega)))
                                                              · set s30 := stMStore s29 ⟨128⟩ val (val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs30
                                                                have hX30 := hX29.trans (stepContinue (k := k28+2) (C := C28+4) (cost := 6+3) hg29 st30 (by omega) (by omega))
                                                                have hc30 : s30.executionEnv.code = powBytecode := by rw [hs30]; simp only [stMStore]; exact hc29
                                                                have hp30 : s30.machineState.pc = ⟨262⟩ := by rw [hs30]; simp only [stMStore]; rw [hp29]; rfl
                                                                have hg30 : s30.machineState.gasAvailable.toNat = g.toNat - (C28 + 13) := by
                                                                  rw [hs30]; simp only [stMStore, hmc30]
                                                                  rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]; omega
                                                                have hk30 : s30.machineState.stack = val :: ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs30]; simp only [stMStore]
                                                                have hmem30 : s30.machineState.memory = powMem2 val := by
                                                                  rw [hs30]; simp only [stMStore]; rw [hmem29, show (⟨128⟩:UInt256).toNat = 128 from by decide]; rfl
                                                                have haw30 : s30.machineState.activeWords = UInt256.ofNat 5 := by rw [hs30]; simp only [stMStore, haw29]; decide
                                                                -- step 31: POP @262
                                                                have st31 := pop_xstep hc30 hp30 (by decide) hk30 (by first | (simp only [List.length_cons]; omega) | omega)
                                                                by_cases g31 : g.toNat < C28 + 15
                                                                · exact Or.inl (hX30.trans (stepOOG (k := k28+3) (C := C28+13) hg30 st31 (by omega) (by omega) (by omega)))
                                                                · set s31 := stPop s30 (⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs31
                                                                  have hX31 := hX30.trans (stepContinue (k := k28+3) (C := C28+13) hg30 st31 (by omega) (by omega))
                                                                  have hc31 : s31.executionEnv.code = powBytecode := by rw [hs31]; simp only [stPop]; exact hc30
                                                                  have hp31 : s31.machineState.pc = ⟨263⟩ := by rw [hs31]; simp only [stPop]; rw [hp30]; rfl
                                                                  have hg31 : s31.machineState.gasAvailable.toNat = g.toNat - (C28 + 15) := by
                                                                    rw [hs31]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                  have hk31 : s31.machineState.stack = ⟨128⟩ :: ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs31]; simp only [stPop]
                                                                  have hmem31 : s31.machineState.memory = powMem2 val := by rw [hs31]; simp only [stPop]; exact hmem30
                                                                  have haw31 : s31.machineState.activeWords = UInt256.ofNat 5 := by rw [hs31]; simp only [stPop]; exact haw30
                                                                  -- step 32: POP @263
                                                                  have st32 := pop_xstep hc31 hp31 (by decide) hk31 (by first | (simp only [List.length_cons]; omega) | omega)
                                                                  by_cases g32 : g.toNat < C28 + 17
                                                                  · exact Or.inl (hX31.trans (stepOOG (k := k28+4) (C := C28+15) hg31 st32 (by omega) (by omega) (by omega)))
                                                                  · set s32 := stPop s31 (⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs32
                                                                    have hX32 := hX31.trans (stepContinue (k := k28+4) (C := C28+15) hg31 st32 (by omega) (by omega))
                                                                    have hc32 : s32.executionEnv.code = powBytecode := by rw [hs32]; simp only [stPop]; exact hc31
                                                                    have hp32 : s32.machineState.pc = ⟨264⟩ := by rw [hs32]; simp only [stPop]; rw [hp31]; rfl
                                                                    have hg32 : s32.machineState.gasAvailable.toNat = g.toNat - (C28 + 17) := by
                                                                      rw [hs32]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                    have hk32 : s32.machineState.stack = ⟨284⟩ :: ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs32]; simp only [stPop]
                                                                    have hmem32 : s32.machineState.memory = powMem2 val := by rw [hs32]; simp only [stPop]; exact hmem31
                                                                    have haw32 : s32.machineState.activeWords = UInt256.ofNat 5 := by rw [hs32]; simp only [stPop]; exact haw31
                                                                    -- step 33: JUMP @264 → 284
                                                                    have st33 := jump_xstep hc32 hp32 (by decide) hk32 (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by first | (simp only [List.length_cons]; omega) | omega)
                                                                    by_cases g33 : g.toNat < C28 + 25
                                                                    · exact Or.inl (hX32.trans (stepOOG (k := k28+5) (C := C28+17) (cost := 8) hg32 st33 (by omega) (by omega) (by omega)))
                                                                    · set s33 := stJump s32 ⟨284⟩ (⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt) with hs33
                                                                      have hX33 := hX32.trans (stepContinue (k := k28+5) (C := C28+17) (cost := 8) hg32 st33 (by omega) (by omega))
                                                                      have hc33 : s33.executionEnv.code = powBytecode := by rw [hs33]; simp only [stJump]; exact hc32
                                                                      have hp33 : s33.machineState.pc = ⟨284⟩ := by rw [hs33]; simp only [stJump]
                                                                      have hg33 : s33.machineState.gasAvailable.toNat = g.toNat - (C28 + 25) := by
                                                                        rw [hs33]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                      have hk33 : s33.machineState.stack = ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs33]; simp only [stJump]
                                                                      have hmem33 : s33.machineState.memory = powMem2 val := by rw [hs33]; simp only [stJump]; exact hmem32
                                                                      have haw33 : s33.machineState.activeWords = UInt256.ofNat 5 := by rw [hs33]; simp only [stJump]; exact haw32
                                                                      -- step 34: JUMPDEST @284
                                                                      have st34 := jumpdest_xstep hc33 hp33 (by decide) (by rw [hk33]; simp only [List.length_cons]; omega)
                                                                      by_cases g34 : g.toNat < C28 + 26
                                                                      · exact Or.inl (hX33.trans (stepOOG (k := k28+6) (C := C28+25) hg33 st34 (by omega) (by omega) (by omega)))
                                                                      · set s34 := stJumpdest s33 with hs34
                                                                        have hX34 := hX33.trans (stepContinue (k := k28+6) (C := C28+25) hg33 st34 (by omega) (by omega))
                                                                        have hc34 : s34.executionEnv.code = powBytecode := by rw [hs34]; simp only [stJumpdest]; exact hc33
                                                                        have hp34 : s34.machineState.pc = ⟨285⟩ := by rw [hs34]; simp only [stJumpdest]; rw [hp33]; rfl
                                                                        have hg34 : s34.machineState.gasAvailable.toNat = g.toNat - (C28 + 26) := by
                                                                          rw [hs34]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                        have hk34 : s34.machineState.stack = ⟨160⟩ :: ⟨128⟩ :: val :: ⟨84⟩ :: Rt := by rw [hs34]; simp only [stJumpdest]; exact hk33
                                                                        have hmem34 : s34.machineState.memory = powMem2 val := by rw [hs34]; simp only [stJumpdest]; exact hmem33
                                                                        have haw34 : s34.machineState.activeWords = UInt256.ofNat 5 := by rw [hs34]; simp only [stJumpdest]; exact haw33
                                                                        -- step 35: SWAP3 @285
                                                                        have st35 := swap3_xstep hc34 hp34 (by decide) hk34 (by first | (simp only [List.length_cons]; omega) | omega)
                                                                        by_cases g35 : g.toNat < C28 + 29
                                                                        · exact Or.inl (hX34.trans (stepOOG (k := k28+7) (C := C28+26) hg34 st35 (by omega) (by omega) (by omega)))
                                                                        · set s35 := stSwap s34 (⟨84⟩ :: ⟨128⟩ :: val :: ⟨160⟩ :: Rt) with hs35
                                                                          have hX35 := hX34.trans (stepContinue (k := k28+7) (C := C28+26) hg34 st35 (by omega) (by omega))
                                                                          have hc35 : s35.executionEnv.code = powBytecode := by rw [hs35]; simp only [stSwap]; exact hc34
                                                                          have hp35 : s35.machineState.pc = ⟨286⟩ := by rw [hs35]; simp only [stSwap]; rw [hp34]; rfl
                                                                          have hg35 : s35.machineState.gasAvailable.toNat = g.toNat - (C28 + 29) := by
                                                                            rw [hs35]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                          have hk35 : s35.machineState.stack = ⟨84⟩ :: ⟨128⟩ :: val :: ⟨160⟩ :: Rt := by rw [hs35]; simp only [stSwap]
                                                                          have hmem35 : s35.machineState.memory = powMem2 val := by rw [hs35]; simp only [stSwap]; exact hmem34
                                                                          have haw35 : s35.machineState.activeWords = UInt256.ofNat 5 := by rw [hs35]; simp only [stSwap]; exact haw34
                                                                          -- step 36: SWAP2 @286
                                                                          have st36 := swap2_xstep hc35 hp35 (by decide) hk35 (by first | (simp only [List.length_cons]; omega) | omega)
                                                                          by_cases g36 : g.toNat < C28 + 32
                                                                          · exact Or.inl (hX35.trans (stepOOG (k := k28+8) (C := C28+29) hg35 st36 (by omega) (by omega) (by omega)))
                                                                          · set s36 := stSwap s35 (val :: ⟨128⟩ :: ⟨84⟩ :: ⟨160⟩ :: Rt) with hs36
                                                                            have hX36 := hX35.trans (stepContinue (k := k28+8) (C := C28+29) hg35 st36 (by omega) (by omega))
                                                                            have hc36 : s36.executionEnv.code = powBytecode := by rw [hs36]; simp only [stSwap]; exact hc35
                                                                            have hp36 : s36.machineState.pc = ⟨287⟩ := by rw [hs36]; simp only [stSwap]; rw [hp35]; rfl
                                                                            have hg36 : s36.machineState.gasAvailable.toNat = g.toNat - (C28 + 32) := by
                                                                              rw [hs36]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                            have hk36 : s36.machineState.stack = val :: ⟨128⟩ :: ⟨84⟩ :: ⟨160⟩ :: Rt := by rw [hs36]; simp only [stSwap]
                                                                            have hmem36 : s36.machineState.memory = powMem2 val := by rw [hs36]; simp only [stSwap]; exact hmem35
                                                                            have haw36 : s36.machineState.activeWords = UInt256.ofNat 5 := by rw [hs36]; simp only [stSwap]; exact haw35
                                                                            -- step 37: POP @287
                                                                            have st37 := pop_xstep hc36 hp36 (by decide) hk36 (by first | (simp only [List.length_cons]; omega) | omega)
                                                                            by_cases g37 : g.toNat < C28 + 34
                                                                            · exact Or.inl (hX36.trans (stepOOG (k := k28+9) (C := C28+32) hg36 st37 (by omega) (by omega) (by omega)))
                                                                            · set s37 := stPop s36 (⟨128⟩ :: ⟨84⟩ :: ⟨160⟩ :: Rt) with hs37
                                                                              have hX37 := hX36.trans (stepContinue (k := k28+9) (C := C28+32) hg36 st37 (by omega) (by omega))
                                                                              have hc37 : s37.executionEnv.code = powBytecode := by rw [hs37]; simp only [stPop]; exact hc36
                                                                              have hp37 : s37.machineState.pc = ⟨288⟩ := by rw [hs37]; simp only [stPop]; rw [hp36]; rfl
                                                                              have hg37 : s37.machineState.gasAvailable.toNat = g.toNat - (C28 + 34) := by
                                                                                rw [hs37]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                              have hk37 : s37.machineState.stack = ⟨128⟩ :: ⟨84⟩ :: ⟨160⟩ :: Rt := by rw [hs37]; simp only [stPop]
                                                                              have hmem37 : s37.machineState.memory = powMem2 val := by rw [hs37]; simp only [stPop]; exact hmem36
                                                                              have haw37 : s37.machineState.activeWords = UInt256.ofNat 5 := by rw [hs37]; simp only [stPop]; exact haw36
                                                                              -- step 38: POP @288
                                                                              have st38 := pop_xstep hc37 hp37 (by decide) hk37 (by first | (simp only [List.length_cons]; omega) | omega)
                                                                              by_cases g38 : g.toNat < C28 + 36
                                                                              · exact Or.inl (hX37.trans (stepOOG (k := k28+10) (C := C28+34) hg37 st38 (by omega) (by omega) (by omega)))
                                                                              · set s38 := stPop s37 (⟨84⟩ :: ⟨160⟩ :: Rt) with hs38
                                                                                have hX38 := hX37.trans (stepContinue (k := k28+10) (C := C28+34) hg37 st38 (by omega) (by omega))
                                                                                have hc38 : s38.executionEnv.code = powBytecode := by rw [hs38]; simp only [stPop]; exact hc37
                                                                                have hp38 : s38.machineState.pc = ⟨289⟩ := by rw [hs38]; simp only [stPop]; rw [hp37]; rfl
                                                                                have hg38 : s38.machineState.gasAvailable.toNat = g.toNat - (C28 + 36) := by
                                                                                  rw [hs38]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                have hk38 : s38.machineState.stack = ⟨84⟩ :: ⟨160⟩ :: Rt := by rw [hs38]; simp only [stPop]
                                                                                have hmem38 : s38.machineState.memory = powMem2 val := by rw [hs38]; simp only [stPop]; exact hmem37
                                                                                have haw38 : s38.machineState.activeWords = UInt256.ofNat 5 := by rw [hs38]; simp only [stPop]; exact haw37
                                                                                -- step 39: JUMP @289 → 84
                                                                                have st39 := jump_xstep hc38 hp38 (by decide) hk38 (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by first | (simp only [List.length_cons]; omega) | omega)
                                                                                by_cases g39 : g.toNat < C28 + 44
                                                                                · exact Or.inl (hX38.trans (stepOOG (k := k28+11) (C := C28+36) (cost := 8) hg38 st39 (by omega) (by omega) (by omega)))
                                                                                · set s39 := stJump s38 ⟨84⟩ (⟨160⟩ :: Rt) with hs39
                                                                                  have hX39 := hX38.trans (stepContinue (k := k28+11) (C := C28+36) (cost := 8) hg38 st39 (by omega) (by omega))
                                                                                  have hc39 : s39.executionEnv.code = powBytecode := by rw [hs39]; simp only [stJump]; exact hc38
                                                                                  have hp39 : s39.machineState.pc = ⟨84⟩ := by rw [hs39]; simp only [stJump]
                                                                                  have hg39 : s39.machineState.gasAvailable.toNat = g.toNat - (C28 + 44) := by
                                                                                    rw [hs39]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                  have hk39 : s39.machineState.stack = ⟨160⟩ :: Rt := by rw [hs39]; simp only [stJump]
                                                                                  have hmem39 : s39.machineState.memory = powMem2 val := by rw [hs39]; simp only [stJump]; exact hmem38
                                                                                  have haw39 : s39.machineState.activeWords = UInt256.ofNat 5 := by rw [hs39]; simp only [stJump]; exact haw38
                                                                                  -- step 40: JUMPDEST @84
                                                                                  have st40 := jumpdest_xstep hc39 hp39 (by decide) (by rw [hk39]; simp only [List.length_cons]; omega)
                                                                                  by_cases g40 : g.toNat < C28 + 45
                                                                                  · exact Or.inl (hX39.trans (stepOOG (k := k28+12) (C := C28+44) hg39 st40 (by omega) (by omega) (by omega)))
                                                                                  · set s40 := stJumpdest s39 with hs40
                                                                                    have hX40 := hX39.trans (stepContinue (k := k28+12) (C := C28+44) hg39 st40 (by omega) (by omega))
                                                                                    have hc40 : s40.executionEnv.code = powBytecode := by rw [hs40]; simp only [stJumpdest]; exact hc39
                                                                                    have hp40 : s40.machineState.pc = ⟨85⟩ := by rw [hs40]; simp only [stJumpdest]; rw [hp39]; rfl
                                                                                    have hg40 : s40.machineState.gasAvailable.toNat = g.toNat - (C28 + 45) := by
                                                                                      rw [hs40]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                    have hk40 : s40.machineState.stack = ⟨160⟩ :: Rt := by rw [hs40]; simp only [stJumpdest]; exact hk39
                                                                                    have hmem40 : s40.machineState.memory = powMem2 val := by rw [hs40]; simp only [stJumpdest]; exact hmem39
                                                                                    have haw40 : s40.machineState.activeWords = UInt256.ofNat 5 := by rw [hs40]; simp only [stJumpdest]; exact haw39
                                                                                    -- step 41: PUSH1 64 @85
                                                                                    have st41 := push1_xstep (argv := ⟨64⟩) hc40 hp40 (by decide) hk40 (by first | (simp only [List.length_cons]; omega) | omega)
                                                                                    by_cases g41 : g.toNat < C28 + 48
                                                                                    · exact Or.inl (hX40.trans (stepOOG (k := k28+13) (C := C28+45) hg40 st41 (by omega) (by omega) (by omega)))
                                                                                    · set s41 := stPush1 s40 ⟨64⟩ with hs41
                                                                                      have hX41 := hX40.trans (stepContinue (k := k28+13) (C := C28+45) hg40 st41 (by omega) (by omega))
                                                                                      have hc41 : s41.executionEnv.code = powBytecode := by rw [hs41]; simp only [stPush1]; exact hc40
                                                                                      have hp41 : s41.machineState.pc = ⟨87⟩ := by rw [hs41]; simp only [stPush1]; rw [hp40]; rfl
                                                                                      have hg41 : s41.machineState.gasAvailable.toNat = g.toNat - (C28 + 48) := by
                                                                                        rw [hs41]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                      have hk41 : s41.machineState.stack = ⟨64⟩ :: ⟨160⟩ :: Rt := by rw [hs41]; simp only [stPush1, hk40]
                                                                                      have hmem41 : s41.machineState.memory = powMem2 val := by rw [hs41]; simp only [stPush1]; exact hmem40
                                                                                      have haw41 : s41.machineState.activeWords = UInt256.ofNat 5 := by rw [hs41]; simp only [stPush1]; exact haw40
                                                                                      -- step 42: MLOAD @87  (reads mem[64] = 128 again)
                                                                                      have h0₄₂ : s41.machineState.stack[0]! = (⟨64⟩:UInt256) := by rw [hk41]; rfl
                                                                                      have hmc42 : memoryExpansionCost s41 .MLOAD = 0 := by
                                                                                        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw41, h0₄₂]; decide
                                                                                      have st42 := mload_xstep hc41 hp41 (by decide) hk41 (by first | (simp only [List.length_cons]; omega) | omega)
                                                                                      rw [hmc42] at st42
                                                                                      by_cases g42 : g.toNat < C28 + 51
                                                                                      · exact Or.inl (hX41.trans (stepOOG (k := k28+14) (C := C28+48) (cost := 0+3) hg41 st42 (by omega) (by omega) (by omega)))
                                                                                      · set s42 := stMLoad s41 ⟨64⟩ (⟨160⟩ :: Rt) with hs42
                                                                                        have hX42 := hX41.trans (stepContinue (k := k28+14) (C := C28+48) (cost := 0+3) hg41 st42 (by omega) (by omega))
                                                                                        have hc42 : s42.executionEnv.code = powBytecode := by rw [hs42]; simp only [stMLoad]; exact hc41
                                                                                        have hp42 : s42.machineState.pc = ⟨88⟩ := by rw [hs42]; simp only [stMLoad]; rw [hp41]; rfl
                                                                                        have hg42 : s42.machineState.gasAvailable.toNat = g.toNat - (C28 + 51) := by
                                                                                          rw [hs42]; simp only [stMLoad, hmc42]; rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]; omega
                                                                                        have hk42 : s42.machineState.stack = ⟨128⟩ :: ⟨160⟩ :: Rt := by
                                                                                          rw [hs42]; simp only [stMLoad]; rw [if_neg (by rw [hmem41, powMem2_size, haw41]; decide)]
                                                                                          rw [hmem41, show (⟨64⟩:UInt256).toNat = 64 from by decide, powMem2_read64,
                                                                                            fromByteArrayBigEndian_toByteArray, show UInt256.ofNat ((⟨128⟩:UInt256).toNat) = ⟨128⟩ from by decide]
                                                                                        have hmem42 : s42.machineState.memory = powMem2 val := by rw [hs42]; simp only [stMLoad]; exact hmem41
                                                                                        have haw42 : s42.machineState.activeWords = UInt256.ofNat 5 := by rw [hs42]; simp only [stMLoad, haw41]; decide
                                                                                        -- step 43: DUP1 @88
                                                                                        have st43 := dup1_xstep hc42 hp42 (by decide) hk42 (by first | (simp only [List.length_cons]; omega) | omega)
                                                                                        by_cases g43 : g.toNat < C28 + 54
                                                                                        · exact Or.inl (hX42.trans (stepOOG (k := k28+15) (C := C28+51) hg42 st43 (by omega) (by omega) (by omega)))
                                                                                        · set s43 := stDup1 s42 ⟨128⟩ (⟨160⟩ :: Rt) with hs43
                                                                                          have hX43 := hX42.trans (stepContinue (k := k28+15) (C := C28+51) hg42 st43 (by omega) (by omega))
                                                                                          have hc43 : s43.executionEnv.code = powBytecode := by rw [hs43]; simp only [stDup1]; exact hc42
                                                                                          have hp43 : s43.machineState.pc = ⟨89⟩ := by rw [hs43]; simp only [stDup1]; rw [hp42]; rfl
                                                                                          have hg43 : s43.machineState.gasAvailable.toNat = g.toNat - (C28 + 54) := by
                                                                                            rw [hs43]; simp only [stDup1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                          have hk43 : s43.machineState.stack = ⟨128⟩ :: ⟨128⟩ :: ⟨160⟩ :: Rt := by rw [hs43]; simp only [stDup1]
                                                                                          have hmem43 : s43.machineState.memory = powMem2 val := by rw [hs43]; simp only [stDup1]; exact hmem42
                                                                                          have haw43 : s43.machineState.activeWords = UInt256.ofNat 5 := by rw [hs43]; simp only [stDup1]; exact haw42
                                                                                          -- step 44: SWAP2 @89
                                                                                          have st44 := swap2_xstep hc43 hp43 (by decide) hk43 (by first | (simp only [List.length_cons]; omega) | omega)
                                                                                          by_cases g44 : g.toNat < C28 + 57
                                                                                          · exact Or.inl (hX43.trans (stepOOG (k := k28+16) (C := C28+54) hg43 st44 (by omega) (by omega) (by omega)))
                                                                                          · set s44 := stSwap s43 (⟨160⟩ :: ⟨128⟩ :: ⟨128⟩ :: Rt) with hs44
                                                                                            have hX44 := hX43.trans (stepContinue (k := k28+16) (C := C28+54) hg43 st44 (by omega) (by omega))
                                                                                            have hc44 : s44.executionEnv.code = powBytecode := by rw [hs44]; simp only [stSwap]; exact hc43
                                                                                            have hp44 : s44.machineState.pc = ⟨90⟩ := by rw [hs44]; simp only [stSwap]; rw [hp43]; rfl
                                                                                            have hg44 : s44.machineState.gasAvailable.toNat = g.toNat - (C28 + 57) := by
                                                                                              rw [hs44]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                            have hk44 : s44.machineState.stack = ⟨160⟩ :: ⟨128⟩ :: ⟨128⟩ :: Rt := by rw [hs44]; simp only [stSwap]
                                                                                            have hmem44 : s44.machineState.memory = powMem2 val := by rw [hs44]; simp only [stSwap]; exact hmem43
                                                                                            have haw44 : s44.machineState.activeWords = UInt256.ofNat 5 := by rw [hs44]; simp only [stSwap]; exact haw43
                                                                                            -- step 45: SUB @90  (160 - 128 = 32)
                                                                                            have st45 := sub_xstep hc44 hp44 (by decide) hk44 (by first | (simp only [List.length_cons]; omega) | omega)
                                                                                            by_cases g45 : g.toNat < C28 + 60
                                                                                            · exact Or.inl (hX44.trans (stepOOG (k := k28+17) (C := C28+57) hg44 st45 (by omega) (by omega) (by omega)))
                                                                                            · set s45 := stBinop s44 (UInt256.sub ⟨160⟩ ⟨128⟩) (⟨128⟩ :: Rt) with hs45
                                                                                              have hX45 := hX44.trans (stepContinue (k := k28+17) (C := C28+57) hg44 st45 (by omega) (by omega))
                                                                                              have hc45 : s45.executionEnv.code = powBytecode := by rw [hs45]; simp only [stBinop]; exact hc44
                                                                                              have hp45 : s45.machineState.pc = ⟨91⟩ := by rw [hs45]; simp only [stBinop]; rw [hp44]; rfl
                                                                                              have hg45 : s45.machineState.gasAvailable.toNat = g.toNat - (C28 + 60) := by
                                                                                                rw [hs45]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                              have hk45 : s45.machineState.stack = ⟨32⟩ :: ⟨128⟩ :: Rt := by rw [hs45]; simp only [stBinop]; rw [sub_160_128]
                                                                                              have hmem45 : s45.machineState.memory = powMem2 val := by rw [hs45]; simp only [stBinop]; exact hmem44
                                                                                              have haw45 : s45.machineState.activeWords = UInt256.ofNat 5 := by rw [hs45]; simp only [stBinop]; exact haw44
                                                                                              -- step 46: SWAP1 @91
                                                                                              have st46 := swap1_xstep hc45 hp45 (by decide) hk45 (by first | (simp only [List.length_cons]; omega) | omega)
                                                                                              by_cases g46 : g.toNat < C28 + 63
                                                                                              · exact Or.inl (hX45.trans (stepOOG (k := k28+18) (C := C28+60) hg45 st46 (by omega) (by omega) (by omega)))
                                                                                              · set s46 := stSwap s45 (⟨128⟩ :: ⟨32⟩ :: Rt) with hs46
                                                                                                have hX46 := hX45.trans (stepContinue (k := k28+18) (C := C28+60) hg45 st46 (by omega) (by omega))
                                                                                                have hc46 : s46.executionEnv.code = powBytecode := by rw [hs46]; simp only [stSwap]; exact hc45
                                                                                                have hp46 : s46.machineState.pc = ⟨92⟩ := by rw [hs46]; simp only [stSwap]; rw [hp45]; rfl
                                                                                                have hg46 : s46.machineState.gasAvailable.toNat = g.toNat - (C28 + 63) := by
                                                                                                  rw [hs46]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                have hk46 : s46.machineState.stack = ⟨128⟩ :: ⟨32⟩ :: Rt := by rw [hs46]; simp only [stSwap]
                                                                                                have hmem46 : s46.machineState.memory = powMem2 val := by rw [hs46]; simp only [stSwap]; exact hmem45
                                                                                                have haw46 : s46.machineState.activeWords = UInt256.ofNat 5 := by rw [hs46]; simp only [stSwap]; exact haw45
                                                                                                -- step 47: RETURN @92  (returns mem[128 .. 160] = toByteArray val)
                                                                                                have h0ᵣ : s46.machineState.stack[0]! = (⟨128⟩:UInt256) := by rw [hk46]; rfl
                                                                                                have h1ᵣ : s46.machineState.stack[1]! = (⟨32⟩:UInt256) := by rw [hk46]; rfl
                                                                                                have hmcr : memoryExpansionCost s46 .RETURN = 0 := by
                                                                                                  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw46, h0ᵣ, h1ᵣ]; decide
                                                                                                have st47 := return_xstep hc46 hp46 (by decide) hk46 (by first | (simp only [List.length_cons]; omega) | omega)
                                                                                                rw [hmcr,
                                                                                                  show s46.machineState.memory.readWithPadding (⟨128⟩:UInt256).toNat (⟨32⟩:UInt256).toNat
                                                                                                      = UInt256.toByteArray val from by
                                                                                                    rw [hmem46, show (⟨128⟩:UInt256).toNat = 128 from by decide,
                                                                                                      show (⟨32⟩:UInt256).toNat = 32 from by decide, powMem2_read128]] at st47
                                                                                                refine Or.inr ⟨stReturn s46 ⟨128⟩ ⟨32⟩ Rt, ?_⟩
                                                                                                exact hX46.trans (stepHaltSuccess (k := k28+19) (C := C28+63) (cost := 0) hg46 st47 (by omega) (by omega))

/-! ## Full success trace — `initState → RETURN(2^n)` (**proved**)

Composes the six forward segments (dispatcher → decode → require → loop → exit → encoder) for a
well-formed `pow2(n)` call with `callvalue = 0`, `calldatasize ≥ 36`, matching selector, and
`n < 256`.  Either the run OOGs, or it succeeds returning the 32-byte big-endian word `2^n`. -/
set_option maxHeartbeats 1000000 in
theorem powX_success {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hn : (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat < 256) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ s', X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
          = .ok (.success s'
              (UInt256.toByteArray
                (UInt256.ofNat (2 ^ (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat)))) := by
  have hsize : I.calldata.size < UInt256.size := by
    have h0 : (2:ℕ)^255 < 2^256 := by norm_num
    have hp : (2:ℕ)^255 < UInt256.size := by simpa [UInt256.size] using h0
    omega
  -- the selector word and the decoded argument
  set sel := UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ with hsel
  set arg := uInt256OfByteArray (I.calldata.readBytes 4 32) with harg
  rcases powX_disp hcode hwv (by omega) hsize hmatch with
    hd | ⟨s1, hX1, hee1, hp1, hg1, hstk1, haw1, hmem1, hC1⟩
  · exact Or.inl hd
  · rcases powX_decode (s0 := initState cA gh bl σ σ₀ g A I) (I := I) (k := 24) (C := 96)
        (by rw [hee1]; exact hcode) hee1 hp1 hstk1 hsz36 hsz255 hg1 (by norm_num) hC1 hX1 with
      hd | ⟨k2, C2, s2, hX2, hc2, hp2, hstk2, hg2, hk2, hCg2, hmem2, haw2⟩
    · exact Or.inl hd
    · rcases powX_require (n := arg) (sel := sel) (R := []) hc2 hp2 hstk2 hn
          (by simp only [List.length_nil]; omega) hg2 hk2 hCg2 hX2 with
        hd | ⟨k3, C3, s3, hX3, hc3, hp3, hstk3, hg3, hk3, hCg3, hmem3, haw3⟩
      · exact Or.inl hd
      · rcases powLoopCore (slot := ⟨0⟩) (n := arg) (REST := [⟨71⟩, sel])
            hn (by simp only [List.length_cons, List.length_nil]; omega)
            arg.toNat ⟨0⟩ ⟨1⟩ k3 C3 s3
            (by rw [show (⟨0⟩:UInt256).toNat = 0 from by decide]; omega)
            (by decide)
            (by rw [show (⟨0⟩:UInt256).toNat = 0 from by decide]; omega)
            hc3 hp3 hstk3 hg3 hk3 hCg3 hX3 with
          hd | ⟨k4, C4, s4, hX4, hc4, hp4, hstk4, hg4, hk4, hCg4, hmem4, haw4⟩
        · exact Or.inl hd
        · rcases powX_exit (a := arg) (val := UInt256.ofNat (2 ^ arg.toNat)) (c := ⟨0⟩)
              (d := arg) (ret := ⟨71⟩) (Rt := [sel]) hc4 hp4 hstk4
              (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
              (by simp only [List.length_cons, List.length_nil]; omega) hg4 hk4 hCg4 hX4 with
            hd | ⟨k5, C5, s5, hX5, hc5, hp5, hstk5, hg5, hk5, hCg5, hmem5, haw5⟩
          · exact Or.inl hd
          · have hmemS : s5.machineState.memory = solcFreePtrMem := by
              rw [hmem5, hmem4, hmem3, hmem2, hmem1]
            have hawS : s5.machineState.activeWords = UInt256.ofNat 3 := by
              rw [haw5, haw4, haw3, haw2, haw1]
            rcases powX_encode (val := UInt256.ofNat (2 ^ arg.toNat)) (Rt := [sel])
                hc5 hp5 hstk5 hmemS hawS (by simp only [List.length_cons, List.length_nil]; omega)
                hg5 hk5 hCg5 hX5 with
              hd | ⟨s6, hX6⟩
            · exact Or.inl hd
            · exact Or.inr ⟨s6, hX6⟩

/-- Lift the success trace to `Ξ`: either out-of-gas, or success returning the 32-byte
    big-endian encoding of `2^n`, with `σ`/`createdAccounts`/substate carried by the final state. -/
theorem powXi_success {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hn : (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat < 256) :
    Ξ cA gh bl σ σ₀ g A I = .error .OutOfGass
      ∨ ∃ s', Ξ cA gh bl σ σ₀ g A I
                = .ok (.success s'
                    (UInt256.toByteArray
                      (UInt256.ofNat (2 ^ (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat)))) := by
  rcases powX_success hcode hwv hsz36 hsz255 hmatch hn with hoog | ⟨s, hX⟩
  · exact Or.inl (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
  · exact Or.inr ⟨_, Xi_success_of_X (by rw [← hcode] at hX; exact hX)⟩

/-! ## Act-side facts for `pow2` -/

/-- Dispatch reduces (via `powSelectorBytes`) to a 4-byte calldata-prefix comparison. -/
theorem powDispatch_eq (cd : ByteArray) :
    dispatchMsg Pow.powContract cd
      = if ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == cd.extract 0 4)
        then some Pow.powTransition else none := by
  simp only [dispatchMsg, Pow.powContract, List.map_cons, List.map_nil, List.find?_cons,
    List.find?_nil, Prod.map, id_eq, Function.comp_apply]
  rw [powSelectorBytes]
  by_cases hb : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == cd.extract 0 4) = true
  · simp [hb]
  · simp only [Bool.not_eq_true] at hb; simp [hb]

/-- `powContract` has exactly one transition, so any successful dispatch yields it. -/
theorem powDispatch_unique {cd : ByteArray} {t : TransitionDecl}
    (h : dispatchMsg Pow.powContract cd = some t) : t = Pow.powTransition := by
  simp only [dispatchMsg, Pow.powContract, List.map_cons, List.map_nil] at h
  split at h
  · rename_i pair heq
    have hmem := List.mem_of_find?_eq_some heq
    simp only [List.mem_singleton, Prod.map, id_eq, Prod.mk.injEq] at hmem
    rw [Option.some.injEq] at h
    rw [← h, hmem.1]
  · exact absurd h (by simp)

/-- Short calldata (< 4 bytes) ⇒ dispatch fails. -/
theorem powDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg Pow.powContract cd = none := by
  rw [powDispatch_eq]
  have hfalse : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == cd.extract 0 4) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have hsz := TruthClaude.Theory.byteArray_size_eq_of_beq hc
    rw [ByteArray.size_extract] at hsz
    simp only [show (⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray).size = 4 from rfl] at hsz
    omega
  simp [hfalse]

/-- Selector mismatch ⇒ dispatch fails. -/
theorem powDispatch_none_nomatch {cd : ByteArray}
    (h : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == cd.extract 0 4) = false) :
    dispatchMsg Pow.powContract cd = none := by
  rw [powDispatch_eq]; simp [h]
