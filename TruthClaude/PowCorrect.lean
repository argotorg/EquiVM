import TruthClaude.Theory
import TruthClaude.Stepping
import TruthClaude.Memory
import TruthClaude.Solc
import TruthClaude.Pow

/-!
# PowCorrect — runtime equivalence for `Pow.sol`'s `pow2(uint256 n)`

Mirrors `TruthCorrect.lean`, but the contract has a function argument and a **`while` loop** over a
symbolic `n` (computing `2^n`, guarded `n < 256`).  This is the first loop example; we build it
Truth-style and factor reusable / solc-boilerplate lemmas out as they emerge.
-/

open Act ABI Ethereum Ethereum.EVM TruthClaude.Theory

set_option maxRecDepth 10000

/-- The deployed runtime bytecode of `Pow.sol` (solc 0.8.35, Shanghai, optimizer off, no metadata). -/
def powBytecode : ByteArray :=
  ⟨#[96, 128, 96, 64, 82, 52, 128, 21, 97, 0, 15, 87, 95, 95, 253, 91, 80, 96, 4, 54, 16, 97, 0, 41,
    87, 95, 53, 96, 224, 28, 128, 99, 68, 43, 127, 251, 20, 97, 0, 45, 87, 91, 95, 95, 253, 91, 97,
    0, 71, 96, 4, 128, 54, 3, 129, 1, 144, 97, 0, 66, 145, 144, 97, 0, 207, 86, 91, 97, 0, 93, 86,
    91, 96, 64, 81, 97, 0, 84, 145, 144, 97, 1, 9, 86, 91, 96, 64, 81, 128, 145, 3, 144, 243, 91,
    95, 97, 1, 0, 130, 16, 97, 0, 107, 87, 95, 95, 253, 91, 95, 96, 1, 144, 80, 95, 95, 144, 80, 91,
    131, 129, 16, 21, 97, 0, 142, 87, 96, 2, 130, 2, 145, 80, 96, 1, 129, 1, 144, 80, 97, 0, 117,
    86, 91, 129, 146, 80, 80, 80, 145, 144, 80, 86, 91, 95, 95, 253, 91, 95, 129, 144, 80, 145, 144,
    80, 86, 91, 97, 0, 174, 129, 97, 0, 156, 86, 91, 129, 20, 97, 0, 184, 87, 95, 95, 253, 91, 80,
    86, 91, 95, 129, 53, 144, 80, 97, 0, 201, 129, 97, 0, 165, 86, 91, 146, 145, 80, 80, 86, 91, 95,
    96, 32, 130, 132, 3, 18, 21, 97, 0, 228, 87, 97, 0, 227, 97, 0, 152, 86, 91, 91, 95, 97, 0, 241,
    132, 130, 133, 1, 97, 0, 187, 86, 91, 145, 80, 80, 146, 145, 80, 80, 86, 91, 97, 1, 3, 129, 97,
    0, 156, 86, 91, 130, 82, 80, 80, 86, 91, 95, 96, 32, 130, 1, 144, 80, 97, 1, 28, 95, 131, 1,
    132, 97, 0, 250, 86, 91, 146, 145, 80, 80, 86]⟩

/-- Configuration: empty storage layout, default external-call ABI (same as `truthConfig`). -/
def powConfig : Config :=
  { storage := { layout := fun _ => none }
    externalABI := defaultExternalCallABI }

/-! ## Trusted axioms (same two opaque ones as Truth; see MISSPEC.md) -/

/-- `keccak("pow2(uint256)")[0:4] = 0x442b7ffb`. -/
axiom powSelectorBytes :
    (ffi.KEC (String.toByteArray (Act.transitionSigStr Pow.powTransition))).extract 0 4
      = ⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩

/-- The `JUMPDEST` set of `powBytecode` (confirmed by `#eval`; `D_J_aux` is `partial`). -/
axiom powValidJumps :
    Ethereum.EVM.D_J powBytecode ⟨0⟩
      = #[⟨15⟩, ⟨41⟩, ⟨45⟩, ⟨66⟩, ⟨71⟩, ⟨84⟩, ⟨93⟩, ⟨107⟩, ⟨117⟩, ⟨142⟩, ⟨152⟩, ⟨156⟩, ⟨165⟩,
          ⟨174⟩, ⟨184⟩, ⟨187⟩, ⟨201⟩, ⟨207⟩, ⟨227⟩, ⟨228⟩, ⟨241⟩, ⟨250⟩, ⟨259⟩, ⟨265⟩, ⟨284⟩]

/-- **Selector decode for `pow2`** (instance of the generic `evmSelectorDecode`): the EVM check
    `eq(0x442b7ffb, SHR(calldataload 0, 224))` equals the dispatcher's 4-byte compare. -/
theorem powEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨1143701499⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0x44 0x2b 0x7f 0xfb ⟨1143701499⟩ (by decide)

/-! ## The loop core (crux) — **proved**

`while (i < n) { r *= 2; i += 1; }`: header `0x75 = 117`, body `0x7e–0x8d`, exit `0x8e = 142`.
Invariant `r = 2^i ∧ i ≤ n < 256`, variant `n − i`.  Proved by induction on the variant; the base
case (`i = n`) is the 7-step guard ending in the taken `JUMPI` to the exit, and each inductive step
is the 19-step body (guard not taken → `r*=2; i+=1` → back-jump) followed by the IH.  The gas `C`
is carried *symbolically* (it grows by 67 per iteration); the OOG-absorbing disjunction means we
never need a closed-form total — confirming the symbolic-gas-under-induction story. -/

theorem powLoopCore {g : UInt256} {s0 : State} {slot n ret : UInt256} (hn : n.toNat < 256) :
    ∀ (var : ℕ) (i r : UInt256) (k C : ℕ) (s : State),
      n.toNat - i.toNat = var → r.toNat = 2 ^ i.toNat → i.toNat ≤ n.toNat →
      s.executionEnv.code = powBytecode → s.machineState.pc = ⟨117⟩ →
      s.machineState.stack = [i, r, slot, n, ret] →
      s.machineState.gasAvailable.toNat = g.toNat - C → k ≤ C → C ≤ g.toNat →
      X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s →
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ (k' C' : ℕ) (s' : State),
          X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k') (D_J powBytecode ⟨0⟩) s'
        ∧ s'.executionEnv.code = powBytecode ∧ s'.machineState.pc = ⟨142⟩
        ∧ s'.machineState.stack = [n, UInt256.ofNat (2 ^ n.toNat), slot, n, ret]
        ∧ s'.machineState.gasAvailable.toNat = g.toNat - C' ∧ k' ≤ C' ∧ C' ≤ g.toNat := by
  intro var
  induction var with
  | zero =>
    intro i r k C s hvar hinv hile hcode hpc hstk hgas hkC hCg hX
    have hin : i.toNat = n.toNat := by omega
    have hieqn : i = n := u256_inj hin
    have hreq : r = UInt256.ofNat (2 ^ n.toNat) :=
      u256_inj (by rw [hinv, hin, ofNat_pow_toNat hn])
    have st0 := jumpdest_xstep hcode hpc (by decide) (by rw [hstk]; simp)
    by_cases g0 : g.toNat < C + 1
    · exact Or.inl (hX.trans (stepOOG (cost:=1) hgas st0 hkC hCg (by omega)))
    · set s1 := stJumpdest s with hs1
      have hX1 := hX.trans (stepContinue (k:=k) (C:=C) (cost:=1) hgas st0 hkC (by omega))
      have hc1 : s1.executionEnv.code = powBytecode := by rw [hs1]; simp only [stJumpdest]; exact hcode
      have hp1 : s1.machineState.pc = ⟨118⟩ := by rw [hs1]; simp only [stJumpdest]; rw [hpc]; rfl
      have hg1 : s1.machineState.gasAvailable.toNat = g.toNat - (C+1) := by
        rw [hs1]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
      have hk1 : s1.machineState.stack = [i,r,slot,n,ret] := by rw [hs1]; simp only [stJumpdest]; exact hstk
      have st1 := dup4_xstep hc1 hp1 (by decide) hk1 (by norm_num)
      by_cases g1 : g.toNat < C + 4
      · exact Or.inl (hX1.trans (stepOOG (k:=k+1) (C:=C+1) (cost:=3) hg1 st1 (by omega) (by omega) (by omega)))
      · set s2 := stSwap s1 [n,i,r,slot,n,ret] with hs2
        have hX2 := hX1.trans (stepContinue (k:=k+1) (C:=C+1) (cost:=3) hg1 st1 (by omega) (by omega))
        have hc2 : s2.executionEnv.code = powBytecode := by rw [hs2]; simp only [stSwap]; exact hc1
        have hp2 : s2.machineState.pc = ⟨119⟩ := by rw [hs2]; simp only [stSwap]; rw [hp1]; rfl
        have hg2 : s2.machineState.gasAvailable.toNat = g.toNat - (C+4) := by
          rw [hs2]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
        have hk2 : s2.machineState.stack = [n,i,r,slot,n,ret] := by rw [hs2]; simp only [stSwap]
        have st2 := dup2_xstep hc2 hp2 (by decide) hk2 (by norm_num)
        by_cases g2 : g.toNat < C + 7
        · exact Or.inl (hX2.trans (stepOOG (k:=k+2) (C:=C+4) (cost:=3) hg2 st2 (by omega) (by omega) (by omega)))
        · set s3 := stSwap s2 [i,n,i,r,slot,n,ret] with hs3
          have hX3 := hX2.trans (stepContinue (k:=k+2) (C:=C+4) (cost:=3) hg2 st2 (by omega) (by omega))
          have hc3 : s3.executionEnv.code = powBytecode := by rw [hs3]; simp only [stSwap]; exact hc2
          have hp3 : s3.machineState.pc = ⟨120⟩ := by rw [hs3]; simp only [stSwap]; rw [hp2]; rfl
          have hg3 : s3.machineState.gasAvailable.toNat = g.toNat - (C+7) := by
            rw [hs3]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
          have hk3 : s3.machineState.stack = [i,n,i,r,slot,n,ret] := by rw [hs3]; simp only [stSwap]
          have st3 := lt_xstep hc3 hp3 (by decide) hk3 (by norm_num)
          by_cases g3 : g.toNat < C + 10
          · exact Or.inl (hX3.trans (stepOOG (k:=k+3) (C:=C+7) (cost:=3) hg3 st3 (by omega) (by omega) (by omega)))
          · set s4 := stBinop s3 (UInt256.lt i n) [i,r,slot,n,ret] with hs4
            have hX4 := hX3.trans (stepContinue (k:=k+3) (C:=C+7) (cost:=3) hg3 st3 (by omega) (by omega))
            have hc4 : s4.executionEnv.code = powBytecode := by rw [hs4]; simp only [stBinop]; exact hc3
            have hp4 : s4.machineState.pc = ⟨121⟩ := by rw [hs4]; simp only [stBinop]; rw [hp3]; rfl
            have hg4 : s4.machineState.gasAvailable.toNat = g.toNat - (C+10) := by
              rw [hs4]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
            have hk4 : s4.machineState.stack = [⟨0⟩,i,r,slot,n,ret] := by
              rw [hs4]; simp only [stBinop]; rw [ult_zero (by omega)]
            have st4 := iszero_xstep hc4 hp4 (by decide) hk4 (by norm_num)
            by_cases g4 : g.toNat < C + 13
            · exact Or.inl (hX4.trans (stepOOG (k:=k+4) (C:=C+10) (cost:=3) hg4 st4 (by omega) (by omega) (by omega)))
            · set s5 := stIsZero s4 ⟨0⟩ [i,r,slot,n,ret] with hs5
              have hX5 := hX4.trans (stepContinue (k:=k+4) (C:=C+10) (cost:=3) hg4 st4 (by omega) (by omega))
              have hc5 : s5.executionEnv.code = powBytecode := by rw [hs5]; simp only [stIsZero]; exact hc4
              have hp5 : s5.machineState.pc = ⟨122⟩ := by rw [hs5]; simp only [stIsZero]; rw [hp4]; rfl
              have hg5 : s5.machineState.gasAvailable.toNat = g.toNat - (C+13) := by
                rw [hs5]; simp only [stIsZero]; rw [toNat_sub_ofNat (by omega)]; omega
              have hk5 : s5.machineState.stack = [⟨1⟩,i,r,slot,n,ret] := by
                rw [hs5]; simp only [stIsZero]; rw [show UInt256.isZero ⟨0⟩ = ⟨1⟩ from by decide]
              have st5 := push2_xstep (argv:=⟨142⟩) hc5 hp5 (by decide) hk5 (by norm_num)
              by_cases g5 : g.toNat < C + 16
              · exact Or.inl (hX5.trans (stepOOG (k:=k+5) (C:=C+13) (cost:=3) hg5 st5 (by omega) (by omega) (by omega)))
              · set s6 := stPush2 s5 ⟨142⟩ with hs6
                have hX6 := hX5.trans (stepContinue (k:=k+5) (C:=C+13) (cost:=3) hg5 st5 (by omega) (by omega))
                have hc6 : s6.executionEnv.code = powBytecode := by rw [hs6]; simp only [stPush2]; exact hc5
                have hp6 : s6.machineState.pc = ⟨125⟩ := by rw [hs6]; simp only [stPush2]; rw [hp5]; rfl
                have hg6 : s6.machineState.gasAvailable.toNat = g.toNat - (C+16) := by
                  rw [hs6]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                have hk6 : s6.machineState.stack = [⟨142⟩,⟨1⟩,i,r,slot,n,ret] := by
                  rw [hs6]; simp only [stPush2, hk5]
                have st6 := jumpi_t_xstep hc6 hp6 (by decide) hk6 (by decide)
                  (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
                by_cases g6 : g.toNat < C + 26
                · exact Or.inl (hX6.trans (stepOOG (k:=k+6) (C:=C+16) (cost:=10) hg6 st6 (by omega) (by omega) (by omega)))
                · set s7 := stJumpiT s6 ⟨142⟩ [i,r,slot,n,ret] with hs7
                  have hX7 := hX6.trans (stepContinue (k:=k+6) (C:=C+16) (cost:=10) hg6 st6 (by omega) (by omega))
                  refine Or.inr ⟨k+7, C+26, s7, ?_, ?_, ?_, ?_, ?_, by omega, by omega⟩
                  · have he : g.toNat + 1 - (k + 6 + 1) = g.toNat + 1 - (k+7) := by omega
                    rw [← he]; exact hX7
                  · rw [hs7]; simp only [stJumpiT]; exact hc6
                  · rw [hs7]; simp only [stJumpiT]
                  · rw [hs7]; simp only [stJumpiT]; rw [hieqn, hreq]
                  · rw [hs7]; simp only [stJumpiT]; rw [toNat_sub_ofNat (by omega)]; omega
  | succ var ih =>
    intro i r k C s hvar hinv hile hcode hpc hstk hgas hkC hCg hX
    have hilt : i.toNat < n.toNat := by omega
    -- guard (7 steps), JUMPI NOT taken (i < n) → body
    have st0 := jumpdest_xstep hcode hpc (by decide) (by rw [hstk]; simp)
    by_cases g0 : g.toNat < C + 1
    · exact Or.inl (hX.trans (stepOOG (cost:=1) hgas st0 hkC hCg (by omega)))
    · set s1 := stJumpdest s with hs1
      have hX1 := hX.trans (stepContinue (k:=k) (C:=C) (cost:=1) hgas st0 hkC (by omega))
      have hc1 : s1.executionEnv.code = powBytecode := by rw [hs1]; simp only [stJumpdest]; exact hcode
      have hp1 : s1.machineState.pc = ⟨118⟩ := by rw [hs1]; simp only [stJumpdest]; rw [hpc]; rfl
      have hg1 : s1.machineState.gasAvailable.toNat = g.toNat - (C+1) := by
        rw [hs1]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
      have hk1 : s1.machineState.stack = [i,r,slot,n,ret] := by rw [hs1]; simp only [stJumpdest]; exact hstk
      have st1 := dup4_xstep hc1 hp1 (by decide) hk1 (by norm_num)
      by_cases g1 : g.toNat < C + 4
      · exact Or.inl (hX1.trans (stepOOG (k:=k+1) (C:=C+1) (cost:=3) hg1 st1 (by omega) (by omega) (by omega)))
      · set s2 := stSwap s1 [n,i,r,slot,n,ret] with hs2
        have hX2 := hX1.trans (stepContinue (k:=k+1) (C:=C+1) (cost:=3) hg1 st1 (by omega) (by omega))
        have hc2 : s2.executionEnv.code = powBytecode := by rw [hs2]; simp only [stSwap]; exact hc1
        have hp2 : s2.machineState.pc = ⟨119⟩ := by rw [hs2]; simp only [stSwap]; rw [hp1]; rfl
        have hg2 : s2.machineState.gasAvailable.toNat = g.toNat - (C+4) := by
          rw [hs2]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
        have hk2 : s2.machineState.stack = [n,i,r,slot,n,ret] := by rw [hs2]; simp only [stSwap]
        have st2 := dup2_xstep hc2 hp2 (by decide) hk2 (by norm_num)
        by_cases g2 : g.toNat < C + 7
        · exact Or.inl (hX2.trans (stepOOG (k:=k+2) (C:=C+4) (cost:=3) hg2 st2 (by omega) (by omega) (by omega)))
        · set s3 := stSwap s2 [i,n,i,r,slot,n,ret] with hs3
          have hX3 := hX2.trans (stepContinue (k:=k+2) (C:=C+4) (cost:=3) hg2 st2 (by omega) (by omega))
          have hc3 : s3.executionEnv.code = powBytecode := by rw [hs3]; simp only [stSwap]; exact hc2
          have hp3 : s3.machineState.pc = ⟨120⟩ := by rw [hs3]; simp only [stSwap]; rw [hp2]; rfl
          have hg3 : s3.machineState.gasAvailable.toNat = g.toNat - (C+7) := by
            rw [hs3]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
          have hk3 : s3.machineState.stack = [i,n,i,r,slot,n,ret] := by rw [hs3]; simp only [stSwap]
          have st3 := lt_xstep hc3 hp3 (by decide) hk3 (by norm_num)
          by_cases g3 : g.toNat < C + 10
          · exact Or.inl (hX3.trans (stepOOG (k:=k+3) (C:=C+7) (cost:=3) hg3 st3 (by omega) (by omega) (by omega)))
          · set s4 := stBinop s3 (UInt256.lt i n) [i,r,slot,n,ret] with hs4
            have hX4 := hX3.trans (stepContinue (k:=k+3) (C:=C+7) (cost:=3) hg3 st3 (by omega) (by omega))
            have hc4 : s4.executionEnv.code = powBytecode := by rw [hs4]; simp only [stBinop]; exact hc3
            have hp4 : s4.machineState.pc = ⟨121⟩ := by rw [hs4]; simp only [stBinop]; rw [hp3]; rfl
            have hg4 : s4.machineState.gasAvailable.toNat = g.toNat - (C+10) := by
              rw [hs4]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
            have hk4 : s4.machineState.stack = [⟨1⟩,i,r,slot,n,ret] := by
              rw [hs4]; simp only [stBinop]; rw [ult_one hilt]
            have st4 := iszero_xstep hc4 hp4 (by decide) hk4 (by norm_num)
            by_cases g4 : g.toNat < C + 13
            · exact Or.inl (hX4.trans (stepOOG (k:=k+4) (C:=C+10) (cost:=3) hg4 st4 (by omega) (by omega) (by omega)))
            · set s5 := stIsZero s4 ⟨1⟩ [i,r,slot,n,ret] with hs5
              have hX5 := hX4.trans (stepContinue (k:=k+4) (C:=C+10) (cost:=3) hg4 st4 (by omega) (by omega))
              have hc5 : s5.executionEnv.code = powBytecode := by rw [hs5]; simp only [stIsZero]; exact hc4
              have hp5 : s5.machineState.pc = ⟨122⟩ := by rw [hs5]; simp only [stIsZero]; rw [hp4]; rfl
              have hg5 : s5.machineState.gasAvailable.toNat = g.toNat - (C+13) := by
                rw [hs5]; simp only [stIsZero]; rw [toNat_sub_ofNat (by omega)]; omega
              have hk5 : s5.machineState.stack = [⟨0⟩,i,r,slot,n,ret] := by
                rw [hs5]; simp only [stIsZero]; rw [show UInt256.isZero ⟨1⟩ = ⟨0⟩ from by decide]
              have st5 := push2_xstep (argv:=⟨142⟩) hc5 hp5 (by decide) hk5 (by norm_num)
              by_cases g5 : g.toNat < C + 16
              · exact Or.inl (hX5.trans (stepOOG (k:=k+5) (C:=C+13) (cost:=3) hg5 st5 (by omega) (by omega) (by omega)))
              · set s6 := stPush2 s5 ⟨142⟩ with hs6
                have hX6 := hX5.trans (stepContinue (k:=k+5) (C:=C+13) (cost:=3) hg5 st5 (by omega) (by omega))
                have hc6 : s6.executionEnv.code = powBytecode := by rw [hs6]; simp only [stPush2]; exact hc5
                have hp6 : s6.machineState.pc = ⟨125⟩ := by rw [hs6]; simp only [stPush2]; rw [hp5]; rfl
                have hg6 : s6.machineState.gasAvailable.toNat = g.toNat - (C+16) := by
                  rw [hs6]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                have hk6 : s6.machineState.stack = [⟨142⟩,⟨0⟩,i,r,slot,n,ret] := by
                  rw [hs6]; simp only [stPush2, hk5]
                have st6 := jumpi_nt_xstep hc6 hp6 (by decide) hk6 (by norm_num)
                by_cases g6 : g.toNat < C + 26
                · exact Or.inl (hX6.trans (stepOOG (k:=k+6) (C:=C+16) (cost:=10) hg6 st6 (by omega) (by omega) (by omega)))
                · set s7 := stJumpiNT s6 [i,r,slot,n,ret] with hs7
                  have hX7 := hX6.trans (stepContinue (k:=k+6) (C:=C+16) (cost:=10) hg6 st6 (by omega) (by omega))
                  have hc7 : s7.executionEnv.code = powBytecode := by rw [hs7]; simp only [stJumpiNT]; exact hc6
                  have hp7 : s7.machineState.pc = ⟨126⟩ := by rw [hs7]; simp only [stJumpiNT]; rw [hp6]; rfl
                  have hg7 : s7.machineState.gasAvailable.toNat = g.toNat - (C+26) := by
                    rw [hs7]; simp only [stJumpiNT]; rw [toNat_sub_ofNat (by omega)]; omega
                  have hk7 : s7.machineState.stack = [i,r,slot,n,ret] := by rw [hs7]; simp only [stJumpiNT]
                  have st7 := push1_xstep (argv:=⟨2⟩) hc7 hp7 (by decide) hk7 (by norm_num)
                  by_cases g7 : g.toNat < C + 29
                  · exact Or.inl (hX7.trans (stepOOG (k:=k+7) (C:=C+26) (cost:=3) hg7 st7 (by omega) (by omega) (by omega)))
                  · set s8 := stPush1 s7 ⟨2⟩ with hs8
                    have hX8 := hX7.trans (stepContinue (k:=k+7) (C:=C+26) (cost:=3) hg7 st7 (by omega) (by omega))
                    have hc8 : s8.executionEnv.code = powBytecode := by rw [hs8]; simp only [stPush1]; exact hc7
                    have hp8 : s8.machineState.pc = ⟨128⟩ := by rw [hs8]; simp only [stPush1]; rw [hp7]; rfl
                    have hg8 : s8.machineState.gasAvailable.toNat = g.toNat - (C+29) := by
                      rw [hs8]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                    have hk8 : s8.machineState.stack = [⟨2⟩,i,r,slot,n,ret] := by rw [hs8]; simp only [stPush1, hk7]
                    have st8 := dup3_xstep hc8 hp8 (by decide) hk8 (by norm_num)
                    by_cases g8 : g.toNat < C + 32
                    · exact Or.inl (hX8.trans (stepOOG (k:=k+8) (C:=C+29) (cost:=3) hg8 st8 (by omega) (by omega) (by omega)))
                    · set s9 := stSwap s8 [r,⟨2⟩,i,r,slot,n,ret] with hs9
                      have hX9 := hX8.trans (stepContinue (k:=k+8) (C:=C+29) (cost:=3) hg8 st8 (by omega) (by omega))
                      have hc9 : s9.executionEnv.code = powBytecode := by rw [hs9]; simp only [stSwap]; exact hc8
                      have hp9 : s9.machineState.pc = ⟨129⟩ := by rw [hs9]; simp only [stSwap]; rw [hp8]; rfl
                      have hg9 : s9.machineState.gasAvailable.toNat = g.toNat - (C+32) := by
                        rw [hs9]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                      have hk9 : s9.machineState.stack = [r,⟨2⟩,i,r,slot,n,ret] := by rw [hs9]; simp only [stSwap]
                      have st9 := mul_xstep hc9 hp9 (by decide) hk9 (by norm_num)
                      by_cases g9 : g.toNat < C + 37
                      · exact Or.inl (hX9.trans (stepOOG (k:=k+9) (C:=C+32) (cost:=5) hg9 st9 (by omega) (by omega) (by omega)))
                      · set s10 := stMul s9 (UInt256.mul r ⟨2⟩) [i,r,slot,n,ret] with hs10
                        have hX10 := hX9.trans (stepContinue (k:=k+9) (C:=C+32) (cost:=5) hg9 st9 (by omega) (by omega))
                        have hc10 : s10.executionEnv.code = powBytecode := by rw [hs10]; simp only [stMul]; exact hc9
                        have hp10 : s10.machineState.pc = ⟨130⟩ := by rw [hs10]; simp only [stMul]; rw [hp9]; rfl
                        have hg10 : s10.machineState.gasAvailable.toNat = g.toNat - (C+37) := by
                          rw [hs10]; simp only [stMul]; rw [toNat_sub_ofNat (by omega)]; omega
                        have hk10 : s10.machineState.stack = [UInt256.mul r ⟨2⟩,i,r,slot,n,ret] := by
                          rw [hs10]; simp only [stMul]
                        have st10 := swap2_xstep hc10 hp10 (by decide) hk10 (by norm_num)
                        by_cases g10 : g.toNat < C + 40
                        · exact Or.inl (hX10.trans (stepOOG (k:=k+10) (C:=C+37) (cost:=3) hg10 st10 (by omega) (by omega) (by omega)))
                        · set s11 := stSwap s10 [r,i,UInt256.mul r ⟨2⟩,slot,n,ret] with hs11
                          have hX11 := hX10.trans (stepContinue (k:=k+10) (C:=C+37) (cost:=3) hg10 st10 (by omega) (by omega))
                          have hc11 : s11.executionEnv.code = powBytecode := by rw [hs11]; simp only [stSwap]; exact hc10
                          have hp11 : s11.machineState.pc = ⟨131⟩ := by rw [hs11]; simp only [stSwap]; rw [hp10]; rfl
                          have hg11 : s11.machineState.gasAvailable.toNat = g.toNat - (C+40) := by
                            rw [hs11]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                          have hk11 : s11.machineState.stack = [r,i,UInt256.mul r ⟨2⟩,slot,n,ret] := by rw [hs11]; simp only [stSwap]
                          have st11 := pop_xstep hc11 hp11 (by decide) hk11 (by norm_num)
                          by_cases g11 : g.toNat < C + 42
                          · exact Or.inl (hX11.trans (stepOOG (k:=k+11) (C:=C+40) (cost:=2) hg11 st11 (by omega) (by omega) (by omega)))
                          · set s12 := stPop s11 [i,UInt256.mul r ⟨2⟩,slot,n,ret] with hs12
                            have hX12 := hX11.trans (stepContinue (k:=k+11) (C:=C+40) (cost:=2) hg11 st11 (by omega) (by omega))
                            have hc12 : s12.executionEnv.code = powBytecode := by rw [hs12]; simp only [stPop]; exact hc11
                            have hp12 : s12.machineState.pc = ⟨132⟩ := by rw [hs12]; simp only [stPop]; rw [hp11]; rfl
                            have hg12 : s12.machineState.gasAvailable.toNat = g.toNat - (C+42) := by
                              rw [hs12]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                            have hk12 : s12.machineState.stack = [i,UInt256.mul r ⟨2⟩,slot,n,ret] := by rw [hs12]; simp only [stPop]
                            have st12 := push1_xstep (argv:=⟨1⟩) hc12 hp12 (by decide) hk12 (by norm_num)
                            by_cases g12 : g.toNat < C + 45
                            · exact Or.inl (hX12.trans (stepOOG (k:=k+12) (C:=C+42) (cost:=3) hg12 st12 (by omega) (by omega) (by omega)))
                            · set s13 := stPush1 s12 ⟨1⟩ with hs13
                              have hX13 := hX12.trans (stepContinue (k:=k+12) (C:=C+42) (cost:=3) hg12 st12 (by omega) (by omega))
                              have hc13 : s13.executionEnv.code = powBytecode := by rw [hs13]; simp only [stPush1]; exact hc12
                              have hp13 : s13.machineState.pc = ⟨134⟩ := by rw [hs13]; simp only [stPush1]; rw [hp12]; rfl
                              have hg13 : s13.machineState.gasAvailable.toNat = g.toNat - (C+45) := by
                                rw [hs13]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                              have hk13 : s13.machineState.stack = [⟨1⟩,i,UInt256.mul r ⟨2⟩,slot,n,ret] := by rw [hs13]; simp only [stPush1, hk12]
                              have st13 := dup2_xstep hc13 hp13 (by decide) hk13 (by norm_num)
                              by_cases g13 : g.toNat < C + 48
                              · exact Or.inl (hX13.trans (stepOOG (k:=k+13) (C:=C+45) (cost:=3) hg13 st13 (by omega) (by omega) (by omega)))
                              · set s14 := stSwap s13 [i,⟨1⟩,i,UInt256.mul r ⟨2⟩,slot,n,ret] with hs14
                                have hX14 := hX13.trans (stepContinue (k:=k+13) (C:=C+45) (cost:=3) hg13 st13 (by omega) (by omega))
                                have hc14 : s14.executionEnv.code = powBytecode := by rw [hs14]; simp only [stSwap]; exact hc13
                                have hp14 : s14.machineState.pc = ⟨135⟩ := by rw [hs14]; simp only [stSwap]; rw [hp13]; rfl
                                have hg14 : s14.machineState.gasAvailable.toNat = g.toNat - (C+48) := by
                                  rw [hs14]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                have hk14 : s14.machineState.stack = [i,⟨1⟩,i,UInt256.mul r ⟨2⟩,slot,n,ret] := by rw [hs14]; simp only [stSwap]
                                have st14 := add_xstep hc14 hp14 (by decide) hk14 (by norm_num)
                                by_cases g14 : g.toNat < C + 51
                                · exact Or.inl (hX14.trans (stepOOG (k:=k+14) (C:=C+48) (cost:=3) hg14 st14 (by omega) (by omega) (by omega)))
                                · set s15 := stBinop s14 (i + ⟨1⟩) [i,UInt256.mul r ⟨2⟩,slot,n,ret] with hs15
                                  have hX15 := hX14.trans (stepContinue (k:=k+14) (C:=C+48) (cost:=3) hg14 st14 (by omega) (by omega))
                                  have hc15 : s15.executionEnv.code = powBytecode := by rw [hs15]; simp only [stBinop]; exact hc14
                                  have hp15 : s15.machineState.pc = ⟨136⟩ := by rw [hs15]; simp only [stBinop]; rw [hp14]; rfl
                                  have hg15 : s15.machineState.gasAvailable.toNat = g.toNat - (C+51) := by
                                    rw [hs15]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                                  have hk15 : s15.machineState.stack = [i + ⟨1⟩,i,UInt256.mul r ⟨2⟩,slot,n,ret] := by rw [hs15]; simp only [stBinop]
                                  have st15 := swap1_xstep hc15 hp15 (by decide) hk15 (by norm_num)
                                  by_cases g15 : g.toNat < C + 54
                                  · exact Or.inl (hX15.trans (stepOOG (k:=k+15) (C:=C+51) (cost:=3) hg15 st15 (by omega) (by omega) (by omega)))
                                  · set s16 := stSwap s15 [i,i + ⟨1⟩,UInt256.mul r ⟨2⟩,slot,n,ret] with hs16
                                    have hX16 := hX15.trans (stepContinue (k:=k+15) (C:=C+51) (cost:=3) hg15 st15 (by omega) (by omega))
                                    have hc16 : s16.executionEnv.code = powBytecode := by rw [hs16]; simp only [stSwap]; exact hc15
                                    have hp16 : s16.machineState.pc = ⟨137⟩ := by rw [hs16]; simp only [stSwap]; rw [hp15]; rfl
                                    have hg16 : s16.machineState.gasAvailable.toNat = g.toNat - (C+54) := by
                                      rw [hs16]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                    have hk16 : s16.machineState.stack = [i,i + ⟨1⟩,UInt256.mul r ⟨2⟩,slot,n,ret] := by rw [hs16]; simp only [stSwap]
                                    have st16 := pop_xstep hc16 hp16 (by decide) hk16 (by norm_num)
                                    by_cases g16 : g.toNat < C + 56
                                    · exact Or.inl (hX16.trans (stepOOG (k:=k+16) (C:=C+54) (cost:=2) hg16 st16 (by omega) (by omega) (by omega)))
                                    · set s17 := stPop s16 [i + ⟨1⟩,UInt256.mul r ⟨2⟩,slot,n,ret] with hs17
                                      have hX17 := hX16.trans (stepContinue (k:=k+16) (C:=C+54) (cost:=2) hg16 st16 (by omega) (by omega))
                                      have hc17 : s17.executionEnv.code = powBytecode := by rw [hs17]; simp only [stPop]; exact hc16
                                      have hp17 : s17.machineState.pc = ⟨138⟩ := by rw [hs17]; simp only [stPop]; rw [hp16]; rfl
                                      have hg17 : s17.machineState.gasAvailable.toNat = g.toNat - (C+56) := by
                                        rw [hs17]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                      have hk17 : s17.machineState.stack = [i + ⟨1⟩,UInt256.mul r ⟨2⟩,slot,n,ret] := by rw [hs17]; simp only [stPop]
                                      have st17 := push2_xstep (argv:=⟨117⟩) hc17 hp17 (by decide) hk17 (by norm_num)
                                      by_cases g17 : g.toNat < C + 59
                                      · exact Or.inl (hX17.trans (stepOOG (k:=k+17) (C:=C+56) (cost:=3) hg17 st17 (by omega) (by omega) (by omega)))
                                      · set s18 := stPush2 s17 ⟨117⟩ with hs18
                                        have hX18 := hX17.trans (stepContinue (k:=k+17) (C:=C+56) (cost:=3) hg17 st17 (by omega) (by omega))
                                        have hc18 : s18.executionEnv.code = powBytecode := by rw [hs18]; simp only [stPush2]; exact hc17
                                        have hp18 : s18.machineState.pc = ⟨141⟩ := by rw [hs18]; simp only [stPush2]; rw [hp17]; rfl
                                        have hg18 : s18.machineState.gasAvailable.toNat = g.toNat - (C+59) := by
                                          rw [hs18]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                                        have hk18 : s18.machineState.stack = [⟨117⟩,i + ⟨1⟩,UInt256.mul r ⟨2⟩,slot,n,ret] := by
                                          rw [hs18]; simp only [stPush2, hk17]
                                        have st18 := jump_xstep hc18 hp18 (by decide) hk18
                                          (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
                                        by_cases g18 : g.toNat < C + 67
                                        · exact Or.inl (hX18.trans (stepOOG (k:=k+18) (C:=C+59) (cost:=8) hg18 st18 (by omega) (by omega) (by omega)))
                                        · set s19 := stJump s18 ⟨117⟩ [i + ⟨1⟩,UInt256.mul r ⟨2⟩,slot,n,ret] with hs19
                                          have hX19 := hX18.trans (stepContinue (k:=k+18) (C:=C+59) (cost:=8) hg18 st18 (by omega) (by omega))
                                          have hc19 : s19.executionEnv.code = powBytecode := by rw [hs19]; simp only [stJump]; exact hc18
                                          have hp19 : s19.machineState.pc = ⟨117⟩ := by rw [hs19]; simp only [stJump]
                                          have hg19 : s19.machineState.gasAvailable.toNat = g.toNat - (C+67) := by
                                            rw [hs19]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                          have hk19 : s19.machineState.stack = [i + ⟨1⟩,UInt256.mul r ⟨2⟩,slot,n,ret] := by
                                            rw [hs19]; simp only [stJump]
                                          have hi1size : i.toNat + 1 < UInt256.size := lt_size_of_lt256 (by omega)
                                          have hi1 : (i + ⟨1⟩).toNat = i.toNat + 1 := add1_toNat hi1size
                                          have hr2size : 2 * r.toNat < UInt256.size := by
                                            rw [hinv, show 2 * 2^i.toNat = 2^(i.toNat+1) from by rw [pow_succ]; ring]
                                            exact pow_lt_size (by omega)
                                          have hr2 : (UInt256.mul r ⟨2⟩).toNat = 2 * r.toNat := mul2_toNat hr2size
                                          have he : g.toNat + 1 - (k + 18 + 1) = g.toNat + 1 - (k + 19) := by omega
                                          rw [he] at hX19
                                          exact ih (i + ⟨1⟩) (UInt256.mul r ⟨2⟩) (k+19) (C+67) s19
                                            (by rw [hi1]; omega)
                                            (by rw [hr2, hi1, hinv, pow_succ]; ring)
                                            (by rw [hi1]; omega)
                                            hc19 hp19 hk19 hg19 (by omega) (by omega) hX19

/-! ## The dispatcher (success path) — reaches the function body at `0x2d`

`callvalue = 0`, `calldatasize ≥ 4`, selector matches `0x442b7ffb`: 24 instructions from
`initState` to the `JUMPDEST` at `0x2d = 45`, leaving the decoded selector word on the stack and
the free-pointer memory in place.  Mirrors `truthX_cvz_*` but with PUSH2 jump targets. -/
theorem powX_disp {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ s, (X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
                = X (g.toNat + 1 - 24) (D_J powBytecode ⟨0⟩) s)
           ∧ s.executionEnv = I ∧ s.machineState.pc = ⟨45⟩
           ∧ s.machineState.gasAvailable.toNat = g.toNat - 96
           ∧ s.machineState.stack
               = [UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
           ∧ s.machineState.activeWords = UInt256.ofNat 3
           ∧ s.machineState.memory = solcFreePtrMem ∧ 96 ≤ g.toNat := by
  have hsztoNat : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size := by
    show (Fin.ofNat _ I.calldata.size).val = I.calldata.size
    simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hsize
  have hlt0 : UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩ = ⟨0⟩ :=
    ult_zero (by rw [hsztoNat]; exact le_trans (show (⟨4⟩ : UInt256).toNat ≤ 4 by decide) hsz)
  rcases solcGuardPrologue (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    with hoog | ⟨s6, hX6, hee6, hpc6, hgas6, hstk6raw, haw6, hmem6, _hg26⟩
  · exact Or.inl hoog
  have hcode6 : s6.executionEnv.code = powBytecode := by rw [hee6]; exact hcode
  have hstk6 : s6.machineState.stack = [⟨1⟩, ⟨0⟩] := by
    rw [hstk6raw, hwv, show UInt256.isZero ⟨0⟩ = ⟨1⟩ from by decide]
  -- 6: PUSH2 0x0f
  have hstep6 := push2_xstep (argv := ⟨15⟩) hcode6 hpc6 (by decide) hstk6 (by norm_num)
  by_cases h6 : g.toNat < 29
  · exact Or.inl (by rw [hX6]; exact stepOOG hgas6 hstep6 (by norm_num) (by omega) (by omega))
  · set s7 := stPush2 s6 ⟨15⟩ with hs7
    have hX7 := hX6.trans (stepContinue (k := 6) (C := 26) hgas6 hstep6 (by norm_num) (by omega))
    have hee7 : s7.executionEnv = I := by rw [hs7]; simp only [stPush2]; exact hee6
    have hcode7 : s7.executionEnv.code = powBytecode := by rw [hee7]; exact hcode
    have hpc7 : s7.machineState.pc = ⟨11⟩ := by rw [hs7]; simp only [stPush2]; rw [hpc6]; rfl
    have hgas7 : s7.machineState.gasAvailable.toNat = g.toNat - 29 := by rw [hs7]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
    have hstk7 : s7.machineState.stack = [⟨15⟩, ⟨1⟩, ⟨0⟩] := by rw [hs7]; simp only [stPush2, hstk6]
    have haw7 : s7.machineState.activeWords = UInt256.ofNat 3 := by rw [hs7]; simp only [stPush2]; exact haw6
    have hmem7 : s7.machineState.memory = solcFreePtrMem := by rw [hs7]; simp only [stPush2]; exact hmem6
    -- 7: JUMPI (taken → 0x0f)
    have hstep7 := jumpi_t_xstep hcode7 hpc7 (by decide) hstk7 (by decide) (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
    by_cases h7 : g.toNat < 39
    · exact Or.inl (by rw [hX7]; exact stepOOG hgas7 hstep7 (by norm_num) (by omega) (by omega))
    · set s8 := stJumpiT s7 ⟨15⟩ [⟨0⟩] with hs8
      have hX8 := hX7.trans (stepContinue (k := 7) (C := 29) hgas7 hstep7 (by norm_num) (by omega))
      have hee8 : s8.executionEnv = I := by rw [hs8]; simp only [stJumpiT]; exact hee7
      have hcode8 : s8.executionEnv.code = powBytecode := by rw [hee8]; exact hcode
      have hpc8 : s8.machineState.pc = ⟨15⟩ := by rw [hs8]; simp only [stJumpiT]
      have hgas8 : s8.machineState.gasAvailable.toNat = g.toNat - 39 := by rw [hs8]; simp only [stJumpiT]; rw [toNat_sub_ofNat (by omega)]; omega
      have hstk8 : s8.machineState.stack = [⟨0⟩] := by rw [hs8]; simp only [stJumpiT]
      have haw8 : s8.machineState.activeWords = UInt256.ofNat 3 := by rw [hs8]; simp only [stJumpiT]; exact haw7
      have hmem8 : s8.machineState.memory = solcFreePtrMem := by rw [hs8]; simp only [stJumpiT]; exact hmem7
      -- 8: JUMPDEST
      have hstep8 := jumpdest_xstep hcode8 hpc8 (by decide) (by rw [hstk8]; norm_num)
      by_cases h8 : g.toNat < 40
      · exact Or.inl (by rw [hX8]; exact stepOOG hgas8 hstep8 (by norm_num) (by omega) (by omega))
      · set s9 := stJumpdest s8 with hs9
        have hX9 := hX8.trans (stepContinue (k := 8) (C := 39) hgas8 hstep8 (by norm_num) (by omega))
        have hee9 : s9.executionEnv = I := by rw [hs9]; simp only [stJumpdest]; exact hee8
        have hcode9 : s9.executionEnv.code = powBytecode := by rw [hee9]; exact hcode
        have hpc9 : s9.machineState.pc = ⟨16⟩ := by rw [hs9]; simp only [stJumpdest]; rw [hpc8]; rfl
        have hgas9 : s9.machineState.gasAvailable.toNat = g.toNat - 40 := by rw [hs9]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
        have hstk9 : s9.machineState.stack = [⟨0⟩] := by rw [hs9]; simp only [stJumpdest]; exact hstk8
        have haw9 : s9.machineState.activeWords = UInt256.ofNat 3 := by rw [hs9]; simp only [stJumpdest]; exact haw8
        have hmem9 : s9.machineState.memory = solcFreePtrMem := by rw [hs9]; simp only [stJumpdest]; exact hmem8
        -- 9: POP
        have hstep9 := pop_xstep hcode9 hpc9 (by decide) hstk9 (by norm_num)
        by_cases h9 : g.toNat < 42
        · exact Or.inl (by rw [hX9]; exact stepOOG hgas9 hstep9 (by norm_num) (by omega) (by omega))
        · set s10 := stPop s9 [] with hs10
          have hX10 := hX9.trans (stepContinue (k := 9) (C := 40) hgas9 hstep9 (by norm_num) (by omega))
          have hee10 : s10.executionEnv = I := by rw [hs10]; simp only [stPop]; exact hee9
          have hcode10 : s10.executionEnv.code = powBytecode := by rw [hee10]; exact hcode
          have hpc10 : s10.machineState.pc = ⟨17⟩ := by rw [hs10]; simp only [stPop]; rw [hpc9]; rfl
          have hgas10 : s10.machineState.gasAvailable.toNat = g.toNat - 42 := by rw [hs10]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
          have hstk10 : s10.machineState.stack = [] := by rw [hs10]; simp only [stPop]
          have haw10 : s10.machineState.activeWords = UInt256.ofNat 3 := by rw [hs10]; simp only [stPop]; exact haw9
          have hmem10 : s10.machineState.memory = solcFreePtrMem := by rw [hs10]; simp only [stPop]; exact hmem9
          -- 10: PUSH1 0x04
          have hstep10 := push1_xstep (argv := ⟨4⟩) hcode10 hpc10 (by decide) hstk10 (by norm_num)
          by_cases h10 : g.toNat < 45
          · exact Or.inl (by rw [hX10]; exact stepOOG hgas10 hstep10 (by norm_num) (by omega) (by omega))
          · set s11 := stPush1 s10 ⟨4⟩ with hs11
            have hX11 := hX10.trans (stepContinue (k := 10) (C := 42) hgas10 hstep10 (by norm_num) (by omega))
            have hee11 : s11.executionEnv = I := by rw [hs11]; simp only [stPush1]; exact hee10
            have hcode11 : s11.executionEnv.code = powBytecode := by rw [hee11]; exact hcode
            have hpc11 : s11.machineState.pc = ⟨19⟩ := by rw [hs11]; simp only [stPush1]; rw [hpc10]; rfl
            have hgas11 : s11.machineState.gasAvailable.toNat = g.toNat - 45 := by rw [hs11]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
            have hstk11 : s11.machineState.stack = [⟨4⟩] := by rw [hs11]; simp only [stPush1, hstk10]
            have haw11 : s11.machineState.activeWords = UInt256.ofNat 3 := by rw [hs11]; simp only [stPush1]; exact haw10
            have hmem11 : s11.machineState.memory = solcFreePtrMem := by rw [hs11]; simp only [stPush1]; exact hmem10
            -- 11: CALLDATASIZE
            have hstep11 := calldatasize_xstep hcode11 hpc11 (by decide) hstk11 (by norm_num)
            by_cases h11 : g.toNat < 47
            · exact Or.inl (by rw [hX11]; exact stepOOG hgas11 hstep11 (by norm_num) (by omega) (by omega))
            · set s12 := stCalldatasize s11 with hs12
              have hX12 := hX11.trans (stepContinue (k := 11) (C := 45) hgas11 hstep11 (by norm_num) (by omega))
              have hee12 : s12.executionEnv = I := by rw [hs12]; simp only [stCalldatasize]; exact hee11
              have hcode12 : s12.executionEnv.code = powBytecode := by rw [hee12]; exact hcode
              have hpc12 : s12.machineState.pc = ⟨20⟩ := by rw [hs12]; simp only [stCalldatasize]; rw [hpc11]; rfl
              have hgas12 : s12.machineState.gasAvailable.toNat = g.toNat - 47 := by rw [hs12]; simp only [stCalldatasize]; rw [toNat_sub_ofNat (by omega)]; omega
              have hstk12 : s12.machineState.stack = [UInt256.ofNat I.calldata.size, ⟨4⟩] := by rw [hs12]; simp only [stCalldatasize, hstk11, hee11]
              have haw12 : s12.machineState.activeWords = UInt256.ofNat 3 := by rw [hs12]; simp only [stCalldatasize]; exact haw11
              have hmem12 : s12.machineState.memory = solcFreePtrMem := by rw [hs12]; simp only [stCalldatasize]; exact hmem11
              -- 12: LT
              have hstep12 := lt_xstep hcode12 hpc12 (by decide) hstk12 (by norm_num)
              by_cases h12 : g.toNat < 50
              · exact Or.inl (by rw [hX12]; exact stepOOG hgas12 hstep12 (by norm_num) (by omega) (by omega))
              · set s13 := stBinop s12 (UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩) [] with hs13
                have hX13 := hX12.trans (stepContinue (k := 12) (C := 47) hgas12 hstep12 (by norm_num) (by omega))
                have hee13 : s13.executionEnv = I := by rw [hs13]; simp only [stBinop]; exact hee12
                have hcode13 : s13.executionEnv.code = powBytecode := by rw [hee13]; exact hcode
                have hpc13 : s13.machineState.pc = ⟨21⟩ := by rw [hs13]; simp only [stBinop]; rw [hpc12]; rfl
                have hgas13 : s13.machineState.gasAvailable.toNat = g.toNat - 50 := by rw [hs13]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                have hstk13 : s13.machineState.stack = [⟨0⟩] := by rw [hs13]; simp only [stBinop]; rw [hlt0]
                have haw13 : s13.machineState.activeWords = UInt256.ofNat 3 := by rw [hs13]; simp only [stBinop]; exact haw12
                have hmem13 : s13.machineState.memory = solcFreePtrMem := by rw [hs13]; simp only [stBinop]; exact hmem12
                -- 13: PUSH2 0x29
                have hstep13 := push2_xstep (argv := ⟨41⟩) hcode13 hpc13 (by decide) hstk13 (by norm_num)
                by_cases h13 : g.toNat < 53
                · exact Or.inl (by rw [hX13]; exact stepOOG hgas13 hstep13 (by norm_num) (by omega) (by omega))
                · set s14 := stPush2 s13 ⟨41⟩ with hs14
                  have hX14 := hX13.trans (stepContinue (k := 13) (C := 50) hgas13 hstep13 (by norm_num) (by omega))
                  have hee14 : s14.executionEnv = I := by rw [hs14]; simp only [stPush2]; exact hee13
                  have hcode14 : s14.executionEnv.code = powBytecode := by rw [hee14]; exact hcode
                  have hpc14 : s14.machineState.pc = ⟨24⟩ := by rw [hs14]; simp only [stPush2]; rw [hpc13]; rfl
                  have hgas14 : s14.machineState.gasAvailable.toNat = g.toNat - 53 := by rw [hs14]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                  have hstk14 : s14.machineState.stack = [⟨41⟩, ⟨0⟩] := by rw [hs14]; simp only [stPush2, hstk13]
                  have haw14 : s14.machineState.activeWords = UInt256.ofNat 3 := by rw [hs14]; simp only [stPush2]; exact haw13
                  have hmem14 : s14.machineState.memory = solcFreePtrMem := by rw [hs14]; simp only [stPush2]; exact hmem13
                  -- 14: JUMPI (not taken → fall to 0x19)
                  have hstep14 := jumpi_nt_xstep hcode14 hpc14 (by decide) hstk14 (by norm_num)
                  by_cases h14 : g.toNat < 63
                  · exact Or.inl (by rw [hX14]; exact stepOOG hgas14 hstep14 (by norm_num) (by omega) (by omega))
                  · set s15 := stJumpiNT s14 [] with hs15
                    have hX15 := hX14.trans (stepContinue (k := 14) (C := 53) hgas14 hstep14 (by norm_num) (by omega))
                    have hee15 : s15.executionEnv = I := by rw [hs15]; simp only [stJumpiNT]; exact hee14
                    have hcode15 : s15.executionEnv.code = powBytecode := by rw [hee15]; exact hcode
                    have hpc15 : s15.machineState.pc = ⟨25⟩ := by rw [hs15]; simp only [stJumpiNT]; rw [hpc14]; rfl
                    have hgas15 : s15.machineState.gasAvailable.toNat = g.toNat - 63 := by rw [hs15]; simp only [stJumpiNT]; rw [toNat_sub_ofNat (by omega)]; omega
                    have hstk15 : s15.machineState.stack = [] := by rw [hs15]; simp only [stJumpiNT]
                    have haw15 : s15.machineState.activeWords = UInt256.ofNat 3 := by rw [hs15]; simp only [stJumpiNT]; exact haw14
                    have hmem15 : s15.machineState.memory = solcFreePtrMem := by rw [hs15]; simp only [stJumpiNT]; exact hmem14
                    -- 15: PUSH0
                    have hstep15 := push0_xstep hcode15 hpc15 (by decide) hstk15 (by norm_num)
                    by_cases h15 : g.toNat < 65
                    · exact Or.inl (by rw [hX15]; exact stepOOG hgas15 hstep15 (by norm_num) (by omega) (by omega))
                    · set s16 := stPush0 s15 with hs16
                      have hX16 := hX15.trans (stepContinue (k := 15) (C := 63) hgas15 hstep15 (by norm_num) (by omega))
                      have hee16 : s16.executionEnv = I := by rw [hs16]; simp only [stPush0]; exact hee15
                      have hcode16 : s16.executionEnv.code = powBytecode := by rw [hee16]; exact hcode
                      have hpc16 : s16.machineState.pc = ⟨26⟩ := by rw [hs16]; simp only [stPush0]; rw [hpc15]; rfl
                      have hgas16 : s16.machineState.gasAvailable.toNat = g.toNat - 65 := by rw [hs16]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                      have hstk16 : s16.machineState.stack = [⟨0⟩] := by rw [hs16]; simp only [stPush0, hstk15]
                      have haw16 : s16.machineState.activeWords = UInt256.ofNat 3 := by rw [hs16]; simp only [stPush0]; exact haw15
                      have hmem16 : s16.machineState.memory = solcFreePtrMem := by rw [hs16]; simp only [stPush0]; exact hmem15
                      -- 16: CALLDATALOAD
                      have hstep16 := calldataload_xstep hcode16 hpc16 (by decide) hstk16 (by norm_num)
                      by_cases h16 : g.toNat < 68
                      · exact Or.inl (by rw [hX16]; exact stepOOG hgas16 hstep16 (by norm_num) (by omega) (by omega))
                      · set s17 := stCalldataload s16 ⟨0⟩ [] with hs17
                        have hX17 := hX16.trans (stepContinue (k := 16) (C := 65) hgas16 hstep16 (by norm_num) (by omega))
                        have hee17 : s17.executionEnv = I := by rw [hs17]; simp only [stCalldataload]; exact hee16
                        have hcode17 : s17.executionEnv.code = powBytecode := by rw [hee17]; exact hcode
                        have hpc17 : s17.machineState.pc = ⟨27⟩ := by rw [hs17]; simp only [stCalldataload]; rw [hpc16]; rfl
                        have hgas17 : s17.machineState.gasAvailable.toNat = g.toNat - 68 := by rw [hs17]; simp only [stCalldataload]; rw [toNat_sub_ofNat (by omega)]; omega
                        have hstk17 : s17.machineState.stack = [uInt256OfByteArray (I.calldata.readBytes 0 32)] := by rw [hs17]; simp only [stCalldataload, hee16]; rfl
                        have haw17 : s17.machineState.activeWords = UInt256.ofNat 3 := by rw [hs17]; simp only [stCalldataload]; exact haw16
                        have hmem17 : s17.machineState.memory = solcFreePtrMem := by rw [hs17]; simp only [stCalldataload]; exact hmem16
                        -- 17: PUSH1 0xe0
                        have hstep17 := push1_xstep (argv := ⟨224⟩) hcode17 hpc17 (by decide) hstk17 (by norm_num)
                        by_cases h17 : g.toNat < 71
                        · exact Or.inl (by rw [hX17]; exact stepOOG hgas17 hstep17 (by norm_num) (by omega) (by omega))
                        · set s18 := stPush1 s17 ⟨224⟩ with hs18
                          have hX18 := hX17.trans (stepContinue (k := 17) (C := 68) hgas17 hstep17 (by norm_num) (by omega))
                          have hee18 : s18.executionEnv = I := by rw [hs18]; simp only [stPush1]; exact hee17
                          have hcode18 : s18.executionEnv.code = powBytecode := by rw [hee18]; exact hcode
                          have hpc18 : s18.machineState.pc = ⟨29⟩ := by rw [hs18]; simp only [stPush1]; rw [hpc17]; rfl
                          have hgas18 : s18.machineState.gasAvailable.toNat = g.toNat - 71 := by rw [hs18]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                          have hstk18 : s18.machineState.stack = [⟨224⟩, uInt256OfByteArray (I.calldata.readBytes 0 32)] := by rw [hs18]; simp only [stPush1, hstk17]
                          have haw18 : s18.machineState.activeWords = UInt256.ofNat 3 := by rw [hs18]; simp only [stPush1]; exact haw17
                          have hmem18 : s18.machineState.memory = solcFreePtrMem := by rw [hs18]; simp only [stPush1]; exact hmem17
                          -- 18: SHR
                          have hstep18 := shr_xstep hcode18 hpc18 (by decide) hstk18 (by norm_num)
                          by_cases h18 : g.toNat < 74
                          · exact Or.inl (by rw [hX18]; exact stepOOG hgas18 hstep18 (by norm_num) (by omega) (by omega))
                          · set sel := UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ with hseldef
                            set s19 := stBinop s18 sel [] with hs19
                            have hX19 := hX18.trans (stepContinue (k := 18) (C := 71) hgas18 hstep18 (by norm_num) (by omega))
                            have hee19 : s19.executionEnv = I := by rw [hs19]; simp only [stBinop]; exact hee18
                            have hcode19 : s19.executionEnv.code = powBytecode := by rw [hee19]; exact hcode
                            have hpc19 : s19.machineState.pc = ⟨30⟩ := by rw [hs19]; simp only [stBinop]; rw [hpc18]; rfl
                            have hgas19 : s19.machineState.gasAvailable.toNat = g.toNat - 74 := by rw [hs19]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                            have hstk19 : s19.machineState.stack = [sel] := by rw [hs19]; simp only [stBinop]
                            have haw19 : s19.machineState.activeWords = UInt256.ofNat 3 := by rw [hs19]; simp only [stBinop]; exact haw18
                            have hmem19 : s19.machineState.memory = solcFreePtrMem := by rw [hs19]; simp only [stBinop]; exact hmem18
                            -- 19: DUP1
                            have hstep19 := dup1_xstep hcode19 hpc19 (by decide) hstk19 (by norm_num)
                            by_cases h19 : g.toNat < 77
                            · exact Or.inl (by rw [hX19]; exact stepOOG hgas19 hstep19 (by norm_num) (by omega) (by omega))
                            · set s20 := stDup1 s19 sel [] with hs20
                              have hX20 := hX19.trans (stepContinue (k := 19) (C := 74) hgas19 hstep19 (by norm_num) (by omega))
                              have hee20 : s20.executionEnv = I := by rw [hs20]; simp only [stDup1]; exact hee19
                              have hcode20 : s20.executionEnv.code = powBytecode := by rw [hee20]; exact hcode
                              have hpc20 : s20.machineState.pc = ⟨31⟩ := by rw [hs20]; simp only [stDup1]; rw [hpc19]; rfl
                              have hgas20 : s20.machineState.gasAvailable.toNat = g.toNat - 77 := by rw [hs20]; simp only [stDup1]; rw [toNat_sub_ofNat (by omega)]; omega
                              have hstk20 : s20.machineState.stack = [sel, sel] := by rw [hs20]; simp only [stDup1]
                              have haw20 : s20.machineState.activeWords = UInt256.ofNat 3 := by rw [hs20]; simp only [stDup1]; exact haw19
                              have hmem20 : s20.machineState.memory = solcFreePtrMem := by rw [hs20]; simp only [stDup1]; exact hmem19
                              -- 20: PUSH4 0x442b7ffb
                              have hstep20 := push4_xstep (argv := ⟨1143701499⟩) hcode20 hpc20 (by decide) hstk20 (by norm_num)
                              by_cases h20 : g.toNat < 80
                              · exact Or.inl (by rw [hX20]; exact stepOOG hgas20 hstep20 (by norm_num) (by omega) (by omega))
                              · set s21 := stPush4 s20 ⟨1143701499⟩ with hs21
                                have hX21 := hX20.trans (stepContinue (k := 20) (C := 77) hgas20 hstep20 (by norm_num) (by omega))
                                have hee21 : s21.executionEnv = I := by rw [hs21]; simp only [stPush4]; exact hee20
                                have hcode21 : s21.executionEnv.code = powBytecode := by rw [hee21]; exact hcode
                                have hpc21 : s21.machineState.pc = ⟨36⟩ := by rw [hs21]; simp only [stPush4]; rw [hpc20]; rfl
                                have hgas21 : s21.machineState.gasAvailable.toNat = g.toNat - 80 := by rw [hs21]; simp only [stPush4]; rw [toNat_sub_ofNat (by omega)]; omega
                                have hstk21 : s21.machineState.stack = [⟨1143701499⟩, sel, sel] := by rw [hs21]; simp only [stPush4, hstk20]
                                have haw21 : s21.machineState.activeWords = UInt256.ofNat 3 := by rw [hs21]; simp only [stPush4]; exact haw20
                                have hmem21 : s21.machineState.memory = solcFreePtrMem := by rw [hs21]; simp only [stPush4]; exact hmem20
                                -- 21: EQ (matches → 1)
                                have heq1 : UInt256.eq ⟨1143701499⟩ sel = ⟨1⟩ := by
                                  rw [hseldef, powEvmSelector hsz, if_pos hmatch]
                                have hstep21 := eq_xstep hcode21 hpc21 (by decide) hstk21 (by norm_num)
                                by_cases h21 : g.toNat < 83
                                · exact Or.inl (by rw [hX21]; exact stepOOG hgas21 hstep21 (by norm_num) (by omega) (by omega))
                                · set s22 := stBinop s21 (UInt256.eq ⟨1143701499⟩ sel) [sel] with hs22
                                  have hX22 := hX21.trans (stepContinue (k := 21) (C := 80) hgas21 hstep21 (by norm_num) (by omega))
                                  have hee22 : s22.executionEnv = I := by rw [hs22]; simp only [stBinop]; exact hee21
                                  have hcode22 : s22.executionEnv.code = powBytecode := by rw [hee22]; exact hcode
                                  have hpc22 : s22.machineState.pc = ⟨37⟩ := by rw [hs22]; simp only [stBinop]; rw [hpc21]; rfl
                                  have hgas22 : s22.machineState.gasAvailable.toNat = g.toNat - 83 := by rw [hs22]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                                  have hstk22 : s22.machineState.stack = [⟨1⟩, sel] := by rw [hs22]; simp only [stBinop]; rw [heq1]
                                  have haw22 : s22.machineState.activeWords = UInt256.ofNat 3 := by rw [hs22]; simp only [stBinop]; exact haw21
                                  have hmem22 : s22.machineState.memory = solcFreePtrMem := by rw [hs22]; simp only [stBinop]; exact hmem21
                                  -- 22: PUSH2 0x2d
                                  have hstep22 := push2_xstep (argv := ⟨45⟩) hcode22 hpc22 (by decide) hstk22 (by norm_num)
                                  by_cases h22 : g.toNat < 86
                                  · exact Or.inl (by rw [hX22]; exact stepOOG hgas22 hstep22 (by norm_num) (by omega) (by omega))
                                  · set s23 := stPush2 s22 ⟨45⟩ with hs23
                                    have hX23 := hX22.trans (stepContinue (k := 22) (C := 83) hgas22 hstep22 (by norm_num) (by omega))
                                    have hee23 : s23.executionEnv = I := by rw [hs23]; simp only [stPush2]; exact hee22
                                    have hcode23 : s23.executionEnv.code = powBytecode := by rw [hee23]; exact hcode
                                    have hpc23 : s23.machineState.pc = ⟨40⟩ := by rw [hs23]; simp only [stPush2]; rw [hpc22]; rfl
                                    have hgas23 : s23.machineState.gasAvailable.toNat = g.toNat - 86 := by rw [hs23]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                                    have hstk23 : s23.machineState.stack = [⟨45⟩, ⟨1⟩, sel] := by rw [hs23]; simp only [stPush2, hstk22]
                                    have haw23 : s23.machineState.activeWords = UInt256.ofNat 3 := by rw [hs23]; simp only [stPush2]; exact haw22
                                    have hmem23 : s23.machineState.memory = solcFreePtrMem := by rw [hs23]; simp only [stPush2]; exact hmem22
                                    -- 23: JUMPI (taken → 0x2d)
                                    have hstep23 := jumpi_t_xstep hcode23 hpc23 (by decide) hstk23 (by decide) (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
                                    by_cases h23 : g.toNat < 96
                                    · exact Or.inl (by rw [hX23]; exact stepOOG hgas23 hstep23 (by norm_num) (by omega) (by omega))
                                    · set s24 := stJumpiT s23 ⟨45⟩ [sel] with hs24
                                      have hX24 := hX23.trans (stepContinue (k := 23) (C := 86) hgas23 hstep23 (by norm_num) (by omega))
                                      refine Or.inr ⟨s24, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
                                      · have he : g.toNat + 1 - (23 + 1) = g.toNat + 1 - 24 := by omega
                                        rw [← he]; exact hX24
                                      · rw [hs24]; simp only [stJumpiT]; exact hee23
                                      · rw [hs24]; simp only [stJumpiT]
                                      · rw [hs24]; simp only [stJumpiT]; rw [toNat_sub_ofNat (by omega)]; omega
                                      · rw [hs24]; simp only [stJumpiT]
                                      · rw [hs24]; simp only [stJumpiT]; exact haw23
                                      · rw [hs24]; simp only [stJumpiT]; exact hmem23


