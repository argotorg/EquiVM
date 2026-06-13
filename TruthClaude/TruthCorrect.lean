import TruthClaude.Theory
import TruthClaude.Stepping

/-!
# Truth — a worked runtime-equivalence example

The contract (Solidity):

```solidity
contract Truth {
  function truth() public pure returns (bool) { return true; }
}
```

This file pins down the three ingredients of a runtime-equivalence claim:
* `truthBytecode` — the deployed EVM runtime bytecode (solc output);
* `truthContract` — the Act specification;
* `truthCorrect`  — the correctness statement.  Proved except the `callvalue == 0` dispatch
  branch (one isolated, documented `sorry`; the `callvalue ≠ 0` behaviour and the entire
  out-of-gas regime are fully proved via the `TruthClaude.Theory`/`Stepping` library).
-/

open Act ABI

/-! ## 1. The contract's runtime bytecode -/

/-- Deployed runtime bytecode of the `Truth` contract. -/
def truthBytecode : ByteArray :=
  ⟨#[
    0x60, 0x80, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15, 0x60, 0x0e, 0x57, 0x5f,
    0x5f, 0xfd, 0x5b, 0x50, 0x60, 0x04, 0x36, 0x10, 0x60, 0x26, 0x57, 0x5f,
    0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63, 0x9e, 0x9f, 0x51, 0xd2, 0x14, 0x60,
    0x2a, 0x57, 0x5b, 0x5f, 0x5f, 0xfd, 0x5b, 0x60, 0x30, 0x60, 0x44, 0x56,
    0x5b, 0x60, 0x40, 0x51, 0x60, 0x3b, 0x91, 0x90, 0x60, 0x64, 0x56, 0x5b,
    0x60, 0x40, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3, 0x5b, 0x5f, 0x60, 0x01,
    0x90, 0x50, 0x90, 0x56, 0x5b, 0x5f, 0x81, 0x15, 0x15, 0x90, 0x50, 0x91,
    0x90, 0x50, 0x56, 0x5b, 0x60, 0x5e, 0x81, 0x60, 0x4c, 0x56, 0x5b, 0x82,
    0x52, 0x50, 0x50, 0x56, 0x5b, 0x5f, 0x60, 0x20, 0x82, 0x01, 0x90, 0x50,
    0x60, 0x75, 0x5f, 0x83, 0x01, 0x84, 0x60, 0x57, 0x56, 0x5b, 0x92, 0x91,
    0x50, 0x50, 0x56
  ]⟩

/-! ## 2. The Act specification -/

/-- The single transition: `truth()` requires zero callvalue and returns `true`.
    (The `require(callvalue == 0)` mirrors the compiler-inserted non-payable guard.) -/
def truthTransition : TransitionDecl :=
  { name := "truth"
    params := []
    returnType := some (.elem .bool)
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0))
      , .return (.boolLit true) ] }

/-- Act specification of the `Truth` contract: no storage, no constructor body,
    a single transition. -/
def truthContract : ContractDecl :=
  { name := "Truth"
    storage := []
    ctor := { params := [], body := [] }
    transitions := [truthTransition] }

/-- Configuration: empty storage layout and the default external-call ABI. -/
def truthConfig : Config :=
  { storage := { layout := fun _ => none }
    externalABI := defaultExternalCallABI }

open Ethereum Ethereum.EVM TruthClaude.Theory

set_option maxRecDepth 10000

/-! ## 3. Trusted axioms for opaque trusted-base computations

`truthCorrect` needs two facts about definitions in the (read-only) trusted base that are
**logically opaque** (see `MISSPEC.md`): the keccak selector of `truth()` (because
`ffi.keccak256` is `@[extern] opaque`) and the valid-jump-destination set of
`truthBytecode` (because `Ethereum.EVM.D_J_aux` is `partial`).  Both values are confirmed
by `#eval` but cannot be reduced in the kernel.  Per the project owner's instruction we
admit them as **trusted axioms** here; the real fix is to make those base definitions
computable (`MISSPEC.md`), after which these axioms become provable by `decide` and can be
deleted.  They are the *only* axioms `truthCorrect` adds beyond Lean's standard three. -/

/-- The 4-byte function selector of `truth()` is `0x9e9f51d2` (keccak of `"truth()"`). -/
axiom truthSelectorBytes :
    (ffi.KEC (String.toByteArray (Act.transitionSigStr truthTransition))).extract 0 4
      = ⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩

/-- The `JUMPDEST` positions of `truthBytecode` (the valid jump targets). -/
axiom truthValidJumps :
    Ethereum.EVM.D_J truthBytecode ⟨0⟩
      = #[⟨14⟩, ⟨38⟩, ⟨42⟩, ⟨48⟩, ⟨59⟩, ⟨68⟩, ⟨76⟩, ⟨87⟩, ⟨94⟩, ⟨100⟩, ⟨117⟩]

/-! ## 4. Truth-specific Act-side facts -/

/-- `truthContract` has exactly one transition, so any successful dispatch yields it. -/
theorem truthDispatch_unique {cd : ByteArray} {t : TransitionDecl}
    (h : dispatchMsg truthContract cd = some t) : t = truthTransition := by
  simp only [dispatchMsg, truthContract, List.map_cons, List.map_nil] at h
  -- `find?` over the single-transition list: the only candidate is `truthTransition`.
  split at h
  · rename_i pair heq
    have hmem := List.mem_of_find?_eq_some heq
    simp only [List.mem_singleton, Prod.map, id_eq, Prod.mk.injEq] at hmem
    rw [Option.some.injEq] at h
    rw [← h, hmem.1]
  · exact absurd h (by simp)

/-- With non-zero call value, the Act body reverts: `require(callvalue == 0)` fails. -/
theorem truthBodyReverts (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecContractBody truthConfig truthContract evm locals truthTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse ?_))
  have hval : (Value.int (Int.ofNat ↑evm.executionEnv.weiValue.val) == Value.int 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro hh
    rw [Value.int.injEq] at hh
    exact h (TruthClaude.Theory.uint256_toNat_eq_zero (Int.ofNat.inj hh))
  show evalExpr? truthConfig _ evm (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool false)
  simp only [evalExpr?, EvalResult.bind, bind, pure, envValue, evalBinaryOp?, hval]

/-! ## 5. The Ξ traces (per scenario) -/

/-- The EVM trace for `callvalue ≠ 0`: 11 instructions ending in `REVERT`, with no taken
    jump and no keccak.  Either runs out of gas, or reverts. -/
theorem truthX_callvalue_ne
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    X (g.toNat + 1) (D_J truthBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ g' o, X (g.toNat + 1) (D_J truthBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
                  = .ok (.revert g' o) := by
  set s0 := initState cA gh bl σ σ₀ g A I with hs0
  have hee0 : s0.executionEnv = I := by rw [hs0]; simp [initState]
  have hcode0 : s0.executionEnv.code = truthBytecode := by rw [hee0]; exact hcode
  have hpc0 : s0.machineState.pc = ⟨0⟩ := by rw [hs0]; simp [initState]; rfl
  have hgas0 : s0.machineState.gasAvailable.toNat = g.toNat - 0 := by rw [hs0]; simp [initState]
  have hstk0 : s0.machineState.stack = [] := by rw [hs0]; simp [initState]; rfl
  have haw0 : s0.machineState.activeWords = ⟨0⟩ := by rw [hs0]; simp [initState]; rfl
  have hX0 : X (g.toNat + 1) (D_J truthBytecode ⟨0⟩) s0
              = X (g.toNat + 1 - 0) (D_J truthBytecode ⟨0⟩) s0 := rfl
  -- STEP 0: PUSH1 0x80 (cost 3, C 0→3)
  have hstep0 := push1_xstep (argv := ⟨128⟩) hcode0 hpc0 (by decide) hstk0 (by norm_num)
  by_cases h0 : g.toNat < 3
  · exact Or.inl (by rw [hX0]; exact stepOOG hgas0 hstep0 (by norm_num) (by omega) (by omega))
  · set s1 := stPush1 s0 ⟨128⟩ with hs1
    have hX1 := hX0.trans (stepContinue (k := 0) (C := 0) hgas0 hstep0 (by norm_num) (by omega))
    have hee1 : s1.executionEnv = I := by rw [hs1]; simp only [stPush1]; exact hee0
    have hcode1 : s1.executionEnv.code = truthBytecode := by rw [hee1]; exact hcode
    have hpc1 : s1.machineState.pc = ⟨0⟩ + UInt256.ofNat 2 := by
      rw [hs1]; simp only [stPush1]; rw [hpc0]
    have hgas1 : s1.machineState.gasAvailable.toNat = g.toNat - 3 := by
      rw [hs1]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
    have hstk1 : s1.machineState.stack = [⟨128⟩] := by rw [hs1]; simp [stPush1, hstk0]
    have haw1 : s1.machineState.activeWords = ⟨0⟩ := by rw [hs1]; simp [stPush1, haw0]
    -- STEP 1: PUSH1 0x40 (cost 3, C 3→6)
    have hstep1 := push1_xstep (argv := ⟨64⟩) hcode1 hpc1 (by decide) hstk1 (by norm_num)
    by_cases h1 : g.toNat < 6
    · exact Or.inl (by rw [hX1]; exact stepOOG hgas1 hstep1 (by norm_num) (by omega) (by omega))
    · set s2 := stPush1 s1 ⟨64⟩ with hs2
      have hX2 := hX1.trans (stepContinue (k := 1) (C := 3) hgas1 hstep1 (by norm_num) (by omega))
      have hee2 : s2.executionEnv = I := by rw [hs2]; simp only [stPush1]; exact hee1
      have hcode2 : s2.executionEnv.code = truthBytecode := by rw [hee2]; exact hcode
      have hpc2 : s2.machineState.pc = (⟨0⟩ + UInt256.ofNat 2) + UInt256.ofNat 2 := by
        rw [hs2]; simp only [stPush1]; rw [hpc1]
      have hgas2 : s2.machineState.gasAvailable.toNat = g.toNat - 6 := by
        rw [hs2]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
      have hstk2 : s2.machineState.stack = [⟨64⟩, ⟨128⟩] := by rw [hs2]; simp [stPush1, hstk1]
      have haw2 : s2.machineState.activeWords = ⟨0⟩ := by rw [hs2]; simp [stPush1, haw1]
      have hmc : memoryExpansionCost s2 .MSTORE = 9 := by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw2, hstk2]; decide
      -- STEP 2: MSTORE (cost 12, C 6→18)
      have hstep2 := mstore_xstep hcode2 hpc2 (by decide) hstk2 (by norm_num)
      rw [hmc] at hstep2
      by_cases h2 : g.toNat < 18
      · exact Or.inl (by rw [hX2]
                         exact stepOOG (cost := 9 + 3) hgas2 hstep2 (by norm_num) (by omega) (by omega))
      · set s3 := stMStore s2 ⟨64⟩ ⟨128⟩ [] with hs3
        have hX3 := hX2.trans (stepContinue (k := 2) (C := 6) (cost := 9 + 3) hgas2 hstep2
                      (by norm_num) (by omega))
        have hee3 : s3.executionEnv = I := by rw [hs3]; simp only [stMStore]; exact hee2
        have hcode3 : s3.executionEnv.code = truthBytecode := by rw [hee3]; exact hcode
        have hpc3 : s3.machineState.pc = ((⟨0⟩ + UInt256.ofNat 2) + UInt256.ofNat 2) + ⟨1⟩ := by
          rw [hs3]; simp only [stMStore]; rw [hpc2]
        have hgas3 : s3.machineState.gasAvailable.toNat = g.toNat - 18 := by
          rw [hs3]; simp only [stMStore, hmc]
          rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega),
              toNat_sub_ofNat (by omega)]; omega
        have hstk3 : s3.machineState.stack = [] := by rw [hs3]; simp [stMStore]
        have haw3 : s3.machineState.activeWords = UInt256.ofNat 3 := by
          rw [hs3]; simp only [stMStore, haw2]; decide
        -- STEP 3: CALLVALUE (cost 2, C 18→20)
        have hstep3 := callvalue_xstep hcode3 hpc3 (by decide) hstk3 (by norm_num)
        by_cases h3 : g.toNat < 20
        · exact Or.inl (by rw [hX3]; exact stepOOG hgas3 hstep3 (by norm_num) (by omega) (by omega))
        · set s4 := stCallvalue s3 with hs4
          have hX4 := hX3.trans (stepContinue (k := 3) (C := 18) hgas3 hstep3 (by norm_num) (by omega))
          have hee4 : s4.executionEnv = I := by rw [hs4]; simp only [stCallvalue]; exact hee3
          have hcode4 : s4.executionEnv.code = truthBytecode := by rw [hee4]; exact hcode
          have hpc4 : s4.machineState.pc = (((⟨0⟩ + UInt256.ofNat 2) + UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩ := by
            rw [hs4]; simp only [stCallvalue]; rw [hpc3]
          have hgas4 : s4.machineState.gasAvailable.toNat = g.toNat - 20 := by
            rw [hs4]; simp only [stCallvalue]; rw [toNat_sub_ofNat (by omega)]; omega
          have hstk4 : s4.machineState.stack = [I.weiValue] := by
            rw [hs4]; simp only [stCallvalue, hstk3, hee3]
          have haw4 : s4.machineState.activeWords = UInt256.ofNat 3 := by
            rw [hs4]; simp only [stCallvalue]; exact haw3
          -- STEP 4: DUP1 (cost 3, C 20→23)
          have hstep4 := dup1_xstep hcode4 hpc4 (by decide) hstk4 (by norm_num)
          by_cases h4 : g.toNat < 23
          · exact Or.inl (by rw [hX4]; exact stepOOG hgas4 hstep4 (by norm_num) (by omega) (by omega))
          · set s5 := stDup1 s4 I.weiValue [] with hs5
            have hX5 := hX4.trans (stepContinue (k := 4) (C := 20) hgas4 hstep4 (by norm_num) (by omega))
            have hee5 : s5.executionEnv = I := by rw [hs5]; simp only [stDup1]; exact hee4
            have hcode5 : s5.executionEnv.code = truthBytecode := by rw [hee5]; exact hcode
            have hpc5 : s5.machineState.pc = ((((⟨0⟩ + UInt256.ofNat 2) + UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩ := by
              rw [hs5]; simp only [stDup1]; rw [hpc4]
            have hgas5 : s5.machineState.gasAvailable.toNat = g.toNat - 23 := by
              rw [hs5]; simp only [stDup1]; rw [toNat_sub_ofNat (by omega)]; omega
            have hstk5 : s5.machineState.stack = [I.weiValue, I.weiValue] := by
              rw [hs5]; simp only [stDup1]
            -- STEP 5: ISZERO (cost 3, C 23→26)
            have hstep5 := iszero_xstep hcode5 hpc5 (by decide) hstk5 (by norm_num)
            by_cases h5 : g.toNat < 26
            · exact Or.inl (by rw [hX5]; exact stepOOG hgas5 hstep5 (by norm_num) (by omega) (by omega))
            · set s6 := stIsZero s5 I.weiValue [I.weiValue] with hs6
              have hX6 := hX5.trans (stepContinue (k := 5) (C := 23) hgas5 hstep5 (by norm_num) (by omega))
              have hee6 : s6.executionEnv = I := by rw [hs6]; simp only [stIsZero]; exact hee5
              have hcode6 : s6.executionEnv.code = truthBytecode := by rw [hee6]; exact hcode
              have hpc6 : s6.machineState.pc = (((((⟨0⟩ + UInt256.ofNat 2) + UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩ := by
                rw [hs6]; simp only [stIsZero]; rw [hpc5]
              have hgas6 : s6.machineState.gasAvailable.toNat = g.toNat - 26 := by
                rw [hs6]; simp only [stIsZero]; rw [toNat_sub_ofNat (by omega)]; omega
              have hstk6 : s6.machineState.stack = [⟨0⟩, I.weiValue] := by
                rw [hs6]; simp only [stIsZero, isZero_eq_zero_of_ne hwv]
              -- STEP 6: PUSH1 0x0e (cost 3, C 26→29)
              have hstep6 := push1_xstep (argv := ⟨14⟩) hcode6 hpc6 (by decide) hstk6 (by norm_num)
              by_cases h6 : g.toNat < 29
              · exact Or.inl (by rw [hX6]; exact stepOOG hgas6 hstep6 (by norm_num) (by omega) (by omega))
              · set s7 := stPush1 s6 ⟨14⟩ with hs7
                have hX7 := hX6.trans (stepContinue (k := 6) (C := 26) hgas6 hstep6 (by norm_num) (by omega))
                have hee7 : s7.executionEnv = I := by rw [hs7]; simp only [stPush1]; exact hee6
                have hcode7 : s7.executionEnv.code = truthBytecode := by rw [hee7]; exact hcode
                have hpc7 : s7.machineState.pc = ((((((⟨0⟩ + UInt256.ofNat 2) + UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2 := by
                  rw [hs7]; simp only [stPush1]; rw [hpc6]
                have hgas7 : s7.machineState.gasAvailable.toNat = g.toNat - 29 := by
                  rw [hs7]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                have hstk7 : s7.machineState.stack = ⟨14⟩ :: ⟨0⟩ :: [I.weiValue] := by
                  rw [hs7]; simp only [stPush1, hstk6]
                -- STEP 7: JUMPI not-taken (cost 10, C 29→39)
                have hstep7 := jumpi_nt_xstep hcode7 hpc7 (by decide) hstk7 (by norm_num)
                by_cases h7 : g.toNat < 39
                · exact Or.inl (by rw [hX7]; exact stepOOG hgas7 hstep7 (by norm_num) (by omega) (by omega))
                · set s8 := stJumpiNT s7 [I.weiValue] with hs8
                  have hX8 := hX7.trans (stepContinue (k := 7) (C := 29) hgas7 hstep7 (by norm_num) (by omega))
                  have hee8 : s8.executionEnv = I := by rw [hs8]; simp only [stJumpiNT]; exact hee7
                  have hcode8 : s8.executionEnv.code = truthBytecode := by rw [hee8]; exact hcode
                  have hpc8 : s8.machineState.pc = (((((((⟨0⟩ + UInt256.ofNat 2) + UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩ := by
                    rw [hs8]; simp only [stJumpiNT]; rw [hpc7]
                  have hgas8 : s8.machineState.gasAvailable.toNat = g.toNat - 39 := by
                    rw [hs8]; simp only [stJumpiNT]; rw [toNat_sub_ofNat (by omega)]; omega
                  have hstk8 : s8.machineState.stack = [I.weiValue] := by
                    rw [hs8]; simp only [stJumpiNT]
                  -- STEP 8: PUSH0 (cost 2, C 39→41)
                  have hstep8 := push0_xstep hcode8 hpc8 (by decide) hstk8 (by norm_num)
                  by_cases h8 : g.toNat < 41
                  · exact Or.inl (by rw [hX8]; exact stepOOG hgas8 hstep8 (by norm_num) (by omega) (by omega))
                  · set s9 := stPush0 s8 with hs9
                    have hX9 := hX8.trans (stepContinue (k := 8) (C := 39) hgas8 hstep8 (by norm_num) (by omega))
                    have hee9 : s9.executionEnv = I := by rw [hs9]; simp only [stPush0]; exact hee8
                    have hcode9 : s9.executionEnv.code = truthBytecode := by rw [hee9]; exact hcode
                    have hpc9 : s9.machineState.pc = ((((((((⟨0⟩ + UInt256.ofNat 2) + UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩ := by
                      rw [hs9]; simp only [stPush0]; rw [hpc8]
                    have hgas9 : s9.machineState.gasAvailable.toNat = g.toNat - 41 := by
                      rw [hs9]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                    have hstk9 : s9.machineState.stack = [⟨0⟩, I.weiValue] := by
                      rw [hs9]; simp only [stPush0, hstk8]
                    -- STEP 9: PUSH0 (cost 2, C 41→43)
                    have hstep9 := push0_xstep hcode9 hpc9 (by decide) hstk9 (by norm_num)
                    by_cases h9 : g.toNat < 43
                    · exact Or.inl (by rw [hX9]; exact stepOOG hgas9 hstep9 (by norm_num) (by omega) (by omega))
                    · set s10 := stPush0 s9 with hs10
                      have hX10 := hX9.trans (stepContinue (k := 9) (C := 41) hgas9 hstep9 (by norm_num) (by omega))
                      have hee10 : s10.executionEnv = I := by rw [hs10]; simp only [stPush0]; exact hee9
                      have hcode10 : s10.executionEnv.code = truthBytecode := by rw [hee10]; exact hcode
                      have hpc10 : s10.machineState.pc = (((((((((⟨0⟩ + UInt256.ofNat 2) + UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩ := by
                        rw [hs10]; simp only [stPush0]; rw [hpc9]
                      have hgas10 : s10.machineState.gasAvailable.toNat = g.toNat - 43 := by
                        rw [hs10]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                      have hstk10 : s10.machineState.stack = [⟨0⟩, ⟨0⟩, I.weiValue] := by
                        rw [hs10]; simp only [stPush0, hstk9]
                      have haw10 : s10.machineState.activeWords = UInt256.ofNat 3 := by
                        rw [hs10, hs9, hs8, hs7, hs6, hs5, hs4]
                        simp only [stPush0, stJumpiNT, stPush1, stIsZero, stDup1, stCallvalue]
                        exact haw4
                      have hmcr : memoryExpansionCost s10 .REVERT = 0 := by
                        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw10, hstk10,
                          List.getElem!_cons_zero, List.getElem!_cons_succ, MachineState.M]
                        decide
                      -- STEP 10: REVERT (halt, cost 0)
                      have hstep10 := revert_xstep hcode10 hpc10 (by decide) hstk10 (by norm_num)
                      rw [hmcr] at hstep10
                      exact Or.inr ⟨_, _, by
                        rw [hX10]
                        exact stepHaltRevert (k := 10) (C := 43) (cost := 0) hgas10 hstep10
                          (by norm_num) (by omega)⟩

/-- **Scenario A** (`callvalue ≠ 0`): the compiler's non-payable guard reverts before any
    taken jump or keccak, so `Ξ` either runs out of gas or reverts.  Lifts the `X` trace. -/
theorem truthXi_callvalue_ne
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    Ξ cA gh bl σ σ₀ g A I = .error .OutOfGass
      ∨ ∃ g' o, Ξ cA gh bl σ σ₀ g A I = .ok (.revert g' o) := by
  rcases truthX_callvalue_ne (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv with h | ⟨g', o, h⟩
  · rw [← hcode] at h; exact Or.inl (Xi_error_of_X h)
  · rw [← hcode] at h; exact Or.inr ⟨g', o, Xi_revert_of_X h⟩

/-- **callvalue = 0**: the main dispatch path; needs the trusted axioms above (taken jumps
    via `truthValidJumps`, selector match via `truthSelectorBytes`). -/
theorem truthReEquiv_callvalueZero
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) :
    runtimeEquivalenceFor truthConfig truthContract cA gh bl σ σ₀ g A I := by
  sorry

/-! ## 6. The correctness statement -/

/-- The runtime bytecode refines the Act specification, for every initial state. -/
theorem truthCorrect :
    runtimeEquivalence!?! truthConfig truthBytecode truthContract := by
  refine ⟨fun cA gh bl σ σ₀ g A I hcode hsize => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact truthReEquiv_callvalueZero hcode hsize hwv
  · -- callvalue ≠ 0: scenario A
    rcases truthXi_callvalue_ne hcode hwv with hoog | ⟨g', o, hrev⟩
    · exact reEquiv_outOfGas hoog
    · by_cases hdisp : dispatchMsg truthContract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        cases truthDispatch_unique ht
        by_cases hdec : decodeCalldata (truthTransition.params.map Param.name)
            (transitionSignature truthTransition).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          refine reEquiv_execution ht hca (truthBodyReverts _ _ ?_) ?_
          · show I.weiValue ≠ ⟨0⟩; exact hwv
          · rw [hrev]; exact .revert rfl rfl
