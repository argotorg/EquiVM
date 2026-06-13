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

/-- Dispatch reduces (via `truthSelectorBytes`) to a 4-byte calldata-prefix comparison. -/
theorem truthDispatch_eq (cd : ByteArray) :
    dispatchMsg truthContract cd
      = if ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4)
        then some truthTransition else none := by
  simp only [dispatchMsg, truthContract, List.map_cons, List.map_nil, List.find?_cons,
    List.find?_nil, Prod.map, id_eq, Function.comp_apply]
  rw [truthSelectorBytes]
  by_cases hb : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4) = true
  · simp [hb]
  · simp only [Bool.not_eq_true] at hb; simp [hb]

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

/-! ### callvalue = 0 dispatcher: the `calldatasize < 4` branch (short-calldata revert) -/

theorem truthContains14 : (D_J truthBytecode ⟨0⟩).contains ⟨14⟩ = true := by
  rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)
theorem truthContains38 : (D_J truthBytecode ⟨0⟩).contains ⟨38⟩ = true := by
  rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)

/-- The 19-instruction dispatcher trace for `callvalue = 0 ∧ calldatasize < 4`: two taken
    jumps (`0x0a → 0x0e`, `0x16 → 0x26`, discharged by `truthValidJumps`) then `REVERT`.
    Either out-of-gas or reverts. -/
theorem truthX_cvz_short
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
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
  have hstep0 := push1_xstep (argv := ⟨128⟩) hcode0 hpc0 (by decide) hstk0 (by norm_num)
  by_cases h0 : g.toNat < 3
  · exact Or.inl (by rw [hX0]; exact stepOOG hgas0 hstep0 (by norm_num) (by omega) (by omega))
  · set s1 := stPush1 s0 ⟨128⟩ with hs1
    have hX1 := hX0.trans (stepContinue (k := 0) (C := 0) hgas0 hstep0 (by norm_num) (by omega))
    have hee1 : s1.executionEnv = I := by rw [hs1]; simp only [stPush1]; exact hee0
    have hcode1 : s1.executionEnv.code = truthBytecode := by rw [hee1]; exact hcode
    have hpc1 : s1.machineState.pc = ⟨0⟩ + UInt256.ofNat 2 := by rw [hs1]; simp only [stPush1]; rw [hpc0]
    have hgas1 : s1.machineState.gasAvailable.toNat = g.toNat - 3 := by
      rw [hs1]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
    have hstk1 : s1.machineState.stack = [⟨128⟩] := by rw [hs1]; simp [stPush1, hstk0]
    have haw1 : s1.machineState.activeWords = ⟨0⟩ := by rw [hs1]; simp [stPush1, haw0]
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
      have hstep2 := mstore_xstep hcode2 hpc2 (by decide) hstk2 (by norm_num)
      rw [hmc] at hstep2
      by_cases h2 : g.toNat < 18
      · exact Or.inl (by rw [hX2]
                         exact stepOOG (cost := 9 + 3) hgas2 hstep2 (by norm_num) (by omega) (by omega))
      · set s3 := stMStore s2 ⟨64⟩ ⟨128⟩ [] with hs3
        have hX3 := hX2.trans (stepContinue (k := 2) (C := 6) (cost := 9 + 3) hgas2 hstep2 (by norm_num) (by omega))
        have hee3 : s3.executionEnv = I := by rw [hs3]; simp only [stMStore]; exact hee2
        have hcode3 : s3.executionEnv.code = truthBytecode := by rw [hee3]; exact hcode
        have hpc3 : s3.machineState.pc = ((⟨0⟩ + UInt256.ofNat 2) + UInt256.ofNat 2) + ⟨1⟩ := by
          rw [hs3]; simp only [stMStore]; rw [hpc2]
        have hgas3 : s3.machineState.gasAvailable.toNat = g.toNat - 18 := by
          rw [hs3]; simp only [stMStore, hmc]
          rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]; omega
        have hstk3 : s3.machineState.stack = [] := by rw [hs3]; simp [stMStore]
        have haw3 : s3.machineState.activeWords = UInt256.ofNat 3 := by
          rw [hs3]; simp only [stMStore, haw2]; decide
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
          have hstk4 : s4.machineState.stack = [⟨0⟩] := by
            rw [hs4]; simp only [stCallvalue, hstk3, hee3, hwv]
          have haw4 : s4.machineState.activeWords = UInt256.ofNat 3 := by
            rw [hs4]; simp only [stCallvalue]; exact haw3
          have hstep4 := dup1_xstep hcode4 hpc4 (by decide) hstk4 (by norm_num)
          by_cases h4 : g.toNat < 23
          · exact Or.inl (by rw [hX4]; exact stepOOG hgas4 hstep4 (by norm_num) (by omega) (by omega))
          · set s5 := stDup1 s4 ⟨0⟩ [] with hs5
            have hX5 := hX4.trans (stepContinue (k := 4) (C := 20) hgas4 hstep4 (by norm_num) (by omega))
            have hee5 : s5.executionEnv = I := by rw [hs5]; simp only [stDup1]; exact hee4
            have hcode5 : s5.executionEnv.code = truthBytecode := by rw [hee5]; exact hcode
            have hpc5 : s5.machineState.pc = ((((⟨0⟩ + UInt256.ofNat 2) + UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩ := by
              rw [hs5]; simp only [stDup1]; rw [hpc4]
            have hgas5 : s5.machineState.gasAvailable.toNat = g.toNat - 23 := by
              rw [hs5]; simp only [stDup1]; rw [toNat_sub_ofNat (by omega)]; omega
            have hstk5 : s5.machineState.stack = [⟨0⟩, ⟨0⟩] := by rw [hs5]; simp only [stDup1]
            have hstep5 := iszero_xstep hcode5 hpc5 (by decide) hstk5 (by norm_num)
            by_cases h5 : g.toNat < 26
            · exact Or.inl (by rw [hX5]; exact stepOOG hgas5 hstep5 (by norm_num) (by omega) (by omega))
            · set s6 := stIsZero s5 ⟨0⟩ [⟨0⟩] with hs6
              have hX6 := hX5.trans (stepContinue (k := 5) (C := 23) hgas5 hstep5 (by norm_num) (by omega))
              have hee6 : s6.executionEnv = I := by rw [hs6]; simp only [stIsZero]; exact hee5
              have hcode6 : s6.executionEnv.code = truthBytecode := by rw [hee6]; exact hcode
              have hpc6 : s6.machineState.pc = (((((⟨0⟩ + UInt256.ofNat 2) + UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩ := by
                rw [hs6]; simp only [stIsZero]; rw [hpc5]
              have hgas6 : s6.machineState.gasAvailable.toNat = g.toNat - 26 := by
                rw [hs6]; simp only [stIsZero]; rw [toNat_sub_ofNat (by omega)]; omega
              have hstk6 : s6.machineState.stack = [⟨1⟩, ⟨0⟩] := by
                rw [hs6]; simp only [stIsZero, isZero_zero]
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
                have hstk7 : s7.machineState.stack = ⟨14⟩ :: ⟨1⟩ :: [⟨0⟩] := by rw [hs7]; simp only [stPush1, hstk6]
                have hstep7 := jumpi_t_xstep hcode7 hpc7 (by decide) hstk7 one_ne_zero_uint
                                (hcode7 ▸ truthContains14) (by norm_num)
                by_cases h7 : g.toNat < 39
                · exact Or.inl (by rw [hX7]; exact stepOOG hgas7 hstep7 (by norm_num) (by omega) (by omega))
                · set s8 := stJumpiT s7 ⟨14⟩ [⟨0⟩] with hs8
                  have hX8 := hX7.trans (stepContinue (k := 7) (C := 29) hgas7 hstep7 (by norm_num) (by omega))
                  have hee8 : s8.executionEnv = I := by rw [hs8]; simp only [stJumpiT]; exact hee7
                  have hcode8 : s8.executionEnv.code = truthBytecode := by rw [hee8]; exact hcode
                  have hpc8 : s8.machineState.pc = ⟨14⟩ := by rw [hs8]; simp only [stJumpiT]
                  have hgas8 : s8.machineState.gasAvailable.toNat = g.toNat - 39 := by
                    rw [hs8]; simp only [stJumpiT]; rw [toNat_sub_ofNat (by omega)]; omega
                  have hstk8 : s8.machineState.stack = [⟨0⟩] := by rw [hs8]; simp only [stJumpiT]
                  have hstep8 := jumpdest_xstep hcode8 hpc8 (by decide) (by rw [hstk8]; norm_num)
                  by_cases h8 : g.toNat < 40
                  · exact Or.inl (by rw [hX8]; exact stepOOG hgas8 hstep8 (by norm_num) (by omega) (by omega))
                  · set s9 := stJumpdest s8 with hs9
                    have hX9 := hX8.trans (stepContinue (k := 8) (C := 39) hgas8 hstep8 (by norm_num) (by omega))
                    have hee9 : s9.executionEnv = I := by rw [hs9]; simp only [stJumpdest]; exact hee8
                    have hcode9 : s9.executionEnv.code = truthBytecode := by rw [hee9]; exact hcode
                    have hpc9 : s9.machineState.pc = ⟨14⟩ + ⟨1⟩ := by rw [hs9]; simp only [stJumpdest]; rw [hpc8]
                    have hgas9 : s9.machineState.gasAvailable.toNat = g.toNat - 40 := by
                      rw [hs9]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                    have hstk9 : s9.machineState.stack = [⟨0⟩] := by rw [hs9]; simp only [stJumpdest]; exact hstk8
                    have hstep9 := pop_xstep hcode9 hpc9 (by decide) hstk9 (by norm_num)
                    by_cases h9 : g.toNat < 42
                    · exact Or.inl (by rw [hX9]; exact stepOOG hgas9 hstep9 (by norm_num) (by omega) (by omega))
                    · set s10 := stPop s9 [] with hs10
                      have hX10 := hX9.trans (stepContinue (k := 9) (C := 40) hgas9 hstep9 (by norm_num) (by omega))
                      have hee10 : s10.executionEnv = I := by rw [hs10]; simp only [stPop]; exact hee9
                      have hcode10 : s10.executionEnv.code = truthBytecode := by rw [hee10]; exact hcode
                      have hpc10 : s10.machineState.pc = (⟨14⟩ + ⟨1⟩) + ⟨1⟩ := by rw [hs10]; simp only [stPop]; rw [hpc9]
                      have hgas10 : s10.machineState.gasAvailable.toNat = g.toNat - 42 := by
                        rw [hs10]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                      have hstk10 : s10.machineState.stack = [] := by rw [hs10]; simp only [stPop]
                      have hstep10 := push1_xstep (argv := ⟨4⟩) hcode10 hpc10 (by decide) hstk10 (by norm_num)
                      by_cases h10 : g.toNat < 45
                      · exact Or.inl (by rw [hX10]; exact stepOOG hgas10 hstep10 (by norm_num) (by omega) (by omega))
                      · set s11 := stPush1 s10 ⟨4⟩ with hs11
                        have hX11 := hX10.trans (stepContinue (k := 10) (C := 42) hgas10 hstep10 (by norm_num) (by omega))
                        have hee11 : s11.executionEnv = I := by rw [hs11]; simp only [stPush1]; exact hee10
                        have hcode11 : s11.executionEnv.code = truthBytecode := by rw [hee11]; exact hcode
                        have hpc11 : s11.machineState.pc = ((⟨14⟩ + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2 := by
                          rw [hs11]; simp only [stPush1]; rw [hpc10]
                        have hgas11 : s11.machineState.gasAvailable.toNat = g.toNat - 45 := by
                          rw [hs11]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                        have hstk11 : s11.machineState.stack = [⟨4⟩] := by rw [hs11]; simp [stPush1, hstk10]
                        have hstep11 := calldatasize_xstep hcode11 hpc11 (by decide) hstk11 (by norm_num)
                        by_cases h11 : g.toNat < 47
                        · exact Or.inl (by rw [hX11]; exact stepOOG hgas11 hstep11 (by norm_num) (by omega) (by omega))
                        · set s12 := stCalldatasize s11 with hs12
                          have hX12 := hX11.trans (stepContinue (k := 11) (C := 45) hgas11 hstep11 (by norm_num) (by omega))
                          have hee12 : s12.executionEnv = I := by rw [hs12]; simp only [stCalldatasize]; exact hee11
                          have hcode12 : s12.executionEnv.code = truthBytecode := by rw [hee12]; exact hcode
                          have hpc12 : s12.machineState.pc = (((⟨14⟩ + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩ := by
                            rw [hs12]; simp only [stCalldatasize]; rw [hpc11]
                          have hgas12 : s12.machineState.gasAvailable.toNat = g.toNat - 47 := by
                            rw [hs12]; simp only [stCalldatasize]; rw [toNat_sub_ofNat (by omega)]; omega
                          have hstk12 : s12.machineState.stack = [UInt256.ofNat I.calldata.size, ⟨4⟩] := by
                            rw [hs12]; simp only [stCalldatasize, hstk11, hee11]
                          have hstep12 := lt_xstep hcode12 hpc12 (by decide) hstk12 (by norm_num)
                          by_cases h12 : g.toNat < 50
                          · exact Or.inl (by rw [hX12]; exact stepOOG hgas12 hstep12 (by norm_num) (by omega) (by omega))
                          · set s13 := stBinop s12 (UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩) [] with hs13
                            have hX13 := hX12.trans (stepContinue (k := 12) (C := 47) hgas12 hstep12 (by norm_num) (by omega))
                            have hee13 : s13.executionEnv = I := by rw [hs13]; simp only [stBinop]; exact hee12
                            have hcode13 : s13.executionEnv.code = truthBytecode := by rw [hee13]; exact hcode
                            have hpc13 : s13.machineState.pc = ((((⟨14⟩ + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩ := by
                              rw [hs13]; simp only [stBinop]; rw [hpc12]
                            have hgas13 : s13.machineState.gasAvailable.toNat = g.toNat - 50 := by
                              rw [hs13]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                            have hstk13 : s13.machineState.stack = [UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩] := by
                              rw [hs13]; simp only [stBinop]
                            have hstep13 := push1_xstep (argv := ⟨38⟩) hcode13 hpc13 (by decide) hstk13 (by norm_num)
                            by_cases h13 : g.toNat < 53
                            · exact Or.inl (by rw [hX13]; exact stepOOG hgas13 hstep13 (by norm_num) (by omega) (by omega))
                            · set s14 := stPush1 s13 ⟨38⟩ with hs14
                              have hX14 := hX13.trans (stepContinue (k := 13) (C := 50) hgas13 hstep13 (by norm_num) (by omega))
                              have hee14 : s14.executionEnv = I := by rw [hs14]; simp only [stPush1]; exact hee13
                              have hcode14 : s14.executionEnv.code = truthBytecode := by rw [hee14]; exact hcode
                              have hpc14 : s14.machineState.pc = (((((⟨14⟩ + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 2 := by
                                rw [hs14]; simp only [stPush1]; rw [hpc13]
                              have hgas14 : s14.machineState.gasAvailable.toNat = g.toNat - 53 := by
                                rw [hs14]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                              have hstk14 : s14.machineState.stack = ⟨38⟩ :: UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩ :: [] := by
                                rw [hs14]; simp only [stPush1, hstk13]
                              have hbne : UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩ ≠ ⟨0⟩ :=
                                lt_four_ne_zero_of_lt hsz
                              have hstep14 := jumpi_t_xstep hcode14 hpc14 (by decide) hstk14 hbne
                                              (hcode14 ▸ truthContains38) (by norm_num)
                              by_cases h14 : g.toNat < 63
                              · exact Or.inl (by rw [hX14]; exact stepOOG hgas14 hstep14 (by norm_num) (by omega) (by omega))
                              · set s15 := stJumpiT s14 ⟨38⟩ [] with hs15
                                have hX15 := hX14.trans (stepContinue (k := 14) (C := 53) hgas14 hstep14 (by norm_num) (by omega))
                                have hee15 : s15.executionEnv = I := by rw [hs15]; simp only [stJumpiT]; exact hee14
                                have hcode15 : s15.executionEnv.code = truthBytecode := by rw [hee15]; exact hcode
                                have hpc15 : s15.machineState.pc = ⟨38⟩ := by rw [hs15]; simp only [stJumpiT]
                                have hgas15 : s15.machineState.gasAvailable.toNat = g.toNat - 63 := by
                                  rw [hs15]; simp only [stJumpiT]; rw [toNat_sub_ofNat (by omega)]; omega
                                have hstk15 : s15.machineState.stack = [] := by rw [hs15]; simp only [stJumpiT]
                                have hstep15 := jumpdest_xstep hcode15 hpc15 (by decide) (by rw [hstk15]; norm_num)
                                by_cases h15 : g.toNat < 64
                                · exact Or.inl (by rw [hX15]; exact stepOOG hgas15 hstep15 (by norm_num) (by omega) (by omega))
                                · set s16 := stJumpdest s15 with hs16
                                  have hX16 := hX15.trans (stepContinue (k := 15) (C := 63) hgas15 hstep15 (by norm_num) (by omega))
                                  have hee16 : s16.executionEnv = I := by rw [hs16]; simp only [stJumpdest]; exact hee15
                                  have hcode16 : s16.executionEnv.code = truthBytecode := by rw [hee16]; exact hcode
                                  have hpc16 : s16.machineState.pc = ⟨38⟩ + ⟨1⟩ := by rw [hs16]; simp only [stJumpdest]; rw [hpc15]
                                  have hgas16 : s16.machineState.gasAvailable.toNat = g.toNat - 64 := by
                                    rw [hs16]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                                  have hstk16 : s16.machineState.stack = [] := by rw [hs16]; simp only [stJumpdest]; exact hstk15
                                  have hstep16 := push0_xstep hcode16 hpc16 (by decide) hstk16 (by norm_num)
                                  by_cases h16 : g.toNat < 66
                                  · exact Or.inl (by rw [hX16]; exact stepOOG hgas16 hstep16 (by norm_num) (by omega) (by omega))
                                  · set s17 := stPush0 s16 with hs17
                                    have hX17 := hX16.trans (stepContinue (k := 16) (C := 64) hgas16 hstep16 (by norm_num) (by omega))
                                    have hee17 : s17.executionEnv = I := by rw [hs17]; simp only [stPush0]; exact hee16
                                    have hcode17 : s17.executionEnv.code = truthBytecode := by rw [hee17]; exact hcode
                                    have hpc17 : s17.machineState.pc = (⟨38⟩ + ⟨1⟩) + ⟨1⟩ := by rw [hs17]; simp only [stPush0]; rw [hpc16]
                                    have hgas17 : s17.machineState.gasAvailable.toNat = g.toNat - 66 := by
                                      rw [hs17]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                                    have hstk17 : s17.machineState.stack = [⟨0⟩] := by rw [hs17]; simp only [stPush0, hstk16]
                                    have hstep17 := push0_xstep hcode17 hpc17 (by decide) hstk17 (by norm_num)
                                    by_cases h17 : g.toNat < 68
                                    · exact Or.inl (by rw [hX17]; exact stepOOG hgas17 hstep17 (by norm_num) (by omega) (by omega))
                                    · set s18 := stPush0 s17 with hs18
                                      have hX18 := hX17.trans (stepContinue (k := 17) (C := 66) hgas17 hstep17 (by norm_num) (by omega))
                                      have hee18 : s18.executionEnv = I := by rw [hs18]; simp only [stPush0]; exact hee17
                                      have hcode18 : s18.executionEnv.code = truthBytecode := by rw [hee18]; exact hcode
                                      have hpc18 : s18.machineState.pc = ((⟨38⟩ + ⟨1⟩) + ⟨1⟩) + ⟨1⟩ := by rw [hs18]; simp only [stPush0]; rw [hpc17]
                                      have hgas18 : s18.machineState.gasAvailable.toNat = g.toNat - 68 := by
                                        rw [hs18]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                                      have hstk18 : s18.machineState.stack = [⟨0⟩, ⟨0⟩] := by rw [hs18]; simp only [stPush0, hstk17]
                                      have haw18 : s18.machineState.activeWords = UInt256.ofNat 3 := by
                                        rw [hs18, hs17, hs16, hs15, hs14, hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4]
                                        simp only [stPush0, stJumpdest, stJumpiT, stPush1, stBinop, stCalldatasize, stPop, stIsZero, stDup1, stCallvalue]
                                        exact haw4
                                      have hmcr : memoryExpansionCost s18 .REVERT = 0 := by
                                        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw18, hstk18,
                                          List.getElem!_cons_zero, List.getElem!_cons_succ, MachineState.M]
                                        decide
                                      have hstep18 := revert_xstep hcode18 hpc18 (by decide) hstk18 (by norm_num)
                                      rw [hmcr] at hstep18
                                      exact Or.inr ⟨_, _, by
                                        rw [hX18]
                                        exact stepHaltRevert (k := 18) (C := 68) (cost := 0) hgas18 hstep18
                                          (by norm_num) (by omega)⟩

/-- Short calldata (`< 4` bytes) cannot match the 4-byte selector ⇒ dispatch fails. -/
theorem truthDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg truthContract cd = none := by
  rw [truthDispatch_eq]
  have hfalse : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have hsz := TruthClaude.Theory.byteArray_size_eq_of_beq hc
    rw [ByteArray.size_extract] at hsz
    simp only [show (⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray).size = 4 from rfl] at hsz
    omega
  simp [hfalse]

/-- **callvalue = 0**: the main dispatch path.  The `calldatasize < 4` branch (short-calldata
    revert) is proved; the `≥ 4` branch (selector compare / `truth()` success) is the remaining
    gap (needs `truthSelectorBytes` wired to the EVM selector and the ABI return encoding). -/
theorem truthReEquiv_callvalueZero
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) :
    runtimeEquivalenceFor truthConfig truthContract cA gh bl σ σ₀ g A I := by
  by_cases hsz : I.calldata.size < 4
  · -- short calldata: EVM reverts (after the two taken jumps); Act fails to dispatch.
    rcases truthX_cvz_short (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcode hwv hsz with hX | ⟨g', o, hX⟩
    · rw [← hcode] at hX; exact reEquiv_outOfGas (Xi_error_of_X hX)
    · rw [← hcode] at hX
      exact reEquiv_noDispatch (truthDispatch_none_short hsz) (Xi_revert_of_X hX)
  · -- calldatasize ≥ 4: selector compare → `truth()` success, or wrong-selector revert.
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
