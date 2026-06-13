import TruthClaude.Theory
import TruthClaude.Stepping
import TruthClaude.Memory

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
* `truthCorrect`  — the correctness statement.  **Fully proved** (no `sorry`): every call —
  `callvalue ≠ 0`, low-gas, short-calldata, wrong-selector, and the `truth()` success path
  (a 93-instruction EVM trace that ABI-encodes and `RETURN`s `true`) — is shown equivalent to
  the Act spec, via the contract-agnostic `TruthClaude.Theory`/`Stepping`/`Memory` libraries.
  `#print axioms truthCorrect` lists only Lean's three, the evmlean `ByteArray_zeroes_size`
  base axiom, the `ffi.zeroes`-content extern spec, and the three documented trusted
  selector/jump axioms (see `MISSPEC.md`) — no `sorryAx`.
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

/-- With zero call value, the Act body returns `true`: `require(callvalue == 0)` passes and
    `return true` yields `(.bool true)` with the frame/EVM-state unchanged. -/
theorem truthBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecContractBody truthConfig truthContract evm locals truthTransition.body
      (.returned { contract := truthContract, locals := locals } evm (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet (ExecBlock.consNormal (ExecStmt.requireTrue ?_)
            (ExecBlock.consReturn (ExecStmt.return ?_)))
  · have hval : (Value.int (Int.ofNat ↑evm.executionEnv.weiValue.val) == Value.int 0) = true := by
      rw [h]; rfl
    show evalExpr? truthConfig _ evm (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true)
    simp only [evalExpr?, EvalResult.bind, bind, pure, envValue, evalBinaryOp?, hval]
  · show evalExpr? truthConfig _ evm (.boolLit true) = .ok (.bool true)
    simp only [evalExpr?]; rfl

/-- **ABI encoding of the `truth()` return.**  `encodeReturnValue?` of `(.bool true)` is the
    32-byte big-endian word `1` — definitionally the EVM `RETURN`/`MSTORE` value
    `UInt256.toByteArray ⟨1⟩` (the opaque `ffi.zeroes` pad cancels; see
    `TruthClaude.Theory.toByteArray_eq_toBytesBE`). -/
theorem truthReturnEncoding :
    encodeReturnValue? (.elem .bool) (.bool true) = some (UInt256.toByteArray ⟨1⟩) := by
  rw [TruthClaude.Theory.toByteArray_eq_toBytesBE]
  simp [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, abiTupleHeadSize?,
    staticABIEncodedSize?, isDynamicABIType, encodeABIValuesFrom?, encodeABIValue?,
    encodeABIWord?, Bool.toUInt256_true]
  rfl

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

/-! ### callvalue = 0 dispatcher -/

theorem truthContains14 : (D_J truthBytecode ⟨0⟩).contains ⟨14⟩ = true := by
  rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)
theorem truthContains38 : (D_J truthBytecode ⟨0⟩).contains ⟨38⟩ = true := by
  rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)
theorem truthContains42 : (D_J truthBytecode ⟨0⟩).contains ⟨42⟩ = true := by
  rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)

/-! ### Selector decode — **proved** (was a trusted axiom; not opaque)

Relating the EVM's `CALLDATALOAD; PUSH 0xe0; SHR` selector to `calldata.extract 0 4` is pure
byte arithmetic.  `Memory.selector_toNat` does the 256-bit-shift ↔ byte-extraction core; below is
the `0x9e9f51d2`-specific bijection and the final equivalence (needs `4 ≤ calldata.size`, which
the dispatch path always has).  No new axioms — only `byteArray_zeroes_toList`. -/

private theorem u256_inj {a b : UInt256} (h : a.toNat = b.toNat) : a = b := by
  cases a; cases b; simp only [UInt256.toNat] at h; exact congrArg UInt256.mk (Fin.ext h)
private theorem u256_eq_self : UInt256.eq ⟨2661241298⟩ ⟨2661241298⟩ = ⟨1⟩ := by decide
private theorem u256_eq_ne {b : UInt256} (h : (⟨2661241298⟩ : UInt256) ≠ b) :
    UInt256.eq ⟨2661241298⟩ b = ⟨0⟩ := by
  simp only [UInt256.eq, Bool.toUInt256, decide_eq_false h]; rfl

/-- Big-endian decode of four bytes equals `0x9e9f51d2` iff the bytes are `[9e,9f,51,d2]`. -/
private theorem be4 (l : List UInt8) (hl : l.length = 4) :
    fromBytesBigEndian l = 2661241298 ↔ l = [0x9e, 0x9f, 0x51, 0xd2] := by
  match l, hl with
  | [b0, b1, b2, b3], _ =>
    unfold fromBytesBigEndian Function.comp
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, fromBytes',
      List.cons.injEq, and_true]
    have h0 := b0.toFin.isLt; have h1 := b1.toFin.isLt
    have h2 := b2.toFin.isLt; have h3 := b3.toFin.isLt
    simp only [UInt8.size] at h0 h1 h2 h3
    have e0 : b0.toFin.val = b0.toNat := rfl; have e1 : b1.toFin.val = b1.toNat := rfl
    have e2 : b2.toFin.val = b2.toNat := rfl; have e3 : b3.toFin.val = b3.toNat := rfl
    rw [e0, e1, e2, e3]
    have l0 : (0x9e : UInt8).toNat = 158 := rfl; have l1 : (0x9f : UInt8).toNat = 159 := rfl
    have l2 : (0x51 : UInt8).toNat = 81 := rfl; have l3 : (0xd2 : UInt8).toNat = 210 := rfl
    constructor
    · intro he
      exact ⟨UInt8.toNat_inj.mp (by omega), UInt8.toNat_inj.mp (by omega),
             UInt8.toNat_inj.mp (by omega), UInt8.toNat_inj.mp (by omega)⟩
    · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

/-- The `ByteArray` `==` selector test equals the first-four-bytes list condition. -/
private theorem extract_eq_iff (cd : ByteArray) (hsz : 4 ≤ cd.size) :
    ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4) = true
      ↔ cd.data.toList.take 4 = [0x9e, 0x9f, 0x51, 0xd2] := by
  rw [show ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4)
        = ((#[0x9e, 0x9f, 0x51, 0xd2] : Array UInt8) == (cd.extract 0 4).data) from rfl,
      beq_iff_eq, ByteArray.data_extract, ← Array.toList_inj, Array.toList_extract]
  show ([0x9e, 0x9f, 0x51, 0xd2] : List UInt8) = (cd.data.toList.drop 0).take (0 + 4 - 0) ↔ _
  rw [List.drop_zero]
  constructor
  · intro he; rw [← he]
  · intro he; rw [he]

/-- **Selector decode** (proved): the EVM selector check `eq(0x9e9f51d2, SHR(calldata,224))`
    agrees with the dispatcher's 4-byte compare `0x9e9f51d2 == calldata.extract 0 4`. -/
theorem truthEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨2661241298⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  have hlen4 : (cd.data.toList.take 4).length = 4 := by
    rw [List.length_take]
    have : 4 ≤ cd.data.toList.length := by rw [Array.length_toList]; exact hsz
    omega
  have hsv : (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩).toNat
             = fromBytesBigEndian (cd.data.toList.take 4) := selector_toNat cd hsz
  by_cases hc : cd.data.toList.take 4 = [0x9e, 0x9f, 0x51, 0xd2]
  · have h1 : UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩ = ⟨2661241298⟩ :=
      u256_inj (by rw [hsv]; exact (be4 _ hlen4).mpr hc)
    rw [if_pos ((extract_eq_iff cd hsz).mpr hc), h1, u256_eq_self]
  · rw [if_neg (fun he => hc ((extract_eq_iff cd hsz).mp he))]
    exact u256_eq_ne (fun he => hc ((be4 _ hlen4).mp (by rw [← hsv, ← he]; rfl)))

/-- The shared dispatcher prefix for `callvalue = 0` (14 instructions: through the taken jump
    `0x0a → 0x0e` and up to the `calldatasize`/`LT`/`PUSH 0x26` at the `0x16` JUMPI).  Either
    out-of-gas, or reaches the `0x16` JUMPI with stack `[0x26, (size < 4)]`. -/
theorem truthX_cvz_prefix
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hwv : I.weiValue = ⟨0⟩) :
    X (g.toNat + 1) (D_J truthBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ s, (X (g.toNat + 1) (D_J truthBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
                = X (g.toNat + 1 - 14) (D_J truthBytecode ⟨0⟩) s)
           ∧ s.executionEnv = I ∧ s.machineState.pc = ⟨22⟩
           ∧ s.machineState.gasAvailable.toNat = g.toNat - 53
           ∧ s.machineState.stack = [⟨38⟩, UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩]
           ∧ s.machineState.activeWords = UInt256.ofNat 3 ∧ 53 ≤ g.toNat := by
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
    have hpc1 : s1.machineState.pc = ⟨2⟩ := by rw [hs1]; simp only [stPush1]; rw [hpc0]; rfl
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
      have hpc2 : s2.machineState.pc = ⟨4⟩ := by rw [hs2]; simp only [stPush1]; rw [hpc1]; rfl
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
        have hpc3 : s3.machineState.pc = ⟨5⟩ := by rw [hs3]; simp only [stMStore]; rw [hpc2]; rfl
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
          have hpc4 : s4.machineState.pc = ⟨6⟩ := by rw [hs4]; simp only [stCallvalue]; rw [hpc3]; rfl
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
            have hpc5 : s5.machineState.pc = ⟨7⟩ := by rw [hs5]; simp only [stDup1]; rw [hpc4]; rfl
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
              have hpc6 : s6.machineState.pc = ⟨8⟩ := by rw [hs6]; simp only [stIsZero]; rw [hpc5]; rfl
              have hgas6 : s6.machineState.gasAvailable.toNat = g.toNat - 26 := by
                rw [hs6]; simp only [stIsZero]; rw [toNat_sub_ofNat (by omega)]; omega
              have hstk6 : s6.machineState.stack = [⟨1⟩, ⟨0⟩] := by
                rw [hs6]; simp only [stIsZero]; rw [isZero_zero]
              have hstep6 := push1_xstep (argv := ⟨14⟩) hcode6 hpc6 (by decide) hstk6 (by norm_num)
              by_cases h6 : g.toNat < 29
              · exact Or.inl (by rw [hX6]; exact stepOOG hgas6 hstep6 (by norm_num) (by omega) (by omega))
              · set s7 := stPush1 s6 ⟨14⟩ with hs7
                have hX7 := hX6.trans (stepContinue (k := 6) (C := 26) hgas6 hstep6 (by norm_num) (by omega))
                have hee7 : s7.executionEnv = I := by rw [hs7]; simp only [stPush1]; exact hee6
                have hcode7 : s7.executionEnv.code = truthBytecode := by rw [hee7]; exact hcode
                have hpc7 : s7.machineState.pc = ⟨10⟩ := by rw [hs7]; simp only [stPush1]; rw [hpc6]; rfl
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
                    have hpc9 : s9.machineState.pc = ⟨15⟩ := by rw [hs9]; simp only [stJumpdest]; rw [hpc8]; rfl
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
                      have hpc10 : s10.machineState.pc = ⟨16⟩ := by rw [hs10]; simp only [stPop]; rw [hpc9]; rfl
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
                        have hpc11 : s11.machineState.pc = ⟨18⟩ := by rw [hs11]; simp only [stPush1]; rw [hpc10]; rfl
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
                          have hpc12 : s12.machineState.pc = ⟨19⟩ := by rw [hs12]; simp only [stCalldatasize]; rw [hpc11]; rfl
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
                            have hpc13 : s13.machineState.pc = ⟨20⟩ := by rw [hs13]; simp only [stBinop]; rw [hpc12]; rfl
                            have hgas13 : s13.machineState.gasAvailable.toNat = g.toNat - 50 := by
                              rw [hs13]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                            have hstk13 : s13.machineState.stack = [UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩] := by
                              rw [hs13]; simp only [stBinop]
                            have hstep13 := push1_xstep (argv := ⟨38⟩) hcode13 hpc13 (by decide) hstk13 (by norm_num)
                            by_cases h13 : g.toNat < 53
                            · exact Or.inl (by rw [hX13]; exact stepOOG hgas13 hstep13 (by norm_num) (by omega) (by omega))
                            · set s14 := stPush1 s13 ⟨38⟩ with hs14
                              have hX14 := hX13.trans (stepContinue (k := 13) (C := 50) hgas13 hstep13 (by norm_num) (by omega))
                              refine Or.inr ⟨s14, hX14, ?_, ?_, ?_, ?_, ?_, by omega⟩
                              · rw [hs14]; simp only [stPush1]; exact hee13
                              · rw [hs14]; simp only [stPush1]; rw [hpc13]; rfl
                              · rw [hs14]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                              · rw [hs14]; simp only [stPush1, hstk13]
                              · rw [hs14]; simp only [stPush1]
                                rw [hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4]
                                simp only [stBinop, stCalldatasize, stPush1, stPop, stJumpdest, stJumpiT,
                                  stIsZero, stDup1, stCallvalue]
                                exact haw4

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
                rw [hs6]; simp only [stIsZero]; rw [isZero_zero]
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

/-- Selector mismatch ⇒ dispatch fails. -/
theorem truthDispatch_none_nomatch {cd : ByteArray}
    (h : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4) = false) :
    dispatchMsg truthContract cd = none := by
  rw [truthDispatch_eq]; simp [h]

/-- **calldatasize ≥ 4, wrong selector**: the dispatcher continues past the `0x16` JUMPI
    (not taken), compares the selector (`EQ = 0` via `truthEvmSelector`), and reverts at
    `0x26`.  Out-of-gas, or reverts. -/
theorem truthX_cvz_revertB
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hmatch : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == I.calldata.extract 0 4) = false) :
    X (g.toNat + 1) (D_J truthBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ g' o, X (g.toNat + 1) (D_J truthBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
                  = .ok (.revert g' o) := by
  rcases truthX_cvz_prefix (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hwv with hoog | ⟨s14, hX14, hee14, hpc14, hgas14, hstk14, haw14, hg53⟩
  · exact Or.inl hoog
  · have hcode14 : s14.executionEnv.code = truthBytecode := by rw [hee14]; exact hcode
    have hlt0 : UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩ = ⟨0⟩ := lt_four_eq_zero_of_ge hsz hsize
    have hstk14' : s14.machineState.stack = ⟨38⟩ :: ⟨0⟩ :: [] := by rw [hstk14, hlt0]
    have hstep14 := jumpi_nt_xstep hcode14 hpc14 (by decide) hstk14' (by norm_num)
    by_cases h14 : g.toNat < 63
    · exact Or.inl (by rw [hX14]; exact stepOOG hgas14 hstep14 (by norm_num) (by omega) (by omega))
    · set s15 := stJumpiNT s14 [] with hs15
      have hX15 := hX14.trans (stepContinue (k := 14) (C := 53) hgas14 hstep14 (by norm_num) (by omega))
      have hee15 : s15.executionEnv = I := by rw [hs15]; simp only [stJumpiNT]; exact hee14
      have hcode15 : s15.executionEnv.code = truthBytecode := by rw [hee15]; exact hcode
      have hpc15 : s15.machineState.pc = ⟨23⟩ := by rw [hs15]; simp only [stJumpiNT]; rw [hpc14]; rfl
      have hgas15 : s15.machineState.gasAvailable.toNat = g.toNat - 63 := by
        rw [hs15]; simp only [stJumpiNT]; rw [toNat_sub_ofNat (by omega)]; omega
      have hstk15 : s15.machineState.stack = [] := by rw [hs15]; simp only [stJumpiNT]
      have haw15 : s15.machineState.activeWords = UInt256.ofNat 3 := by rw [hs15]; simp only [stJumpiNT]; exact haw14
      have hstep15 := push0_xstep hcode15 hpc15 (by decide) hstk15 (by norm_num)
      by_cases h15 : g.toNat < 65
      · exact Or.inl (by rw [hX15]; exact stepOOG hgas15 hstep15 (by norm_num) (by omega) (by omega))
      · set s16 := stPush0 s15 with hs16
        have hX16 := hX15.trans (stepContinue (k := 15) (C := 63) hgas15 hstep15 (by norm_num) (by omega))
        have hee16 : s16.executionEnv = I := by rw [hs16]; simp only [stPush0]; exact hee15
        have hcode16 : s16.executionEnv.code = truthBytecode := by rw [hee16]; exact hcode
        have hpc16 : s16.machineState.pc = ⟨24⟩ := by rw [hs16]; simp only [stPush0]; rw [hpc15]; rfl
        have hgas16 : s16.machineState.gasAvailable.toNat = g.toNat - 65 := by
          rw [hs16]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
        have hstk16 : s16.machineState.stack = [⟨0⟩] := by rw [hs16]; simp only [stPush0, hstk15]
        have haw16 : s16.machineState.activeWords = UInt256.ofNat 3 := by rw [hs16]; simp only [stPush0]; exact haw15
        have hstep16 := calldataload_xstep hcode16 hpc16 (by decide) hstk16 (by norm_num)
        by_cases h16 : g.toNat < 68
        · exact Or.inl (by rw [hX16]; exact stepOOG hgas16 hstep16 (by norm_num) (by omega) (by omega))
        · set s17 := stCalldataload s16 ⟨0⟩ [] with hs17
          have hX17 := hX16.trans (stepContinue (k := 16) (C := 65) hgas16 hstep16 (by norm_num) (by omega))
          have hee17 : s17.executionEnv = I := by rw [hs17]; simp only [stCalldataload]; exact hee16
          have hcode17 : s17.executionEnv.code = truthBytecode := by rw [hee17]; exact hcode
          have hpc17 : s17.machineState.pc = ⟨25⟩ := by rw [hs17]; simp only [stCalldataload]; rw [hpc16]; rfl
          have hgas17 : s17.machineState.gasAvailable.toNat = g.toNat - 68 := by
            rw [hs17]; simp only [stCalldataload]; rw [toNat_sub_ofNat (by omega)]; omega
          have hstk17 : s17.machineState.stack = [uInt256OfByteArray (I.calldata.readBytes 0 32)] := by
            rw [hs17]; simp only [stCalldataload, hee16]; rfl
          have haw17 : s17.machineState.activeWords = UInt256.ofNat 3 := by rw [hs17]; simp only [stCalldataload]; exact haw16
          have hstep17 := push1_xstep (argv := ⟨224⟩) hcode17 hpc17 (by decide) hstk17 (by norm_num)
          by_cases h17 : g.toNat < 71
          · exact Or.inl (by rw [hX17]; exact stepOOG hgas17 hstep17 (by norm_num) (by omega) (by omega))
          · set s18 := stPush1 s17 ⟨224⟩ with hs18
            have hX18 := hX17.trans (stepContinue (k := 17) (C := 68) hgas17 hstep17 (by norm_num) (by omega))
            have hee18 : s18.executionEnv = I := by rw [hs18]; simp only [stPush1]; exact hee17
            have hcode18 : s18.executionEnv.code = truthBytecode := by rw [hee18]; exact hcode
            have hpc18 : s18.machineState.pc = ⟨27⟩ := by rw [hs18]; simp only [stPush1]; rw [hpc17]; rfl
            have hgas18 : s18.machineState.gasAvailable.toNat = g.toNat - 71 := by
              rw [hs18]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
            have hstk18 : s18.machineState.stack = [⟨224⟩, uInt256OfByteArray (I.calldata.readBytes 0 32)] := by
              rw [hs18]; simp only [stPush1, hstk17]
            have hstep18 := shr_xstep hcode18 hpc18 (by decide) hstk18 (by norm_num)
            by_cases h18 : g.toNat < 74
            · exact Or.inl (by rw [hX18]; exact stepOOG hgas18 hstep18 (by norm_num) (by omega) (by omega))
            · set s19 := stBinop s18 (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩) [] with hs19
              have hX19 := hX18.trans (stepContinue (k := 18) (C := 71) hgas18 hstep18 (by norm_num) (by omega))
              have hee19 : s19.executionEnv = I := by rw [hs19]; simp only [stBinop]; exact hee18
              have hcode19 : s19.executionEnv.code = truthBytecode := by rw [hee19]; exact hcode
              have hpc19 : s19.machineState.pc = ⟨28⟩ := by rw [hs19]; simp only [stBinop]; rw [hpc18]; rfl
              have hgas19 : s19.machineState.gasAvailable.toNat = g.toNat - 74 := by
                rw [hs19]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
              have hstk19 : s19.machineState.stack = [UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩] := by
                rw [hs19]; simp only [stBinop]
              have hstep19 := dup1_xstep hcode19 hpc19 (by decide) hstk19 (by norm_num)
              by_cases h19 : g.toNat < 77
              · exact Or.inl (by rw [hX19]; exact stepOOG hgas19 hstep19 (by norm_num) (by omega) (by omega))
              · set sel := UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ with hsel
                set s20 := stDup1 s19 sel [] with hs20
                have hX20 := hX19.trans (stepContinue (k := 19) (C := 74) hgas19 hstep19 (by norm_num) (by omega))
                have hee20 : s20.executionEnv = I := by rw [hs20]; simp only [stDup1]; exact hee19
                have hcode20 : s20.executionEnv.code = truthBytecode := by rw [hee20]; exact hcode
                have hpc20 : s20.machineState.pc = ⟨29⟩ := by rw [hs20]; simp only [stDup1]; rw [hpc19]; rfl
                have hgas20 : s20.machineState.gasAvailable.toNat = g.toNat - 77 := by
                  rw [hs20]; simp only [stDup1]; rw [toNat_sub_ofNat (by omega)]; omega
                have hstk20 : s20.machineState.stack = [sel, sel] := by rw [hs20]; simp only [stDup1]
                have hstep20 := push4_xstep (argv := ⟨2661241298⟩) hcode20 hpc20 (by decide) hstk20 (by norm_num)
                by_cases h20 : g.toNat < 80
                · exact Or.inl (by rw [hX20]; exact stepOOG hgas20 hstep20 (by norm_num) (by omega) (by omega))
                · set s21 := stPush4 s20 ⟨2661241298⟩ with hs21
                  have hX21 := hX20.trans (stepContinue (k := 20) (C := 77) hgas20 hstep20 (by norm_num) (by omega))
                  have hee21 : s21.executionEnv = I := by rw [hs21]; simp only [stPush4]; exact hee20
                  have hcode21 : s21.executionEnv.code = truthBytecode := by rw [hee21]; exact hcode
                  have hpc21 : s21.machineState.pc = ⟨34⟩ := by rw [hs21]; simp only [stPush4]; rw [hpc20]; rfl
                  have hgas21 : s21.machineState.gasAvailable.toNat = g.toNat - 80 := by
                    rw [hs21]; simp only [stPush4]; rw [toNat_sub_ofNat (by omega)]; omega
                  have hstk21 : s21.machineState.stack = [⟨2661241298⟩, sel, sel] := by rw [hs21]; simp only [stPush4, hstk20]
                  have hstep21 := eq_xstep hcode21 hpc21 (by decide) hstk21 (by norm_num)
                  by_cases h21 : g.toNat < 83
                  · exact Or.inl (by rw [hX21]; exact stepOOG hgas21 hstep21 (by norm_num) (by omega) (by omega))
                  · set s22 := stBinop s21 (UInt256.eq ⟨2661241298⟩ sel) [sel] with hs22
                    have hX22 := hX21.trans (stepContinue (k := 21) (C := 80) hgas21 hstep21 (by norm_num) (by omega))
                    have hee22 : s22.executionEnv = I := by rw [hs22]; simp only [stBinop]; exact hee21
                    have hcode22 : s22.executionEnv.code = truthBytecode := by rw [hee22]; exact hcode
                    have hpc22 : s22.machineState.pc = ⟨35⟩ := by rw [hs22]; simp only [stBinop]; rw [hpc21]; rfl
                    have hgas22 : s22.machineState.gasAvailable.toNat = g.toNat - 83 := by
                      rw [hs22]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                    have heq0 : UInt256.eq ⟨2661241298⟩ sel = ⟨0⟩ := by
                      rw [hsel, truthEvmSelector hsz]; simp [hmatch]
                    have hstk22 : s22.machineState.stack = [UInt256.eq ⟨2661241298⟩ sel, sel] := by rw [hs22]; simp only [stBinop]
                    have hstep22 := push1_xstep (argv := ⟨42⟩) hcode22 hpc22 (by decide) hstk22 (by norm_num)
                    by_cases h22 : g.toNat < 86
                    · exact Or.inl (by rw [hX22]; exact stepOOG hgas22 hstep22 (by norm_num) (by omega) (by omega))
                    · set s23 := stPush1 s22 ⟨42⟩ with hs23
                      have hX23 := hX22.trans (stepContinue (k := 22) (C := 83) hgas22 hstep22 (by norm_num) (by omega))
                      have hee23 : s23.executionEnv = I := by rw [hs23]; simp only [stPush1]; exact hee22
                      have hcode23 : s23.executionEnv.code = truthBytecode := by rw [hee23]; exact hcode
                      have hpc23 : s23.machineState.pc = ⟨37⟩ := by rw [hs23]; simp only [stPush1]; rw [hpc22]; rfl
                      have hgas23 : s23.machineState.gasAvailable.toNat = g.toNat - 86 := by
                        rw [hs23]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                      have hstk23 : s23.machineState.stack = ⟨42⟩ :: ⟨0⟩ :: [sel] := by
                        rw [hs23]; simp only [stPush1, hstk22, heq0]
                      have hstep23 := jumpi_nt_xstep hcode23 hpc23 (by decide) hstk23 (by norm_num)
                      by_cases h23 : g.toNat < 96
                      · exact Or.inl (by rw [hX23]; exact stepOOG hgas23 hstep23 (by norm_num) (by omega) (by omega))
                      · set s24 := stJumpiNT s23 [sel] with hs24
                        have hX24 := hX23.trans (stepContinue (k := 23) (C := 86) hgas23 hstep23 (by norm_num) (by omega))
                        have hee24 : s24.executionEnv = I := by rw [hs24]; simp only [stJumpiNT]; exact hee23
                        have hcode24 : s24.executionEnv.code = truthBytecode := by rw [hee24]; exact hcode
                        have hpc24 : s24.machineState.pc = ⟨38⟩ := by rw [hs24]; simp only [stJumpiNT]; rw [hpc23]; rfl
                        have hgas24 : s24.machineState.gasAvailable.toNat = g.toNat - 96 := by
                          rw [hs24]; simp only [stJumpiNT]; rw [toNat_sub_ofNat (by omega)]; omega
                        have hstk24 : s24.machineState.stack = [sel] := by rw [hs24]; simp only [stJumpiNT]
                        have haw24 : s24.machineState.activeWords = UInt256.ofNat 3 := by
                          rw [hs24, hs23, hs22, hs21, hs20, hs19, hs18, hs17, hs16]
                          simp only [stJumpiNT, stPush1, stBinop, stPush4, stDup1, stCalldataload, stPush0]
                          exact haw15
                        have hstep24 := jumpdest_xstep hcode24 hpc24 (by decide) (by rw [hstk24]; norm_num)
                        by_cases h24 : g.toNat < 97
                        · exact Or.inl (by rw [hX24]; exact stepOOG hgas24 hstep24 (by norm_num) (by omega) (by omega))
                        · set s25 := stJumpdest s24 with hs25
                          have hX25 := hX24.trans (stepContinue (k := 24) (C := 96) hgas24 hstep24 (by norm_num) (by omega))
                          have hee25 : s25.executionEnv = I := by rw [hs25]; simp only [stJumpdest]; exact hee24
                          have hcode25 : s25.executionEnv.code = truthBytecode := by rw [hee25]; exact hcode
                          have hpc25 : s25.machineState.pc = ⟨39⟩ := by rw [hs25]; simp only [stJumpdest]; rw [hpc24]; rfl
                          have hgas25 : s25.machineState.gasAvailable.toNat = g.toNat - 97 := by
                            rw [hs25]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                          have hstk25 : s25.machineState.stack = [sel] := by rw [hs25]; simp only [stJumpdest]; exact hstk24
                          have haw25 : s25.machineState.activeWords = UInt256.ofNat 3 := by rw [hs25]; simp only [stJumpdest]; exact haw24
                          have hstep25 := push0_xstep hcode25 hpc25 (by decide) hstk25 (by norm_num)
                          by_cases h25 : g.toNat < 99
                          · exact Or.inl (by rw [hX25]; exact stepOOG hgas25 hstep25 (by norm_num) (by omega) (by omega))
                          · set s26 := stPush0 s25 with hs26
                            have hX26 := hX25.trans (stepContinue (k := 25) (C := 97) hgas25 hstep25 (by norm_num) (by omega))
                            have hee26 : s26.executionEnv = I := by rw [hs26]; simp only [stPush0]; exact hee25
                            have hcode26 : s26.executionEnv.code = truthBytecode := by rw [hee26]; exact hcode
                            have hpc26 : s26.machineState.pc = ⟨40⟩ := by rw [hs26]; simp only [stPush0]; rw [hpc25]; rfl
                            have hgas26 : s26.machineState.gasAvailable.toNat = g.toNat - 99 := by
                              rw [hs26]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                            have hstk26 : s26.machineState.stack = [⟨0⟩, sel] := by rw [hs26]; simp only [stPush0, hstk25]
                            have haw26 : s26.machineState.activeWords = UInt256.ofNat 3 := by rw [hs26]; simp only [stPush0]; exact haw25
                            have hstep26 := push0_xstep hcode26 hpc26 (by decide) hstk26 (by norm_num)
                            by_cases h26 : g.toNat < 101
                            · exact Or.inl (by rw [hX26]; exact stepOOG hgas26 hstep26 (by norm_num) (by omega) (by omega))
                            · set s27 := stPush0 s26 with hs27
                              have hX27 := hX26.trans (stepContinue (k := 26) (C := 99) hgas26 hstep26 (by norm_num) (by omega))
                              have hee27 : s27.executionEnv = I := by rw [hs27]; simp only [stPush0]; exact hee26
                              have hcode27 : s27.executionEnv.code = truthBytecode := by rw [hee27]; exact hcode
                              have hpc27 : s27.machineState.pc = ⟨41⟩ := by rw [hs27]; simp only [stPush0]; rw [hpc26]; rfl
                              have hgas27 : s27.machineState.gasAvailable.toNat = g.toNat - 101 := by
                                rw [hs27]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                              have hstk27 : s27.machineState.stack = [⟨0⟩, ⟨0⟩, sel] := by rw [hs27]; simp only [stPush0, hstk26]
                              have haw27 : s27.machineState.activeWords = UInt256.ofNat 3 := by rw [hs27]; simp only [stPush0]; exact haw26
                              have hmcr : memoryExpansionCost s27 .REVERT = 0 := by
                                simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw27, hstk27,
                                  List.getElem!_cons_zero, List.getElem!_cons_succ, MachineState.M]
                                decide
                              have hstep27 := revert_xstep hcode27 hpc27 (by decide) hstk27 (by norm_num)
                              rw [hmcr] at hstep27
                              exact Or.inr ⟨_, _, by
                                rw [hX27]
                                exact stepHaltRevert (k := 27) (C := 101) (cost := 0) hgas27 hstep27
                                  (by norm_num) (by omega)⟩

/-! ## Concrete memory states of the `truth()` epilogue -/

/-- Memory after solc stores the free pointer `0x80` at `0x40`. -/
noncomputable def truthMem1 : ByteArray :=
  (UInt256.toByteArray ⟨128⟩).write 0 ByteArray.empty 64 32
/-- Memory after solc additionally stores the return word `1` at `0x80`. -/
noncomputable def truthMem2 : ByteArray :=
  (UInt256.toByteArray ⟨1⟩).write 0 truthMem1 128 32

theorem truthMem1_eq :
    truthMem1 = (ByteArray.empty ++ ffi.ByteArray.zeroes (USize.ofNat 64)) ++ UInt256.toByteArray ⟨128⟩ := by
  rw [truthMem1, toByteArray_write_eq _ _ _ (by decide) (by exact lt_usize _ (by norm_num))]; rfl
theorem truthMem1_size : truthMem1.size = 96 := by
  rw [truthMem1_eq, ByteArray.size_append, ByteArray.size_append, zeroes_ofNat_size _ (by norm_num),
      toByteArray_size]; decide
theorem truthMem1_read64 : truthMem1.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := truthMem1_size; omega), truthMem1_eq,
      extract_append_right' _ _ _ _
        (by rw [ByteArray.size_append, zeroes_ofNat_size _ (by norm_num)]; rfl)
        (by rw [ByteArray.size_append, zeroes_ofNat_size _ (by norm_num), toByteArray_size]; rfl)]
theorem truthMem2_eq :
    truthMem2 = (truthMem1 ++ ffi.ByteArray.zeroes (USize.ofNat 32)) ++ UInt256.toByteArray ⟨1⟩ := by
  rw [truthMem2, toByteArray_write_eq _ _ _ (by rw [truthMem1_size]; omega)
        (by rw [truthMem1_size]; exact lt_usize _ (by norm_num))]
  norm_num [truthMem1_size]
theorem truthMem2_size : truthMem2.size = 160 := by
  rw [truthMem2_eq, ByteArray.size_append, ByteArray.size_append, truthMem1_size,
      zeroes_ofNat_size _ (by norm_num), toByteArray_size]
theorem truthMem1pad_size : (truthMem1 ++ ffi.ByteArray.zeroes (USize.ofNat 32)).size = 128 := by
  rw [ByteArray.size_append, truthMem1_size, zeroes_ofNat_size _ (by norm_num)]
theorem truthMem2_read64 : truthMem2.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := truthMem2_size; omega), truthMem2_eq,
      extract_append_left _ _ _ _ (by have := truthMem1pad_size; omega),
      extract_append_left _ _ _ _ (by have := truthMem1_size; omega),
      ← readWithPadding_eq_extract _ _ (by have := truthMem1_size; omega), truthMem1_read64]
theorem truthMem2_read128 : truthMem2.readWithPadding 128 32 = UInt256.toByteArray ⟨1⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := truthMem2_size; omega), truthMem2_eq,
      extract_append_right' _ _ _ _ (by have := truthMem1pad_size; omega)
        (by have := truthMem1pad_size; have := toByteArray_size (⟨1⟩ : UInt256); omega)]

/-- Decoding `truth()`'s (empty) argument list always succeeds with the empty store. -/
theorem truthDecode_empty {I : Ethereum.ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (truthTransition.params.map Param.name)
      (transitionSignature truthTransition).paramTypes I.calldata = some ∅ := by
  have hlen : ¬ (I.calldata.toList.length < 4) := by
    rw [TruthClaude.Theory.byteArray_toList_eq, Array.length_toList]
    have : I.calldata.size = I.calldata.data.size := rfl
    omega
  show decodeCalldata [] [] I.calldata = some ∅
  unfold decodeCalldata
  rw [if_neg hlen]
  rfl

set_option maxHeartbeats 1200000 in
/-- **The `truth()` success trace** (generated, 93 EVM instructions).  With zero call value,
    ≥4-byte calldata and the matching selector, the dispatcher jumps into `truth()`, which stores
    the free pointer and the bool `1` in memory and `RETURN`s the 32-byte word `1`; each step is
    either out-of-gas or advances.  `σ`/`createdAccounts`/substate are preserved (no `SSTORE`). -/
theorem truthX_cvz_success {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hmatch : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    X (g.toNat + 1) (D_J truthBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ s, X (g.toNat + 1) (D_J truthBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
                = .ok (.success s (UInt256.toByteArray ⟨1⟩))
           ∧ s.createdAccounts = cA ∧ s.accountMap = σ ∧ s.substate = A := by
  set s0 := initState cA gh bl σ σ₀ g A I with hs0
  have hee0 : s0.executionEnv = I := by rw [hs0]; simp [initState]
  have hcode0 : s0.executionEnv.code = truthBytecode := by rw [hee0]; exact hcode
  have hpc0 : s0.machineState.pc = ⟨0⟩ := by rw [hs0]; simp [initState]; rfl
  have hgas0 : s0.machineState.gasAvailable.toNat = g.toNat - 0 := by rw [hs0]; simp [initState]
  have hstk0 : s0.machineState.stack = [] := by rw [hs0]; simp [initState]; rfl
  have haw0 : s0.machineState.activeWords = UInt256.ofNat 0 := by rw [hs0]; simp [initState]; rfl
  have hmem0 : s0.machineState.memory = ByteArray.empty := by rw [hs0]; simp [initState]; rfl
  have hX0 : X (g.toNat + 1) (D_J truthBytecode ⟨0⟩) s0 = X (g.toNat + 1 - 0) (D_J truthBytecode ⟨0⟩) s0 := rfl
  -- step 0: push1
  have hstep0 := push1_xstep (argv := ⟨128⟩) hcode0 hpc0 (by decide) hstk0 (by norm_num)
  by_cases h0 : g.toNat < 3
  · exact Or.inl (by rw [hX0]; exact stepOOG hgas0 hstep0 (by norm_num) (by omega) (by omega))
  · set s1 := stPush1 s0 ⟨128⟩ with hs1
    have hX1 := hX0.trans (stepContinue (k := 0) (C := 0) hgas0 hstep0 (by norm_num) (by omega))
    have hee1 : s1.executionEnv = I := by rw [hs1]; simp only [stPush1]; exact hee0
    have hcode1 : s1.executionEnv.code = truthBytecode := by rw [hee1]; exact hcode
    have hpc1 : s1.machineState.pc = ⟨2⟩ := by rw [hs1]; simp only [stPush1]; rw [hpc0]; rfl
    have hgas1 : s1.machineState.gasAvailable.toNat = g.toNat - 3 := by rw [hs1]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
    have hstk1 : s1.machineState.stack = [⟨128⟩] := by rw [hs1]; simp only [stPush1, hstk0]
    have haw1 : s1.machineState.activeWords = (UInt256.ofNat 0) := by rw [hs1]; simp only [stPush1]; exact haw0
    have hmem1 : s1.machineState.memory = ByteArray.empty := by rw [hs1]; simp only [stPush1]; exact hmem0
    -- step 1: push1
    have hstep1 := push1_xstep (argv := ⟨64⟩) hcode1 hpc1 (by decide) hstk1 (by norm_num)
    by_cases h1 : g.toNat < 6
    · exact Or.inl (by rw [hX1]; exact stepOOG hgas1 hstep1 (by norm_num) (by omega) (by omega))
    · set s2 := stPush1 s1 ⟨64⟩ with hs2
      have hX2 := hX1.trans (stepContinue (k := 1) (C := 3) hgas1 hstep1 (by norm_num) (by omega))
      have hee2 : s2.executionEnv = I := by rw [hs2]; simp only [stPush1]; exact hee1
      have hcode2 : s2.executionEnv.code = truthBytecode := by rw [hee2]; exact hcode
      have hpc2 : s2.machineState.pc = ⟨4⟩ := by rw [hs2]; simp only [stPush1]; rw [hpc1]; rfl
      have hgas2 : s2.machineState.gasAvailable.toNat = g.toNat - 6 := by rw [hs2]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
      have hstk2 : s2.machineState.stack = [⟨64⟩, ⟨128⟩] := by rw [hs2]; simp only [stPush1, hstk1]
      have haw2 : s2.machineState.activeWords = (UInt256.ofNat 0) := by rw [hs2]; simp only [stPush1]; exact haw1
      have hmem2 : s2.machineState.memory = ByteArray.empty := by rw [hs2]; simp only [stPush1]; exact hmem1
      -- step 2: mstore
      have hmc2 : memoryExpansionCost s2 .MSTORE = 9 := by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw2, hstk2, Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide
      have hstep2 := mstore_xstep hcode2 hpc2 (by decide) hstk2 (by norm_num)
      rw [hmc2] at hstep2
      by_cases h2 : g.toNat < 18
      · exact Or.inl (by rw [hX2]; exact stepOOG (cost := 9 + 3) hgas2 hstep2 (by norm_num) (by omega) (by omega))
      · set s3 := stMStore s2 ⟨64⟩ ⟨128⟩ [] with hs3
        have hX3 := hX2.trans (stepContinue (k := 2) (C := 6) (cost := 9 + 3) hgas2 hstep2 (by norm_num) (by omega))
        have hee3 : s3.executionEnv = I := by rw [hs3]; simp only [stMStore]; exact hee2
        have hcode3 : s3.executionEnv.code = truthBytecode := by rw [hee3]; exact hcode
        have hpc3 : s3.machineState.pc = ⟨5⟩ := by rw [hs3]; simp only [stMStore]; rw [hpc2]; rfl
        have hgas3 : s3.machineState.gasAvailable.toNat = g.toNat - 18 := by rw [hs3]; simp only [stMStore, hmc2]; rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]; omega
        have hstk3 : s3.machineState.stack = [] := by rw [hs3]; simp [stMStore]
        have haw3 : s3.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs3]; simp only [stMStore, haw2]; decide
        have hmem3 : s3.machineState.memory = truthMem1 := by rw [hs3]; simp only [stMStore]; rw [hmem2, show (⟨64⟩:UInt256).toNat = 64 from by decide]; rfl
        -- step 3: callvalue
        have hstep3 := callvalue_xstep hcode3 hpc3 (by decide) hstk3 (by norm_num)
        by_cases h3 : g.toNat < 20
        · exact Or.inl (by rw [hX3]; exact stepOOG hgas3 hstep3 (by norm_num) (by omega) (by omega))
        · set s4 := stCallvalue s3 with hs4
          have hX4 := hX3.trans (stepContinue (k := 3) (C := 18) hgas3 hstep3 (by norm_num) (by omega))
          have hee4 : s4.executionEnv = I := by rw [hs4]; simp only [stCallvalue]; exact hee3
          have hcode4 : s4.executionEnv.code = truthBytecode := by rw [hee4]; exact hcode
          have hpc4 : s4.machineState.pc = ⟨6⟩ := by rw [hs4]; simp only [stCallvalue]; rw [hpc3]; rfl
          have hgas4 : s4.machineState.gasAvailable.toNat = g.toNat - 20 := by rw [hs4]; simp only [stCallvalue]; rw [toNat_sub_ofNat (by omega)]; omega
          have hstk4 : s4.machineState.stack = [⟨0⟩] := by rw [hs4]; simp only [stCallvalue, hee3, hwv, hstk3]
          have haw4 : s4.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs4]; simp only [stCallvalue]; exact haw3
          have hmem4 : s4.machineState.memory = truthMem1 := by rw [hs4]; simp only [stCallvalue]; exact hmem3
          -- step 4: dup1
          have hstep4 := dup1_xstep hcode4 hpc4 (by decide) hstk4 (by norm_num)
          by_cases h4 : g.toNat < 23
          · exact Or.inl (by rw [hX4]; exact stepOOG hgas4 hstep4 (by norm_num) (by omega) (by omega))
          · set s5 := stDup1 s4 ⟨0⟩ [] with hs5
            have hX5 := hX4.trans (stepContinue (k := 4) (C := 20) hgas4 hstep4 (by norm_num) (by omega))
            have hee5 : s5.executionEnv = I := by rw [hs5]; simp only [stDup1]; exact hee4
            have hcode5 : s5.executionEnv.code = truthBytecode := by rw [hee5]; exact hcode
            have hpc5 : s5.machineState.pc = ⟨7⟩ := by rw [hs5]; simp only [stDup1]; rw [hpc4]; rfl
            have hgas5 : s5.machineState.gasAvailable.toNat = g.toNat - 23 := by rw [hs5]; simp only [stDup1]; rw [toNat_sub_ofNat (by omega)]; omega
            have hstk5 : s5.machineState.stack = [⟨0⟩, ⟨0⟩] := by rw [hs5]; simp only [stDup1]
            have haw5 : s5.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs5]; simp only [stDup1]; exact haw4
            have hmem5 : s5.machineState.memory = truthMem1 := by rw [hs5]; simp only [stDup1]; exact hmem4
            -- step 5: iszero
            have hstep5 := iszero_xstep hcode5 hpc5 (by decide) hstk5 (by norm_num)
            by_cases h5 : g.toNat < 26
            · exact Or.inl (by rw [hX5]; exact stepOOG hgas5 hstep5 (by norm_num) (by omega) (by omega))
            · set s6 := stIsZero s5 ⟨0⟩ [⟨0⟩] with hs6
              have hX6 := hX5.trans (stepContinue (k := 5) (C := 23) hgas5 hstep5 (by norm_num) (by omega))
              have hee6 : s6.executionEnv = I := by rw [hs6]; simp only [stIsZero]; exact hee5
              have hcode6 : s6.executionEnv.code = truthBytecode := by rw [hee6]; exact hcode
              have hpc6 : s6.machineState.pc = ⟨8⟩ := by rw [hs6]; simp only [stIsZero]; rw [hpc5]; rfl
              have hgas6 : s6.machineState.gasAvailable.toNat = g.toNat - 26 := by rw [hs6]; simp only [stIsZero]; rw [toNat_sub_ofNat (by omega)]; omega
              have hstk6 : s6.machineState.stack = [⟨1⟩, ⟨0⟩] := by rw [hs6]; simp only [stIsZero]; rw [show (UInt256.isZero ⟨0⟩) = ⟨1⟩ from by decide]
              have haw6 : s6.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs6]; simp only [stIsZero]; exact haw5
              have hmem6 : s6.machineState.memory = truthMem1 := by rw [hs6]; simp only [stIsZero]; exact hmem5
              -- step 6: push1
              have hstep6 := push1_xstep (argv := ⟨14⟩) hcode6 hpc6 (by decide) hstk6 (by norm_num)
              by_cases h6 : g.toNat < 29
              · exact Or.inl (by rw [hX6]; exact stepOOG hgas6 hstep6 (by norm_num) (by omega) (by omega))
              · set s7 := stPush1 s6 ⟨14⟩ with hs7
                have hX7 := hX6.trans (stepContinue (k := 6) (C := 26) hgas6 hstep6 (by norm_num) (by omega))
                have hee7 : s7.executionEnv = I := by rw [hs7]; simp only [stPush1]; exact hee6
                have hcode7 : s7.executionEnv.code = truthBytecode := by rw [hee7]; exact hcode
                have hpc7 : s7.machineState.pc = ⟨10⟩ := by rw [hs7]; simp only [stPush1]; rw [hpc6]; rfl
                have hgas7 : s7.machineState.gasAvailable.toNat = g.toNat - 29 := by rw [hs7]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                have hstk7 : s7.machineState.stack = [⟨14⟩, ⟨1⟩, ⟨0⟩] := by rw [hs7]; simp only [stPush1, hstk6]
                have haw7 : s7.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs7]; simp only [stPush1]; exact haw6
                have hmem7 : s7.machineState.memory = truthMem1 := by rw [hs7]; simp only [stPush1]; exact hmem6
                -- step 7: jumpi_t
                have hstep7 := jumpi_t_xstep hcode7 hpc7 (by decide) hstk7 (by decide) (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
                by_cases h7 : g.toNat < 39
                · exact Or.inl (by rw [hX7]; exact stepOOG hgas7 hstep7 (by norm_num) (by omega) (by omega))
                · set s8 := stJumpiT s7 ⟨14⟩ [⟨0⟩] with hs8
                  have hX8 := hX7.trans (stepContinue (k := 7) (C := 29) hgas7 hstep7 (by norm_num) (by omega))
                  have hee8 : s8.executionEnv = I := by rw [hs8]; simp only [stJumpiT]; exact hee7
                  have hcode8 : s8.executionEnv.code = truthBytecode := by rw [hee8]; exact hcode
                  have hpc8 : s8.machineState.pc = ⟨14⟩ := by rw [hs8]; simp only [stJumpiT]
                  have hgas8 : s8.machineState.gasAvailable.toNat = g.toNat - 39 := by rw [hs8]; simp only [stJumpiT]; rw [toNat_sub_ofNat (by omega)]; omega
                  have hstk8 : s8.machineState.stack = [⟨0⟩] := by rw [hs8]; simp only [stJumpiT]
                  have haw8 : s8.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs8]; simp only [stJumpiT]; exact haw7
                  have hmem8 : s8.machineState.memory = truthMem1 := by rw [hs8]; simp only [stJumpiT]; exact hmem7
                  -- step 8: jumpdest
                  have hstep8 := jumpdest_xstep hcode8 hpc8 (by decide) (by rw [hstk8]; simp)
                  by_cases h8 : g.toNat < 40
                  · exact Or.inl (by rw [hX8]; exact stepOOG hgas8 hstep8 (by norm_num) (by omega) (by omega))
                  · set s9 := stJumpdest s8 with hs9
                    have hX9 := hX8.trans (stepContinue (k := 8) (C := 39) hgas8 hstep8 (by norm_num) (by omega))
                    have hee9 : s9.executionEnv = I := by rw [hs9]; simp only [stJumpdest]; exact hee8
                    have hcode9 : s9.executionEnv.code = truthBytecode := by rw [hee9]; exact hcode
                    have hpc9 : s9.machineState.pc = ⟨15⟩ := by rw [hs9]; simp only [stJumpdest]; rw [hpc8]; rfl
                    have hgas9 : s9.machineState.gasAvailable.toNat = g.toNat - 40 := by rw [hs9]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                    have hstk9 : s9.machineState.stack = [⟨0⟩] := by rw [hs9]; simp only [stJumpdest]; exact hstk8
                    have haw9 : s9.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs9]; simp only [stJumpdest]; exact haw8
                    have hmem9 : s9.machineState.memory = truthMem1 := by rw [hs9]; simp only [stJumpdest]; exact hmem8
                    -- step 9: pop
                    have hstep9 := pop_xstep hcode9 hpc9 (by decide) hstk9 (by norm_num)
                    by_cases h9 : g.toNat < 42
                    · exact Or.inl (by rw [hX9]; exact stepOOG hgas9 hstep9 (by norm_num) (by omega) (by omega))
                    · set s10 := stPop s9 [] with hs10
                      have hX10 := hX9.trans (stepContinue (k := 9) (C := 40) hgas9 hstep9 (by norm_num) (by omega))
                      have hee10 : s10.executionEnv = I := by rw [hs10]; simp only [stPop]; exact hee9
                      have hcode10 : s10.executionEnv.code = truthBytecode := by rw [hee10]; exact hcode
                      have hpc10 : s10.machineState.pc = ⟨16⟩ := by rw [hs10]; simp only [stPop]; rw [hpc9]; rfl
                      have hgas10 : s10.machineState.gasAvailable.toNat = g.toNat - 42 := by rw [hs10]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                      have hstk10 : s10.machineState.stack = [] := by rw [hs10]; simp only [stPop]
                      have haw10 : s10.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs10]; simp only [stPop]; exact haw9
                      have hmem10 : s10.machineState.memory = truthMem1 := by rw [hs10]; simp only [stPop]; exact hmem9
                      -- step 10: push1
                      have hstep10 := push1_xstep (argv := ⟨4⟩) hcode10 hpc10 (by decide) hstk10 (by norm_num)
                      by_cases h10 : g.toNat < 45
                      · exact Or.inl (by rw [hX10]; exact stepOOG hgas10 hstep10 (by norm_num) (by omega) (by omega))
                      · set s11 := stPush1 s10 ⟨4⟩ with hs11
                        have hX11 := hX10.trans (stepContinue (k := 10) (C := 42) hgas10 hstep10 (by norm_num) (by omega))
                        have hee11 : s11.executionEnv = I := by rw [hs11]; simp only [stPush1]; exact hee10
                        have hcode11 : s11.executionEnv.code = truthBytecode := by rw [hee11]; exact hcode
                        have hpc11 : s11.machineState.pc = ⟨18⟩ := by rw [hs11]; simp only [stPush1]; rw [hpc10]; rfl
                        have hgas11 : s11.machineState.gasAvailable.toNat = g.toNat - 45 := by rw [hs11]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                        have hstk11 : s11.machineState.stack = [⟨4⟩] := by rw [hs11]; simp only [stPush1, hstk10]
                        have haw11 : s11.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs11]; simp only [stPush1]; exact haw10
                        have hmem11 : s11.machineState.memory = truthMem1 := by rw [hs11]; simp only [stPush1]; exact hmem10
                        -- step 11: calldatasize
                        have hstep11 := calldatasize_xstep hcode11 hpc11 (by decide) hstk11 (by norm_num)
                        by_cases h11 : g.toNat < 47
                        · exact Or.inl (by rw [hX11]; exact stepOOG hgas11 hstep11 (by norm_num) (by omega) (by omega))
                        · set s12 := stCalldatasize s11 with hs12
                          have hX12 := hX11.trans (stepContinue (k := 11) (C := 45) hgas11 hstep11 (by norm_num) (by omega))
                          have hee12 : s12.executionEnv = I := by rw [hs12]; simp only [stCalldatasize]; exact hee11
                          have hcode12 : s12.executionEnv.code = truthBytecode := by rw [hee12]; exact hcode
                          have hpc12 : s12.machineState.pc = ⟨19⟩ := by rw [hs12]; simp only [stCalldatasize]; rw [hpc11]; rfl
                          have hgas12 : s12.machineState.gasAvailable.toNat = g.toNat - 47 := by rw [hs12]; simp only [stCalldatasize]; rw [toNat_sub_ofNat (by omega)]; omega
                          have hstk12 : s12.machineState.stack = [(UInt256.ofNat I.calldata.size), ⟨4⟩] := by rw [hs12]; simp only [stCalldatasize, hee11, hstk11]
                          have haw12 : s12.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs12]; simp only [stCalldatasize]; exact haw11
                          have hmem12 : s12.machineState.memory = truthMem1 := by rw [hs12]; simp only [stCalldatasize]; exact hmem11
                          -- step 12: lt_sz
                          have hstep12 := lt_xstep hcode12 hpc12 (by decide) hstk12 (by norm_num)
                          by_cases h12 : g.toNat < 50
                          · exact Or.inl (by rw [hX12]; exact stepOOG hgas12 hstep12 (by norm_num) (by omega) (by omega))
                          · set s13 := stBinop s12 (UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩) [] with hs13
                            have hX13 := hX12.trans (stepContinue (k := 12) (C := 47) hgas12 hstep12 (by norm_num) (by omega))
                            have hee13 : s13.executionEnv = I := by rw [hs13]; simp only [stBinop]; exact hee12
                            have hcode13 : s13.executionEnv.code = truthBytecode := by rw [hee13]; exact hcode
                            have hpc13 : s13.machineState.pc = ⟨20⟩ := by rw [hs13]; simp only [stBinop]; rw [hpc12]; rfl
                            have hgas13 : s13.machineState.gasAvailable.toNat = g.toNat - 50 := by rw [hs13]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                            have hstk13 : s13.machineState.stack = [⟨0⟩] := by rw [hs13]; simp only [stBinop]; rw [show (UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩) = ⟨0⟩ from lt_four_eq_zero_of_ge hsz hsize]
                            have haw13 : s13.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs13]; simp only [stBinop]; exact haw12
                            have hmem13 : s13.machineState.memory = truthMem1 := by rw [hs13]; simp only [stBinop]; exact hmem12
                            -- step 13: push1
                            have hstep13 := push1_xstep (argv := ⟨38⟩) hcode13 hpc13 (by decide) hstk13 (by norm_num)
                            by_cases h13 : g.toNat < 53
                            · exact Or.inl (by rw [hX13]; exact stepOOG hgas13 hstep13 (by norm_num) (by omega) (by omega))
                            · set s14 := stPush1 s13 ⟨38⟩ with hs14
                              have hX14 := hX13.trans (stepContinue (k := 13) (C := 50) hgas13 hstep13 (by norm_num) (by omega))
                              have hee14 : s14.executionEnv = I := by rw [hs14]; simp only [stPush1]; exact hee13
                              have hcode14 : s14.executionEnv.code = truthBytecode := by rw [hee14]; exact hcode
                              have hpc14 : s14.machineState.pc = ⟨22⟩ := by rw [hs14]; simp only [stPush1]; rw [hpc13]; rfl
                              have hgas14 : s14.machineState.gasAvailable.toNat = g.toNat - 53 := by rw [hs14]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                              have hstk14 : s14.machineState.stack = [⟨38⟩, ⟨0⟩] := by rw [hs14]; simp only [stPush1, hstk13]
                              have haw14 : s14.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs14]; simp only [stPush1]; exact haw13
                              have hmem14 : s14.machineState.memory = truthMem1 := by rw [hs14]; simp only [stPush1]; exact hmem13
                              -- step 14: jumpi_nt
                              have hstep14 := jumpi_nt_xstep hcode14 hpc14 (by decide) hstk14 (by norm_num)
                              by_cases h14 : g.toNat < 63
                              · exact Or.inl (by rw [hX14]; exact stepOOG hgas14 hstep14 (by norm_num) (by omega) (by omega))
                              · set s15 := stJumpiNT s14 [] with hs15
                                have hX15 := hX14.trans (stepContinue (k := 14) (C := 53) hgas14 hstep14 (by norm_num) (by omega))
                                have hee15 : s15.executionEnv = I := by rw [hs15]; simp only [stJumpiNT]; exact hee14
                                have hcode15 : s15.executionEnv.code = truthBytecode := by rw [hee15]; exact hcode
                                have hpc15 : s15.machineState.pc = ⟨23⟩ := by rw [hs15]; simp only [stJumpiNT]; rw [hpc14]; rfl
                                have hgas15 : s15.machineState.gasAvailable.toNat = g.toNat - 63 := by rw [hs15]; simp only [stJumpiNT]; rw [toNat_sub_ofNat (by omega)]; omega
                                have hstk15 : s15.machineState.stack = [] := by rw [hs15]; simp only [stJumpiNT]
                                have haw15 : s15.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs15]; simp only [stJumpiNT]; exact haw14
                                have hmem15 : s15.machineState.memory = truthMem1 := by rw [hs15]; simp only [stJumpiNT]; exact hmem14
                                -- step 15: push0
                                have hstep15 := push0_xstep hcode15 hpc15 (by decide) hstk15 (by norm_num)
                                by_cases h15 : g.toNat < 65
                                · exact Or.inl (by rw [hX15]; exact stepOOG hgas15 hstep15 (by norm_num) (by omega) (by omega))
                                · set s16 := stPush0 s15 with hs16
                                  have hX16 := hX15.trans (stepContinue (k := 15) (C := 63) hgas15 hstep15 (by norm_num) (by omega))
                                  have hee16 : s16.executionEnv = I := by rw [hs16]; simp only [stPush0]; exact hee15
                                  have hcode16 : s16.executionEnv.code = truthBytecode := by rw [hee16]; exact hcode
                                  have hpc16 : s16.machineState.pc = ⟨24⟩ := by rw [hs16]; simp only [stPush0]; rw [hpc15]; rfl
                                  have hgas16 : s16.machineState.gasAvailable.toNat = g.toNat - 65 := by rw [hs16]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                                  have hstk16 : s16.machineState.stack = [⟨0⟩] := by rw [hs16]; simp only [stPush0, hstk15]
                                  have haw16 : s16.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs16]; simp only [stPush0]; exact haw15
                                  have hmem16 : s16.machineState.memory = truthMem1 := by rw [hs16]; simp only [stPush0]; exact hmem15
                                  -- step 16: calldataload
                                  have hstep16 := calldataload_xstep hcode16 hpc16 (by decide) hstk16 (by norm_num)
                                  by_cases h16 : g.toNat < 68
                                  · exact Or.inl (by rw [hX16]; exact stepOOG hgas16 hstep16 (by norm_num) (by omega) (by omega))
                                  · set s17 := stCalldataload s16 ⟨0⟩ [] with hs17
                                    have hX17 := hX16.trans (stepContinue (k := 16) (C := 65) hgas16 hstep16 (by norm_num) (by omega))
                                    have hee17 : s17.executionEnv = I := by rw [hs17]; simp only [stCalldataload]; exact hee16
                                    have hcode17 : s17.executionEnv.code = truthBytecode := by rw [hee17]; exact hcode
                                    have hpc17 : s17.machineState.pc = ⟨25⟩ := by rw [hs17]; simp only [stCalldataload]; rw [hpc16]; rfl
                                    have hgas17 : s17.machineState.gasAvailable.toNat = g.toNat - 68 := by rw [hs17]; simp only [stCalldataload]; rw [toNat_sub_ofNat (by omega)]; omega
                                    have hstk17 : s17.machineState.stack = [(uInt256OfByteArray (I.calldata.readBytes 0 32))] := by rw [hs17]; simp only [stCalldataload, hee16]; rfl
                                    have haw17 : s17.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs17]; simp only [stCalldataload]; exact haw16
                                    have hmem17 : s17.machineState.memory = truthMem1 := by rw [hs17]; simp only [stCalldataload]; exact hmem16
                                    -- step 17: push1
                                    have hstep17 := push1_xstep (argv := ⟨224⟩) hcode17 hpc17 (by decide) hstk17 (by norm_num)
                                    by_cases h17 : g.toNat < 71
                                    · exact Or.inl (by rw [hX17]; exact stepOOG hgas17 hstep17 (by norm_num) (by omega) (by omega))
                                    · set s18 := stPush1 s17 ⟨224⟩ with hs18
                                      have hX18 := hX17.trans (stepContinue (k := 17) (C := 68) hgas17 hstep17 (by norm_num) (by omega))
                                      have hee18 : s18.executionEnv = I := by rw [hs18]; simp only [stPush1]; exact hee17
                                      have hcode18 : s18.executionEnv.code = truthBytecode := by rw [hee18]; exact hcode
                                      have hpc18 : s18.machineState.pc = ⟨27⟩ := by rw [hs18]; simp only [stPush1]; rw [hpc17]; rfl
                                      have hgas18 : s18.machineState.gasAvailable.toNat = g.toNat - 71 := by rw [hs18]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                                      have hstk18 : s18.machineState.stack = [⟨224⟩, (uInt256OfByteArray (I.calldata.readBytes 0 32))] := by rw [hs18]; simp only [stPush1, hstk17]
                                      have haw18 : s18.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs18]; simp only [stPush1]; exact haw17
                                      have hmem18 : s18.machineState.memory = truthMem1 := by rw [hs18]; simp only [stPush1]; exact hmem17
                                      -- step 18: shr
                                      have hstep18 := shr_xstep hcode18 hpc18 (by decide) hstk18 (by norm_num)
                                      by_cases h18 : g.toNat < 74
                                      · exact Or.inl (by rw [hX18]; exact stepOOG hgas18 hstep18 (by norm_num) (by omega) (by omega))
                                      · set s19 := stBinop s18 (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩) [] with hs19
                                        have hX19 := hX18.trans (stepContinue (k := 18) (C := 71) hgas18 hstep18 (by norm_num) (by omega))
                                        have hee19 : s19.executionEnv = I := by rw [hs19]; simp only [stBinop]; exact hee18
                                        have hcode19 : s19.executionEnv.code = truthBytecode := by rw [hee19]; exact hcode
                                        have hpc19 : s19.machineState.pc = ⟨28⟩ := by rw [hs19]; simp only [stBinop]; rw [hpc18]; rfl
                                        have hgas19 : s19.machineState.gasAvailable.toNat = g.toNat - 74 := by rw [hs19]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                                        have hstk19 : s19.machineState.stack = [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs19]; simp only [stBinop]
                                        have haw19 : s19.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs19]; simp only [stBinop]; exact haw18
                                        have hmem19 : s19.machineState.memory = truthMem1 := by rw [hs19]; simp only [stBinop]; exact hmem18
                                        -- step 19: dup1
                                        have hstep19 := dup1_xstep hcode19 hpc19 (by decide) hstk19 (by norm_num)
                                        by_cases h19 : g.toNat < 77
                                        · exact Or.inl (by rw [hX19]; exact stepOOG hgas19 hstep19 (by norm_num) (by omega) (by omega))
                                        · set s20 := stDup1 s19 (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩) [] with hs20
                                          have hX20 := hX19.trans (stepContinue (k := 19) (C := 74) hgas19 hstep19 (by norm_num) (by omega))
                                          have hee20 : s20.executionEnv = I := by rw [hs20]; simp only [stDup1]; exact hee19
                                          have hcode20 : s20.executionEnv.code = truthBytecode := by rw [hee20]; exact hcode
                                          have hpc20 : s20.machineState.pc = ⟨29⟩ := by rw [hs20]; simp only [stDup1]; rw [hpc19]; rfl
                                          have hgas20 : s20.machineState.gasAvailable.toNat = g.toNat - 77 := by rw [hs20]; simp only [stDup1]; rw [toNat_sub_ofNat (by omega)]; omega
                                          have hstk20 : s20.machineState.stack = [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩), (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs20]; simp only [stDup1]
                                          have haw20 : s20.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs20]; simp only [stDup1]; exact haw19
                                          have hmem20 : s20.machineState.memory = truthMem1 := by rw [hs20]; simp only [stDup1]; exact hmem19
                                          -- step 20: push4
                                          have hstep20 := push4_xstep (argv := ⟨2661241298⟩) hcode20 hpc20 (by decide) hstk20 (by norm_num)
                                          by_cases h20 : g.toNat < 80
                                          · exact Or.inl (by rw [hX20]; exact stepOOG hgas20 hstep20 (by norm_num) (by omega) (by omega))
                                          · set s21 := stPush4 s20 ⟨2661241298⟩ with hs21
                                            have hX21 := hX20.trans (stepContinue (k := 20) (C := 77) hgas20 hstep20 (by norm_num) (by omega))
                                            have hee21 : s21.executionEnv = I := by rw [hs21]; simp only [stPush4]; exact hee20
                                            have hcode21 : s21.executionEnv.code = truthBytecode := by rw [hee21]; exact hcode
                                            have hpc21 : s21.machineState.pc = ⟨34⟩ := by rw [hs21]; simp only [stPush4]; rw [hpc20]; rfl
                                            have hgas21 : s21.machineState.gasAvailable.toNat = g.toNat - 80 := by rw [hs21]; simp only [stPush4]; rw [toNat_sub_ofNat (by omega)]; omega
                                            have hstk21 : s21.machineState.stack = [⟨2661241298⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩), (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs21]; simp only [stPush4, hstk20]
                                            have haw21 : s21.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs21]; simp only [stPush4]; exact haw20
                                            have hmem21 : s21.machineState.memory = truthMem1 := by rw [hs21]; simp only [stPush4]; exact hmem20
                                            -- step 21: eq_sel
                                            have hstep21 := eq_xstep hcode21 hpc21 (by decide) hstk21 (by norm_num)
                                            by_cases h21 : g.toNat < 83
                                            · exact Or.inl (by rw [hX21]; exact stepOOG hgas21 hstep21 (by norm_num) (by omega) (by omega))
                                            · set s22 := stBinop s21 (UInt256.eq ⟨2661241298⟩ (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)) [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs22
                                              have hX22 := hX21.trans (stepContinue (k := 21) (C := 80) hgas21 hstep21 (by norm_num) (by omega))
                                              have hee22 : s22.executionEnv = I := by rw [hs22]; simp only [stBinop]; exact hee21
                                              have hcode22 : s22.executionEnv.code = truthBytecode := by rw [hee22]; exact hcode
                                              have hpc22 : s22.machineState.pc = ⟨35⟩ := by rw [hs22]; simp only [stBinop]; rw [hpc21]; rfl
                                              have hgas22 : s22.machineState.gasAvailable.toNat = g.toNat - 83 := by rw [hs22]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                                              have hstk22 : s22.machineState.stack = [⟨1⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs22]; simp only [stBinop]; rw [show (UInt256.eq ⟨2661241298⟩ (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)) = ⟨1⟩ from by rw [truthEvmSelector hsz]; simp [hmatch]]
                                              have haw22 : s22.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs22]; simp only [stBinop]; exact haw21
                                              have hmem22 : s22.machineState.memory = truthMem1 := by rw [hs22]; simp only [stBinop]; exact hmem21
                                              -- step 22: push1
                                              have hstep22 := push1_xstep (argv := ⟨42⟩) hcode22 hpc22 (by decide) hstk22 (by norm_num)
                                              by_cases h22 : g.toNat < 86
                                              · exact Or.inl (by rw [hX22]; exact stepOOG hgas22 hstep22 (by norm_num) (by omega) (by omega))
                                              · set s23 := stPush1 s22 ⟨42⟩ with hs23
                                                have hX23 := hX22.trans (stepContinue (k := 22) (C := 83) hgas22 hstep22 (by norm_num) (by omega))
                                                have hee23 : s23.executionEnv = I := by rw [hs23]; simp only [stPush1]; exact hee22
                                                have hcode23 : s23.executionEnv.code = truthBytecode := by rw [hee23]; exact hcode
                                                have hpc23 : s23.machineState.pc = ⟨37⟩ := by rw [hs23]; simp only [stPush1]; rw [hpc22]; rfl
                                                have hgas23 : s23.machineState.gasAvailable.toNat = g.toNat - 86 := by rw [hs23]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                have hstk23 : s23.machineState.stack = [⟨42⟩, ⟨1⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs23]; simp only [stPush1, hstk22]
                                                have haw23 : s23.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs23]; simp only [stPush1]; exact haw22
                                                have hmem23 : s23.machineState.memory = truthMem1 := by rw [hs23]; simp only [stPush1]; exact hmem22
                                                -- step 23: jumpi_t
                                                have hstep23 := jumpi_t_xstep hcode23 hpc23 (by decide) hstk23 (by decide) (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
                                                by_cases h23 : g.toNat < 96
                                                · exact Or.inl (by rw [hX23]; exact stepOOG hgas23 hstep23 (by norm_num) (by omega) (by omega))
                                                · set s24 := stJumpiT s23 ⟨42⟩ [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs24
                                                  have hX24 := hX23.trans (stepContinue (k := 23) (C := 86) hgas23 hstep23 (by norm_num) (by omega))
                                                  have hee24 : s24.executionEnv = I := by rw [hs24]; simp only [stJumpiT]; exact hee23
                                                  have hcode24 : s24.executionEnv.code = truthBytecode := by rw [hee24]; exact hcode
                                                  have hpc24 : s24.machineState.pc = ⟨42⟩ := by rw [hs24]; simp only [stJumpiT]
                                                  have hgas24 : s24.machineState.gasAvailable.toNat = g.toNat - 96 := by rw [hs24]; simp only [stJumpiT]; rw [toNat_sub_ofNat (by omega)]; omega
                                                  have hstk24 : s24.machineState.stack = [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs24]; simp only [stJumpiT]
                                                  have haw24 : s24.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs24]; simp only [stJumpiT]; exact haw23
                                                  have hmem24 : s24.machineState.memory = truthMem1 := by rw [hs24]; simp only [stJumpiT]; exact hmem23
                                                  -- step 24: jumpdest
                                                  have hstep24 := jumpdest_xstep hcode24 hpc24 (by decide) (by rw [hstk24]; simp)
                                                  by_cases h24 : g.toNat < 97
                                                  · exact Or.inl (by rw [hX24]; exact stepOOG hgas24 hstep24 (by norm_num) (by omega) (by omega))
                                                  · set s25 := stJumpdest s24 with hs25
                                                    have hX25 := hX24.trans (stepContinue (k := 24) (C := 96) hgas24 hstep24 (by norm_num) (by omega))
                                                    have hee25 : s25.executionEnv = I := by rw [hs25]; simp only [stJumpdest]; exact hee24
                                                    have hcode25 : s25.executionEnv.code = truthBytecode := by rw [hee25]; exact hcode
                                                    have hpc25 : s25.machineState.pc = ⟨43⟩ := by rw [hs25]; simp only [stJumpdest]; rw [hpc24]; rfl
                                                    have hgas25 : s25.machineState.gasAvailable.toNat = g.toNat - 97 := by rw [hs25]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                                                    have hstk25 : s25.machineState.stack = [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs25]; simp only [stJumpdest]; exact hstk24
                                                    have haw25 : s25.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs25]; simp only [stJumpdest]; exact haw24
                                                    have hmem25 : s25.machineState.memory = truthMem1 := by rw [hs25]; simp only [stJumpdest]; exact hmem24
                                                    -- step 25: push1
                                                    have hstep25 := push1_xstep (argv := ⟨48⟩) hcode25 hpc25 (by decide) hstk25 (by norm_num)
                                                    by_cases h25 : g.toNat < 100
                                                    · exact Or.inl (by rw [hX25]; exact stepOOG hgas25 hstep25 (by norm_num) (by omega) (by omega))
                                                    · set s26 := stPush1 s25 ⟨48⟩ with hs26
                                                      have hX26 := hX25.trans (stepContinue (k := 25) (C := 97) hgas25 hstep25 (by norm_num) (by omega))
                                                      have hee26 : s26.executionEnv = I := by rw [hs26]; simp only [stPush1]; exact hee25
                                                      have hcode26 : s26.executionEnv.code = truthBytecode := by rw [hee26]; exact hcode
                                                      have hpc26 : s26.machineState.pc = ⟨45⟩ := by rw [hs26]; simp only [stPush1]; rw [hpc25]; rfl
                                                      have hgas26 : s26.machineState.gasAvailable.toNat = g.toNat - 100 := by rw [hs26]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                      have hstk26 : s26.machineState.stack = [⟨48⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs26]; simp only [stPush1, hstk25]
                                                      have haw26 : s26.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs26]; simp only [stPush1]; exact haw25
                                                      have hmem26 : s26.machineState.memory = truthMem1 := by rw [hs26]; simp only [stPush1]; exact hmem25
                                                      -- step 26: push1
                                                      have hstep26 := push1_xstep (argv := ⟨68⟩) hcode26 hpc26 (by decide) hstk26 (by norm_num)
                                                      by_cases h26 : g.toNat < 103
                                                      · exact Or.inl (by rw [hX26]; exact stepOOG hgas26 hstep26 (by norm_num) (by omega) (by omega))
                                                      · set s27 := stPush1 s26 ⟨68⟩ with hs27
                                                        have hX27 := hX26.trans (stepContinue (k := 26) (C := 100) hgas26 hstep26 (by norm_num) (by omega))
                                                        have hee27 : s27.executionEnv = I := by rw [hs27]; simp only [stPush1]; exact hee26
                                                        have hcode27 : s27.executionEnv.code = truthBytecode := by rw [hee27]; exact hcode
                                                        have hpc27 : s27.machineState.pc = ⟨47⟩ := by rw [hs27]; simp only [stPush1]; rw [hpc26]; rfl
                                                        have hgas27 : s27.machineState.gasAvailable.toNat = g.toNat - 103 := by rw [hs27]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                        have hstk27 : s27.machineState.stack = [⟨68⟩, ⟨48⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs27]; simp only [stPush1, hstk26]
                                                        have haw27 : s27.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs27]; simp only [stPush1]; exact haw26
                                                        have hmem27 : s27.machineState.memory = truthMem1 := by rw [hs27]; simp only [stPush1]; exact hmem26
                                                        -- step 27: jump
                                                        have hstep27 := jump_xstep hcode27 hpc27 (by decide) hstk27 (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
                                                        by_cases h27 : g.toNat < 111
                                                        · exact Or.inl (by rw [hX27]; exact stepOOG hgas27 hstep27 (by norm_num) (by omega) (by omega))
                                                        · set s28 := stJump s27 ⟨68⟩ [⟨48⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs28
                                                          have hX28 := hX27.trans (stepContinue (k := 27) (C := 103) hgas27 hstep27 (by norm_num) (by omega))
                                                          have hee28 : s28.executionEnv = I := by rw [hs28]; simp only [stJump]; exact hee27
                                                          have hcode28 : s28.executionEnv.code = truthBytecode := by rw [hee28]; exact hcode
                                                          have hpc28 : s28.machineState.pc = ⟨68⟩ := by rw [hs28]; simp only [stJump]
                                                          have hgas28 : s28.machineState.gasAvailable.toNat = g.toNat - 111 := by rw [hs28]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                                          have hstk28 : s28.machineState.stack = [⟨48⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs28]; simp only [stJump]
                                                          have haw28 : s28.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs28]; simp only [stJump]; exact haw27
                                                          have hmem28 : s28.machineState.memory = truthMem1 := by rw [hs28]; simp only [stJump]; exact hmem27
                                                          -- step 28: jumpdest
                                                          have hstep28 := jumpdest_xstep hcode28 hpc28 (by decide) (by rw [hstk28]; simp)
                                                          by_cases h28 : g.toNat < 112
                                                          · exact Or.inl (by rw [hX28]; exact stepOOG hgas28 hstep28 (by norm_num) (by omega) (by omega))
                                                          · set s29 := stJumpdest s28 with hs29
                                                            have hX29 := hX28.trans (stepContinue (k := 28) (C := 111) hgas28 hstep28 (by norm_num) (by omega))
                                                            have hee29 : s29.executionEnv = I := by rw [hs29]; simp only [stJumpdest]; exact hee28
                                                            have hcode29 : s29.executionEnv.code = truthBytecode := by rw [hee29]; exact hcode
                                                            have hpc29 : s29.machineState.pc = ⟨69⟩ := by rw [hs29]; simp only [stJumpdest]; rw [hpc28]; rfl
                                                            have hgas29 : s29.machineState.gasAvailable.toNat = g.toNat - 112 := by rw [hs29]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                                                            have hstk29 : s29.machineState.stack = [⟨48⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs29]; simp only [stJumpdest]; exact hstk28
                                                            have haw29 : s29.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs29]; simp only [stJumpdest]; exact haw28
                                                            have hmem29 : s29.machineState.memory = truthMem1 := by rw [hs29]; simp only [stJumpdest]; exact hmem28
                                                            -- step 29: push0
                                                            have hstep29 := push0_xstep hcode29 hpc29 (by decide) hstk29 (by norm_num)
                                                            by_cases h29 : g.toNat < 114
                                                            · exact Or.inl (by rw [hX29]; exact stepOOG hgas29 hstep29 (by norm_num) (by omega) (by omega))
                                                            · set s30 := stPush0 s29 with hs30
                                                              have hX30 := hX29.trans (stepContinue (k := 29) (C := 112) hgas29 hstep29 (by norm_num) (by omega))
                                                              have hee30 : s30.executionEnv = I := by rw [hs30]; simp only [stPush0]; exact hee29
                                                              have hcode30 : s30.executionEnv.code = truthBytecode := by rw [hee30]; exact hcode
                                                              have hpc30 : s30.machineState.pc = ⟨70⟩ := by rw [hs30]; simp only [stPush0]; rw [hpc29]; rfl
                                                              have hgas30 : s30.machineState.gasAvailable.toNat = g.toNat - 114 := by rw [hs30]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                                                              have hstk30 : s30.machineState.stack = [⟨0⟩, ⟨48⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs30]; simp only [stPush0, hstk29]
                                                              have haw30 : s30.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs30]; simp only [stPush0]; exact haw29
                                                              have hmem30 : s30.machineState.memory = truthMem1 := by rw [hs30]; simp only [stPush0]; exact hmem29
                                                              -- step 30: push1
                                                              have hstep30 := push1_xstep (argv := ⟨1⟩) hcode30 hpc30 (by decide) hstk30 (by norm_num)
                                                              by_cases h30 : g.toNat < 117
                                                              · exact Or.inl (by rw [hX30]; exact stepOOG hgas30 hstep30 (by norm_num) (by omega) (by omega))
                                                              · set s31 := stPush1 s30 ⟨1⟩ with hs31
                                                                have hX31 := hX30.trans (stepContinue (k := 30) (C := 114) hgas30 hstep30 (by norm_num) (by omega))
                                                                have hee31 : s31.executionEnv = I := by rw [hs31]; simp only [stPush1]; exact hee30
                                                                have hcode31 : s31.executionEnv.code = truthBytecode := by rw [hee31]; exact hcode
                                                                have hpc31 : s31.machineState.pc = ⟨72⟩ := by rw [hs31]; simp only [stPush1]; rw [hpc30]; rfl
                                                                have hgas31 : s31.machineState.gasAvailable.toNat = g.toNat - 117 := by rw [hs31]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                have hstk31 : s31.machineState.stack = [⟨1⟩, ⟨0⟩, ⟨48⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs31]; simp only [stPush1, hstk30]
                                                                have haw31 : s31.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs31]; simp only [stPush1]; exact haw30
                                                                have hmem31 : s31.machineState.memory = truthMem1 := by rw [hs31]; simp only [stPush1]; exact hmem30
                                                                -- step 31: swap1
                                                                have hstep31 := swap1_xstep hcode31 hpc31 (by decide) hstk31 (by norm_num)
                                                                by_cases h31 : g.toNat < 120
                                                                · exact Or.inl (by rw [hX31]; exact stepOOG hgas31 hstep31 (by norm_num) (by omega) (by omega))
                                                                · set s32 := stSwap s31 [⟨0⟩, ⟨1⟩, ⟨48⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs32
                                                                  have hX32 := hX31.trans (stepContinue (k := 31) (C := 117) hgas31 hstep31 (by norm_num) (by omega))
                                                                  have hee32 : s32.executionEnv = I := by rw [hs32]; simp only [stSwap]; exact hee31
                                                                  have hcode32 : s32.executionEnv.code = truthBytecode := by rw [hee32]; exact hcode
                                                                  have hpc32 : s32.machineState.pc = ⟨73⟩ := by rw [hs32]; simp only [stSwap]; rw [hpc31]; rfl
                                                                  have hgas32 : s32.machineState.gasAvailable.toNat = g.toNat - 120 := by rw [hs32]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                  have hstk32 : s32.machineState.stack = [⟨0⟩, ⟨1⟩, ⟨48⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs32]; simp only [stSwap]
                                                                  have haw32 : s32.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs32]; simp only [stSwap]; exact haw31
                                                                  have hmem32 : s32.machineState.memory = truthMem1 := by rw [hs32]; simp only [stSwap]; exact hmem31
                                                                  -- step 32: pop
                                                                  have hstep32 := pop_xstep hcode32 hpc32 (by decide) hstk32 (by norm_num)
                                                                  by_cases h32 : g.toNat < 122
                                                                  · exact Or.inl (by rw [hX32]; exact stepOOG hgas32 hstep32 (by norm_num) (by omega) (by omega))
                                                                  · set s33 := stPop s32 [⟨1⟩, ⟨48⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs33
                                                                    have hX33 := hX32.trans (stepContinue (k := 32) (C := 120) hgas32 hstep32 (by norm_num) (by omega))
                                                                    have hee33 : s33.executionEnv = I := by rw [hs33]; simp only [stPop]; exact hee32
                                                                    have hcode33 : s33.executionEnv.code = truthBytecode := by rw [hee33]; exact hcode
                                                                    have hpc33 : s33.machineState.pc = ⟨74⟩ := by rw [hs33]; simp only [stPop]; rw [hpc32]; rfl
                                                                    have hgas33 : s33.machineState.gasAvailable.toNat = g.toNat - 122 := by rw [hs33]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                    have hstk33 : s33.machineState.stack = [⟨1⟩, ⟨48⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs33]; simp only [stPop]
                                                                    have haw33 : s33.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs33]; simp only [stPop]; exact haw32
                                                                    have hmem33 : s33.machineState.memory = truthMem1 := by rw [hs33]; simp only [stPop]; exact hmem32
                                                                    -- step 33: swap1
                                                                    have hstep33 := swap1_xstep hcode33 hpc33 (by decide) hstk33 (by norm_num)
                                                                    by_cases h33 : g.toNat < 125
                                                                    · exact Or.inl (by rw [hX33]; exact stepOOG hgas33 hstep33 (by norm_num) (by omega) (by omega))
                                                                    · set s34 := stSwap s33 [⟨48⟩, ⟨1⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs34
                                                                      have hX34 := hX33.trans (stepContinue (k := 33) (C := 122) hgas33 hstep33 (by norm_num) (by omega))
                                                                      have hee34 : s34.executionEnv = I := by rw [hs34]; simp only [stSwap]; exact hee33
                                                                      have hcode34 : s34.executionEnv.code = truthBytecode := by rw [hee34]; exact hcode
                                                                      have hpc34 : s34.machineState.pc = ⟨75⟩ := by rw [hs34]; simp only [stSwap]; rw [hpc33]; rfl
                                                                      have hgas34 : s34.machineState.gasAvailable.toNat = g.toNat - 125 := by rw [hs34]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                      have hstk34 : s34.machineState.stack = [⟨48⟩, ⟨1⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs34]; simp only [stSwap]
                                                                      have haw34 : s34.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs34]; simp only [stSwap]; exact haw33
                                                                      have hmem34 : s34.machineState.memory = truthMem1 := by rw [hs34]; simp only [stSwap]; exact hmem33
                                                                      -- step 34: jump
                                                                      have hstep34 := jump_xstep hcode34 hpc34 (by decide) hstk34 (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
                                                                      by_cases h34 : g.toNat < 133
                                                                      · exact Or.inl (by rw [hX34]; exact stepOOG hgas34 hstep34 (by norm_num) (by omega) (by omega))
                                                                      · set s35 := stJump s34 ⟨48⟩ [⟨1⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs35
                                                                        have hX35 := hX34.trans (stepContinue (k := 34) (C := 125) hgas34 hstep34 (by norm_num) (by omega))
                                                                        have hee35 : s35.executionEnv = I := by rw [hs35]; simp only [stJump]; exact hee34
                                                                        have hcode35 : s35.executionEnv.code = truthBytecode := by rw [hee35]; exact hcode
                                                                        have hpc35 : s35.machineState.pc = ⟨48⟩ := by rw [hs35]; simp only [stJump]
                                                                        have hgas35 : s35.machineState.gasAvailable.toNat = g.toNat - 133 := by rw [hs35]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                        have hstk35 : s35.machineState.stack = [⟨1⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs35]; simp only [stJump]
                                                                        have haw35 : s35.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs35]; simp only [stJump]; exact haw34
                                                                        have hmem35 : s35.machineState.memory = truthMem1 := by rw [hs35]; simp only [stJump]; exact hmem34
                                                                        -- step 35: jumpdest
                                                                        have hstep35 := jumpdest_xstep hcode35 hpc35 (by decide) (by rw [hstk35]; simp)
                                                                        by_cases h35 : g.toNat < 134
                                                                        · exact Or.inl (by rw [hX35]; exact stepOOG hgas35 hstep35 (by norm_num) (by omega) (by omega))
                                                                        · set s36 := stJumpdest s35 with hs36
                                                                          have hX36 := hX35.trans (stepContinue (k := 35) (C := 133) hgas35 hstep35 (by norm_num) (by omega))
                                                                          have hee36 : s36.executionEnv = I := by rw [hs36]; simp only [stJumpdest]; exact hee35
                                                                          have hcode36 : s36.executionEnv.code = truthBytecode := by rw [hee36]; exact hcode
                                                                          have hpc36 : s36.machineState.pc = ⟨49⟩ := by rw [hs36]; simp only [stJumpdest]; rw [hpc35]; rfl
                                                                          have hgas36 : s36.machineState.gasAvailable.toNat = g.toNat - 134 := by rw [hs36]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                          have hstk36 : s36.machineState.stack = [⟨1⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs36]; simp only [stJumpdest]; exact hstk35
                                                                          have haw36 : s36.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs36]; simp only [stJumpdest]; exact haw35
                                                                          have hmem36 : s36.machineState.memory = truthMem1 := by rw [hs36]; simp only [stJumpdest]; exact hmem35
                                                                          -- step 36: push1
                                                                          have hstep36 := push1_xstep (argv := ⟨64⟩) hcode36 hpc36 (by decide) hstk36 (by norm_num)
                                                                          by_cases h36 : g.toNat < 137
                                                                          · exact Or.inl (by rw [hX36]; exact stepOOG hgas36 hstep36 (by norm_num) (by omega) (by omega))
                                                                          · set s37 := stPush1 s36 ⟨64⟩ with hs37
                                                                            have hX37 := hX36.trans (stepContinue (k := 36) (C := 134) hgas36 hstep36 (by norm_num) (by omega))
                                                                            have hee37 : s37.executionEnv = I := by rw [hs37]; simp only [stPush1]; exact hee36
                                                                            have hcode37 : s37.executionEnv.code = truthBytecode := by rw [hee37]; exact hcode
                                                                            have hpc37 : s37.machineState.pc = ⟨51⟩ := by rw [hs37]; simp only [stPush1]; rw [hpc36]; rfl
                                                                            have hgas37 : s37.machineState.gasAvailable.toNat = g.toNat - 137 := by rw [hs37]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                            have hstk37 : s37.machineState.stack = [⟨64⟩, ⟨1⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs37]; simp only [stPush1, hstk36]
                                                                            have haw37 : s37.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs37]; simp only [stPush1]; exact haw36
                                                                            have hmem37 : s37.machineState.memory = truthMem1 := by rw [hs37]; simp only [stPush1]; exact hmem36
                                                                            -- step 37: mload
                                                                            have hmc37 : memoryExpansionCost s37 .MLOAD = 0 := by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw37, hstk37, Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide
                                                                            have hstep37 := mload_xstep hcode37 hpc37 (by decide) hstk37 (by norm_num)
                                                                            rw [hmc37] at hstep37
                                                                            by_cases h37 : g.toNat < 140
                                                                            · exact Or.inl (by rw [hX37]; exact stepOOG (cost := 0 + 3) hgas37 hstep37 (by norm_num) (by omega) (by omega))
                                                                            · set s38 := stMLoad s37 ⟨64⟩ [⟨1⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs38
                                                                              have hX38 := hX37.trans (stepContinue (k := 37) (C := 137) (cost := 0 + 3) hgas37 hstep37 (by norm_num) (by omega))
                                                                              have hee38 : s38.executionEnv = I := by rw [hs38]; simp only [stMLoad]; exact hee37
                                                                              have hcode38 : s38.executionEnv.code = truthBytecode := by rw [hee38]; exact hcode
                                                                              have hpc38 : s38.machineState.pc = ⟨52⟩ := by rw [hs38]; simp only [stMLoad]; rw [hpc37]; rfl
                                                                              have hgas38 : s38.machineState.gasAvailable.toNat = g.toNat - 140 := by rw [hs38]; simp only [stMLoad, hmc37]; rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]; omega
                                                                              have hstk38 : s38.machineState.stack = [⟨128⟩, ⟨1⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs38]; simp only [stMLoad]; rw [if_neg (by rw [hmem37, truthMem1_size, haw37]; decide)]; rw [hmem37, show (⟨64⟩:UInt256).toNat = 64 from by decide, truthMem1_read64, fromByteArrayBigEndian_toByteArray, show UInt256.ofNat ((⟨128⟩:UInt256).toNat) = ⟨128⟩ from by decide]
                                                                              have haw38 : s38.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs38]; simp only [stMLoad, haw37]; decide
                                                                              have hmem38 : s38.machineState.memory = truthMem1 := by rw [hs38]; simp only [stMLoad]; exact hmem37
                                                                              -- step 38: push1
                                                                              have hstep38 := push1_xstep (argv := ⟨59⟩) hcode38 hpc38 (by decide) hstk38 (by norm_num)
                                                                              by_cases h38 : g.toNat < 143
                                                                              · exact Or.inl (by rw [hX38]; exact stepOOG hgas38 hstep38 (by norm_num) (by omega) (by omega))
                                                                              · set s39 := stPush1 s38 ⟨59⟩ with hs39
                                                                                have hX39 := hX38.trans (stepContinue (k := 38) (C := 140) hgas38 hstep38 (by norm_num) (by omega))
                                                                                have hee39 : s39.executionEnv = I := by rw [hs39]; simp only [stPush1]; exact hee38
                                                                                have hcode39 : s39.executionEnv.code = truthBytecode := by rw [hee39]; exact hcode
                                                                                have hpc39 : s39.machineState.pc = ⟨54⟩ := by rw [hs39]; simp only [stPush1]; rw [hpc38]; rfl
                                                                                have hgas39 : s39.machineState.gasAvailable.toNat = g.toNat - 143 := by rw [hs39]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                have hstk39 : s39.machineState.stack = [⟨59⟩, ⟨128⟩, ⟨1⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs39]; simp only [stPush1, hstk38]
                                                                                have haw39 : s39.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs39]; simp only [stPush1]; exact haw38
                                                                                have hmem39 : s39.machineState.memory = truthMem1 := by rw [hs39]; simp only [stPush1]; exact hmem38
                                                                                -- step 39: swap2
                                                                                have hstep39 := swap2_xstep hcode39 hpc39 (by decide) hstk39 (by norm_num)
                                                                                by_cases h39 : g.toNat < 146
                                                                                · exact Or.inl (by rw [hX39]; exact stepOOG hgas39 hstep39 (by norm_num) (by omega) (by omega))
                                                                                · set s40 := stSwap s39 [⟨1⟩, ⟨128⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs40
                                                                                  have hX40 := hX39.trans (stepContinue (k := 39) (C := 143) hgas39 hstep39 (by norm_num) (by omega))
                                                                                  have hee40 : s40.executionEnv = I := by rw [hs40]; simp only [stSwap]; exact hee39
                                                                                  have hcode40 : s40.executionEnv.code = truthBytecode := by rw [hee40]; exact hcode
                                                                                  have hpc40 : s40.machineState.pc = ⟨55⟩ := by rw [hs40]; simp only [stSwap]; rw [hpc39]; rfl
                                                                                  have hgas40 : s40.machineState.gasAvailable.toNat = g.toNat - 146 := by rw [hs40]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                  have hstk40 : s40.machineState.stack = [⟨1⟩, ⟨128⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs40]; simp only [stSwap]
                                                                                  have haw40 : s40.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs40]; simp only [stSwap]; exact haw39
                                                                                  have hmem40 : s40.machineState.memory = truthMem1 := by rw [hs40]; simp only [stSwap]; exact hmem39
                                                                                  -- step 40: swap1
                                                                                  have hstep40 := swap1_xstep hcode40 hpc40 (by decide) hstk40 (by norm_num)
                                                                                  by_cases h40 : g.toNat < 149
                                                                                  · exact Or.inl (by rw [hX40]; exact stepOOG hgas40 hstep40 (by norm_num) (by omega) (by omega))
                                                                                  · set s41 := stSwap s40 [⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs41
                                                                                    have hX41 := hX40.trans (stepContinue (k := 40) (C := 146) hgas40 hstep40 (by norm_num) (by omega))
                                                                                    have hee41 : s41.executionEnv = I := by rw [hs41]; simp only [stSwap]; exact hee40
                                                                                    have hcode41 : s41.executionEnv.code = truthBytecode := by rw [hee41]; exact hcode
                                                                                    have hpc41 : s41.machineState.pc = ⟨56⟩ := by rw [hs41]; simp only [stSwap]; rw [hpc40]; rfl
                                                                                    have hgas41 : s41.machineState.gasAvailable.toNat = g.toNat - 149 := by rw [hs41]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                    have hstk41 : s41.machineState.stack = [⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs41]; simp only [stSwap]
                                                                                    have haw41 : s41.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs41]; simp only [stSwap]; exact haw40
                                                                                    have hmem41 : s41.machineState.memory = truthMem1 := by rw [hs41]; simp only [stSwap]; exact hmem40
                                                                                    -- step 41: push1
                                                                                    have hstep41 := push1_xstep (argv := ⟨100⟩) hcode41 hpc41 (by decide) hstk41 (by norm_num)
                                                                                    by_cases h41 : g.toNat < 152
                                                                                    · exact Or.inl (by rw [hX41]; exact stepOOG hgas41 hstep41 (by norm_num) (by omega) (by omega))
                                                                                    · set s42 := stPush1 s41 ⟨100⟩ with hs42
                                                                                      have hX42 := hX41.trans (stepContinue (k := 41) (C := 149) hgas41 hstep41 (by norm_num) (by omega))
                                                                                      have hee42 : s42.executionEnv = I := by rw [hs42]; simp only [stPush1]; exact hee41
                                                                                      have hcode42 : s42.executionEnv.code = truthBytecode := by rw [hee42]; exact hcode
                                                                                      have hpc42 : s42.machineState.pc = ⟨58⟩ := by rw [hs42]; simp only [stPush1]; rw [hpc41]; rfl
                                                                                      have hgas42 : s42.machineState.gasAvailable.toNat = g.toNat - 152 := by rw [hs42]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                      have hstk42 : s42.machineState.stack = [⟨100⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs42]; simp only [stPush1, hstk41]
                                                                                      have haw42 : s42.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs42]; simp only [stPush1]; exact haw41
                                                                                      have hmem42 : s42.machineState.memory = truthMem1 := by rw [hs42]; simp only [stPush1]; exact hmem41
                                                                                      -- step 42: jump
                                                                                      have hstep42 := jump_xstep hcode42 hpc42 (by decide) hstk42 (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
                                                                                      by_cases h42 : g.toNat < 160
                                                                                      · exact Or.inl (by rw [hX42]; exact stepOOG hgas42 hstep42 (by norm_num) (by omega) (by omega))
                                                                                      · set s43 := stJump s42 ⟨100⟩ [⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs43
                                                                                        have hX43 := hX42.trans (stepContinue (k := 42) (C := 152) hgas42 hstep42 (by norm_num) (by omega))
                                                                                        have hee43 : s43.executionEnv = I := by rw [hs43]; simp only [stJump]; exact hee42
                                                                                        have hcode43 : s43.executionEnv.code = truthBytecode := by rw [hee43]; exact hcode
                                                                                        have hpc43 : s43.machineState.pc = ⟨100⟩ := by rw [hs43]; simp only [stJump]
                                                                                        have hgas43 : s43.machineState.gasAvailable.toNat = g.toNat - 160 := by rw [hs43]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                        have hstk43 : s43.machineState.stack = [⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs43]; simp only [stJump]
                                                                                        have haw43 : s43.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs43]; simp only [stJump]; exact haw42
                                                                                        have hmem43 : s43.machineState.memory = truthMem1 := by rw [hs43]; simp only [stJump]; exact hmem42
                                                                                        -- step 43: jumpdest
                                                                                        have hstep43 := jumpdest_xstep hcode43 hpc43 (by decide) (by rw [hstk43]; simp)
                                                                                        by_cases h43 : g.toNat < 161
                                                                                        · exact Or.inl (by rw [hX43]; exact stepOOG hgas43 hstep43 (by norm_num) (by omega) (by omega))
                                                                                        · set s44 := stJumpdest s43 with hs44
                                                                                          have hX44 := hX43.trans (stepContinue (k := 43) (C := 160) hgas43 hstep43 (by norm_num) (by omega))
                                                                                          have hee44 : s44.executionEnv = I := by rw [hs44]; simp only [stJumpdest]; exact hee43
                                                                                          have hcode44 : s44.executionEnv.code = truthBytecode := by rw [hee44]; exact hcode
                                                                                          have hpc44 : s44.machineState.pc = ⟨101⟩ := by rw [hs44]; simp only [stJumpdest]; rw [hpc43]; rfl
                                                                                          have hgas44 : s44.machineState.gasAvailable.toNat = g.toNat - 161 := by rw [hs44]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                          have hstk44 : s44.machineState.stack = [⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs44]; simp only [stJumpdest]; exact hstk43
                                                                                          have haw44 : s44.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs44]; simp only [stJumpdest]; exact haw43
                                                                                          have hmem44 : s44.machineState.memory = truthMem1 := by rw [hs44]; simp only [stJumpdest]; exact hmem43
                                                                                          -- step 44: push0
                                                                                          have hstep44 := push0_xstep hcode44 hpc44 (by decide) hstk44 (by norm_num)
                                                                                          by_cases h44 : g.toNat < 163
                                                                                          · exact Or.inl (by rw [hX44]; exact stepOOG hgas44 hstep44 (by norm_num) (by omega) (by omega))
                                                                                          · set s45 := stPush0 s44 with hs45
                                                                                            have hX45 := hX44.trans (stepContinue (k := 44) (C := 161) hgas44 hstep44 (by norm_num) (by omega))
                                                                                            have hee45 : s45.executionEnv = I := by rw [hs45]; simp only [stPush0]; exact hee44
                                                                                            have hcode45 : s45.executionEnv.code = truthBytecode := by rw [hee45]; exact hcode
                                                                                            have hpc45 : s45.machineState.pc = ⟨102⟩ := by rw [hs45]; simp only [stPush0]; rw [hpc44]; rfl
                                                                                            have hgas45 : s45.machineState.gasAvailable.toNat = g.toNat - 163 := by rw [hs45]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                            have hstk45 : s45.machineState.stack = [⟨0⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs45]; simp only [stPush0, hstk44]
                                                                                            have haw45 : s45.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs45]; simp only [stPush0]; exact haw44
                                                                                            have hmem45 : s45.machineState.memory = truthMem1 := by rw [hs45]; simp only [stPush0]; exact hmem44
                                                                                            -- step 45: push1
                                                                                            have hstep45 := push1_xstep (argv := ⟨32⟩) hcode45 hpc45 (by decide) hstk45 (by norm_num)
                                                                                            by_cases h45 : g.toNat < 166
                                                                                            · exact Or.inl (by rw [hX45]; exact stepOOG hgas45 hstep45 (by norm_num) (by omega) (by omega))
                                                                                            · set s46 := stPush1 s45 ⟨32⟩ with hs46
                                                                                              have hX46 := hX45.trans (stepContinue (k := 45) (C := 163) hgas45 hstep45 (by norm_num) (by omega))
                                                                                              have hee46 : s46.executionEnv = I := by rw [hs46]; simp only [stPush1]; exact hee45
                                                                                              have hcode46 : s46.executionEnv.code = truthBytecode := by rw [hee46]; exact hcode
                                                                                              have hpc46 : s46.machineState.pc = ⟨104⟩ := by rw [hs46]; simp only [stPush1]; rw [hpc45]; rfl
                                                                                              have hgas46 : s46.machineState.gasAvailable.toNat = g.toNat - 166 := by rw [hs46]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                              have hstk46 : s46.machineState.stack = [⟨32⟩, ⟨0⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs46]; simp only [stPush1, hstk45]
                                                                                              have haw46 : s46.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs46]; simp only [stPush1]; exact haw45
                                                                                              have hmem46 : s46.machineState.memory = truthMem1 := by rw [hs46]; simp only [stPush1]; exact hmem45
                                                                                              -- step 46: dup3
                                                                                              have hstep46 := dup3_xstep hcode46 hpc46 (by decide) hstk46 (by norm_num)
                                                                                              by_cases h46 : g.toNat < 169
                                                                                              · exact Or.inl (by rw [hX46]; exact stepOOG hgas46 hstep46 (by norm_num) (by omega) (by omega))
                                                                                              · set s47 := stSwap s46 [⟨128⟩, ⟨32⟩, ⟨0⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs47
                                                                                                have hX47 := hX46.trans (stepContinue (k := 46) (C := 166) hgas46 hstep46 (by norm_num) (by omega))
                                                                                                have hee47 : s47.executionEnv = I := by rw [hs47]; simp only [stSwap]; exact hee46
                                                                                                have hcode47 : s47.executionEnv.code = truthBytecode := by rw [hee47]; exact hcode
                                                                                                have hpc47 : s47.machineState.pc = ⟨105⟩ := by rw [hs47]; simp only [stSwap]; rw [hpc46]; rfl
                                                                                                have hgas47 : s47.machineState.gasAvailable.toNat = g.toNat - 169 := by rw [hs47]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                have hstk47 : s47.machineState.stack = [⟨128⟩, ⟨32⟩, ⟨0⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs47]; simp only [stSwap]
                                                                                                have haw47 : s47.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs47]; simp only [stSwap]; exact haw46
                                                                                                have hmem47 : s47.machineState.memory = truthMem1 := by rw [hs47]; simp only [stSwap]; exact hmem46
                                                                                                -- step 47: add
                                                                                                have hstep47 := add_xstep hcode47 hpc47 (by decide) hstk47 (by norm_num)
                                                                                                by_cases h47 : g.toNat < 172
                                                                                                · exact Or.inl (by rw [hX47]; exact stepOOG hgas47 hstep47 (by norm_num) (by omega) (by omega))
                                                                                                · set s48 := stBinop s47 (⟨128⟩ + ⟨32⟩) [⟨0⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs48
                                                                                                  have hX48 := hX47.trans (stepContinue (k := 47) (C := 169) hgas47 hstep47 (by norm_num) (by omega))
                                                                                                  have hee48 : s48.executionEnv = I := by rw [hs48]; simp only [stBinop]; exact hee47
                                                                                                  have hcode48 : s48.executionEnv.code = truthBytecode := by rw [hee48]; exact hcode
                                                                                                  have hpc48 : s48.machineState.pc = ⟨106⟩ := by rw [hs48]; simp only [stBinop]; rw [hpc47]; rfl
                                                                                                  have hgas48 : s48.machineState.gasAvailable.toNat = g.toNat - 172 := by rw [hs48]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                  have hstk48 : s48.machineState.stack = [⟨160⟩, ⟨0⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs48]; simp only [stBinop]; rw [show ((⟨128⟩:UInt256) + ⟨32⟩) = ⟨160⟩ from by decide]
                                                                                                  have haw48 : s48.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs48]; simp only [stBinop]; exact haw47
                                                                                                  have hmem48 : s48.machineState.memory = truthMem1 := by rw [hs48]; simp only [stBinop]; exact hmem47
                                                                                                  -- step 48: swap1
                                                                                                  have hstep48 := swap1_xstep hcode48 hpc48 (by decide) hstk48 (by norm_num)
                                                                                                  by_cases h48 : g.toNat < 175
                                                                                                  · exact Or.inl (by rw [hX48]; exact stepOOG hgas48 hstep48 (by norm_num) (by omega) (by omega))
                                                                                                  · set s49 := stSwap s48 [⟨0⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs49
                                                                                                    have hX49 := hX48.trans (stepContinue (k := 48) (C := 172) hgas48 hstep48 (by norm_num) (by omega))
                                                                                                    have hee49 : s49.executionEnv = I := by rw [hs49]; simp only [stSwap]; exact hee48
                                                                                                    have hcode49 : s49.executionEnv.code = truthBytecode := by rw [hee49]; exact hcode
                                                                                                    have hpc49 : s49.machineState.pc = ⟨107⟩ := by rw [hs49]; simp only [stSwap]; rw [hpc48]; rfl
                                                                                                    have hgas49 : s49.machineState.gasAvailable.toNat = g.toNat - 175 := by rw [hs49]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                    have hstk49 : s49.machineState.stack = [⟨0⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs49]; simp only [stSwap]
                                                                                                    have haw49 : s49.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs49]; simp only [stSwap]; exact haw48
                                                                                                    have hmem49 : s49.machineState.memory = truthMem1 := by rw [hs49]; simp only [stSwap]; exact hmem48
                                                                                                    -- step 49: pop
                                                                                                    have hstep49 := pop_xstep hcode49 hpc49 (by decide) hstk49 (by norm_num)
                                                                                                    by_cases h49 : g.toNat < 177
                                                                                                    · exact Or.inl (by rw [hX49]; exact stepOOG hgas49 hstep49 (by norm_num) (by omega) (by omega))
                                                                                                    · set s50 := stPop s49 [⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs50
                                                                                                      have hX50 := hX49.trans (stepContinue (k := 49) (C := 175) hgas49 hstep49 (by norm_num) (by omega))
                                                                                                      have hee50 : s50.executionEnv = I := by rw [hs50]; simp only [stPop]; exact hee49
                                                                                                      have hcode50 : s50.executionEnv.code = truthBytecode := by rw [hee50]; exact hcode
                                                                                                      have hpc50 : s50.machineState.pc = ⟨108⟩ := by rw [hs50]; simp only [stPop]; rw [hpc49]; rfl
                                                                                                      have hgas50 : s50.machineState.gasAvailable.toNat = g.toNat - 177 := by rw [hs50]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                      have hstk50 : s50.machineState.stack = [⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs50]; simp only [stPop]
                                                                                                      have haw50 : s50.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs50]; simp only [stPop]; exact haw49
                                                                                                      have hmem50 : s50.machineState.memory = truthMem1 := by rw [hs50]; simp only [stPop]; exact hmem49
                                                                                                      -- step 50: push1
                                                                                                      have hstep50 := push1_xstep (argv := ⟨117⟩) hcode50 hpc50 (by decide) hstk50 (by norm_num)
                                                                                                      by_cases h50 : g.toNat < 180
                                                                                                      · exact Or.inl (by rw [hX50]; exact stepOOG hgas50 hstep50 (by norm_num) (by omega) (by omega))
                                                                                                      · set s51 := stPush1 s50 ⟨117⟩ with hs51
                                                                                                        have hX51 := hX50.trans (stepContinue (k := 50) (C := 177) hgas50 hstep50 (by norm_num) (by omega))
                                                                                                        have hee51 : s51.executionEnv = I := by rw [hs51]; simp only [stPush1]; exact hee50
                                                                                                        have hcode51 : s51.executionEnv.code = truthBytecode := by rw [hee51]; exact hcode
                                                                                                        have hpc51 : s51.machineState.pc = ⟨110⟩ := by rw [hs51]; simp only [stPush1]; rw [hpc50]; rfl
                                                                                                        have hgas51 : s51.machineState.gasAvailable.toNat = g.toNat - 180 := by rw [hs51]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                        have hstk51 : s51.machineState.stack = [⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs51]; simp only [stPush1, hstk50]
                                                                                                        have haw51 : s51.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs51]; simp only [stPush1]; exact haw50
                                                                                                        have hmem51 : s51.machineState.memory = truthMem1 := by rw [hs51]; simp only [stPush1]; exact hmem50
                                                                                                        -- step 51: push0
                                                                                                        have hstep51 := push0_xstep hcode51 hpc51 (by decide) hstk51 (by norm_num)
                                                                                                        by_cases h51 : g.toNat < 182
                                                                                                        · exact Or.inl (by rw [hX51]; exact stepOOG hgas51 hstep51 (by norm_num) (by omega) (by omega))
                                                                                                        · set s52 := stPush0 s51 with hs52
                                                                                                          have hX52 := hX51.trans (stepContinue (k := 51) (C := 180) hgas51 hstep51 (by norm_num) (by omega))
                                                                                                          have hee52 : s52.executionEnv = I := by rw [hs52]; simp only [stPush0]; exact hee51
                                                                                                          have hcode52 : s52.executionEnv.code = truthBytecode := by rw [hee52]; exact hcode
                                                                                                          have hpc52 : s52.machineState.pc = ⟨111⟩ := by rw [hs52]; simp only [stPush0]; rw [hpc51]; rfl
                                                                                                          have hgas52 : s52.machineState.gasAvailable.toNat = g.toNat - 182 := by rw [hs52]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                          have hstk52 : s52.machineState.stack = [⟨0⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs52]; simp only [stPush0, hstk51]
                                                                                                          have haw52 : s52.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs52]; simp only [stPush0]; exact haw51
                                                                                                          have hmem52 : s52.machineState.memory = truthMem1 := by rw [hs52]; simp only [stPush0]; exact hmem51
                                                                                                          -- step 52: dup4
                                                                                                          have hstep52 := dup4_xstep hcode52 hpc52 (by decide) hstk52 (by norm_num)
                                                                                                          by_cases h52 : g.toNat < 185
                                                                                                          · exact Or.inl (by rw [hX52]; exact stepOOG hgas52 hstep52 (by norm_num) (by omega) (by omega))
                                                                                                          · set s53 := stSwap s52 [⟨128⟩, ⟨0⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs53
                                                                                                            have hX53 := hX52.trans (stepContinue (k := 52) (C := 182) hgas52 hstep52 (by norm_num) (by omega))
                                                                                                            have hee53 : s53.executionEnv = I := by rw [hs53]; simp only [stSwap]; exact hee52
                                                                                                            have hcode53 : s53.executionEnv.code = truthBytecode := by rw [hee53]; exact hcode
                                                                                                            have hpc53 : s53.machineState.pc = ⟨112⟩ := by rw [hs53]; simp only [stSwap]; rw [hpc52]; rfl
                                                                                                            have hgas53 : s53.machineState.gasAvailable.toNat = g.toNat - 185 := by rw [hs53]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                            have hstk53 : s53.machineState.stack = [⟨128⟩, ⟨0⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs53]; simp only [stSwap]
                                                                                                            have haw53 : s53.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs53]; simp only [stSwap]; exact haw52
                                                                                                            have hmem53 : s53.machineState.memory = truthMem1 := by rw [hs53]; simp only [stSwap]; exact hmem52
                                                                                                            -- step 53: add
                                                                                                            have hstep53 := add_xstep hcode53 hpc53 (by decide) hstk53 (by norm_num)
                                                                                                            by_cases h53 : g.toNat < 188
                                                                                                            · exact Or.inl (by rw [hX53]; exact stepOOG hgas53 hstep53 (by norm_num) (by omega) (by omega))
                                                                                                            · set s54 := stBinop s53 (⟨128⟩ + ⟨0⟩) [⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs54
                                                                                                              have hX54 := hX53.trans (stepContinue (k := 53) (C := 185) hgas53 hstep53 (by norm_num) (by omega))
                                                                                                              have hee54 : s54.executionEnv = I := by rw [hs54]; simp only [stBinop]; exact hee53
                                                                                                              have hcode54 : s54.executionEnv.code = truthBytecode := by rw [hee54]; exact hcode
                                                                                                              have hpc54 : s54.machineState.pc = ⟨113⟩ := by rw [hs54]; simp only [stBinop]; rw [hpc53]; rfl
                                                                                                              have hgas54 : s54.machineState.gasAvailable.toNat = g.toNat - 188 := by rw [hs54]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                              have hstk54 : s54.machineState.stack = [⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs54]; simp only [stBinop]; rw [show ((⟨128⟩:UInt256) + ⟨0⟩) = ⟨128⟩ from by decide]
                                                                                                              have haw54 : s54.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs54]; simp only [stBinop]; exact haw53
                                                                                                              have hmem54 : s54.machineState.memory = truthMem1 := by rw [hs54]; simp only [stBinop]; exact hmem53
                                                                                                              -- step 54: dup5
                                                                                                              have hstep54 := dup5_xstep hcode54 hpc54 (by decide) hstk54 (by norm_num)
                                                                                                              by_cases h54 : g.toNat < 191
                                                                                                              · exact Or.inl (by rw [hX54]; exact stepOOG hgas54 hstep54 (by norm_num) (by omega) (by omega))
                                                                                                              · set s55 := stSwap s54 [⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs55
                                                                                                                have hX55 := hX54.trans (stepContinue (k := 54) (C := 188) hgas54 hstep54 (by norm_num) (by omega))
                                                                                                                have hee55 : s55.executionEnv = I := by rw [hs55]; simp only [stSwap]; exact hee54
                                                                                                                have hcode55 : s55.executionEnv.code = truthBytecode := by rw [hee55]; exact hcode
                                                                                                                have hpc55 : s55.machineState.pc = ⟨114⟩ := by rw [hs55]; simp only [stSwap]; rw [hpc54]; rfl
                                                                                                                have hgas55 : s55.machineState.gasAvailable.toNat = g.toNat - 191 := by rw [hs55]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                have hstk55 : s55.machineState.stack = [⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs55]; simp only [stSwap]
                                                                                                                have haw55 : s55.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs55]; simp only [stSwap]; exact haw54
                                                                                                                have hmem55 : s55.machineState.memory = truthMem1 := by rw [hs55]; simp only [stSwap]; exact hmem54
                                                                                                                -- step 55: push1
                                                                                                                have hstep55 := push1_xstep (argv := ⟨87⟩) hcode55 hpc55 (by decide) hstk55 (by norm_num)
                                                                                                                by_cases h55 : g.toNat < 194
                                                                                                                · exact Or.inl (by rw [hX55]; exact stepOOG hgas55 hstep55 (by norm_num) (by omega) (by omega))
                                                                                                                · set s56 := stPush1 s55 ⟨87⟩ with hs56
                                                                                                                  have hX56 := hX55.trans (stepContinue (k := 55) (C := 191) hgas55 hstep55 (by norm_num) (by omega))
                                                                                                                  have hee56 : s56.executionEnv = I := by rw [hs56]; simp only [stPush1]; exact hee55
                                                                                                                  have hcode56 : s56.executionEnv.code = truthBytecode := by rw [hee56]; exact hcode
                                                                                                                  have hpc56 : s56.machineState.pc = ⟨116⟩ := by rw [hs56]; simp only [stPush1]; rw [hpc55]; rfl
                                                                                                                  have hgas56 : s56.machineState.gasAvailable.toNat = g.toNat - 194 := by rw [hs56]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                  have hstk56 : s56.machineState.stack = [⟨87⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs56]; simp only [stPush1, hstk55]
                                                                                                                  have haw56 : s56.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs56]; simp only [stPush1]; exact haw55
                                                                                                                  have hmem56 : s56.machineState.memory = truthMem1 := by rw [hs56]; simp only [stPush1]; exact hmem55
                                                                                                                  -- step 56: jump
                                                                                                                  have hstep56 := jump_xstep hcode56 hpc56 (by decide) hstk56 (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
                                                                                                                  by_cases h56 : g.toNat < 202
                                                                                                                  · exact Or.inl (by rw [hX56]; exact stepOOG hgas56 hstep56 (by norm_num) (by omega) (by omega))
                                                                                                                  · set s57 := stJump s56 ⟨87⟩ [⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs57
                                                                                                                    have hX57 := hX56.trans (stepContinue (k := 56) (C := 194) hgas56 hstep56 (by norm_num) (by omega))
                                                                                                                    have hee57 : s57.executionEnv = I := by rw [hs57]; simp only [stJump]; exact hee56
                                                                                                                    have hcode57 : s57.executionEnv.code = truthBytecode := by rw [hee57]; exact hcode
                                                                                                                    have hpc57 : s57.machineState.pc = ⟨87⟩ := by rw [hs57]; simp only [stJump]
                                                                                                                    have hgas57 : s57.machineState.gasAvailable.toNat = g.toNat - 202 := by rw [hs57]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                    have hstk57 : s57.machineState.stack = [⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs57]; simp only [stJump]
                                                                                                                    have haw57 : s57.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs57]; simp only [stJump]; exact haw56
                                                                                                                    have hmem57 : s57.machineState.memory = truthMem1 := by rw [hs57]; simp only [stJump]; exact hmem56
                                                                                                                    -- step 57: jumpdest
                                                                                                                    have hstep57 := jumpdest_xstep hcode57 hpc57 (by decide) (by rw [hstk57]; simp)
                                                                                                                    by_cases h57 : g.toNat < 203
                                                                                                                    · exact Or.inl (by rw [hX57]; exact stepOOG hgas57 hstep57 (by norm_num) (by omega) (by omega))
                                                                                                                    · set s58 := stJumpdest s57 with hs58
                                                                                                                      have hX58 := hX57.trans (stepContinue (k := 57) (C := 202) hgas57 hstep57 (by norm_num) (by omega))
                                                                                                                      have hee58 : s58.executionEnv = I := by rw [hs58]; simp only [stJumpdest]; exact hee57
                                                                                                                      have hcode58 : s58.executionEnv.code = truthBytecode := by rw [hee58]; exact hcode
                                                                                                                      have hpc58 : s58.machineState.pc = ⟨88⟩ := by rw [hs58]; simp only [stJumpdest]; rw [hpc57]; rfl
                                                                                                                      have hgas58 : s58.machineState.gasAvailable.toNat = g.toNat - 203 := by rw [hs58]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                      have hstk58 : s58.machineState.stack = [⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs58]; simp only [stJumpdest]; exact hstk57
                                                                                                                      have haw58 : s58.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs58]; simp only [stJumpdest]; exact haw57
                                                                                                                      have hmem58 : s58.machineState.memory = truthMem1 := by rw [hs58]; simp only [stJumpdest]; exact hmem57
                                                                                                                      -- step 58: push1
                                                                                                                      have hstep58 := push1_xstep (argv := ⟨94⟩) hcode58 hpc58 (by decide) hstk58 (by norm_num)
                                                                                                                      by_cases h58 : g.toNat < 206
                                                                                                                      · exact Or.inl (by rw [hX58]; exact stepOOG hgas58 hstep58 (by norm_num) (by omega) (by omega))
                                                                                                                      · set s59 := stPush1 s58 ⟨94⟩ with hs59
                                                                                                                        have hX59 := hX58.trans (stepContinue (k := 58) (C := 203) hgas58 hstep58 (by norm_num) (by omega))
                                                                                                                        have hee59 : s59.executionEnv = I := by rw [hs59]; simp only [stPush1]; exact hee58
                                                                                                                        have hcode59 : s59.executionEnv.code = truthBytecode := by rw [hee59]; exact hcode
                                                                                                                        have hpc59 : s59.machineState.pc = ⟨90⟩ := by rw [hs59]; simp only [stPush1]; rw [hpc58]; rfl
                                                                                                                        have hgas59 : s59.machineState.gasAvailable.toNat = g.toNat - 206 := by rw [hs59]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                        have hstk59 : s59.machineState.stack = [⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs59]; simp only [stPush1, hstk58]
                                                                                                                        have haw59 : s59.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs59]; simp only [stPush1]; exact haw58
                                                                                                                        have hmem59 : s59.machineState.memory = truthMem1 := by rw [hs59]; simp only [stPush1]; exact hmem58
                                                                                                                        -- step 59: dup2
                                                                                                                        have hstep59 := dup2_xstep hcode59 hpc59 (by decide) hstk59 (by norm_num)
                                                                                                                        by_cases h59 : g.toNat < 209
                                                                                                                        · exact Or.inl (by rw [hX59]; exact stepOOG hgas59 hstep59 (by norm_num) (by omega) (by omega))
                                                                                                                        · set s60 := stSwap s59 [⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs60
                                                                                                                          have hX60 := hX59.trans (stepContinue (k := 59) (C := 206) hgas59 hstep59 (by norm_num) (by omega))
                                                                                                                          have hee60 : s60.executionEnv = I := by rw [hs60]; simp only [stSwap]; exact hee59
                                                                                                                          have hcode60 : s60.executionEnv.code = truthBytecode := by rw [hee60]; exact hcode
                                                                                                                          have hpc60 : s60.machineState.pc = ⟨91⟩ := by rw [hs60]; simp only [stSwap]; rw [hpc59]; rfl
                                                                                                                          have hgas60 : s60.machineState.gasAvailable.toNat = g.toNat - 209 := by rw [hs60]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                          have hstk60 : s60.machineState.stack = [⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs60]; simp only [stSwap]
                                                                                                                          have haw60 : s60.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs60]; simp only [stSwap]; exact haw59
                                                                                                                          have hmem60 : s60.machineState.memory = truthMem1 := by rw [hs60]; simp only [stSwap]; exact hmem59
                                                                                                                          -- step 60: push1
                                                                                                                          have hstep60 := push1_xstep (argv := ⟨76⟩) hcode60 hpc60 (by decide) hstk60 (by norm_num)
                                                                                                                          by_cases h60 : g.toNat < 212
                                                                                                                          · exact Or.inl (by rw [hX60]; exact stepOOG hgas60 hstep60 (by norm_num) (by omega) (by omega))
                                                                                                                          · set s61 := stPush1 s60 ⟨76⟩ with hs61
                                                                                                                            have hX61 := hX60.trans (stepContinue (k := 60) (C := 209) hgas60 hstep60 (by norm_num) (by omega))
                                                                                                                            have hee61 : s61.executionEnv = I := by rw [hs61]; simp only [stPush1]; exact hee60
                                                                                                                            have hcode61 : s61.executionEnv.code = truthBytecode := by rw [hee61]; exact hcode
                                                                                                                            have hpc61 : s61.machineState.pc = ⟨93⟩ := by rw [hs61]; simp only [stPush1]; rw [hpc60]; rfl
                                                                                                                            have hgas61 : s61.machineState.gasAvailable.toNat = g.toNat - 212 := by rw [hs61]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                            have hstk61 : s61.machineState.stack = [⟨76⟩, ⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs61]; simp only [stPush1, hstk60]
                                                                                                                            have haw61 : s61.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs61]; simp only [stPush1]; exact haw60
                                                                                                                            have hmem61 : s61.machineState.memory = truthMem1 := by rw [hs61]; simp only [stPush1]; exact hmem60
                                                                                                                            -- step 61: jump
                                                                                                                            have hstep61 := jump_xstep hcode61 hpc61 (by decide) hstk61 (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
                                                                                                                            by_cases h61 : g.toNat < 220
                                                                                                                            · exact Or.inl (by rw [hX61]; exact stepOOG hgas61 hstep61 (by norm_num) (by omega) (by omega))
                                                                                                                            · set s62 := stJump s61 ⟨76⟩ [⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs62
                                                                                                                              have hX62 := hX61.trans (stepContinue (k := 61) (C := 212) hgas61 hstep61 (by norm_num) (by omega))
                                                                                                                              have hee62 : s62.executionEnv = I := by rw [hs62]; simp only [stJump]; exact hee61
                                                                                                                              have hcode62 : s62.executionEnv.code = truthBytecode := by rw [hee62]; exact hcode
                                                                                                                              have hpc62 : s62.machineState.pc = ⟨76⟩ := by rw [hs62]; simp only [stJump]
                                                                                                                              have hgas62 : s62.machineState.gasAvailable.toNat = g.toNat - 220 := by rw [hs62]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                              have hstk62 : s62.machineState.stack = [⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs62]; simp only [stJump]
                                                                                                                              have haw62 : s62.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs62]; simp only [stJump]; exact haw61
                                                                                                                              have hmem62 : s62.machineState.memory = truthMem1 := by rw [hs62]; simp only [stJump]; exact hmem61
                                                                                                                              -- step 62: jumpdest
                                                                                                                              have hstep62 := jumpdest_xstep hcode62 hpc62 (by decide) (by rw [hstk62]; simp)
                                                                                                                              by_cases h62 : g.toNat < 221
                                                                                                                              · exact Or.inl (by rw [hX62]; exact stepOOG hgas62 hstep62 (by norm_num) (by omega) (by omega))
                                                                                                                              · set s63 := stJumpdest s62 with hs63
                                                                                                                                have hX63 := hX62.trans (stepContinue (k := 62) (C := 220) hgas62 hstep62 (by norm_num) (by omega))
                                                                                                                                have hee63 : s63.executionEnv = I := by rw [hs63]; simp only [stJumpdest]; exact hee62
                                                                                                                                have hcode63 : s63.executionEnv.code = truthBytecode := by rw [hee63]; exact hcode
                                                                                                                                have hpc63 : s63.machineState.pc = ⟨77⟩ := by rw [hs63]; simp only [stJumpdest]; rw [hpc62]; rfl
                                                                                                                                have hgas63 : s63.machineState.gasAvailable.toNat = g.toNat - 221 := by rw [hs63]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                have hstk63 : s63.machineState.stack = [⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs63]; simp only [stJumpdest]; exact hstk62
                                                                                                                                have haw63 : s63.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs63]; simp only [stJumpdest]; exact haw62
                                                                                                                                have hmem63 : s63.machineState.memory = truthMem1 := by rw [hs63]; simp only [stJumpdest]; exact hmem62
                                                                                                                                -- step 63: push0
                                                                                                                                have hstep63 := push0_xstep hcode63 hpc63 (by decide) hstk63 (by norm_num)
                                                                                                                                by_cases h63 : g.toNat < 223
                                                                                                                                · exact Or.inl (by rw [hX63]; exact stepOOG hgas63 hstep63 (by norm_num) (by omega) (by omega))
                                                                                                                                · set s64 := stPush0 s63 with hs64
                                                                                                                                  have hX64 := hX63.trans (stepContinue (k := 63) (C := 221) hgas63 hstep63 (by norm_num) (by omega))
                                                                                                                                  have hee64 : s64.executionEnv = I := by rw [hs64]; simp only [stPush0]; exact hee63
                                                                                                                                  have hcode64 : s64.executionEnv.code = truthBytecode := by rw [hee64]; exact hcode
                                                                                                                                  have hpc64 : s64.machineState.pc = ⟨78⟩ := by rw [hs64]; simp only [stPush0]; rw [hpc63]; rfl
                                                                                                                                  have hgas64 : s64.machineState.gasAvailable.toNat = g.toNat - 223 := by rw [hs64]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                  have hstk64 : s64.machineState.stack = [⟨0⟩, ⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs64]; simp only [stPush0, hstk63]
                                                                                                                                  have haw64 : s64.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs64]; simp only [stPush0]; exact haw63
                                                                                                                                  have hmem64 : s64.machineState.memory = truthMem1 := by rw [hs64]; simp only [stPush0]; exact hmem63
                                                                                                                                  -- step 64: dup2
                                                                                                                                  have hstep64 := dup2_xstep hcode64 hpc64 (by decide) hstk64 (by norm_num)
                                                                                                                                  by_cases h64 : g.toNat < 226
                                                                                                                                  · exact Or.inl (by rw [hX64]; exact stepOOG hgas64 hstep64 (by norm_num) (by omega) (by omega))
                                                                                                                                  · set s65 := stSwap s64 [⟨1⟩, ⟨0⟩, ⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs65
                                                                                                                                    have hX65 := hX64.trans (stepContinue (k := 64) (C := 223) hgas64 hstep64 (by norm_num) (by omega))
                                                                                                                                    have hee65 : s65.executionEnv = I := by rw [hs65]; simp only [stSwap]; exact hee64
                                                                                                                                    have hcode65 : s65.executionEnv.code = truthBytecode := by rw [hee65]; exact hcode
                                                                                                                                    have hpc65 : s65.machineState.pc = ⟨79⟩ := by rw [hs65]; simp only [stSwap]; rw [hpc64]; rfl
                                                                                                                                    have hgas65 : s65.machineState.gasAvailable.toNat = g.toNat - 226 := by rw [hs65]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                    have hstk65 : s65.machineState.stack = [⟨1⟩, ⟨0⟩, ⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs65]; simp only [stSwap]
                                                                                                                                    have haw65 : s65.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs65]; simp only [stSwap]; exact haw64
                                                                                                                                    have hmem65 : s65.machineState.memory = truthMem1 := by rw [hs65]; simp only [stSwap]; exact hmem64
                                                                                                                                    -- step 65: iszero
                                                                                                                                    have hstep65 := iszero_xstep hcode65 hpc65 (by decide) hstk65 (by norm_num)
                                                                                                                                    by_cases h65 : g.toNat < 229
                                                                                                                                    · exact Or.inl (by rw [hX65]; exact stepOOG hgas65 hstep65 (by norm_num) (by omega) (by omega))
                                                                                                                                    · set s66 := stIsZero s65 ⟨1⟩ [⟨0⟩, ⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs66
                                                                                                                                      have hX66 := hX65.trans (stepContinue (k := 65) (C := 226) hgas65 hstep65 (by norm_num) (by omega))
                                                                                                                                      have hee66 : s66.executionEnv = I := by rw [hs66]; simp only [stIsZero]; exact hee65
                                                                                                                                      have hcode66 : s66.executionEnv.code = truthBytecode := by rw [hee66]; exact hcode
                                                                                                                                      have hpc66 : s66.machineState.pc = ⟨80⟩ := by rw [hs66]; simp only [stIsZero]; rw [hpc65]; rfl
                                                                                                                                      have hgas66 : s66.machineState.gasAvailable.toNat = g.toNat - 229 := by rw [hs66]; simp only [stIsZero]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                      have hstk66 : s66.machineState.stack = [⟨0⟩, ⟨0⟩, ⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs66]; simp only [stIsZero]; rw [show (UInt256.isZero ⟨1⟩) = ⟨0⟩ from by decide]
                                                                                                                                      have haw66 : s66.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs66]; simp only [stIsZero]; exact haw65
                                                                                                                                      have hmem66 : s66.machineState.memory = truthMem1 := by rw [hs66]; simp only [stIsZero]; exact hmem65
                                                                                                                                      -- step 66: iszero
                                                                                                                                      have hstep66 := iszero_xstep hcode66 hpc66 (by decide) hstk66 (by norm_num)
                                                                                                                                      by_cases h66 : g.toNat < 232
                                                                                                                                      · exact Or.inl (by rw [hX66]; exact stepOOG hgas66 hstep66 (by norm_num) (by omega) (by omega))
                                                                                                                                      · set s67 := stIsZero s66 ⟨0⟩ [⟨0⟩, ⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs67
                                                                                                                                        have hX67 := hX66.trans (stepContinue (k := 66) (C := 229) hgas66 hstep66 (by norm_num) (by omega))
                                                                                                                                        have hee67 : s67.executionEnv = I := by rw [hs67]; simp only [stIsZero]; exact hee66
                                                                                                                                        have hcode67 : s67.executionEnv.code = truthBytecode := by rw [hee67]; exact hcode
                                                                                                                                        have hpc67 : s67.machineState.pc = ⟨81⟩ := by rw [hs67]; simp only [stIsZero]; rw [hpc66]; rfl
                                                                                                                                        have hgas67 : s67.machineState.gasAvailable.toNat = g.toNat - 232 := by rw [hs67]; simp only [stIsZero]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                        have hstk67 : s67.machineState.stack = [⟨1⟩, ⟨0⟩, ⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs67]; simp only [stIsZero]; rw [show (UInt256.isZero ⟨0⟩) = ⟨1⟩ from by decide]
                                                                                                                                        have haw67 : s67.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs67]; simp only [stIsZero]; exact haw66
                                                                                                                                        have hmem67 : s67.machineState.memory = truthMem1 := by rw [hs67]; simp only [stIsZero]; exact hmem66
                                                                                                                                        -- step 67: swap1
                                                                                                                                        have hstep67 := swap1_xstep hcode67 hpc67 (by decide) hstk67 (by norm_num)
                                                                                                                                        by_cases h67 : g.toNat < 235
                                                                                                                                        · exact Or.inl (by rw [hX67]; exact stepOOG hgas67 hstep67 (by norm_num) (by omega) (by omega))
                                                                                                                                        · set s68 := stSwap s67 [⟨0⟩, ⟨1⟩, ⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs68
                                                                                                                                          have hX68 := hX67.trans (stepContinue (k := 67) (C := 232) hgas67 hstep67 (by norm_num) (by omega))
                                                                                                                                          have hee68 : s68.executionEnv = I := by rw [hs68]; simp only [stSwap]; exact hee67
                                                                                                                                          have hcode68 : s68.executionEnv.code = truthBytecode := by rw [hee68]; exact hcode
                                                                                                                                          have hpc68 : s68.machineState.pc = ⟨82⟩ := by rw [hs68]; simp only [stSwap]; rw [hpc67]; rfl
                                                                                                                                          have hgas68 : s68.machineState.gasAvailable.toNat = g.toNat - 235 := by rw [hs68]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                          have hstk68 : s68.machineState.stack = [⟨0⟩, ⟨1⟩, ⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs68]; simp only [stSwap]
                                                                                                                                          have haw68 : s68.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs68]; simp only [stSwap]; exact haw67
                                                                                                                                          have hmem68 : s68.machineState.memory = truthMem1 := by rw [hs68]; simp only [stSwap]; exact hmem67
                                                                                                                                          -- step 68: pop
                                                                                                                                          have hstep68 := pop_xstep hcode68 hpc68 (by decide) hstk68 (by norm_num)
                                                                                                                                          by_cases h68 : g.toNat < 237
                                                                                                                                          · exact Or.inl (by rw [hX68]; exact stepOOG hgas68 hstep68 (by norm_num) (by omega) (by omega))
                                                                                                                                          · set s69 := stPop s68 [⟨1⟩, ⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs69
                                                                                                                                            have hX69 := hX68.trans (stepContinue (k := 68) (C := 235) hgas68 hstep68 (by norm_num) (by omega))
                                                                                                                                            have hee69 : s69.executionEnv = I := by rw [hs69]; simp only [stPop]; exact hee68
                                                                                                                                            have hcode69 : s69.executionEnv.code = truthBytecode := by rw [hee69]; exact hcode
                                                                                                                                            have hpc69 : s69.machineState.pc = ⟨83⟩ := by rw [hs69]; simp only [stPop]; rw [hpc68]; rfl
                                                                                                                                            have hgas69 : s69.machineState.gasAvailable.toNat = g.toNat - 237 := by rw [hs69]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                            have hstk69 : s69.machineState.stack = [⟨1⟩, ⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs69]; simp only [stPop]
                                                                                                                                            have haw69 : s69.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs69]; simp only [stPop]; exact haw68
                                                                                                                                            have hmem69 : s69.machineState.memory = truthMem1 := by rw [hs69]; simp only [stPop]; exact hmem68
                                                                                                                                            -- step 69: swap2
                                                                                                                                            have hstep69 := swap2_xstep hcode69 hpc69 (by decide) hstk69 (by norm_num)
                                                                                                                                            by_cases h69 : g.toNat < 240
                                                                                                                                            · exact Or.inl (by rw [hX69]; exact stepOOG hgas69 hstep69 (by norm_num) (by omega) (by omega))
                                                                                                                                            · set s70 := stSwap s69 [⟨94⟩, ⟨1⟩, ⟨1⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs70
                                                                                                                                              have hX70 := hX69.trans (stepContinue (k := 69) (C := 237) hgas69 hstep69 (by norm_num) (by omega))
                                                                                                                                              have hee70 : s70.executionEnv = I := by rw [hs70]; simp only [stSwap]; exact hee69
                                                                                                                                              have hcode70 : s70.executionEnv.code = truthBytecode := by rw [hee70]; exact hcode
                                                                                                                                              have hpc70 : s70.machineState.pc = ⟨84⟩ := by rw [hs70]; simp only [stSwap]; rw [hpc69]; rfl
                                                                                                                                              have hgas70 : s70.machineState.gasAvailable.toNat = g.toNat - 240 := by rw [hs70]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                              have hstk70 : s70.machineState.stack = [⟨94⟩, ⟨1⟩, ⟨1⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs70]; simp only [stSwap]
                                                                                                                                              have haw70 : s70.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs70]; simp only [stSwap]; exact haw69
                                                                                                                                              have hmem70 : s70.machineState.memory = truthMem1 := by rw [hs70]; simp only [stSwap]; exact hmem69
                                                                                                                                              -- step 70: swap1
                                                                                                                                              have hstep70 := swap1_xstep hcode70 hpc70 (by decide) hstk70 (by norm_num)
                                                                                                                                              by_cases h70 : g.toNat < 243
                                                                                                                                              · exact Or.inl (by rw [hX70]; exact stepOOG hgas70 hstep70 (by norm_num) (by omega) (by omega))
                                                                                                                                              · set s71 := stSwap s70 [⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs71
                                                                                                                                                have hX71 := hX70.trans (stepContinue (k := 70) (C := 240) hgas70 hstep70 (by norm_num) (by omega))
                                                                                                                                                have hee71 : s71.executionEnv = I := by rw [hs71]; simp only [stSwap]; exact hee70
                                                                                                                                                have hcode71 : s71.executionEnv.code = truthBytecode := by rw [hee71]; exact hcode
                                                                                                                                                have hpc71 : s71.machineState.pc = ⟨85⟩ := by rw [hs71]; simp only [stSwap]; rw [hpc70]; rfl
                                                                                                                                                have hgas71 : s71.machineState.gasAvailable.toNat = g.toNat - 243 := by rw [hs71]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                have hstk71 : s71.machineState.stack = [⟨1⟩, ⟨94⟩, ⟨1⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs71]; simp only [stSwap]
                                                                                                                                                have haw71 : s71.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs71]; simp only [stSwap]; exact haw70
                                                                                                                                                have hmem71 : s71.machineState.memory = truthMem1 := by rw [hs71]; simp only [stSwap]; exact hmem70
                                                                                                                                                -- step 71: pop
                                                                                                                                                have hstep71 := pop_xstep hcode71 hpc71 (by decide) hstk71 (by norm_num)
                                                                                                                                                by_cases h71 : g.toNat < 245
                                                                                                                                                · exact Or.inl (by rw [hX71]; exact stepOOG hgas71 hstep71 (by norm_num) (by omega) (by omega))
                                                                                                                                                · set s72 := stPop s71 [⟨94⟩, ⟨1⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs72
                                                                                                                                                  have hX72 := hX71.trans (stepContinue (k := 71) (C := 243) hgas71 hstep71 (by norm_num) (by omega))
                                                                                                                                                  have hee72 : s72.executionEnv = I := by rw [hs72]; simp only [stPop]; exact hee71
                                                                                                                                                  have hcode72 : s72.executionEnv.code = truthBytecode := by rw [hee72]; exact hcode
                                                                                                                                                  have hpc72 : s72.machineState.pc = ⟨86⟩ := by rw [hs72]; simp only [stPop]; rw [hpc71]; rfl
                                                                                                                                                  have hgas72 : s72.machineState.gasAvailable.toNat = g.toNat - 245 := by rw [hs72]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                  have hstk72 : s72.machineState.stack = [⟨94⟩, ⟨1⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs72]; simp only [stPop]
                                                                                                                                                  have haw72 : s72.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs72]; simp only [stPop]; exact haw71
                                                                                                                                                  have hmem72 : s72.machineState.memory = truthMem1 := by rw [hs72]; simp only [stPop]; exact hmem71
                                                                                                                                                  -- step 72: jump
                                                                                                                                                  have hstep72 := jump_xstep hcode72 hpc72 (by decide) hstk72 (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
                                                                                                                                                  by_cases h72 : g.toNat < 253
                                                                                                                                                  · exact Or.inl (by rw [hX72]; exact stepOOG hgas72 hstep72 (by norm_num) (by omega) (by omega))
                                                                                                                                                  · set s73 := stJump s72 ⟨94⟩ [⟨1⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs73
                                                                                                                                                    have hX73 := hX72.trans (stepContinue (k := 72) (C := 245) hgas72 hstep72 (by norm_num) (by omega))
                                                                                                                                                    have hee73 : s73.executionEnv = I := by rw [hs73]; simp only [stJump]; exact hee72
                                                                                                                                                    have hcode73 : s73.executionEnv.code = truthBytecode := by rw [hee73]; exact hcode
                                                                                                                                                    have hpc73 : s73.machineState.pc = ⟨94⟩ := by rw [hs73]; simp only [stJump]
                                                                                                                                                    have hgas73 : s73.machineState.gasAvailable.toNat = g.toNat - 253 := by rw [hs73]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                    have hstk73 : s73.machineState.stack = [⟨1⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs73]; simp only [stJump]
                                                                                                                                                    have haw73 : s73.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs73]; simp only [stJump]; exact haw72
                                                                                                                                                    have hmem73 : s73.machineState.memory = truthMem1 := by rw [hs73]; simp only [stJump]; exact hmem72
                                                                                                                                                    -- step 73: jumpdest
                                                                                                                                                    have hstep73 := jumpdest_xstep hcode73 hpc73 (by decide) (by rw [hstk73]; simp)
                                                                                                                                                    by_cases h73 : g.toNat < 254
                                                                                                                                                    · exact Or.inl (by rw [hX73]; exact stepOOG hgas73 hstep73 (by norm_num) (by omega) (by omega))
                                                                                                                                                    · set s74 := stJumpdest s73 with hs74
                                                                                                                                                      have hX74 := hX73.trans (stepContinue (k := 73) (C := 253) hgas73 hstep73 (by norm_num) (by omega))
                                                                                                                                                      have hee74 : s74.executionEnv = I := by rw [hs74]; simp only [stJumpdest]; exact hee73
                                                                                                                                                      have hcode74 : s74.executionEnv.code = truthBytecode := by rw [hee74]; exact hcode
                                                                                                                                                      have hpc74 : s74.machineState.pc = ⟨95⟩ := by rw [hs74]; simp only [stJumpdest]; rw [hpc73]; rfl
                                                                                                                                                      have hgas74 : s74.machineState.gasAvailable.toNat = g.toNat - 254 := by rw [hs74]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                      have hstk74 : s74.machineState.stack = [⟨1⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs74]; simp only [stJumpdest]; exact hstk73
                                                                                                                                                      have haw74 : s74.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs74]; simp only [stJumpdest]; exact haw73
                                                                                                                                                      have hmem74 : s74.machineState.memory = truthMem1 := by rw [hs74]; simp only [stJumpdest]; exact hmem73
                                                                                                                                                      -- step 74: dup3
                                                                                                                                                      have hstep74 := dup3_xstep hcode74 hpc74 (by decide) hstk74 (by norm_num)
                                                                                                                                                      by_cases h74 : g.toNat < 257
                                                                                                                                                      · exact Or.inl (by rw [hX74]; exact stepOOG hgas74 hstep74 (by norm_num) (by omega) (by omega))
                                                                                                                                                      · set s75 := stSwap s74 [⟨128⟩, ⟨1⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs75
                                                                                                                                                        have hX75 := hX74.trans (stepContinue (k := 74) (C := 254) hgas74 hstep74 (by norm_num) (by omega))
                                                                                                                                                        have hee75 : s75.executionEnv = I := by rw [hs75]; simp only [stSwap]; exact hee74
                                                                                                                                                        have hcode75 : s75.executionEnv.code = truthBytecode := by rw [hee75]; exact hcode
                                                                                                                                                        have hpc75 : s75.machineState.pc = ⟨96⟩ := by rw [hs75]; simp only [stSwap]; rw [hpc74]; rfl
                                                                                                                                                        have hgas75 : s75.machineState.gasAvailable.toNat = g.toNat - 257 := by rw [hs75]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                        have hstk75 : s75.machineState.stack = [⟨128⟩, ⟨1⟩, ⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs75]; simp only [stSwap]
                                                                                                                                                        have haw75 : s75.machineState.activeWords = (UInt256.ofNat 3) := by rw [hs75]; simp only [stSwap]; exact haw74
                                                                                                                                                        have hmem75 : s75.machineState.memory = truthMem1 := by rw [hs75]; simp only [stSwap]; exact hmem74
                                                                                                                                                        -- step 75: mstore
                                                                                                                                                        have hmc75 : memoryExpansionCost s75 .MSTORE = 6 := by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw75, hstk75, Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide
                                                                                                                                                        have hstep75 := mstore_xstep hcode75 hpc75 (by decide) hstk75 (by norm_num)
                                                                                                                                                        rw [hmc75] at hstep75
                                                                                                                                                        by_cases h75 : g.toNat < 266
                                                                                                                                                        · exact Or.inl (by rw [hX75]; exact stepOOG (cost := 6 + 3) hgas75 hstep75 (by norm_num) (by omega) (by omega))
                                                                                                                                                        · set s76 := stMStore s75 ⟨128⟩ ⟨1⟩ [⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs76
                                                                                                                                                          have hX76 := hX75.trans (stepContinue (k := 75) (C := 257) (cost := 6 + 3) hgas75 hstep75 (by norm_num) (by omega))
                                                                                                                                                          have hee76 : s76.executionEnv = I := by rw [hs76]; simp only [stMStore]; exact hee75
                                                                                                                                                          have hcode76 : s76.executionEnv.code = truthBytecode := by rw [hee76]; exact hcode
                                                                                                                                                          have hpc76 : s76.machineState.pc = ⟨97⟩ := by rw [hs76]; simp only [stMStore]; rw [hpc75]; rfl
                                                                                                                                                          have hgas76 : s76.machineState.gasAvailable.toNat = g.toNat - 266 := by rw [hs76]; simp only [stMStore, hmc75]; rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                          have hstk76 : s76.machineState.stack = [⟨1⟩, ⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs76]; simp [stMStore]
                                                                                                                                                          have haw76 : s76.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs76]; simp only [stMStore, haw75]; decide
                                                                                                                                                          have hmem76 : s76.machineState.memory = truthMem2 := by rw [hs76]; simp only [stMStore]; rw [hmem75, show (⟨128⟩:UInt256).toNat = 128 from by decide]; rfl
                                                                                                                                                          -- step 76: pop
                                                                                                                                                          have hstep76 := pop_xstep hcode76 hpc76 (by decide) hstk76 (by norm_num)
                                                                                                                                                          by_cases h76 : g.toNat < 268
                                                                                                                                                          · exact Or.inl (by rw [hX76]; exact stepOOG hgas76 hstep76 (by norm_num) (by omega) (by omega))
                                                                                                                                                          · set s77 := stPop s76 [⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs77
                                                                                                                                                            have hX77 := hX76.trans (stepContinue (k := 76) (C := 266) hgas76 hstep76 (by norm_num) (by omega))
                                                                                                                                                            have hee77 : s77.executionEnv = I := by rw [hs77]; simp only [stPop]; exact hee76
                                                                                                                                                            have hcode77 : s77.executionEnv.code = truthBytecode := by rw [hee77]; exact hcode
                                                                                                                                                            have hpc77 : s77.machineState.pc = ⟨98⟩ := by rw [hs77]; simp only [stPop]; rw [hpc76]; rfl
                                                                                                                                                            have hgas77 : s77.machineState.gasAvailable.toNat = g.toNat - 268 := by rw [hs77]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                            have hstk77 : s77.machineState.stack = [⟨128⟩, ⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs77]; simp only [stPop]
                                                                                                                                                            have haw77 : s77.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs77]; simp only [stPop]; exact haw76
                                                                                                                                                            have hmem77 : s77.machineState.memory = truthMem2 := by rw [hs77]; simp only [stPop]; exact hmem76
                                                                                                                                                            -- step 77: pop
                                                                                                                                                            have hstep77 := pop_xstep hcode77 hpc77 (by decide) hstk77 (by norm_num)
                                                                                                                                                            by_cases h77 : g.toNat < 270
                                                                                                                                                            · exact Or.inl (by rw [hX77]; exact stepOOG hgas77 hstep77 (by norm_num) (by omega) (by omega))
                                                                                                                                                            · set s78 := stPop s77 [⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs78
                                                                                                                                                              have hX78 := hX77.trans (stepContinue (k := 77) (C := 268) hgas77 hstep77 (by norm_num) (by omega))
                                                                                                                                                              have hee78 : s78.executionEnv = I := by rw [hs78]; simp only [stPop]; exact hee77
                                                                                                                                                              have hcode78 : s78.executionEnv.code = truthBytecode := by rw [hee78]; exact hcode
                                                                                                                                                              have hpc78 : s78.machineState.pc = ⟨99⟩ := by rw [hs78]; simp only [stPop]; rw [hpc77]; rfl
                                                                                                                                                              have hgas78 : s78.machineState.gasAvailable.toNat = g.toNat - 270 := by rw [hs78]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                              have hstk78 : s78.machineState.stack = [⟨117⟩, ⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs78]; simp only [stPop]
                                                                                                                                                              have haw78 : s78.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs78]; simp only [stPop]; exact haw77
                                                                                                                                                              have hmem78 : s78.machineState.memory = truthMem2 := by rw [hs78]; simp only [stPop]; exact hmem77
                                                                                                                                                              -- step 78: jump
                                                                                                                                                              have hstep78 := jump_xstep hcode78 hpc78 (by decide) hstk78 (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
                                                                                                                                                              by_cases h78 : g.toNat < 278
                                                                                                                                                              · exact Or.inl (by rw [hX78]; exact stepOOG hgas78 hstep78 (by norm_num) (by omega) (by omega))
                                                                                                                                                              · set s79 := stJump s78 ⟨117⟩ [⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs79
                                                                                                                                                                have hX79 := hX78.trans (stepContinue (k := 78) (C := 270) hgas78 hstep78 (by norm_num) (by omega))
                                                                                                                                                                have hee79 : s79.executionEnv = I := by rw [hs79]; simp only [stJump]; exact hee78
                                                                                                                                                                have hcode79 : s79.executionEnv.code = truthBytecode := by rw [hee79]; exact hcode
                                                                                                                                                                have hpc79 : s79.machineState.pc = ⟨117⟩ := by rw [hs79]; simp only [stJump]
                                                                                                                                                                have hgas79 : s79.machineState.gasAvailable.toNat = g.toNat - 278 := by rw [hs79]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                                have hstk79 : s79.machineState.stack = [⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs79]; simp only [stJump]
                                                                                                                                                                have haw79 : s79.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs79]; simp only [stJump]; exact haw78
                                                                                                                                                                have hmem79 : s79.machineState.memory = truthMem2 := by rw [hs79]; simp only [stJump]; exact hmem78
                                                                                                                                                                -- step 79: jumpdest
                                                                                                                                                                have hstep79 := jumpdest_xstep hcode79 hpc79 (by decide) (by rw [hstk79]; simp)
                                                                                                                                                                by_cases h79 : g.toNat < 279
                                                                                                                                                                · exact Or.inl (by rw [hX79]; exact stepOOG hgas79 hstep79 (by norm_num) (by omega) (by omega))
                                                                                                                                                                · set s80 := stJumpdest s79 with hs80
                                                                                                                                                                  have hX80 := hX79.trans (stepContinue (k := 79) (C := 278) hgas79 hstep79 (by norm_num) (by omega))
                                                                                                                                                                  have hee80 : s80.executionEnv = I := by rw [hs80]; simp only [stJumpdest]; exact hee79
                                                                                                                                                                  have hcode80 : s80.executionEnv.code = truthBytecode := by rw [hee80]; exact hcode
                                                                                                                                                                  have hpc80 : s80.machineState.pc = ⟨118⟩ := by rw [hs80]; simp only [stJumpdest]; rw [hpc79]; rfl
                                                                                                                                                                  have hgas80 : s80.machineState.gasAvailable.toNat = g.toNat - 279 := by rw [hs80]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                                  have hstk80 : s80.machineState.stack = [⟨160⟩, ⟨128⟩, ⟨1⟩, ⟨59⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs80]; simp only [stJumpdest]; exact hstk79
                                                                                                                                                                  have haw80 : s80.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs80]; simp only [stJumpdest]; exact haw79
                                                                                                                                                                  have hmem80 : s80.machineState.memory = truthMem2 := by rw [hs80]; simp only [stJumpdest]; exact hmem79
                                                                                                                                                                  -- step 80: swap3
                                                                                                                                                                  have hstep80 := swap3_xstep hcode80 hpc80 (by decide) hstk80 (by norm_num)
                                                                                                                                                                  by_cases h80 : g.toNat < 282
                                                                                                                                                                  · exact Or.inl (by rw [hX80]; exact stepOOG hgas80 hstep80 (by norm_num) (by omega) (by omega))
                                                                                                                                                                  · set s81 := stSwap s80 [⟨59⟩, ⟨128⟩, ⟨1⟩, ⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs81
                                                                                                                                                                    have hX81 := hX80.trans (stepContinue (k := 80) (C := 279) hgas80 hstep80 (by norm_num) (by omega))
                                                                                                                                                                    have hee81 : s81.executionEnv = I := by rw [hs81]; simp only [stSwap]; exact hee80
                                                                                                                                                                    have hcode81 : s81.executionEnv.code = truthBytecode := by rw [hee81]; exact hcode
                                                                                                                                                                    have hpc81 : s81.machineState.pc = ⟨119⟩ := by rw [hs81]; simp only [stSwap]; rw [hpc80]; rfl
                                                                                                                                                                    have hgas81 : s81.machineState.gasAvailable.toNat = g.toNat - 282 := by rw [hs81]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                                    have hstk81 : s81.machineState.stack = [⟨59⟩, ⟨128⟩, ⟨1⟩, ⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs81]; simp only [stSwap]
                                                                                                                                                                    have haw81 : s81.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs81]; simp only [stSwap]; exact haw80
                                                                                                                                                                    have hmem81 : s81.machineState.memory = truthMem2 := by rw [hs81]; simp only [stSwap]; exact hmem80
                                                                                                                                                                    -- step 81: swap2
                                                                                                                                                                    have hstep81 := swap2_xstep hcode81 hpc81 (by decide) hstk81 (by norm_num)
                                                                                                                                                                    by_cases h81 : g.toNat < 285
                                                                                                                                                                    · exact Or.inl (by rw [hX81]; exact stepOOG hgas81 hstep81 (by norm_num) (by omega) (by omega))
                                                                                                                                                                    · set s82 := stSwap s81 [⟨1⟩, ⟨128⟩, ⟨59⟩, ⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs82
                                                                                                                                                                      have hX82 := hX81.trans (stepContinue (k := 81) (C := 282) hgas81 hstep81 (by norm_num) (by omega))
                                                                                                                                                                      have hee82 : s82.executionEnv = I := by rw [hs82]; simp only [stSwap]; exact hee81
                                                                                                                                                                      have hcode82 : s82.executionEnv.code = truthBytecode := by rw [hee82]; exact hcode
                                                                                                                                                                      have hpc82 : s82.machineState.pc = ⟨120⟩ := by rw [hs82]; simp only [stSwap]; rw [hpc81]; rfl
                                                                                                                                                                      have hgas82 : s82.machineState.gasAvailable.toNat = g.toNat - 285 := by rw [hs82]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                                      have hstk82 : s82.machineState.stack = [⟨1⟩, ⟨128⟩, ⟨59⟩, ⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs82]; simp only [stSwap]
                                                                                                                                                                      have haw82 : s82.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs82]; simp only [stSwap]; exact haw81
                                                                                                                                                                      have hmem82 : s82.machineState.memory = truthMem2 := by rw [hs82]; simp only [stSwap]; exact hmem81
                                                                                                                                                                      -- step 82: pop
                                                                                                                                                                      have hstep82 := pop_xstep hcode82 hpc82 (by decide) hstk82 (by norm_num)
                                                                                                                                                                      by_cases h82 : g.toNat < 287
                                                                                                                                                                      · exact Or.inl (by rw [hX82]; exact stepOOG hgas82 hstep82 (by norm_num) (by omega) (by omega))
                                                                                                                                                                      · set s83 := stPop s82 [⟨128⟩, ⟨59⟩, ⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs83
                                                                                                                                                                        have hX83 := hX82.trans (stepContinue (k := 82) (C := 285) hgas82 hstep82 (by norm_num) (by omega))
                                                                                                                                                                        have hee83 : s83.executionEnv = I := by rw [hs83]; simp only [stPop]; exact hee82
                                                                                                                                                                        have hcode83 : s83.executionEnv.code = truthBytecode := by rw [hee83]; exact hcode
                                                                                                                                                                        have hpc83 : s83.machineState.pc = ⟨121⟩ := by rw [hs83]; simp only [stPop]; rw [hpc82]; rfl
                                                                                                                                                                        have hgas83 : s83.machineState.gasAvailable.toNat = g.toNat - 287 := by rw [hs83]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                                        have hstk83 : s83.machineState.stack = [⟨128⟩, ⟨59⟩, ⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs83]; simp only [stPop]
                                                                                                                                                                        have haw83 : s83.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs83]; simp only [stPop]; exact haw82
                                                                                                                                                                        have hmem83 : s83.machineState.memory = truthMem2 := by rw [hs83]; simp only [stPop]; exact hmem82
                                                                                                                                                                        -- step 83: pop
                                                                                                                                                                        have hstep83 := pop_xstep hcode83 hpc83 (by decide) hstk83 (by norm_num)
                                                                                                                                                                        by_cases h83 : g.toNat < 289
                                                                                                                                                                        · exact Or.inl (by rw [hX83]; exact stepOOG hgas83 hstep83 (by norm_num) (by omega) (by omega))
                                                                                                                                                                        · set s84 := stPop s83 [⟨59⟩, ⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs84
                                                                                                                                                                          have hX84 := hX83.trans (stepContinue (k := 83) (C := 287) hgas83 hstep83 (by norm_num) (by omega))
                                                                                                                                                                          have hee84 : s84.executionEnv = I := by rw [hs84]; simp only [stPop]; exact hee83
                                                                                                                                                                          have hcode84 : s84.executionEnv.code = truthBytecode := by rw [hee84]; exact hcode
                                                                                                                                                                          have hpc84 : s84.machineState.pc = ⟨122⟩ := by rw [hs84]; simp only [stPop]; rw [hpc83]; rfl
                                                                                                                                                                          have hgas84 : s84.machineState.gasAvailable.toNat = g.toNat - 289 := by rw [hs84]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                                          have hstk84 : s84.machineState.stack = [⟨59⟩, ⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs84]; simp only [stPop]
                                                                                                                                                                          have haw84 : s84.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs84]; simp only [stPop]; exact haw83
                                                                                                                                                                          have hmem84 : s84.machineState.memory = truthMem2 := by rw [hs84]; simp only [stPop]; exact hmem83
                                                                                                                                                                          -- step 84: jump
                                                                                                                                                                          have hstep84 := jump_xstep hcode84 hpc84 (by decide) hstk84 (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
                                                                                                                                                                          by_cases h84 : g.toNat < 297
                                                                                                                                                                          · exact Or.inl (by rw [hX84]; exact stepOOG hgas84 hstep84 (by norm_num) (by omega) (by omega))
                                                                                                                                                                          · set s85 := stJump s84 ⟨59⟩ [⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs85
                                                                                                                                                                            have hX85 := hX84.trans (stepContinue (k := 84) (C := 289) hgas84 hstep84 (by norm_num) (by omega))
                                                                                                                                                                            have hee85 : s85.executionEnv = I := by rw [hs85]; simp only [stJump]; exact hee84
                                                                                                                                                                            have hcode85 : s85.executionEnv.code = truthBytecode := by rw [hee85]; exact hcode
                                                                                                                                                                            have hpc85 : s85.machineState.pc = ⟨59⟩ := by rw [hs85]; simp only [stJump]
                                                                                                                                                                            have hgas85 : s85.machineState.gasAvailable.toNat = g.toNat - 297 := by rw [hs85]; simp only [stJump]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                                            have hstk85 : s85.machineState.stack = [⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs85]; simp only [stJump]
                                                                                                                                                                            have haw85 : s85.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs85]; simp only [stJump]; exact haw84
                                                                                                                                                                            have hmem85 : s85.machineState.memory = truthMem2 := by rw [hs85]; simp only [stJump]; exact hmem84
                                                                                                                                                                            -- step 85: jumpdest
                                                                                                                                                                            have hstep85 := jumpdest_xstep hcode85 hpc85 (by decide) (by rw [hstk85]; simp)
                                                                                                                                                                            by_cases h85 : g.toNat < 298
                                                                                                                                                                            · exact Or.inl (by rw [hX85]; exact stepOOG hgas85 hstep85 (by norm_num) (by omega) (by omega))
                                                                                                                                                                            · set s86 := stJumpdest s85 with hs86
                                                                                                                                                                              have hX86 := hX85.trans (stepContinue (k := 85) (C := 297) hgas85 hstep85 (by norm_num) (by omega))
                                                                                                                                                                              have hee86 : s86.executionEnv = I := by rw [hs86]; simp only [stJumpdest]; exact hee85
                                                                                                                                                                              have hcode86 : s86.executionEnv.code = truthBytecode := by rw [hee86]; exact hcode
                                                                                                                                                                              have hpc86 : s86.machineState.pc = ⟨60⟩ := by rw [hs86]; simp only [stJumpdest]; rw [hpc85]; rfl
                                                                                                                                                                              have hgas86 : s86.machineState.gasAvailable.toNat = g.toNat - 298 := by rw [hs86]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                                              have hstk86 : s86.machineState.stack = [⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs86]; simp only [stJumpdest]; exact hstk85
                                                                                                                                                                              have haw86 : s86.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs86]; simp only [stJumpdest]; exact haw85
                                                                                                                                                                              have hmem86 : s86.machineState.memory = truthMem2 := by rw [hs86]; simp only [stJumpdest]; exact hmem85
                                                                                                                                                                              -- step 86: push1
                                                                                                                                                                              have hstep86 := push1_xstep (argv := ⟨64⟩) hcode86 hpc86 (by decide) hstk86 (by norm_num)
                                                                                                                                                                              by_cases h86 : g.toNat < 301
                                                                                                                                                                              · exact Or.inl (by rw [hX86]; exact stepOOG hgas86 hstep86 (by norm_num) (by omega) (by omega))
                                                                                                                                                                              · set s87 := stPush1 s86 ⟨64⟩ with hs87
                                                                                                                                                                                have hX87 := hX86.trans (stepContinue (k := 86) (C := 298) hgas86 hstep86 (by norm_num) (by omega))
                                                                                                                                                                                have hee87 : s87.executionEnv = I := by rw [hs87]; simp only [stPush1]; exact hee86
                                                                                                                                                                                have hcode87 : s87.executionEnv.code = truthBytecode := by rw [hee87]; exact hcode
                                                                                                                                                                                have hpc87 : s87.machineState.pc = ⟨62⟩ := by rw [hs87]; simp only [stPush1]; rw [hpc86]; rfl
                                                                                                                                                                                have hgas87 : s87.machineState.gasAvailable.toNat = g.toNat - 301 := by rw [hs87]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                                                have hstk87 : s87.machineState.stack = [⟨64⟩, ⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs87]; simp only [stPush1, hstk86]
                                                                                                                                                                                have haw87 : s87.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs87]; simp only [stPush1]; exact haw86
                                                                                                                                                                                have hmem87 : s87.machineState.memory = truthMem2 := by rw [hs87]; simp only [stPush1]; exact hmem86
                                                                                                                                                                                -- step 87: mload
                                                                                                                                                                                have hmc87 : memoryExpansionCost s87 .MLOAD = 0 := by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw87, hstk87, Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide
                                                                                                                                                                                have hstep87 := mload_xstep hcode87 hpc87 (by decide) hstk87 (by norm_num)
                                                                                                                                                                                rw [hmc87] at hstep87
                                                                                                                                                                                by_cases h87 : g.toNat < 304
                                                                                                                                                                                · exact Or.inl (by rw [hX87]; exact stepOOG (cost := 0 + 3) hgas87 hstep87 (by norm_num) (by omega) (by omega))
                                                                                                                                                                                · set s88 := stMLoad s87 ⟨64⟩ [⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs88
                                                                                                                                                                                  have hX88 := hX87.trans (stepContinue (k := 87) (C := 301) (cost := 0 + 3) hgas87 hstep87 (by norm_num) (by omega))
                                                                                                                                                                                  have hee88 : s88.executionEnv = I := by rw [hs88]; simp only [stMLoad]; exact hee87
                                                                                                                                                                                  have hcode88 : s88.executionEnv.code = truthBytecode := by rw [hee88]; exact hcode
                                                                                                                                                                                  have hpc88 : s88.machineState.pc = ⟨63⟩ := by rw [hs88]; simp only [stMLoad]; rw [hpc87]; rfl
                                                                                                                                                                                  have hgas88 : s88.machineState.gasAvailable.toNat = g.toNat - 304 := by rw [hs88]; simp only [stMLoad, hmc87]; rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                                                  have hstk88 : s88.machineState.stack = [⟨128⟩, ⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs88]; simp only [stMLoad]; rw [if_neg (by rw [hmem87, truthMem2_size, haw87]; decide)]; rw [hmem87, show (⟨64⟩:UInt256).toNat = 64 from by decide, truthMem2_read64, fromByteArrayBigEndian_toByteArray, show UInt256.ofNat ((⟨128⟩:UInt256).toNat) = ⟨128⟩ from by decide]
                                                                                                                                                                                  have haw88 : s88.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs88]; simp only [stMLoad, haw87]; decide
                                                                                                                                                                                  have hmem88 : s88.machineState.memory = truthMem2 := by rw [hs88]; simp only [stMLoad]; exact hmem87
                                                                                                                                                                                  -- step 88: dup1
                                                                                                                                                                                  have hstep88 := dup1_xstep hcode88 hpc88 (by decide) hstk88 (by norm_num)
                                                                                                                                                                                  by_cases h88 : g.toNat < 307
                                                                                                                                                                                  · exact Or.inl (by rw [hX88]; exact stepOOG hgas88 hstep88 (by norm_num) (by omega) (by omega))
                                                                                                                                                                                  · set s89 := stDup1 s88 ⟨128⟩ [⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs89
                                                                                                                                                                                    have hX89 := hX88.trans (stepContinue (k := 88) (C := 304) hgas88 hstep88 (by norm_num) (by omega))
                                                                                                                                                                                    have hee89 : s89.executionEnv = I := by rw [hs89]; simp only [stDup1]; exact hee88
                                                                                                                                                                                    have hcode89 : s89.executionEnv.code = truthBytecode := by rw [hee89]; exact hcode
                                                                                                                                                                                    have hpc89 : s89.machineState.pc = ⟨64⟩ := by rw [hs89]; simp only [stDup1]; rw [hpc88]; rfl
                                                                                                                                                                                    have hgas89 : s89.machineState.gasAvailable.toNat = g.toNat - 307 := by rw [hs89]; simp only [stDup1]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                                                    have hstk89 : s89.machineState.stack = [⟨128⟩, ⟨128⟩, ⟨160⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs89]; simp only [stDup1]
                                                                                                                                                                                    have haw89 : s89.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs89]; simp only [stDup1]; exact haw88
                                                                                                                                                                                    have hmem89 : s89.machineState.memory = truthMem2 := by rw [hs89]; simp only [stDup1]; exact hmem88
                                                                                                                                                                                    -- step 89: swap2
                                                                                                                                                                                    have hstep89 := swap2_xstep hcode89 hpc89 (by decide) hstk89 (by norm_num)
                                                                                                                                                                                    by_cases h89 : g.toNat < 310
                                                                                                                                                                                    · exact Or.inl (by rw [hX89]; exact stepOOG hgas89 hstep89 (by norm_num) (by omega) (by omega))
                                                                                                                                                                                    · set s90 := stSwap s89 [⟨160⟩, ⟨128⟩, ⟨128⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs90
                                                                                                                                                                                      have hX90 := hX89.trans (stepContinue (k := 89) (C := 307) hgas89 hstep89 (by norm_num) (by omega))
                                                                                                                                                                                      have hee90 : s90.executionEnv = I := by rw [hs90]; simp only [stSwap]; exact hee89
                                                                                                                                                                                      have hcode90 : s90.executionEnv.code = truthBytecode := by rw [hee90]; exact hcode
                                                                                                                                                                                      have hpc90 : s90.machineState.pc = ⟨65⟩ := by rw [hs90]; simp only [stSwap]; rw [hpc89]; rfl
                                                                                                                                                                                      have hgas90 : s90.machineState.gasAvailable.toNat = g.toNat - 310 := by rw [hs90]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                                                      have hstk90 : s90.machineState.stack = [⟨160⟩, ⟨128⟩, ⟨128⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs90]; simp only [stSwap]
                                                                                                                                                                                      have haw90 : s90.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs90]; simp only [stSwap]; exact haw89
                                                                                                                                                                                      have hmem90 : s90.machineState.memory = truthMem2 := by rw [hs90]; simp only [stSwap]; exact hmem89
                                                                                                                                                                                      -- step 90: sub
                                                                                                                                                                                      have hstep90 := sub_xstep hcode90 hpc90 (by decide) hstk90 (by norm_num)
                                                                                                                                                                                      by_cases h90 : g.toNat < 313
                                                                                                                                                                                      · exact Or.inl (by rw [hX90]; exact stepOOG hgas90 hstep90 (by norm_num) (by omega) (by omega))
                                                                                                                                                                                      · set s91 := stBinop s90 (UInt256.sub ⟨160⟩ ⟨128⟩) [⟨128⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs91
                                                                                                                                                                                        have hX91 := hX90.trans (stepContinue (k := 90) (C := 310) hgas90 hstep90 (by norm_num) (by omega))
                                                                                                                                                                                        have hee91 : s91.executionEnv = I := by rw [hs91]; simp only [stBinop]; exact hee90
                                                                                                                                                                                        have hcode91 : s91.executionEnv.code = truthBytecode := by rw [hee91]; exact hcode
                                                                                                                                                                                        have hpc91 : s91.machineState.pc = ⟨66⟩ := by rw [hs91]; simp only [stBinop]; rw [hpc90]; rfl
                                                                                                                                                                                        have hgas91 : s91.machineState.gasAvailable.toNat = g.toNat - 313 := by rw [hs91]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                                                        have hstk91 : s91.machineState.stack = [⟨32⟩, ⟨128⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs91]; simp only [stBinop]; rw [show (UInt256.sub ⟨160⟩ ⟨128⟩) = ⟨32⟩ from by decide]
                                                                                                                                                                                        have haw91 : s91.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs91]; simp only [stBinop]; exact haw90
                                                                                                                                                                                        have hmem91 : s91.machineState.memory = truthMem2 := by rw [hs91]; simp only [stBinop]; exact hmem90
                                                                                                                                                                                        -- step 91: swap1
                                                                                                                                                                                        have hstep91 := swap1_xstep hcode91 hpc91 (by decide) hstk91 (by norm_num)
                                                                                                                                                                                        by_cases h91 : g.toNat < 316
                                                                                                                                                                                        · exact Or.inl (by rw [hX91]; exact stepOOG hgas91 hstep91 (by norm_num) (by omega) (by omega))
                                                                                                                                                                                        · set s92 := stSwap s91 [⟨128⟩, ⟨32⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] with hs92
                                                                                                                                                                                          have hX92 := hX91.trans (stepContinue (k := 91) (C := 313) hgas91 hstep91 (by norm_num) (by omega))
                                                                                                                                                                                          have hee92 : s92.executionEnv = I := by rw [hs92]; simp only [stSwap]; exact hee91
                                                                                                                                                                                          have hcode92 : s92.executionEnv.code = truthBytecode := by rw [hee92]; exact hcode
                                                                                                                                                                                          have hpc92 : s92.machineState.pc = ⟨67⟩ := by rw [hs92]; simp only [stSwap]; rw [hpc91]; rfl
                                                                                                                                                                                          have hgas92 : s92.machineState.gasAvailable.toNat = g.toNat - 316 := by rw [hs92]; simp only [stSwap]; rw [toNat_sub_ofNat (by omega)]; omega
                                                                                                                                                                                          have hstk92 : s92.machineState.stack = [⟨128⟩, ⟨32⟩, (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)] := by rw [hs92]; simp only [stSwap]
                                                                                                                                                                                          have haw92 : s92.machineState.activeWords = (UInt256.ofNat 5) := by rw [hs92]; simp only [stSwap]; exact haw91
                                                                                                                                                                                          have hmem92 : s92.machineState.memory = truthMem2 := by rw [hs92]; simp only [stSwap]; exact hmem91
                                                                                                                                                                                          -- step 92: return (halt success)
                                                                                                                                                                                          have hmc92 : memoryExpansionCost s92 .RETURN = 0 := by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw92, hstk92, Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide
                                                                                                                                                                                          have hstep92 := return_xstep hcode92 hpc92 (by decide) hstk92 (by norm_num)
                                                                                                                                                                                          rw [hmc92] at hstep92
                                                                                                                                                                                          have houtput92 : s92.machineState.memory.readWithPadding (⟨128⟩:UInt256).toNat (⟨32⟩:UInt256).toNat = UInt256.toByteArray ⟨1⟩ := by rw [hmem92, show (⟨128⟩:UInt256).toNat = 128 from by decide, show (⟨32⟩:UInt256).toNat = 32 from by decide, truthMem2_read128]
                                                                                                                                                                                          rw [houtput92] at hstep92
                                                                                                                                                                                          exact Or.inr ⟨stReturn s92 ⟨128⟩ ⟨32⟩ [(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)], by rw [hX92]; exact stepHaltSuccess (k := 92) (C := 316) hgas92 hstep92 (by norm_num) (by omega), rfl, rfl, rfl⟩

/-- Lift the success trace to `Ξ`: either out-of-gas, or success returning
    `UInt256.toByteArray ⟨1⟩` with `σ`/`createdAccounts`/substate unchanged. -/
theorem truthXi_cvz_success
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hmatch : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    Ξ cA gh bl σ σ₀ g A I = .error .OutOfGass
      ∨ ∃ g', Ξ cA gh bl σ σ₀ g A I
                = .ok (.success (cA, σ, g', A) (UInt256.toByteArray ⟨1⟩)) := by
  rcases truthX_cvz_success hcode hwv hsz hsize hmatch with hoog | ⟨s, hX, hca, hσ, hsub⟩
  · exact Or.inl (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
  · refine Or.inr ⟨s.machineState.gasAvailable, ?_⟩
    have hxi := Xi_success_of_X (by rw [← hcode] at hX; exact hX)
    rw [hca, hσ, hsub] at hxi; exact hxi

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
  · -- calldatasize ≥ 4: split on the selector.
    rw [not_lt] at hsz
    by_cases hmatch : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == I.calldata.extract 0 4) = true
    · -- matching selector → `truth()` runs and returns `true`.
      rcases truthXi_cvz_success (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hmatch with hoog | ⟨g', hsucc⟩
      · exact reEquiv_outOfGas hoog
      · have hd : dispatchMsg truthContract I.calldata = some truthTransition := by
          rw [truthDispatch_eq, if_pos hmatch]
        refine reEquiv_execution hd (truthDecode_empty hsz)
          (truthBodyReturns (initState cA gh bl σ σ₀ g A I) ∅ ?_) ?_
        · show (initState cA gh bl σ σ₀ g A I).executionEnv.weiValue = ⟨0⟩
          simp only [initState]; exact hwv
        · rw [hsucc]
          exact execResultsEquiv.success rfl rfl rfl rfl
            (returnEquiv.returned rfl rfl truthReturnEncoding)
    · -- wrong selector → EVM reverts at `0x26`; Act fails to dispatch.
      rw [Bool.not_eq_true] at hmatch
      rcases truthX_cvz_revertB (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hmatch with hX | ⟨g', o, hX⟩
      · rw [← hcode] at hX; exact reEquiv_outOfGas (Xi_error_of_X hX)
      · rw [← hcode] at hX
        exact reEquiv_noDispatch (truthDispatch_none_nomatch hmatch) (Xi_revert_of_X hX)

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
