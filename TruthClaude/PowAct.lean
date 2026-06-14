import TruthClaude.PowSegments

/-!
# Pow — Act-side coupling and the final `powCorrect` statement

The EVM-side forward trace, success composition, and `Ξ` lift live in `PowSegments`/`PowCorrect`.
This file carries the **Act-level** facts (dispatch, calldata decode, return encoding, the body
execution including the `while` loop) and assembles the runtime-equivalence theorem.
-/

open Act ABI Ethereum Ethereum.EVM TruthClaude.Theory

namespace TruthClaude

set_option maxRecDepth 10000

/-! ## Calldata byte alignment for the `uint256` argument at offset 4 -/

/-- `copySlice 4 ∅ 0 32` is `cd`'s bytes `[4, 36)`. -/
theorem copySlice4_toList (cd : ByteArray) :
    (cd.copySlice 4 ByteArray.empty 0 32).data.toList = (cd.data.toList.drop 4).take 32 := by
  rw [ByteArray.data_copySlice]
  simp [Array.toList_extract, List.extract]

theorem copySlice4_size (cd : ByteArray) (hsz : 36 ≤ cd.size) :
    (cd.copySlice 4 ByteArray.empty 0 32).size = 32 := by
  show (cd.copySlice 4 ByteArray.empty 0 32).data.size = 32
  rw [← Array.length_toList, copySlice4_toList, List.length_take, List.length_drop,
    Array.length_toList]
  have : cd.data.size = cd.size := rfl
  omega

/-- `readBytes cd 4 32` is `cd`'s bytes `[4, 36)` when `cd` has at least 36 bytes (no padding). -/
theorem readBytes4_toList (cd : ByteArray) (hsz : 36 ≤ cd.size) :
    (ByteArray.readBytes cd 4 32).data.toList = (cd.data.toList.drop 4).take 32 := by
  unfold ByteArray.readBytes
  rw [if_pos (by decide : (decide (4 < 2 ^ 64) && decide (32 < 2 ^ 64)) = true)]
  rw [ByteArray.toList_data_append, copySlice4_toList, copySlice4_size cd hsz]
  simp [byteArray_zeroes_toList]

/-- `uInt256OfByteArray` is big-endian decode then `ofNat`. -/
theorem uInt256OfByteArray_eq (arr : ByteArray) :
    uInt256OfByteArray arr = UInt256.ofNat (fromByteArrayBigEndian arr) := by
  unfold uInt256OfByteArray fromByteArrayBigEndian fromBytesBigEndian
  rw [byteArray_toList_eq]; rfl

/-- The word the Act decoder reads for the `uint256` argument equals the EVM's `CALLDATALOAD 4`. -/
theorem decode_arg_word_eq {I : Ethereum.ExecutionEnv} (hsz : 36 ≤ I.calldata.size) :
    ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)
      = uInt256OfByteArray (I.calldata.readBytes 4 32) := by
  rw [uInt256OfByteArray_eq]
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 2
  rw [byteArray_toList_eq (I.calldata.readBytes 4 32), readBytes4_toList _ hsz]
  simp [byteArray_toList_eq]

/-- **Calldata decode for `pow2(uint256 n)`.**  With at least 36 bytes of calldata, decoding
    succeeds, binding `n` to the EVM's `CALLDATALOAD 4` value. -/
theorem powDecode_n {I : Ethereum.ExecutionEnv} (hsz : 36 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata (Pow.powTransition.params.map Param.name)
        (transitionSignature Pow.powTransition).paramTypes I.calldata
      = some ((∅ : Act.Store).insert "n"
          (.int (Int.ofNat (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat))) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hwlt : (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).val.val < EVM.twoPow 256 :=
    (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).val.isLt
  show decodeCalldata ["n"] [Pow.uint256] I.calldata = _
  unfold decodeCalldata decodeCalldata.decodeArgs
  rw [if_neg (by rw [htlen]; omega)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, Pow.uint256,
    decodeABIValues?, decodeABIValue?, readWord?, readBytes?, decodeABIWord?,
    bind, Option.bind, List.drop_zero, htake, hwlt, if_true,
    Bool.false_eq_true, if_false, Nat.zero_add, Nat.add_zero]
  rw [decode_arg_word_eq hsz]
  rfl

/-- **Calldata decode fails** when `4 ≤ size < 36`: the `uint256` argument can't be read. -/
theorem powDecode_none {I : Ethereum.ExecutionEnv} (hsz36 : I.calldata.size < 36) :
    decodeCalldata (Pow.powTransition.params.map Param.name)
        (transitionSignature Pow.powTransition).paramTypes I.calldata = none := by
  by_cases hsz4 : I.calldata.size < 4
  · show decodeCalldata ["n"] [Pow.uint256] I.calldata = none
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]; rfl
    unfold decodeCalldata; rw [if_pos (by rw [htlen]; omega)]
  · have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]; rfl
    have htake : ¬ (((I.calldata.toList.drop 4).take 32).length = 32) := by
      rw [List.length_take, List.length_drop, htlen]; omega
    show decodeCalldata ["n"] [Pow.uint256] I.calldata = none
    unfold decodeCalldata decodeCalldata.decodeArgs
    rw [if_neg (by rw [htlen]; omega)]
    rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
    simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, Pow.uint256,
      decodeABIValues?, decodeABIValue?, readWord?, readBytes?, bind, Option.bind,
      Nat.add_zero, Nat.zero_add, List.drop_zero, Bool.false_eq_true, if_false, htake]

/-- **Calldata decode fails** when `2^255 + 4 ≤ size`: the args region (`size − 4`) is `≥ 2^255`, so
    solc's **signed** length check `SLT(size − 4, 32) = 1` reverts.  The spec's decoder rejects the
    same calldata via the matching guard (`ABI/Decode.lean`).  Pairs with `powX_hugearg`. -/
theorem powDecode_none_huge {I : Ethereum.ExecutionEnv} (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (Pow.powTransition.params.map Param.name)
        (transitionSignature Pow.powTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  show decodeCalldata ["n"] [Pow.uint256] I.calldata = none
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega)]
  rw [if_pos (⟨rfl, by rw [List.length_drop, htlen]; omega⟩)]

/-! ## EVM revert trace: non-zero call value -/

/-- **`callvalue ≠ 0`**: the non-payable guard fails — `ISZERO` gives `0`, the `JUMPI` is not
    taken, and execution reverts at `PUSH0; PUSH0; REVERT`. -/
theorem powX_callvalue_ne {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ g' o, X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
                  = .ok (.revert g' o) := by
  rcases solcGuardPrologue (code := powBytecode) hcode (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) with
    hd | ⟨s, hX, hee, hp, hg, hstk, haw, hmem, hC, _hacc⟩
  · exact Or.inl hd
  · have hcs : s.executionEnv.code = powBytecode := by rw [hee]; exact hcode
    have st1 := push2_xstep (argv := ⟨15⟩) hcs hp (by decide) hstk (by norm_num)
    by_cases g1 : g.toNat < 29
    · exact Or.inl (hX.trans (stepOOG (k := 6) (C := 26) hg st1 (by omega) hC (by omega)))
    · set s1 := stPush2 s ⟨15⟩ with hs1
      have hX1 := hX.trans (stepContinue (k := 6) (C := 26) hg st1 (by omega) (by omega))
      have hc1 : s1.executionEnv.code = powBytecode := by rw [hs1]; simp only [stPush2]; exact hcs
      have hp1 : s1.machineState.pc = ⟨11⟩ := by rw [hs1]; simp only [stPush2]; rw [hp]; rfl
      have hg1 : s1.machineState.gasAvailable.toNat = g.toNat - 29 := by
        rw [hs1]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
      have hk1 : s1.machineState.stack = ⟨15⟩ :: ⟨0⟩ :: [I.weiValue] := by
        rw [hs1]; simp only [stPush2, hstk]; rw [isZero_eq_zero_of_ne hwv]
      have st2 := jumpi_nt_xstep hc1 hp1 (by decide) hk1 (by norm_num)
      by_cases g2 : g.toNat < 39
      · exact Or.inl (hX1.trans (stepOOG (k := 7) (C := 29) (cost := 10) hg1 st2 (by omega) (by omega) (by omega)))
      · set s2 := stJumpiNT s1 [I.weiValue] with hs2
        have hX2 := hX1.trans (stepContinue (k := 7) (C := 29) (cost := 10) hg1 st2 (by omega) (by omega))
        have hc2 : s2.executionEnv.code = powBytecode := by rw [hs2]; simp only [stJumpiNT]; exact hc1
        have hp2 : s2.machineState.pc = ⟨12⟩ := by rw [hs2]; simp only [stJumpiNT]; rw [hp1]; rfl
        have hg2 : s2.machineState.gasAvailable.toNat = g.toNat - 39 := by
          rw [hs2]; simp only [stJumpiNT]; rw [toNat_sub_ofNat (by omega)]; omega
        have hk2 : s2.machineState.stack = [I.weiValue] := by rw [hs2]; simp only [stJumpiNT]
        exact solcRevert0 hc2 hp2 (by decide) (by decide) (by decide) hk2 (by norm_num) hg2
          (by omega) (by omega) hX2

/-- Lift any `X`-level revert/OOG result to `Ξ`. -/
theorem powXi_of_revert {cA gh bl σ σ₀ A I} {g : UInt256} (hcode : I.code = powBytecode)
    (h : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
        ∨ ∃ g' o, X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
                    = .ok (.revert g' o)) :
    Ξ cA gh bl σ σ₀ g A I = .error .OutOfGass
      ∨ ∃ g' o, Ξ cA gh bl σ σ₀ g A I = .ok (.revert g' o) := by
  rcases h with hd | ⟨g', o, hX⟩
  · exact Or.inl (Xi_error_of_X (by rw [← hcode] at hd; exact hd))
  · exact Or.inr ⟨g', o, Xi_revert_of_X (by rw [← hcode] at hX; exact hX)⟩

/-- `Ξ` lift of the `callvalue ≠ 0` revert. -/
theorem powXi_callvalue_ne {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    Ξ cA gh bl σ σ₀ g A I = .error .OutOfGass
      ∨ ∃ g' o, Ξ cA gh bl σ σ₀ g A I = .ok (.revert g' o) :=
  powXi_of_revert hcode (powX_callvalue_ne hcode hwv)

/-! ## EVM revert trace: short calldata (`size < 4`) -/

/-- **`callvalue = 0`, `calldatasize < 4`**: the guard passes, but the calldata-size check
    (`lt(size, 4)`) takes the `JUMPI` to the `0x29` revert stub. -/
theorem powX_short {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ g' o, X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
                  = .ok (.revert g' o) := by
  rcases solcGuardPrologue (code := powBytecode) hcode (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) with
    hd | ⟨s, hX, hee, hp, hg, hstk, haw, hmem, hC, _hacc⟩
  · exact Or.inl hd
  · have hcs : s.executionEnv.code = powBytecode := by rw [hee]; exact hcode
    have hstk0 : s.machineState.stack = ⟨1⟩ :: ⟨0⟩ :: [] := by
      rw [hstk, hwv, isZero_zero]
    -- PUSH2 15
    have st1 := push2_xstep (argv := ⟨15⟩) hcs hp (by decide) hstk0 (by norm_num)
    by_cases g1 : g.toNat < 29
    · exact Or.inl (hX.trans (stepOOG (k := 6) (C := 26) hg st1 (by omega) hC (by omega)))
    · set s1 := stPush2 s ⟨15⟩ with hs1
      have hX1 := hX.trans (stepContinue (k := 6) (C := 26) hg st1 (by omega) (by omega))
      have hc1 : s1.executionEnv.code = powBytecode := by rw [hs1]; simp only [stPush2]; exact hcs
      have he1 : s1.executionEnv = I := by rw [hs1]; simp only [stPush2]; exact hee
      have hp1 : s1.machineState.pc = ⟨11⟩ := by rw [hs1]; simp only [stPush2]; rw [hp]; rfl
      have hg1 : s1.machineState.gasAvailable.toNat = g.toNat - 29 := by
        rw [hs1]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
      have hk1 : s1.machineState.stack = ⟨15⟩ :: ⟨1⟩ :: [⟨0⟩] := by rw [hs1]; simp only [stPush2, hstk0]
      -- JUMPI taken → 15
      have st2 := jumpi_t_xstep hc1 hp1 (by decide) hk1 (by decide)
        (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
      by_cases g2 : g.toNat < 39
      · exact Or.inl (hX1.trans (stepOOG (k := 7) (C := 29) (cost := 10) hg1 st2 (by omega) (by omega) (by omega)))
      · set s2 := stJumpiT s1 ⟨15⟩ [⟨0⟩] with hs2
        have hX2 := hX1.trans (stepContinue (k := 7) (C := 29) (cost := 10) hg1 st2 (by omega) (by omega))
        have hc2 : s2.executionEnv.code = powBytecode := by rw [hs2]; simp only [stJumpiT]; exact hc1
        have he2 : s2.executionEnv = I := by rw [hs2]; simp only [stJumpiT]; exact he1
        have hp2 : s2.machineState.pc = ⟨15⟩ := by rw [hs2]; simp only [stJumpiT]
        have hg2 : s2.machineState.gasAvailable.toNat = g.toNat - 39 := by
          rw [hs2]; simp only [stJumpiT]; rw [toNat_sub_ofNat (by omega)]; omega
        have hk2 : s2.machineState.stack = [⟨0⟩] := by rw [hs2]; simp only [stJumpiT]
        -- JUMPDEST 15
        have st3 := jumpdest_xstep hc2 hp2 (by decide) (by rw [hk2]; simp)
        by_cases g3 : g.toNat < 40
        · exact Or.inl (hX2.trans (stepOOG (k := 8) (C := 39) hg2 st3 (by omega) (by omega) (by omega)))
        · set s3 := stJumpdest s2 with hs3
          have hX3 := hX2.trans (stepContinue (k := 8) (C := 39) hg2 st3 (by omega) (by omega))
          have hc3 : s3.executionEnv.code = powBytecode := by rw [hs3]; simp only [stJumpdest]; exact hc2
          have he3 : s3.executionEnv = I := by rw [hs3]; simp only [stJumpdest]; exact he2
          have hp3 : s3.machineState.pc = ⟨16⟩ := by rw [hs3]; simp only [stJumpdest]; rw [hp2]; rfl
          have hg3 : s3.machineState.gasAvailable.toNat = g.toNat - 40 := by
            rw [hs3]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
          have hk3 : s3.machineState.stack = [⟨0⟩] := by rw [hs3]; simp only [stJumpdest]; exact hk2
          -- POP
          have st4 := pop_xstep hc3 hp3 (by decide) hk3 (by simp)
          by_cases g4 : g.toNat < 42
          · exact Or.inl (hX3.trans (stepOOG (k := 9) (C := 40) hg3 st4 (by omega) (by omega) (by omega)))
          · set s4 := stPop s3 [] with hs4
            have hX4 := hX3.trans (stepContinue (k := 9) (C := 40) hg3 st4 (by omega) (by omega))
            have hc4 : s4.executionEnv.code = powBytecode := by rw [hs4]; simp only [stPop]; exact hc3
            have he4 : s4.executionEnv = I := by rw [hs4]; simp only [stPop]; exact he3
            have hp4 : s4.machineState.pc = ⟨17⟩ := by rw [hs4]; simp only [stPop]; rw [hp3]; rfl
            have hg4 : s4.machineState.gasAvailable.toNat = g.toNat - 42 := by
              rw [hs4]; simp only [stPop]; rw [toNat_sub_ofNat (by omega)]; omega
            have hk4 : s4.machineState.stack = [] := by rw [hs4]; simp only [stPop]
            -- PUSH1 4
            have st5 := push1_xstep (argv := ⟨4⟩) hc4 hp4 (by decide) hk4 (by norm_num)
            by_cases g5 : g.toNat < 45
            · exact Or.inl (hX4.trans (stepOOG (k := 10) (C := 42) hg4 st5 (by omega) (by omega) (by omega)))
            · set s5 := stPush1 s4 ⟨4⟩ with hs5
              have hX5 := hX4.trans (stepContinue (k := 10) (C := 42) hg4 st5 (by omega) (by omega))
              have hc5 : s5.executionEnv.code = powBytecode := by rw [hs5]; simp only [stPush1]; exact hc4
              have he5 : s5.executionEnv = I := by rw [hs5]; simp only [stPush1]; exact he4
              have hp5 : s5.machineState.pc = ⟨19⟩ := by rw [hs5]; simp only [stPush1]; rw [hp4]; rfl
              have hg5 : s5.machineState.gasAvailable.toNat = g.toNat - 45 := by
                rw [hs5]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
              have hk5 : s5.machineState.stack = [⟨4⟩] := by rw [hs5]; simp only [stPush1, hk4]
              -- CALLDATASIZE
              have st6 := calldatasize_xstep hc5 hp5 (by decide) hk5 (by norm_num)
              by_cases g6 : g.toNat < 47
              · exact Or.inl (hX5.trans (stepOOG (k := 11) (C := 45) hg5 st6 (by omega) (by omega) (by omega)))
              · set s6 := stCalldatasize s5 with hs6
                have hX6 := hX5.trans (stepContinue (k := 11) (C := 45) hg5 st6 (by omega) (by omega))
                have hc6 : s6.executionEnv.code = powBytecode := by rw [hs6]; simp only [stCalldatasize]; exact hc5
                have hp6 : s6.machineState.pc = ⟨20⟩ := by rw [hs6]; simp only [stCalldatasize]; rw [hp5]; rfl
                have hg6 : s6.machineState.gasAvailable.toNat = g.toNat - 47 := by
                  rw [hs6]; simp only [stCalldatasize]; rw [toNat_sub_ofNat (by omega)]; omega
                have hk6 : s6.machineState.stack = UInt256.ofNat I.calldata.size :: [⟨4⟩] := by
                  rw [hs6]; simp only [stCalldatasize, hk5]; rw [he5]
                -- LT  (size < 4 ⇒ 1)
                have st7 := lt_xstep hc6 hp6 (by decide) hk6 (by norm_num)
                by_cases g7 : g.toNat < 50
                · exact Or.inl (hX6.trans (stepOOG (k := 12) (C := 47) hg6 st7 (by omega) (by omega) (by omega)))
                · set s7 := stBinop s6 (UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩) [] with hs7
                  have hX7 := hX6.trans (stepContinue (k := 12) (C := 47) hg6 st7 (by omega) (by omega))
                  have hc7 : s7.executionEnv.code = powBytecode := by rw [hs7]; simp only [stBinop]; exact hc6
                  have hp7 : s7.machineState.pc = ⟨21⟩ := by rw [hs7]; simp only [stBinop]; rw [hp6]; rfl
                  have hg7 : s7.machineState.gasAvailable.toNat = g.toNat - 50 := by
                    rw [hs7]; simp only [stBinop]; rw [toNat_sub_ofNat (by omega)]; omega
                  have hk7 : s7.machineState.stack = [⟨1⟩] := by
                    rw [hs7]; simp only [stBinop]
                    rw [ult_one (by rw [ulit_toNat' _ (lt_size_of_lt256 (by omega)),
                      show (⟨4⟩ : UInt256).toNat = 4 from by decide]; omega)]
                  -- PUSH2 41
                  have st8 := push2_xstep (argv := ⟨41⟩) hc7 hp7 (by decide) hk7 (by norm_num)
                  by_cases g8 : g.toNat < 53
                  · exact Or.inl (hX7.trans (stepOOG (k := 13) (C := 50) hg7 st8 (by omega) (by omega) (by omega)))
                  · set s8 := stPush2 s7 ⟨41⟩ with hs8
                    have hX8 := hX7.trans (stepContinue (k := 13) (C := 50) hg7 st8 (by omega) (by omega))
                    have hc8 : s8.executionEnv.code = powBytecode := by rw [hs8]; simp only [stPush2]; exact hc7
                    have hp8 : s8.machineState.pc = ⟨24⟩ := by rw [hs8]; simp only [stPush2]; rw [hp7]; rfl
                    have hg8 : s8.machineState.gasAvailable.toNat = g.toNat - 53 := by
                      rw [hs8]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
                    have hk8 : s8.machineState.stack = ⟨41⟩ :: [⟨1⟩] := by rw [hs8]; simp only [stPush2, hk7]
                    -- JUMPI taken → 41
                    have st9 := jumpi_t_xstep hc8 hp8 (by decide) hk8 (by decide)
                      (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)
                    by_cases g9 : g.toNat < 63
                    · exact Or.inl (hX8.trans (stepOOG (k := 14) (C := 53) (cost := 10) hg8 st9 (by omega) (by omega) (by omega)))
                    · set s9 := stJumpiT s8 ⟨41⟩ [] with hs9
                      have hX9 := hX8.trans (stepContinue (k := 14) (C := 53) (cost := 10) hg8 st9 (by omega) (by omega))
                      have hc9 : s9.executionEnv.code = powBytecode := by rw [hs9]; simp only [stJumpiT]; exact hc8
                      have hp9 : s9.machineState.pc = ⟨41⟩ := by rw [hs9]; simp only [stJumpiT]
                      have hg9 : s9.machineState.gasAvailable.toNat = g.toNat - 63 := by
                        rw [hs9]; simp only [stJumpiT]; rw [toNat_sub_ofNat (by omega)]; omega
                      have hk9 : s9.machineState.stack = [] := by rw [hs9]; simp only [stJumpiT]
                      -- JUMPDEST 41
                      have st10 := jumpdest_xstep hc9 hp9 (by decide) (by rw [hk9]; simp)
                      by_cases g10 : g.toNat < 64
                      · exact Or.inl (hX9.trans (stepOOG (k := 15) (C := 63) hg9 st10 (by omega) (by omega) (by omega)))
                      · set s10 := stJumpdest s9 with hs10
                        have hX10 := hX9.trans (stepContinue (k := 15) (C := 63) hg9 st10 (by omega) (by omega))
                        have hc10 : s10.executionEnv.code = powBytecode := by rw [hs10]; simp only [stJumpdest]; exact hc9
                        have hp10 : s10.machineState.pc = ⟨42⟩ := by rw [hs10]; simp only [stJumpdest]; rw [hp9]; rfl
                        have hg10 : s10.machineState.gasAvailable.toNat = g.toNat - 64 := by
                          rw [hs10]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
                        have hk10 : s10.machineState.stack = [] := by rw [hs10]; simp only [stJumpdest]; exact hk9
                        exact solcRevert0 hc10 hp10 (by decide) (by decide) (by decide) hk10 (by simp)
                          hg10 (by omega) (by omega) hX10

/-- `Ξ` lift of the short-calldata revert. -/
theorem powXi_short {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    Ξ cA gh bl σ σ₀ g A I = .error .OutOfGass
      ∨ ∃ g' o, Ξ cA gh bl σ σ₀ g A I = .ok (.revert g' o) :=
  powXi_of_revert hcode (powX_short hcode hwv hsz)

/-! ## EVM revert trace: `n ≥ 256` (reuses `powX_disp` + `powX_decode`) -/

/-- **`callvalue = 0`, valid selector, `calldatasize ≥ 36`, `n ≥ 256`**: dispatch and decode
    succeed (reusing `powX_disp`/`powX_decode`), then `require(n < 256)` reverts. -/
theorem powX_nlarge {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hn : 256 ≤ (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ g' o, X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
                  = .ok (.revert g' o) := by
  have hsize : I.calldata.size < UInt256.size := by
    have h0 : (2:ℕ)^255 + 4 < 2^256 := by norm_num
    have hp : (2:ℕ)^255 + 4 < UInt256.size := by simpa [UInt256.size] using h0
    omega
  set sel := UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ with hsel
  set arg := uInt256OfByteArray (I.calldata.readBytes 4 32) with harg
  rcases powX_disp hcode hwv (by omega) hsize hmatch with
    hd | ⟨s1, hX1, hee1, hp1, hg1, hstk1, haw1, hmem1, hC1, _hacc1⟩
  · exact Or.inl hd
  · rcases powX_decode (s0 := initState cA gh bl σ σ₀ g A I) (I := I) (k := 24) (C := 96)
        (by rw [hee1]; exact hcode) hee1 hp1 hstk1 hsz36 hsz255 hg1 (by norm_num) hC1 hX1 with
      hd | ⟨k2, C2, s2, hX2, hc2, hp2, hstk2, hg2, hk2, hCg2, hmem2, haw2⟩
    · exact Or.inl hd
    · exact powX_require_revert (n := arg) (sel := sel) (R := []) hc2 hp2 hstk2 hn
        (by simp only [List.length_nil]; omega) hg2 hk2 hCg2 hX2

/-- `Ξ` lift of the `n ≥ 256` revert. -/
theorem powXi_nlarge {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hn : 256 ≤ (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat) :
    Ξ cA gh bl σ σ₀ g A I = .error .OutOfGass
      ∨ ∃ g' o, Ξ cA gh bl σ σ₀ g A I = .ok (.revert g' o) :=
  powXi_of_revert hcode (powX_nlarge hcode hwv hsz36 hsz255 hmatch hn)

/-! ## EVM revert trace: wrong selector (reuses `powX_dispToEq`) -/

/-- **`callvalue = 0`, `calldatasize ≥ 4`, selector mismatch**: reuses `powX_dispToEq`, then the
    `EQ` is `0`, the dispatch `JUMPI` is not taken, and execution reverts at `0x29`. -/
theorem powX_nomatch {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = false) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ g' o, X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
                  = .ok (.revert g' o) := by
  rcases powX_dispToEq hcode hwv hsz hsize with
    hoog | ⟨s22, hX22, hee22, hpc22, hgas22, hstk22, haw22, hmem22, hg83⟩
  · exact Or.inl hoog
  · set sel := UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ with hseldef
    have hcode22 : s22.executionEnv.code = powBytecode := by rw [hee22]; exact hcode
    have heq0 : UInt256.eq ⟨1143701499⟩ sel = ⟨0⟩ := by
      rw [hseldef, powEvmSelector hsz, if_neg (by rw [hmatch]; decide)]
    have hstk22' : s22.machineState.stack = [⟨0⟩, sel] := by rw [hstk22, heq0]
    have hstep22 := push2_xstep (argv := ⟨45⟩) hcode22 hpc22 (by decide) hstk22' (by norm_num)
    by_cases h22 : g.toNat < 86
    · exact Or.inl (by rw [hX22]; exact stepOOG hgas22 hstep22 (by norm_num) (by omega) (by omega))
    · set s23 := stPush2 s22 ⟨45⟩ with hs23
      have hX23 := hX22.trans (stepContinue (k := 22) (C := 83) hgas22 hstep22 (by norm_num) (by omega))
      have hcode23 : s23.executionEnv.code = powBytecode := by rw [hs23]; simp only [stPush2]; exact hcode22
      have hpc23 : s23.machineState.pc = ⟨40⟩ := by rw [hs23]; simp only [stPush2]; rw [hpc22]; rfl
      have hgas23 : s23.machineState.gasAvailable.toNat = g.toNat - 86 := by
        rw [hs23]; simp only [stPush2]; rw [toNat_sub_ofNat (by omega)]; omega
      have hstk23 : s23.machineState.stack = ⟨45⟩ :: ⟨0⟩ :: [sel] := by rw [hs23]; simp only [stPush2, hstk22']
      have hstep23 := jumpi_nt_xstep hcode23 hpc23 (by decide) hstk23 (by norm_num)
      by_cases h23 : g.toNat < 96
      · exact Or.inl (by rw [hX23]; exact stepOOG (k := 23) (C := 86) (cost := 10) hgas23 hstep23 (by omega) (by omega) (by omega))
      · set s24 := stJumpiNT s23 [sel] with hs24
        have hX24 := hX23.trans (stepContinue (k := 23) (C := 86) (cost := 10) hgas23 hstep23 (by omega) (by omega))
        have hcode24 : s24.executionEnv.code = powBytecode := by rw [hs24]; simp only [stJumpiNT]; exact hcode23
        have hpc24 : s24.machineState.pc = ⟨41⟩ := by rw [hs24]; simp only [stJumpiNT]; rw [hpc23]; rfl
        have hgas24 : s24.machineState.gasAvailable.toNat = g.toNat - 96 := by
          rw [hs24]; simp only [stJumpiNT]; rw [toNat_sub_ofNat (by omega)]; omega
        have hstk24 : s24.machineState.stack = [sel] := by rw [hs24]; simp only [stJumpiNT]
        have hstep24 := jumpdest_xstep hcode24 hpc24 (by decide) (by rw [hstk24]; simp)
        by_cases h24 : g.toNat < 97
        · exact Or.inl (by rw [hX24]; exact stepOOG (k := 24) (C := 96) hgas24 hstep24 (by omega) (by omega) (by omega))
        · set s25 := stJumpdest s24 with hs25
          have hX25 := hX24.trans (stepContinue (k := 24) (C := 96) hgas24 hstep24 (by omega) (by omega))
          have hcode25 : s25.executionEnv.code = powBytecode := by rw [hs25]; simp only [stJumpdest]; exact hcode24
          have hpc25 : s25.machineState.pc = ⟨42⟩ := by rw [hs25]; simp only [stJumpdest]; rw [hpc24]; rfl
          have hgas25 : s25.machineState.gasAvailable.toNat = g.toNat - 97 := by
            rw [hs25]; simp only [stJumpdest]; rw [toNat_sub_ofNat (by omega)]; omega
          have hstk25 : s25.machineState.stack = [sel] := by rw [hs25]; simp only [stJumpdest]; exact hstk24
          exact solcRevert0 hcode25 hpc25 (by decide) (by decide) (by decide) hstk25 (by simp)
            hgas25 (by omega) (by omega) hX25

/-- `Ξ` lift of the wrong-selector revert. -/
theorem powXi_nomatch {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = false) :
    Ξ cA gh bl σ σ₀ g A I = .error .OutOfGass
      ∨ ∃ g' o, Ξ cA gh bl σ σ₀ g A I = .ok (.revert g' o) :=
  powXi_of_revert hcode (powX_nomatch hcode hwv hsz hsize hmatch)

/-! ## EVM revert trace: short argument (`4 ≤ size < 36`, reuses disp + decode prefixes) -/

/-- **`callvalue = 0`, valid selector, `4 ≤ calldatasize < 36`**: dispatch and the decode
    call-setup succeed (reusing `powX_disp` + `powX_decodeToCf`), then the decoder's bounds check
    (`SLT(size−4, 32) = 1`) reverts. -/
theorem powX_shortarg {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsz36 : I.calldata.size < 36)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ g' o, X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
                  = .ok (.revert g' o) := by
  have hsize : I.calldata.size < UInt256.size := lt_size_of_lt256 (by omega)
  have hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply slt32_one; rw [sub4_toNat (by omega) hsize]; omega
  rcases powX_disp hcode hwv hsz4 hsize hmatch with
    hd | ⟨s1, hX1, hee1, hp1, hg1, hstk1, haw1, hmem1, hC1, _hacc1⟩
  · exact Or.inl hd
  · rcases powX_decodeToCf (s0 := initState cA gh bl σ σ₀ g A I) (I := I) (k := 24) (C := 96)
        (by rw [hee1]; exact hcode) hee1 hp1 hstk1 hsz4 hsize hg1 (by norm_num) hC1 hX1 with
      hd | ⟨k2, C2, s2, hX2, hc2, he2, hp2, hstk2, hg2, hk2, hCg2, hmem2, haw2⟩
    · exact Or.inl hd
    · exact powRoutine_cf_revert (I := I)
        (ret := ⟨66⟩)
        (R' := ⟨71⟩ :: [UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩])
        hc2 he2 hp2 hstk2 hsz4 hsize hsltval (by simp only [List.length_cons, List.length_nil]; omega)
        hg2 hk2 hCg2 hX2

/-- `Ξ` lift of the short-argument revert. -/
theorem powXi_shortarg {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsz36 : I.calldata.size < 36)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    Ξ cA gh bl σ σ₀ g A I = .error .OutOfGass
      ∨ ∃ g' o, Ξ cA gh bl σ σ₀ g A I = .ok (.revert g' o) :=
  powXi_of_revert hcode (powX_shortarg hcode hwv hsz4 hsz36 hmatch)

/-! ## EVM revert trace: huge calldata (`calldatasize ≥ 2^255 + 4`) -/

/-- **`callvalue = 0`, valid selector, `calldatasize ≥ 2^255 + 4`**: dispatch and the decoder
    call-setup succeed, but the decoder's **signed** bounds check `SLT(size − 4, 32) = 1` reverts —
    here because `size − 4 ≥ 2^255` is a negative two's-complement word.  Mirrors `powX_shortarg`
    (same trace, `slt32_one_high` instead of `slt32_one`); the matching Act failure is
    `powDecode_none_huge`. -/
theorem powX_hugearg {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ g' o, X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
                  = .ok (.revert g' o) := by
  have hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply slt32_one_high; rw [sub4_toNat (by omega) hsize]; omega
  rcases powX_disp hcode hwv (by omega) hsize hmatch with
    hd | ⟨s1, hX1, hee1, hp1, hg1, hstk1, haw1, hmem1, hC1, _hacc1⟩
  · exact Or.inl hd
  · rcases powX_decodeToCf (s0 := initState cA gh bl σ σ₀ g A I) (I := I) (k := 24) (C := 96)
        (by rw [hee1]; exact hcode) hee1 hp1 hstk1 (by omega) hsize hg1 (by norm_num) hC1 hX1 with
      hd | ⟨k2, C2, s2, hX2, hc2, he2, hp2, hstk2, hg2, hk2, hCg2, hmem2, haw2⟩
    · exact Or.inl hd
    · exact powRoutine_cf_revert (I := I)
        (ret := ⟨66⟩)
        (R' := ⟨71⟩ :: [UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩])
        hc2 he2 hp2 hstk2 (by omega) hsize hsltval (by simp only [List.length_cons, List.length_nil]; omega)
        hg2 hk2 hCg2 hX2

/-- `Ξ` lift of the huge-calldata revert. -/
theorem powXi_hugearg {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    Ξ cA gh bl σ σ₀ g A I = .error .OutOfGass
      ∨ ∃ g' o, Ξ cA gh bl σ σ₀ g A I = .ok (.revert g' o) :=
  powXi_of_revert hcode (powX_hugearg hcode hwv hbig hsize hmatch)

/-! ## Dispatch -/

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

/-! ## Store / expression-evaluation helpers -/

/-- Reading a freshly-inserted key. -/
theorem store_get_self (L : Act.Store) (k : Ident) (v : Value) :
    (L.insert k v).get? k = some v := by simp

/-- Reading a key untouched by an insert of a different key. -/
theorem store_get_ne (L : Act.Store) {k a : Ident} (v : Value) (h : (k == a) = false) :
    (L.insert k v).get? a = L.get? a := by
  simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, h]

/-- `i < n` evaluates from the locals. -/
theorem evalLt {cfg : Config} {C : ContractDecl} {L : Act.Store} {evm : EVM.State} {a b : Int}
    (hi : L.get? "i" = some (.int a)) (hn : L.get? "n" = some (.int b)) :
    evalExpr? cfg { contract := C, locals := L } evm (.binary .lt (.var "i") (.var "n"))
      = .ok (.bool (a < b)) := by
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption, hi, hn]

/-- `r * 2` evaluates from the locals. -/
theorem evalMul2 {cfg : Config} {C : ContractDecl} {L : Act.Store} {evm : EVM.State} {a : Int}
    (hr : L.get? "r" = some (.int a)) :
    evalExpr? cfg { contract := C, locals := L } evm (.binary .mul (.var "r") (.intLit 2))
      = .ok (.int (a * 2)) := by
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption, hr]

/-- `i + 1` evaluates from the locals. -/
theorem evalAdd1 {cfg : Config} {C : ContractDecl} {L : Act.Store} {evm : EVM.State} {a : Int}
    (hi : L.get? "i" = some (.int a)) :
    evalExpr? cfg { contract := C, locals := L } evm (.binary .add (.var "i") (.intLit 1))
      = .ok (.int (a + 1)) := by
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption, hi]

/-- Reading a plain variable from the locals. -/
theorem evalVar {cfg : Config} {C : ContractDecl} {L : Act.Store} {evm : EVM.State} {name : Ident}
    {v : Value} (h : L.get? name = some v) :
    evalExpr? cfg { contract := C, locals := L } evm (.var name) = .ok v := by
  simp only [evalExpr?, EvalResult.ofOption, h]

/-! ## The Act `while` loop computes `2^n` (by induction on the variant `n − i`) -/

/-- The loop body of `pow2`. -/
def powLoopBody : List Stmt :=
  [ .letDecl "r" (some Pow.uint256) (.binary .mul (.var "r") (.intLit 2)),
    .letDecl "i" (some Pow.uint256) (.binary .add (.var "i") (.intLit 1)) ]

/-- The loop condition of `pow2`. -/
def powLoopCond : Expr := .binary .lt (.var "i") (.var "n")

/-- **Act-side loop core.**  With locals `i ↦ i`, `r ↦ 2^i`, `n ↦ N` and `i ≤ N`, the `while`
    runs (in unbounded `Int`) to an `.ok` state whose locals read `r ↦ 2^N`.  Proved by induction
    on the variant `N − i`, mirroring the EVM `powLoopCore`. -/
theorem powLoopActCore {cfg : Config} {C : ContractDecl} {evm : EVM.State} (N : ℕ) :
    ∀ (var i : ℕ) (L : Act.Store),
      N - i = var → i ≤ N →
      L.get? "i" = some (.int (Int.ofNat i)) →
      L.get? "r" = some (.int (Int.ofNat (2 ^ i))) →
      L.get? "n" = some (.int (Int.ofNat N)) →
      ∃ L', ExecStmt cfg { contract := C, locals := L } evm (.while powLoopCond powLoopBody)
              (.ok { contract := C, locals := L' } evm)
            ∧ L'.get? "r" = some (.int (Int.ofNat (2 ^ N))) := by
  intro var
  induction var with
  | zero =>
    intro i L hvar hile hi hr hn
    have hiN : i = N := by omega
    refine ⟨L, ExecStmt.whileFalse ?_, by rw [hr, hiN]⟩
    show evalExpr? cfg { contract := C, locals := L } evm powLoopCond = .ok (.bool false)
    rw [powLoopCond, evalLt hi hn]
    have hge : ¬ (Int.ofNat i < Int.ofNat N) := by simp only [Int.ofNat_eq_natCast, Nat.cast_lt]; omega
    rw [decide_eq_false hge]
  | succ var ih =>
    intro i L hvar hile hi hr hn
    have hilt : i < N := by omega
    have e1 : (Int.ofNat i + 1 : Int) = Int.ofNat (i + 1) := by
      simp only [Int.ofNat_eq_natCast]; push_cast; ring
    have e2 : (Int.ofNat (2 ^ i) * 2 : Int) = Int.ofNat (2 ^ (i + 1)) := by
      simp only [Int.ofNat_eq_natCast]; push_cast [pow_succ]; ring
    -- the two body `letDecl`s, producing locals L2
    set L1 := L.insert "r" (.int (Int.ofNat (2 ^ i) * 2)) with hL1
    set L2 := L1.insert "i" (.int (Int.ofNat i + 1)) with hL2
    have hL2i : L2.get? "i" = some (.int (Int.ofNat (i + 1))) := by
      rw [hL2, store_get_self, e1]
    have hL2r : L2.get? "r" = some (.int (Int.ofNat (2 ^ (i + 1)))) := by
      rw [hL2, store_get_ne _ _ (by decide), hL1, store_get_self, e2]
    have hL2n : L2.get? "n" = some (.int (Int.ofNat N)) := by
      rw [hL2, store_get_ne _ _ (by decide), hL1, store_get_ne _ _ (by decide), hn]
    -- run the body block to `.ok {locals := L2} evm`
    have hbody : ExecBlock cfg { contract := C, locals := L } evm powLoopBody
                   (.ok { contract := C, locals := L2 } evm) := by
      refine ExecBlock.consNormal (ExecStmt.letDecl ?_) (ExecBlock.consNormal (ExecStmt.letDecl ?_)
                ExecBlock.nil)
      · rw [evalMul2 hr]
      · show evalExpr? cfg { contract := C, locals := L1 } evm (.binary .add (.var "i") (.intLit 1))
            = .ok (.int (Int.ofNat i + 1))
        rw [evalAdd1 (by rw [hL1, store_get_ne _ _ (by decide), hi])]
    -- recurse via the IH at `i+1`
    obtain ⟨L', hwhile, hL'r⟩ := ih (i + 1) L2 (by omega) (by omega) hL2i hL2r hL2n
    refine ⟨L', ExecStmt.whileTrue ?_ hbody hwhile, hL'r⟩
    show evalExpr? cfg { contract := C, locals := L } evm powLoopCond = .ok (.bool true)
    rw [powLoopCond, evalLt hi hn]
    have hlt : Int.ofNat i < Int.ofNat N := by simp only [Int.ofNat_eq_natCast, Nat.cast_lt]; omega
    rw [decide_eq_true hlt]

/-! ## The Act body returns `2^n` (callvalue 0, n < 256) -/

/-- `require(callvalue == 0)` passes when the call value is zero. -/
theorem evalReqCV {cfg : Config} {C : ContractDecl} {L : Act.Store} {evm : EVM.State}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    evalExpr? cfg { contract := C, locals := L } evm
        (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) := by
  have hval : (Value.int (Int.ofNat evm.executionEnv.weiValue.val) == Value.int 0) = true := by
    rw [hwv]; rfl
  simp only [evalExpr?, EvalResult.bind, bind, envValue, evalBinaryOp?, hval]

/-- `require(n < 256)` passes when the argument is in range. -/
theorem evalReqN {cfg : Config} {C : ContractDecl} {L : Act.Store} {evm : EVM.State} {N : ℕ}
    (hn : L.get? "n" = some (.int (Int.ofNat N))) (hN : N < 256) :
    evalExpr? cfg { contract := C, locals := L } evm
        (.binary .lt (.var "n") (.intLit 256)) = .ok (.bool true) := by
  have h : (Int.ofNat N < (256 : Int)) := by simp only [Int.ofNat_eq_natCast]; omega
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption, hn]
  rw [decide_eq_true h]

/-- **The Act body computes `2^n`.**  With zero call value, `n < 256`, and the decoded argument
    `n ↦ N` in the locals, `pow2`'s body runs to `return (2^N)` (unbounded `Int`). -/
theorem powBodyReturns (evm : EVM.State) (locals : Act.Store) {N : ℕ}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hN : N < 256)
    (hn : locals.get? "n" = some (.int (Int.ofNat N))) :
    ∃ L', ExecContractBody powConfig Pow.powContract evm locals Pow.powTransition.body
            (.returned { contract := Pow.powContract, locals := L' } evm
              (some (.int (Int.ofNat (2 ^ N))))) := by
  -- locals after `r := 1` and `i := 0`
  set Lr := locals.insert "r" (.int 1) with hLr
  set Lri := Lr.insert "i" (.int 0) with hLri
  have hLri_i : Lri.get? "i" = some (.int (Int.ofNat 0)) := by rw [hLri, store_get_self]; rfl
  have hLri_r : Lri.get? "r" = some (.int (Int.ofNat (2 ^ 0))) := by
    rw [hLri, store_get_ne _ _ (by decide), hLr, store_get_self]; rfl
  have hLri_n : Lri.get? "n" = some (.int (Int.ofNat N)) := by
    rw [hLri, store_get_ne _ _ (by decide), hLr, store_get_ne _ _ (by decide), hn]
  -- run the loop
  obtain ⟨L', hwhile, hL'r⟩ :=
    powLoopActCore (cfg := powConfig) (C := Pow.powContract) (evm := evm) N
      N 0 Lri (by omega) (by omega) hLri_i hLri_r hLri_n
  refine ⟨L', ExecFuncBody.execBlockRet ?_⟩
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalReqCV hwv))
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalReqN hn hN))
    (ExecBlock.consNormal (ExecStmt.letDecl (value := .int 1) (by simp only [evalExpr?]; rfl))
    (ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?]; rfl))
    (ExecBlock.consNormal hwhile
    (ExecBlock.consReturn (ExecStmt.return (evalVar hL'r)))))))

/-! ## The Act body reverts (callvalue ≠ 0, or n ≥ 256) -/

/-- Non-zero call value ⇒ `require(callvalue == 0)` fails, body reverts. -/
theorem powBodyReverts_cv (evm : EVM.State) (locals : Act.Store)
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecContractBody powConfig Pow.powContract evm locals Pow.powTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse ?_))
  have hval : (Value.int (Int.ofNat evm.executionEnv.weiValue.val) == Value.int 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro hh
    rw [Value.int.injEq] at hh
    exact h (TruthClaude.Theory.uint256_toNat_eq_zero (Int.ofNat.inj hh))
  show evalExpr? powConfig _ evm (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool false)
  simp only [evalExpr?, EvalResult.bind, bind, pure, envValue, evalBinaryOp?, hval]

/-- `n ≥ 256` (with zero call value) ⇒ `require(n < 256)` fails, body reverts. -/
theorem powBodyReverts_n (evm : EVM.State) (locals : Act.Store) {N : ℕ}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hN : 256 ≤ N)
    (hn : locals.get? "n" = some (.int (Int.ofNat N))) :
    ExecContractBody powConfig Pow.powContract evm locals Pow.powTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert (ExecBlock.consNormal (ExecStmt.requireTrue (evalReqCV hwv))
    (ExecBlock.consRevert (ExecStmt.requireFalse ?_)))
  have h : ¬ (Int.ofNat N < (256 : Int)) := by simp only [Int.ofNat_eq_natCast]; omega
  show evalExpr? powConfig _ evm (.binary .lt (.var "n") (.intLit 256)) = .ok (.bool false)
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption, hn]
  rw [decide_eq_false h]

/-! ## ABI encoding of the `uint256` return value `2^n` -/

/-- `EVM.word` and `UInt256.ofNat` agree (both are `⟨n % 2^256⟩`). -/
theorem evm_word_eq_ofNat (n : ℕ) : EVM.word n = UInt256.ofNat n := rfl

/-- The 32-byte big-endian ABI encoding of `2^N` (for `N < 256`, so it fits a word) is exactly the
    EVM `RETURN` word `UInt256.ofNat (2^N)`. -/
theorem powReturnEncoding {N : ℕ} (hN : N < 256) :
    encodeReturnValue? Pow.uint256 (.int (Int.ofNat (2 ^ N)))
      = some (UInt256.toByteArray (UInt256.ofNat (2 ^ N))) := by
  have hlt : Int.ofNat (2 ^ N) < Int.ofNat (EVM.twoPow 256) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_lt, EVM.twoPow]
    exact Nat.pow_lt_pow_right (by norm_num) hN
  -- the single ABI value encodes to the 32 big-endian bytes of `ofNat (2^N)`
  have hval : encodeABIValue? Pow.uint256 (.int (Int.ofNat (2 ^ N)))
                = some (EVM.Word.toBytesBE (UInt256.ofNat (2 ^ N))) := by
    simp only [Pow.uint256, encodeABIValue?, encodeABIWord?]
    rw [if_neg (by decide), if_pos ⟨Int.natCast_nonneg _, hlt⟩, evm_word_eq_ofNat]; rfl
  have hdyn : isDynamicABIType Pow.uint256 = false := rfl
  have hhead : abiTupleHeadSize? [Pow.uint256] = some 32 := by
    simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, Pow.uint256, bind,
      Option.bind]
    decide
  rw [toByteArray_eq_toBytesBE,
    show encodeReturnValue? Pow.uint256 (.int (Int.ofNat (2 ^ N)))
        = encodeReturnValues? [Pow.uint256] [.int (Int.ofNat (2 ^ N))] from rfl]
  simp only [encodeReturnValues?, encodeABIValues?, hhead, encodeABIValuesFrom?, hval, hdyn,
    bind, Option.bind, if_false, Bool.false_eq_true, List.nil_append, List.append_nil]

/-! ## The runtime-equivalence assembly -/

/-- The dispatched transition's `n`-store the decoder produces. -/
private def powCallargs (I : Ethereum.ExecutionEnv) : Act.Store :=
  (∅ : Act.Store).insert "n"
    (.int (Int.ofNat (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat))

/-- **`callvalue = 0` case**: split on calldata size and the selector to land in one of
    `noDispatch` / `decodingFailed` / `execution`. -/
theorem powReEquiv_callvalueZero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) :
    runtimeEquivalenceFor powConfig Pow.powContract cA gh bl σ σ₀ g A I := by
  by_cases hsz4 : I.calldata.size < 4
  · rcases powXi_short hcode hwv hsz4 with hoog | ⟨g', o, hrev⟩
    · exact reEquiv_outOfGas hoog
    · exact reEquiv_noDispatch (powDispatch_none_short hsz4) hrev
  · rw [not_lt] at hsz4
    by_cases hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true
    · have hd : dispatchMsg Pow.powContract I.calldata = some Pow.powTransition := by
        rw [powDispatch_eq, if_pos hmatch]
      by_cases hsz36 : I.calldata.size < 36
      · -- decode fails ⇒ decodingFailed
        rcases powXi_shortarg hcode hwv hsz4 hsz36 hmatch with hoog | ⟨g', o, hrev⟩
        · exact reEquiv_outOfGas hoog
        · exact reEquiv_decodingFailed hd (powDecode_none hsz36) hrev
      · rw [not_lt] at hsz36
        by_cases hbig : 2 ^ 255 + 4 ≤ I.calldata.size
        · -- huge calldata: solc's signed `SLT(size−4,32)` reverts (decoder), Act decode fails too
          rcases powXi_hugearg hcode hwv hbig hsize hmatch with hoog | ⟨g', o, hrev⟩
          · exact reEquiv_outOfGas hoog
          · exact reEquiv_decodingFailed hd (powDecode_none_huge hbig) hrev
        · rw [not_le] at hbig
          by_cases hn : (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat < 256
          · -- success
            rcases powXi_success hcode hwv hsz36 hbig hmatch hn with hoog | ⟨g', A', hsucc⟩
            · exact reEquiv_outOfGas hoog
            · obtain ⟨L', hbody⟩ := powBodyReturns (initState cA gh bl σ σ₀ g A I) (powCallargs I)
                (by simp only [initState]; exact hwv) hn (by rw [powCallargs, store_get_self])
              refine reEquiv_execution hd (powDecode_n hsz36 hbig) hbody ?_
              rw [hsucc]
              exact execResultsEquiv.success rfl rfl rfl rfl
                (returnEquiv.returned rfl rfl (powReturnEncoding hn))
          · -- n ≥ 256 ⇒ body reverts (execution)
            rw [not_lt] at hn
            rcases powXi_nlarge hcode hwv hsz36 hbig hmatch hn with hoog | ⟨g', o, hrev⟩
            · exact reEquiv_outOfGas hoog
            · refine reEquiv_execution hd (powDecode_n hsz36 hbig)
                (powBodyReverts_n (initState cA gh bl σ σ₀ g A I) (powCallargs I)
                  (by simp only [initState]; exact hwv) hn (by rw [powCallargs, store_get_self])) ?_
              rw [hrev]; exact execResultsEquiv.revert rfl rfl
    · -- wrong selector ⇒ noDispatch
      rw [Bool.not_eq_true] at hmatch
      rcases powXi_nomatch hcode hwv hsz4 hsize hmatch with hoog | ⟨g', o, hrev⟩
      · exact reEquiv_outOfGas hoog
      · exact reEquiv_noDispatch (powDispatch_none_nomatch hmatch) hrev

/-- **Runtime equivalence of `Pow.sol`'s `pow2` bytecode and its Act specification.** -/
theorem powCorrect : runtimeEquivalence!?! powConfig powBytecode Pow.powContract := by
  refine ⟨fun cA gh bl σ σ₀ g A I hcode hsize => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact powReEquiv_callvalueZero hcode hwv hsize
  · rcases powXi_callvalue_ne hcode hwv with hoog | ⟨g', o, hrev⟩
    · exact reEquiv_outOfGas hoog
    · by_cases hdisp : dispatchMsg Pow.powContract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        cases powDispatch_unique ht
        by_cases hdec : decodeCalldata (Pow.powTransition.params.map Param.name)
            (transitionSignature Pow.powTransition).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          refine reEquiv_execution ht hca
            (powBodyReverts_cv (initState cA gh bl σ σ₀ g A I) callargs ?_) ?_
          · show (initState cA gh bl σ σ₀ g A I).executionEnv.weiValue ≠ ⟨0⟩
            simp only [initState]; exact hwv
          · rw [hrev]; exact execResultsEquiv.revert rfl rfl

end TruthClaude
