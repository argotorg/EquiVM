import TruthClaude.PowSegments

/-!
# Pow — Act-side coupling and the final `powCorrect` statement

The EVM-side forward trace, success composition, and `Ξ` lift live in `PowSegments`/`PowCorrect`.
This file carries the **Act-level** facts (dispatch, calldata decode, return encoding, the body
execution including the `while` loop) and assembles the runtime-equivalence theorem.
-/

open Act ABI Ethereum Ethereum.EVM TruthClaude.Theory TruthClaude.Reach

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
    RDrev powBytecode g (initState cA gh bl σ σ₀ g A I) := by
  -- prologue → PUSH2 0x0f · JUMPI (not taken: callvalue ≠ 0 ⇒ iszero = 0) → revert stub, one `RD`
  exact solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      |>.push2 ⟨15⟩ (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.jumpiNT (by decide) (isZero_eq_zero_of_ne hwv)
        (by simp only [List.length_cons, List.length_nil]; omega)
      |>.push0 (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.push0 (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.rev 0 (by decide) (fun s _ hstks => memExpRevert0 s hstks)
        (by simp only [List.length_cons, List.length_nil]; omega)

/-- Lift any `X`-level revert/OOG result to `Ξ`. -/
theorem powXi_of_revert {cA gh bl σ σ₀ A I} {g : UInt256} (hcode : I.code = powBytecode)
    (h : RDrev powBytecode g (initState cA gh bl σ σ₀ g A I)) :
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
    RDrev powBytecode g (initState cA gh bl σ σ₀ g A I) := by
  -- prologue → guard JUMPI (taken, cv=0) → JUMPDEST·POP·PUSH1 4·CALLDATASIZE·LT (=1, size<4)·PUSH2 41·
  --   JUMPI (taken → 41)·JUMPDEST → revert stub at pc 42, as one `RD`
  exact solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        |>.push2 ⟨15⟩ (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
        |>.jumpiT (by decide) (by rw [hwv]; decide)
          (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
          (by simp only [List.length_cons, List.length_nil]; omega)
        |>.jumpdest (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
        |>.pop (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
        |>.push1 ⟨4⟩ (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
        |>.calldatasize (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
        |>.lt (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
        |>.push2 ⟨41⟩ (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
        |>.jumpiT (by decide)
          (by rw [ult_one (by rw [ulit_toNat' _ (lt_size_of_lt256 (by omega)),
            show (⟨4⟩ : UInt256).toNat = 4 from by decide]; omega)]; decide)
          (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
          (by simp only [List.length_cons, List.length_nil]; omega)
        |>.jumpdest (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
        |>.push0 (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
        |>.push0 (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
        |>.rev 0 (by decide) (fun s _ hstks => memExpRevert0 s hstks)
          (by simp only [List.length_cons, List.length_nil]; omega)

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
    RDrev powBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsize : I.calldata.size < UInt256.size := by
    have h0 : (2:ℕ)^255 + 4 < 2^256 := by norm_num
    have hp : (2:ℕ)^255 + 4 < UInt256.size := by simpa [UInt256.size] using h0
    omega
  set sel := UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ with hsel
  set arg := uInt256OfByteArray (I.calldata.readBytes 4 32) with harg
  have hsltval0 : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ := by
    apply slt32_zero <;> (rw [sub4_toNat (by omega) hsize]; omega)
  have h256 : (⟨256⟩ : UInt256).toNat = 256 := by
    show (Fin.ofNat _ 256).val = 256; simp only [Fin.ofNat]
    exact Nat.mod_eq_of_lt (by have := pow_lt_size (show (8:ℕ) < 256 by norm_num); norm_num at this; exact this)
  have hltval : UInt256.lt arg ⟨256⟩ = ⟨0⟩ := ult_zero (by rw [h256]; exact hn)
  -- dispatcher → decoder → cf → require-revert (n ≥ 256), threaded as one `RD` ⇒ `RDrev`
  have rdDec := powX_disp (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
        hcode hwv (by omega) hsize hmatch
      |>.routinedecodeToCf (by omega) hsize
      |>.routinecf hsltval0 (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
          (by simp only [List.length_cons, List.length_nil]; omega)
  rw [show ((⟨4⟩ : UInt256) + ⟨0⟩).toNat = 4 from add40_toNat, ← harg] at rdDec
  exact rdDec |>.routinerequire_revert hltval (by simp only [List.length_nil]; omega)

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
    RDrev powBytecode g (initState cA gh bl σ σ₀ g A I) := by
  -- selector compare resolves to `0` (mismatch); the dispatch JUMPI falls through to the revert stub
  have rd := powX_dispToEq (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsz hsize
  rw [show UInt256.eq ⟨1143701499⟩
        (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩) = ⟨0⟩
      from by rw [powEvmSelector hsz, if_neg (by rw [hmatch]; decide)]] at rd
  exact rd
      |>.push2 ⟨45⟩ (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.jumpiNT (by decide) rfl (by simp only [List.length_cons, List.length_nil]; omega)
      |>.jumpdest (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.push0 (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.push0 (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.rev 0 (by decide) (fun s _ hstks => memExpRevert0 s hstks)
        (by simp only [List.length_cons, List.length_nil]; omega)

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
    RDrev powBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsize : I.calldata.size < UInt256.size := lt_size_of_lt256 (by omega)
  have hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply slt32_one; rw [sub4_toNat (by omega) hsize]; omega
  -- dispatcher → decoder set-up → Cf-revert (SLT bounds check fails), threaded as one `RD` ⇒ `RDrev`
  exact powX_disp hcode hwv hsz4 hsize hmatch
      |>.routinedecodeToCf (by omega) hsize
      |>.routinecf_revert hsltval (by simp only [List.length_cons, List.length_nil]; omega)

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
    RDrev powBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply slt32_one_high; rw [sub4_toNat (by omega) hsize]; omega
  -- dispatcher → decoder set-up → Cf-revert (SLT bounds check fails), threaded as one `RD` ⇒ `RDrev`
  exact powX_disp hcode hwv (by omega) hsize hmatch
      |>.routinedecodeToCf (by omega) hsize
      |>.routinecf_revert hsltval (by simp only [List.length_cons, List.length_nil]; omega)

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
