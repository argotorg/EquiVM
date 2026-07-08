import Benchmarks.Dss.Cat.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cat

/-!
# Cat `bite(bytes32,address)` — `vat.ilks(ilk)` external-call helper

The `bite` routine's first sub-call is `STATICCALL vat.ilks(ilk)` (a `view` function →
`perm := false`).  From the routine entry at pc `1163` (stack `[urn, ilk, 419, sel]`, memory
`solcFreePtrMem`) solc builds the calldata `ilks(bytes32)` in scratch memory `[0x80..0xa4)`, guards
the target code size (`EXTCODESIZE` @1233), and issues the `STATICCALL` @1248 requesting a 5-word
(`0xa0`) return window at `0x80`.

This file provides:
* the **memory-encoding coupling** (`catBiteIlksEncode_eq`): the bytes solc places in memory equal
  `config.externalABI.encode? "ilks" [ilk]`;
* the **reusable call combinators** (`RD.catBiteIlks*`) that step guard + `STATICCALL` and produce
  the `Θ`/`typedCallViaEVM` witness (STATICCALL preserves this-storage via
  `typedCallViaEVM_static_storage_findD_of_accountMapEquiv`), or `RDrev` on the missing-code / call-
  failure branches.

The definitions are parametrised over the ilk word `ilk : UInt256`, so the trace agent can apply the
combinators with the concrete calldata ilk carried on the stack.
-/

/-! ## Selector / pointer constants (solc computes `ilks` selector as `0x6cb1c69b << 225`). -/

abbrev catBiteIlksSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨1823590043⟩ ⟨225⟩

/-- `0xd9638d36` — the `ilks(bytes32)` selector. -/
abbrev catBiteIlksSelectorWord : UInt256 :=
  ⟨3647180086⟩

abbrev catBiteIlksOutPtr : UInt256 := ⟨128⟩

abbrev catBiteIlksInSize : UInt256 :=
  UInt256.add (UInt256.sub catBiteIlksOutPtr catBiteIlksOutPtr) ⟨36⟩

abbrev catBiteIlksEndPtr : UInt256 :=
  UInt256.add catBiteIlksOutPtr ⟨36⟩

/-- The `ilks` return window is 5 words (`0xa0`). -/
abbrev catBiteIlksOutSize : UInt256 := ⟨160⟩

/-- The `vat` address (slot 3, `addrLoc`) masked to 160 bits — the STATICCALL target. -/
abbrev catBiteVatTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  catAddressReturnWord ⟨3⟩ σ I

/-! ## Scratch-memory calldata layout (`selector @0x80`, `ilk @0x84`). -/

noncomputable def catBiteIlksSelectorMem (mem : ByteArray) : ByteArray :=
  catBiteIlksSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def catBiteIlksCalldataMem (ilk : UInt256) (mem : ByteArray) : ByteArray :=
  ilk.toByteArray.write 0 (catBiteIlksSelectorMem mem) 132 32

theorem catBiteIlksSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (catBiteIlksSelectorMem mem).size = 160 := by
  unfold catBiteIlksSelectorMem
  exact toByteArray_write32_size_of_ge mem catBiteIlksSelectorShifted 128 96 160 hmem
    (by omega) (by native_decide) (by omega)

theorem catBiteIlksSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (catBiteIlksSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold catBiteIlksSelectorMem
  rw [toByteArray_write_read_below_of_gap catBiteIlksSelectorShifted mem 128 64
    (by rw [hmem]) (by omega) (by rw [hmem]; native_decide), hread64]

theorem catBiteIlksCalldataMem_size (ilk : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (catBiteIlksCalldataMem ilk mem).size = 164 := by
  unfold catBiteIlksCalldataMem
  exact toByteArray_write32_size_of_le (catBiteIlksSelectorMem mem) ilk
    132 160 164 (catBiteIlksSelectorMem_size hmem)
    (by rw [catBiteIlksSelectorMem_size hmem]; omega) (by omega)

theorem catBiteIlksCalldataMem_read64 (ilk : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (catBiteIlksCalldataMem ilk mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold catBiteIlksCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [catBiteIlksSelectorMem_size hmem]; omega) (by omega),
    catBiteIlksSelectorMem_read64 hmem hread64]

theorem catBiteIlksSelectorMem_selector {mem : ByteArray} (hmem : mem.size = 96) :
    (catBiteIlksSelectorMem mem).extract 128 132 = vatIlksSelector := by
  unfold catBiteIlksSelectorMem
  have hgap : 128 - mem.size < USize.size := by
    rw [hmem]; native_decide
  rw [toByteArray_write_eq catBiteIlksSelectorShifted mem 128 (by omega) hgap]
  have hprefix :
      (mem ++ ffi.ByteArray.zeroes (USize.ofNat (128 - mem.size))).size = 128 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size,
      USize.toNat_ofNat_of_lt' hgap, hmem]
  rw [extract_append_right_window _ _ 128 132 (by rw [hprefix]), hprefix,
    show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    toByteArray_eq_toBytesBE]
  native_decide

theorem catBiteIlksCalldataMem_read128_36 (ilk : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (catBiteIlksCalldataMem ilk mem).readWithPadding 128 36 =
      vatIlksSelector ++ ilk.toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [catBiteIlksCalldataMem_size ilk hmem]), catBiteIlksCalldataMem,
    write32_eq _ (catBiteIlksSelectorMem mem) 132 (by rw [toByteArray_size])
      (by rw [catBiteIlksSelectorMem_size hmem]; omega)]
  have hAsz : ((catBiteIlksSelectorMem mem).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, catBiteIlksSelectorMem_size hmem]; omega
  have hBsz : (ilk.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]; omega
  have hPsz :
      ((catBiteIlksSelectorMem mem).extract 0 132 ++ ilk.toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : ilk.toByteArray.extract 0 32 = ilk.toByteArray := by
    have h := @ByteArray.extract_zero_size ilk.toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), catBiteIlksSelectorMem_selector hmem,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

/-- **Memory-encoding coupling.**  Given the ilk word `ilk` and its big-endian byte view `ilkBytes`
(the calldata slice), the scratch-memory calldata equals `encode? "ilks" [ilk]`. -/
theorem catBiteIlksEncode_eq (ilk : UInt256) (ilkBytes : List UInt8) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hbytes : ilkBytes = EVM.Word.toBytesBE ilk) :
    config.externalABI.encode? "ilks" [.fixedBytes bytes32Width ilkBytes] =
      some ((catBiteIlksCalldataMem ilk mem).readWithPadding
        catBiteIlksOutPtr.toNat catBiteIlksInSize.toNat) := by
  change config.externalABI.encode? "ilks" [.fixedBytes bytes32Width ilkBytes] =
    some ((catBiteIlksCalldataMem ilk mem).readWithPadding 128 36)
  rw [catBiteIlksCalldataMem_read128_36 ilk hmem]
  have hlen : (EVM.Word.toBytesBE ilk).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size ilk
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, vatIlksSelector,
    selectorBytes, hbytes, hlen, ABI.zeroBytes, word_toBytesBE_toByteArray_eq_toByteArray]

/-! ## Guard + `STATICCALL` combinators -/

/-- Step the `vat.ilks` calldata build + `EXTCODESIZE` guard site.  From the `bite` routine entry
(`pc 1163`, stack `[urn, ilk] ++ R`, memory `solcFreePtrMem`) to the `EXTCODESIZE` @1233 with the
target duplicated on top and the `STATICCALL` argument frame assembled below. -/
theorem RD.catBiteIlksToStaticcallGuard
    {cA gh bl σ σ₀ A I} {g : UInt256} {urn ilk : UInt256} {R : List UInt256} {k C : ℕ}
    (hR : R.length + 16 ≤ 1024)
    (rd1163 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1163⟩
      (urn :: ilk :: R) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1233⟩
      (catBiteVatTargetWord σ I :: catBiteVatTargetWord σ I ::
        catBiteIlksOutPtr :: catBiteIlksInSize :: catBiteIlksOutPtr :: catBiteIlksOutSize ::
        catBiteIlksEndPtr :: catBiteIlksSelectorWord :: catBiteVatTargetWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: urn :: ilk :: R)
      (catBiteIlksCalldataMem ilk solcFreePtrMem) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  have htargetMask :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        (catSlotWord ⟨3⟩ σ I) = catBiteVatTargetWord σ I := by
    have hmask :
        UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
      native_decide
    show UInt256.land _ (catSlotWord ⟨3⟩ σ I) =
      UInt256.land (catSlotWord ⟨3⟩ σ I) solcAddrMask
    rw [u256_land_comm, hmask]
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide) solcFreePtrMem_read64
  have hcallMem : (catBiteIlksCalldataMem ilk solcFreePtrMem).size = 164 :=
    catBiteIlksCalldataMem_size ilk solcFreePtrMem_size
  have hcallRead64 :
      (catBiteIlksCalldataMem ilk solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    catBiteIlksCalldataMem_read64 ilk solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (catBiteIlksCalldataMem ilk solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
      (fromByteArrayBigEndian
          ((catBiteIlksCalldataMem ilk solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have rd1164 := rd1163.jumpdest (by native_decide) (by evm_ov)
  have rd1166 := rd1164.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1167, C1167, rd1167raw⟩ := rd1166.sload (by native_decide) (by evm_ov)
  have rd1167 : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1167⟩
      (catSlotWord ⟨3⟩ σ I :: urn :: ilk :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1167 C1167 := by
    simpa [catSlotWord, solcSlotWord] using rd1167raw
  have rd1233 := evm_run rd1167 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨1823590043⟩,
    push1 ⟨225⟩,
    shl,
    dup2,
    raw mstore 6 (catBiteIlksSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩,
    dup2,
    add,
    dup6,
    swap1,
    raw mstore 3 (catBiteIlksCalldataMem ilk solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    push1 ⟨0⟩,
    swap3,
    dup4,
    swap3,
    dup4,
    swap3,
    dup4,
    swap3,
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    and,
    swap2,
    push4 ⟨3647180086⟩,
    swap2,
    push1 ⟨36⟩,
    dup1,
    dup4,
    add,
    swap3,
    push1 ⟨160⟩,
    swap3,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup7,
    dup1]
  exact ⟨_, _, by
    simpa [catBiteIlksOutPtr, catBiteIlksInSize, catBiteIlksOutSize, catBiteIlksEndPtr,
      catBiteIlksSelectorWord, htargetMask] using rd1233⟩

end Benchmarks.Dss.Cat
