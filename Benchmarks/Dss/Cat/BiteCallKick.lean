import Benchmarks.Dss.Cat.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cat

/-!
# Cat `bite` — external `milkFlip.kick(urn, vow, tab, dink, 0)` call helper

Memory-encoding coupling and the reusable RD stepping lemma for the last external call in `bite`:
`id = milkFlip.kick(urn, vow, tab, dink, 0)` — a `perm := true` `CALL` with five 32-byte
static arguments (`address, address, uint256, uint256, uint256`).

The solc scratch layout at the call site (free pointer `0x80`):

```
[128,132)  selector 0x351de600
[132,164)  urn   & addrMask   (address)
[164,196)  vow   & addrMask   (address)
[196,228)  tab                (uint256)
[228,260)  dink               (uint256)
[260,292)  0                  (uint256)
```

so `inOffset = 128`, `inSize = 164`, `outOffset = 128`, `outSize = 32`.

PCs: EXTCODESIZE guard `2516`, guard-ok `JUMPDEST 2528`, `CALL 2531`, success guard `ISZERO 2532`,
success-ok `JUMPDEST 2548`, first return-decode instruction `2550`.
Selector `0x351de600` = `891151872`.
-/

/-! ## Memory-encoding coupling -/

abbrev kickSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨891151872⟩ ⟨224⟩

/-- Word `0x351de600` written at scratch offset `128`. -/
noncomputable def kickSelectorMem (mem : ByteArray) : ByteArray :=
  kickSelectorShifted.toByteArray.write 0 mem 128 32

/-- The full 164-byte `kick` calldata written over `mem` (selector + five argument words). -/
noncomputable def kickCalldataMem (urn vow tab dink : UInt256) (mem : ByteArray) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0
    (dink.toByteArray.write 0
      (tab.toByteArray.write 0
        (vow.toByteArray.write 0
          (urn.toByteArray.write 0 (kickSelectorMem mem) 132 32)
          164 32)
        196 32)
      228 32)
    260 32

theorem kickSelectorMem_size {mem : ByteArray} (hmem : 292 ≤ mem.size) :
    (kickSelectorMem mem).size = mem.size := by
  unfold kickSelectorMem
  exact toByteArray_write32_size_of_le mem kickSelectorShifted 128 mem.size mem.size rfl
    (by omega) (by omega)

theorem kickCalldataMem_size (urn vow tab dink : UInt256) {mem : ByteArray}
    (hmem : 292 ≤ mem.size) :
    (kickCalldataMem urn vow tab dink mem).size = mem.size := by
  have h0 := kickSelectorMem_size hmem
  unfold kickCalldataMem
  have h1 : (urn.toByteArray.write 0 (kickSelectorMem mem) 132 32).size = mem.size :=
    toByteArray_write32_size_of_le _ urn 132 mem.size mem.size h0 (by omega) (by omega)
  have h2 : (vow.toByteArray.write 0 (urn.toByteArray.write 0 (kickSelectorMem mem) 132 32)
      164 32).size = mem.size :=
    toByteArray_write32_size_of_le _ vow 164 mem.size mem.size h1 (by omega) (by omega)
  have h3 : (tab.toByteArray.write 0 (vow.toByteArray.write 0
      (urn.toByteArray.write 0 (kickSelectorMem mem) 132 32) 164 32) 196 32).size = mem.size :=
    toByteArray_write32_size_of_le _ tab 196 mem.size mem.size h2 (by omega) (by omega)
  have h4 : (dink.toByteArray.write 0 (tab.toByteArray.write 0 (vow.toByteArray.write 0
      (urn.toByteArray.write 0 (kickSelectorMem mem) 132 32) 164 32) 196 32) 228 32).size
        = mem.size :=
    toByteArray_write32_size_of_le _ dink 228 mem.size mem.size h3 (by omega) (by omega)
  exact toByteArray_write32_size_of_le _ ⟨0⟩ 260 mem.size mem.size h4 (by omega) (by omega)

theorem kickCalldataMem_size_aux1 (urn vow tab dink : UInt256) {mem : ByteArray}
    (hmem : 292 ≤ mem.size) :
    (urn.toByteArray.write 0 (kickSelectorMem mem) 132 32).size = mem.size :=
  toByteArray_write32_size_of_le _ urn 132 mem.size mem.size (kickSelectorMem_size hmem)
    (by rw [kickSelectorMem_size hmem]; omega) (by omega)

theorem kickCalldataMem_size_aux2 (urn vow tab dink : UInt256) {mem : ByteArray}
    (hmem : 292 ≤ mem.size) :
    (vow.toByteArray.write 0 (urn.toByteArray.write 0 (kickSelectorMem mem) 132 32)
      164 32).size = mem.size :=
  toByteArray_write32_size_of_le _ vow 164 mem.size mem.size
    (kickCalldataMem_size_aux1 urn vow tab dink hmem)
    (by rw [kickCalldataMem_size_aux1 urn vow tab dink hmem]; omega) (by omega)

theorem kickCalldataMem_size_aux3 (urn vow tab dink : UInt256) {mem : ByteArray}
    (hmem : 292 ≤ mem.size) :
    (tab.toByteArray.write 0 (vow.toByteArray.write 0
      (urn.toByteArray.write 0 (kickSelectorMem mem) 132 32) 164 32) 196 32).size = mem.size :=
  toByteArray_write32_size_of_le _ tab 196 mem.size mem.size
    (kickCalldataMem_size_aux2 urn vow tab dink hmem)
    (by rw [kickCalldataMem_size_aux2 urn vow tab dink hmem]; omega) (by omega)

theorem kickCalldataMem_size_aux4 (urn vow tab dink : UInt256) {mem : ByteArray}
    (hmem : 292 ≤ mem.size) :
    (dink.toByteArray.write 0 (tab.toByteArray.write 0 (vow.toByteArray.write 0
      (urn.toByteArray.write 0 (kickSelectorMem mem) 132 32) 164 32) 196 32) 228 32).size
        = mem.size :=
  toByteArray_write32_size_of_le _ dink 228 mem.size mem.size
    (kickCalldataMem_size_aux3 urn vow tab dink hmem)
    (by rw [kickCalldataMem_size_aux3 urn vow tab dink hmem]; omega) (by omega)

theorem kickSelectorMem_read64 {mem : ByteArray} (hmem : 292 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (kickSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold kickSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size]) (by omega) (by omega), hread64]

theorem kickCalldataMem_read64 (urn vow tab dink : UInt256) {mem : ByteArray}
    (hmem : 292 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (kickCalldataMem urn vow tab dink mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  have h0 := kickSelectorMem_size hmem
  have h0r := kickSelectorMem_read64 hmem hread64
  unfold kickCalldataMem
  rw [write32_read_below _ _ 260 64 (by rw [toByteArray_size])
      (by rw [kickCalldataMem_size_aux4 urn vow tab dink hmem]; omega) (by omega),
    write32_read_below _ _ 228 64 (by rw [toByteArray_size])
      (by rw [kickCalldataMem_size_aux3 urn vow tab dink hmem]; omega) (by omega),
    write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [kickCalldataMem_size_aux2 urn vow tab dink hmem]; omega) (by omega),
    write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [kickCalldataMem_size_aux1 urn vow tab dink hmem]; omega) (by omega),
    write32_read_below _ _ 132 64 (by rw [toByteArray_size]) (by rw [h0]; omega) (by omega),
    h0r]

/-- The `kick` selector word occupies the first four bytes of the scratch. -/
theorem kickSelectorMem_selector {mem : ByteArray} (hmem : 292 ≤ mem.size) :
    (kickSelectorMem mem).extract 128 132 = kickerKickSelector := by
  have hread : (kickSelectorMem mem).readWithPadding 128 4 = kickerKickSelector := by
    unfold kickSelectorMem
    rw [write32_read_prefix_len _ _ 128 4 (by rw [toByteArray_size]) (by omega)
      (by omega) (by omega) (by norm_num)]
    unfold kickSelectorShifted kickerKickSelector selectorBytes
    native_decide
  rw [readWithPadding_eq_extract' _ 128 4 (by norm_num) (by norm_num)
      (by rw [kickSelectorMem_size hmem]; omega)] at hread
  simpa using hread

theorem kickCalldataMem_read128_164 (urn vow tab dink : UInt256) {mem : ByteArray}
    (hmem : 292 ≤ mem.size) :
    (kickCalldataMem urn vow tab dink mem).readWithPadding 128 164 =
      kickerKickSelector ++ urn.toByteArray ++ vow.toByteArray ++ tab.toByteArray ++
        dink.toByteArray ++ (⟨0⟩ : UInt256).toByteArray := by
  let final := kickCalldataMem urn vow tab dink mem
  have hfinalSize : final.size = mem.size := kickCalldataMem_size urn vow tab dink hmem
  have h0 := kickSelectorMem_size hmem
  have s1 := kickCalldataMem_size_aux1 urn vow tab dink hmem
  have s2 := kickCalldataMem_size_aux2 urn vow tab dink hmem
  have s3 := kickCalldataMem_size_aux3 urn vow tab dink hmem
  have s4 := kickCalldataMem_size_aux4 urn vow tab dink hmem
  -- selector [128,132)
  have hselRead : final.readWithPadding 128 4 = kickerKickSelector := by
    show (kickCalldataMem urn vow tab dink mem).readWithPadding 128 4 = kickerKickSelector
    unfold kickCalldataMem
    rw [write32_read_below_len _ _ 260 128 4 (by rw [toByteArray_size]) (by rw [s4]; omega)
        (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ 228 128 4 (by rw [toByteArray_size]) (by rw [s3]; omega)
        (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size]) (by rw [s2]; omega)
        (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size]) (by rw [s1]; omega)
        (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size]) (by rw [h0]; omega)
        (by omega) (by omega) (by omega) (by norm_num)]
    have := kickSelectorMem_selector hmem
    rw [readWithPadding_eq_extract' _ 128 4 (by norm_num) (by norm_num)
      (by rw [h0]; omega)]
    simpa using this
  -- urn [132,164)
  have hurnRead : final.readWithPadding 132 32 = urn.toByteArray := by
    show (kickCalldataMem urn vow tab dink mem).readWithPadding 132 32 = urn.toByteArray
    unfold kickCalldataMem
    rw [write32_read_below_len _ _ 260 132 32 (by rw [toByteArray_size]) (by rw [s4]; omega)
        (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ 228 132 32 (by rw [toByteArray_size]) (by rw [s3]; omega)
        (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ 196 132 32 (by rw [toByteArray_size]) (by rw [s2]; omega)
        (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ 164 132 32 (by rw [toByteArray_size]) (by rw [s1]; omega)
        (by omega) (by omega) (by omega) (by norm_num),
      write32_read_back _ _ 132 (by rw [toByteArray_size]) (by rw [h0]; omega),
      toByteArray_extract_all]
  -- vow [164,196)
  have hvowRead : final.readWithPadding 164 32 = vow.toByteArray := by
    show (kickCalldataMem urn vow tab dink mem).readWithPadding 164 32 = vow.toByteArray
    unfold kickCalldataMem
    rw [write32_read_below_len _ _ 260 164 32 (by rw [toByteArray_size]) (by rw [s4]; omega)
        (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ 228 164 32 (by rw [toByteArray_size]) (by rw [s3]; omega)
        (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ 196 164 32 (by rw [toByteArray_size]) (by rw [s2]; omega)
        (by omega) (by omega) (by omega) (by norm_num),
      write32_read_back _ _ 164 (by rw [toByteArray_size]) (by rw [s1]; omega),
      toByteArray_extract_all]
  -- tab [196,228)
  have htabRead : final.readWithPadding 196 32 = tab.toByteArray := by
    show (kickCalldataMem urn vow tab dink mem).readWithPadding 196 32 = tab.toByteArray
    unfold kickCalldataMem
    rw [write32_read_below_len _ _ 260 196 32 (by rw [toByteArray_size]) (by rw [s4]; omega)
        (by omega) (by omega) (by omega) (by norm_num),
      write32_read_below_len _ _ 228 196 32 (by rw [toByteArray_size]) (by rw [s3]; omega)
        (by omega) (by omega) (by omega) (by norm_num),
      write32_read_back _ _ 196 (by rw [toByteArray_size]) (by rw [s2]; omega),
      toByteArray_extract_all]
  -- dink [228,260)
  have hdinkRead : final.readWithPadding 228 32 = dink.toByteArray := by
    show (kickCalldataMem urn vow tab dink mem).readWithPadding 228 32 = dink.toByteArray
    unfold kickCalldataMem
    rw [write32_read_below_len _ _ 260 228 32 (by rw [toByteArray_size]) (by rw [s4]; omega)
        (by omega) (by omega) (by omega) (by norm_num),
      write32_read_back _ _ 228 (by rw [toByteArray_size]) (by rw [s3]; omega),
      toByteArray_extract_all]
  -- 0 [260,292)
  have hzeroRead : final.readWithPadding 260 32 = (⟨0⟩ : UInt256).toByteArray := by
    show (kickCalldataMem urn vow tab dink mem).readWithPadding 260 32 =
      (⟨0⟩ : UInt256).toByteArray
    unfold kickCalldataMem
    rw [write32_read_back _ _ 260 (by rw [toByteArray_size]) (by rw [s4]; omega),
      toByteArray_extract_all]
  -- assemble
  rw [readWithPadding_eq_extract' final 128 164 (by norm_num) (by norm_num)
    (by rw [hfinalSize]; omega)]
  have hselExt : final.extract 128 132 = kickerKickSelector := by
    rw [← readWithPadding_eq_extract' final 128 4 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hselRead
  have hurnExt : final.extract 132 164 = urn.toByteArray := by
    rw [← readWithPadding_eq_extract' final 132 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hurnRead
  have hvowExt : final.extract 164 196 = vow.toByteArray := by
    rw [← readWithPadding_eq_extract' final 164 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hvowRead
  have htabExt : final.extract 196 228 = tab.toByteArray := by
    rw [← readWithPadding_eq_extract' final 196 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact htabRead
  have hdinkExt : final.extract 228 260 = dink.toByteArray := by
    rw [← readWithPadding_eq_extract' final 228 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hdinkRead
  have hzeroExt : final.extract 260 292 = (⟨0⟩ : UInt256).toByteArray := by
    rw [← readWithPadding_eq_extract' final 260 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hzeroRead
  have hsplit : final.extract 128 292 =
      final.extract 128 132 ++ final.extract 132 164 ++ final.extract 164 196 ++
        final.extract 196 228 ++ final.extract 228 260 ++ final.extract 260 292 := by
    rw [show final.extract 128 292 = final.extract 128 132 ++ final.extract 132 292 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 132 292 = final.extract 132 164 ++ final.extract 164 292 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 164 292 = final.extract 164 196 ++ final.extract 196 292 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 196 292 = final.extract 196 228 ++ final.extract 228 292 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 228 292 = final.extract 228 260 ++ final.extract 260 292 by
      rw [ByteArray.extract_append_extract]; norm_num]
    simp [ByteArray.append_assoc]
  rw [show (128 : ℕ) + 164 = 292 from rfl, hsplit, hselExt, hurnExt, hvowExt, htabExt, hdinkExt,
    hzeroExt]

/-- **Coupling.**  The bytecode-constructed `kick` calldata slice equals the spec-level ABI
    encoding of `kick(urn, vow, tab, dink, 0)`.  `urn`/`vow` are the masked address words. -/
theorem kickEncode_eq (urn vow tab dink : UInt256) {mem : ByteArray}
    (hmem : 292 ≤ mem.size)
    (hurn : urn.toNat < EVM.addressModulus) (hvow : vow.toNat < EVM.addressModulus) :
    config.externalABI.encode? "kick"
        [.address (AccountAddress.ofNat urn.toNat), .address (AccountAddress.ofNat vow.toNat),
          .int (Int.ofNat tab.toNat), .int (Int.ofNat dink.toNat), .int 0] =
      some ((kickCalldataMem urn vow tab dink mem).readWithPadding 128 164) := by
  rw [kickCalldataMem_read128_164 urn vow tab dink hmem]
  have hurnWord : EVM.word ↑(AccountAddress.ofNat urn.toNat) = urn := by
    have haddrVal : (AccountAddress.ofNat urn.toNat).val = urn.toNat := by
      unfold AccountAddress.ofNat
      simp only [Fin.val_ofNat]
      exact Nat.mod_eq_of_lt (by
        simpa [AccountAddress.size] using hurn)
    change UInt256.ofNat (AccountAddress.ofNat urn.toNat).val = urn
    rw [haddrVal]; exact u256_ofNat_toNat _
  have hvowWord : EVM.word ↑(AccountAddress.ofNat vow.toNat) = vow := by
    have haddrVal : (AccountAddress.ofNat vow.toNat).val = vow.toNat := by
      unfold AccountAddress.ofNat
      simp only [Fin.val_ofNat]
      exact Nat.mod_eq_of_lt (by
        simpa [AccountAddress.size] using hvow)
    change UInt256.ofNat (AccountAddress.ofNat vow.toNat).val = vow
    rw [haddrVal]; exact u256_ofNat_toNat _
  have htabWord : EVM.word tab.toNat = tab := by
    show UInt256.ofNat tab.toNat = tab; exact u256_ofNat_toNat tab
  have hdinkWord : EVM.word dink.toNat = dink := by
    show UInt256.ofNat dink.toNat = dink; exact u256_ofNat_toNat dink
  have hsizeEq : EVM.twoPow 256 = UInt256.size := by native_decide
  have hzeroLt : 0 < EVM.twoPow 256 := by native_decide
  have htabLt : tab.toNat < EVM.twoPow 256 := by rw [hsizeEq]; exact tab.val.isLt
  have hdinkLt : dink.toNat < EVM.twoPow 256 := by rw [hsizeEq]; exact dink.val.isLt
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, uint256, uint256Int,
    kickerKickSelector, selectorBytes, hurnWord, hvowWord, htabWord, hdinkWord,
    htabLt, hdinkLt, hzeroLt, word_toBytesBE_toByteArray_eq_toByteArray]
  have hw0 : EVM.word 0 = (⟨0⟩ : UInt256) := by decide
  simp [hw0, ByteArray.append_assoc]

/-! ## RD stepping — guard, CALL, success guard

The trace agent supplies an RD at the EXTCODESIZE guard (pc `2516`) with the CALL scratch words on
the stack and generic memory `mem`; these lemmas step through guard + CALL + success guard,
producing the `Θ` witness (with `mem.readWithPadding 128 164` as calldata) and an RD at pc `2550`
(first return-decode instruction), or `RDrev` on the failure branches. -/

/-- Missing-code branch: `EXTCODESIZE = 0` reverts. -/
theorem RD.catBiteKickGuardMissing {cA gh bl σ σ₀ A I} {g target : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2516⟩
      (target :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨164⟩ :: ⟨128⟩ :: ⟨32⟩ :: R)
      mem aw rdata (cAx, σx) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σx target = ⟨0⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2516⟩) (okPc := ⟨2528⟩) rd hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons]; omega)

/-- Present-code branch: step the guard to the `GAS`, reaching the `CALL` at pc `2531`. -/
theorem RD.catBiteKickGuardOk {cA gh bl σ σ₀ A I} {g target : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2516⟩
      (target :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨164⟩ :: ⟨128⟩ :: ⟨32⟩ :: R)
      mem aw rdata (cAx, σx) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σx target ≠ ⟨0⟩)
    (hov : R.length + 9 ≤ 1024) :
    ∃ gasWord k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      (gasWord :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨164⟩ :: ⟨128⟩ :: ⟨32⟩ :: R)
      mem aw rdata (cAx, σx) k' C' := by
  obtain ⟨gasWord, k', C', rd'⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2516⟩) (okPc := ⟨2528⟩) rd hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp only [List.length_cons]; omega)
  exact ⟨gasWord, k', C', by simpa using rd'⟩

/-- Execute the `CALL` (`perm := true`, value `0`, `depth < 1024`): the `Θ` witness plus the RD at
    the success guard (pc `2532`). -/
theorem RD.catBiteKickPostCall {cA gh bl σ σ₀ A I} {g target gasWord : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      (gasWord :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨164⟩ :: ⟨128⟩ :: ⟨32⟩ :: R)
      mem aw rdata (cAx, σx) k C)
    (hdepth : I.depth.val < 1024) (hov : R.length + 1 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cAx gh bl σx σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 target) (toExecute σx (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding 128 164) (I.depth + 1) I.header I.perm)
      ∧ RD catBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2532⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: R)
          (o.write 0 mem 128 (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
          (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat 128 164) 128 32))
          o (cA', σ') k' C'
      ∧ o.size < UInt256.size := by
  obtain ⟨cA', σ', z, o, Ain, callGas, k', C', hΘ, rd2532, hout⟩ :=
    RD.call rd (by native_decide) hdepth (by simpa using hov)
  refine ⟨cA', σ', z, o, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · simpa using rd2532

/-- Depth-limit branch: at `depth = 1024` the `CALL` pushes status `0` without a `Θ` call. -/
theorem RD.catBiteKickCallDepthLimit {cA gh bl σ σ₀ A I} {g target gasWord : UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      (gasWord :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨164⟩ :: ⟨128⟩ :: ⟨32⟩ :: R)
      mem aw rdata (cAx, σx) k C)
    (hdepth : I.depth = 1024) (hov : R.length + 1 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2532⟩ (⟨0⟩ :: R)
      (ByteArray.empty.write 0 mem 128 (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat 128 164) 128 32))
      ByteArray.empty (cAx, σx) k' C' := by
  obtain ⟨k', C', rd'⟩ := RD.callDepthLimit rd (by native_decide) hdepth (by simpa using hov)
  exact ⟨k', C', by simpa using rd'⟩

/-- Success guard, failure branch: status `0` bubbles the return data and reverts. -/
theorem RD.catBiteKickCallFailed {cA gh bl σ σ₀ A I} {g : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2532⟩ (⟨0⟩ :: R)
      mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2532⟩) (okPc := ⟨2548⟩) rd rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize hov

/-- Success guard, ok branch: status `≠ 0` reaches the first return-decode instruction (pc `2550`)
    with the return data left in memory/returndata. -/
theorem RD.catBiteKickCallSucceeded {cA gh bl σ σ₀ A I} {g status : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2532⟩ (status :: R)
      mem aw rdata acc k C)
    (hstatus : status ≠ ⟨0⟩)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2550⟩ R
      mem aw rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨2532⟩) (okPc := ⟨2548⟩) rd hstatus
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide) hov

end Benchmarks.Dss.Cat
