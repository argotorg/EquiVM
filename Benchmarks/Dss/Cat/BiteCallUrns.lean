import Benchmarks.Dss.Cat.Common
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cat

/-!
# Cat `bite` — the `vat.urns(bytes32,address)` external `STATICCALL` helper

Second external call of `bite` (`vat.urns(ilk, urn)`, `perm := false`, view → `STATICCALL`).
Guard `EXTCODESIZE` at pc `1383`, `STATICCALL` at pc `1398`; the return is a 2-uint256 tuple
`[ink, art]` copied to `mem[outPtr, outPtr+64)`.

* **item 1** — the calldata byte-layout: `biteUrnsCalldataMem` places the `urns` selector at
  `128`, `ilk` at `132`, `urn` at `164`; `biteUrnsEncode_eq` proves that slice equals
  `config.externalABI.encode? "urns" [ilk, urn]`;
* **item 2** — `RD.catBiteUrns*`: from an `RD` at the `EXTCODESIZE` guard pc `1383` (args + built
  memory on the stack, stated generically over the incoming stack tail `R` and the pre-call
  memory `mem`), step through guard + `STATICCALL`, producing the `Θ` witness / `callCoincides`
  coupling on success (STATICCALL preserves this-storage), or `RDrev` on `codesize == 0` /
  call failure / depth limit; then the 2-word return decode `RD.catBiteUrnsReturnDecodeOk`.

The ilk-argument abbrevs are named `biteUrnsIlk*` to avoid colliding with `BiteSource`'s
`biteIlk*`, since both files are imported together in `Bite.lean`.
-/

/-! ## Argument words -/

/-- `bite`'s `ilk` argument, as the raw 32 calldata bytes (offset 4). -/
abbrev biteUrnsIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

/-- `bite`'s `ilk` argument as a word. -/
abbrev biteUrnsIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

/-- `bite`'s `urn` argument as an address (matches `biteLocals`). -/
abbrev biteUrnAddr (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 36).toNat

/-- `bite`'s `urn` argument as the canonical 160-bit word the bytecode masks into memory. -/
abbrev biteUrnWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (biteUrnAddr I).val

theorem biteUrnsIlkBytes_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (biteUrnsIlkBytes I).length = 32 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [biteUrnsIlkBytes, List.length_take, List.length_drop, htlen]
  omega

theorem biteUrnsIlkBytes_eq_toBytesBE {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    biteUrnsIlkBytes I = EVM.Word.toBytesBE (biteUrnsIlkWord I) := by
  have hlen32 : (biteUrnsIlkBytes I).length = 32 := biteUrnsIlkBytes_length hsz36
  have hword : ABI.bytesToWord (biteUrnsIlkBytes I) = biteUrnsIlkWord I := by
    simpa [biteUrnsIlkBytes, biteUrnsIlkWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hto := toBytesBE_bytesToWord_of_length (bs := biteUrnsIlkBytes I) hlen32
  rw [hword] at hto
  exact hto.symm

/-! ## Calldata memory model

The `urns` selector `0x2424be5c` is `0x09092f97 << 2`; the bytecode pushes `0x09092f97` and
shifts left by `226 = 224 + 2`. -/

abbrev biteUrnsSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨151596951⟩ ⟨226⟩

/-- Free-pointer scratch with the `urns` selector word written at offset `128`. -/
noncomputable def biteUrnsSelectorMem (mem : ByteArray) : ByteArray :=
  biteUrnsSelectorShifted.toByteArray.write 0 mem 128 32

/-- ... plus `ilk` written at offset `132`. -/
noncomputable def biteUrnsIlkMem (ilkW : UInt256) (mem : ByteArray) : ByteArray :=
  ilkW.toByteArray.write 0 (biteUrnsSelectorMem mem) 132 32

/-- ... plus `urn` written at offset `164`: the complete `urns(bytes32,address)` calldata. -/
noncomputable def biteUrnsCalldataMem (ilkW urnW : UInt256) (mem : ByteArray) : ByteArray :=
  urnW.toByteArray.write 0 (biteUrnsIlkMem ilkW mem) 164 32

theorem biteUrnsSelectorMem_size {mem : ByteArray} (hmem : 196 ≤ mem.size) :
    (biteUrnsSelectorMem mem).size = mem.size := by
  unfold biteUrnsSelectorMem
  exact toByteArray_write32_size_of_le mem biteUrnsSelectorShifted 128 mem.size mem.size
    rfl (by omega) (by omega)

theorem biteUrnsIlkMem_size {ilkW : UInt256} {mem : ByteArray} (hmem : 196 ≤ mem.size) :
    (biteUrnsIlkMem ilkW mem).size = mem.size := by
  unfold biteUrnsIlkMem
  exact toByteArray_write32_size_of_le (biteUrnsSelectorMem mem) ilkW 132 mem.size mem.size
    (biteUrnsSelectorMem_size hmem) (by rw [biteUrnsSelectorMem_size hmem]; omega) (by omega)

theorem biteUrnsCalldataMem_size {ilkW urnW : UInt256} {mem : ByteArray}
    (hmem : 196 ≤ mem.size) :
    (biteUrnsCalldataMem ilkW urnW mem).size = mem.size := by
  unfold biteUrnsCalldataMem
  exact toByteArray_write32_size_of_le (biteUrnsIlkMem ilkW mem) urnW 164 mem.size mem.size
    (biteUrnsIlkMem_size hmem) (by rw [biteUrnsIlkMem_size hmem]; omega) (by omega)

theorem biteUrnsSelectorMem_read64 {mem : ByteArray} (hmem : 196 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (biteUrnsSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold biteUrnsSelectorMem
  rw [write32_read_below_len _ _ 128 64 32 (by rw [toByteArray_size]) (by omega)
    (by omega) (by omega) (by omega) (by norm_num), hread64]

theorem biteUrnsIlkMem_read64 {ilkW : UInt256} {mem : ByteArray} (hmem : 196 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (biteUrnsIlkMem ilkW mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold biteUrnsIlkMem
  rw [write32_read_below_len _ _ 132 64 32 (by rw [toByteArray_size])
    (by rw [biteUrnsSelectorMem_size hmem]; omega) (by omega)
    (by rw [biteUrnsSelectorMem_size hmem]; omega) (by omega) (by norm_num),
    biteUrnsSelectorMem_read64 hmem hread64]

theorem biteUrnsCalldataMem_read64 {ilkW urnW : UInt256} {mem : ByteArray}
    (hmem : 196 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (biteUrnsCalldataMem ilkW urnW mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold biteUrnsCalldataMem
  rw [write32_read_below_len _ _ 164 64 32 (by rw [toByteArray_size])
    (by rw [biteUrnsIlkMem_size hmem]; omega) (by omega)
    (by rw [biteUrnsIlkMem_size hmem]; omega) (by omega) (by norm_num),
    biteUrnsIlkMem_read64 hmem hread64]

/-! ### The calldata slice `[128, 196)` -/

theorem biteUrnsCalldataMem_read128_68 {ilkW urnW : UInt256} {mem : ByteArray}
    (hmem : 196 ≤ mem.size) :
    (biteUrnsCalldataMem ilkW urnW mem).readWithPadding 128 68 =
      vatUrnsSelector ++ ilkW.toByteArray ++ urnW.toByteArray := by
  let final := biteUrnsCalldataMem ilkW urnW mem
  have hfinalSize : final.size = mem.size := biteUrnsCalldataMem_size hmem
  -- selector at [128,132)
  have hselectorRead : final.readWithPadding 128 4 = vatUrnsSelector := by
    dsimp only [final]
    unfold biteUrnsCalldataMem
    rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
      (by rw [biteUrnsIlkMem_size hmem]; omega) (by omega)
      (by rw [biteUrnsIlkMem_size hmem]; omega) (by omega) (by norm_num)]
    unfold biteUrnsIlkMem
    rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
      (by rw [biteUrnsSelectorMem_size hmem]; omega) (by omega)
      (by rw [biteUrnsSelectorMem_size hmem]; omega) (by omega) (by norm_num)]
    unfold biteUrnsSelectorMem
    rw [write32_read_prefix_len _ _ 128 4 (by rw [toByteArray_size]) (by omega)
      (by omega) (by omega) (by norm_num)]
    unfold biteUrnsSelectorShifted vatUrnsSelector selectorBytes
    native_decide
  -- ilk at [132,164)
  have hilkRead : final.readWithPadding 132 32 = ilkW.toByteArray := by
    dsimp only [final]
    unfold biteUrnsCalldataMem
    rw [write32_read_below_len _ _ 164 132 32 (by rw [toByteArray_size])
      (by rw [biteUrnsIlkMem_size hmem]; omega) (by omega)
      (by rw [biteUrnsIlkMem_size hmem]; omega) (by omega) (by norm_num)]
    unfold biteUrnsIlkMem
    rw [write32_read_prefix_len _ _ 132 32 (by rw [toByteArray_size])
      (by rw [biteUrnsSelectorMem_size hmem]; omega) (by omega) (by omega) (by norm_num)]
    rw [toByteArray_extract_all]
  -- urn at [164,196)
  have hurnRead : final.readWithPadding 164 32 = urnW.toByteArray := by
    dsimp only [final]
    unfold biteUrnsCalldataMem
    rw [write32_read_prefix_len _ _ 164 32 (by rw [toByteArray_size])
      (by rw [biteUrnsIlkMem_size hmem]; omega) (by omega) (by omega) (by norm_num)]
    rw [toByteArray_extract_all]
  rw [readWithPadding_eq_extract' final 128 68 (by norm_num) (by norm_num)
    (by rw [hfinalSize]; omega)]
  have hselectorExt : final.extract 128 132 = vatUrnsSelector := by
    rw [← readWithPadding_eq_extract' final 128 4 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hselectorRead
  have hilkExt : final.extract 132 164 = ilkW.toByteArray := by
    rw [← readWithPadding_eq_extract' final 132 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hilkRead
  have hurnExt : final.extract 164 196 = urnW.toByteArray := by
    rw [← readWithPadding_eq_extract' final 164 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hurnRead
  have hsplit : final.extract 128 196 =
      final.extract 128 132 ++ final.extract 132 164 ++ final.extract 164 196 := by
    rw [show final.extract 128 196 = final.extract 128 132 ++ final.extract 132 196 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 132 196 = final.extract 132 164 ++ final.extract 164 196 by
      rw [ByteArray.extract_append_extract]; norm_num]
    simp
  rw [hsplit, hselectorExt, hilkExt, hurnExt]

/-! ### Encoding coupling -/

/-- The `urn` address encodes as `EVM.word` of its `.val`, which is `biteUrnWord` by definition. -/
theorem biteUrns_addrWord (I : ExecutionEnv) :
    EVM.word (↑(biteUrnAddr I) : ℕ) = biteUrnWord I := rfl

/-- **Item 1 — calldata / ABI-encoding coupling.**  The slice the bytecode built in memory at the
    `STATICCALL` calldata pointer equals `encode? "urns" [ilk, urn]`. -/
theorem biteUrnsEncode_eq (I : ExecutionEnv) {mem : ByteArray} (hmem : 196 ≤ mem.size)
    (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.encode? "urns"
        [.fixedBytes bytes32Width (biteUrnsIlkBytes I), .address (biteUrnAddr I)] =
      some ((biteUrnsCalldataMem (biteUrnsIlkWord I) (biteUrnWord I) mem).readWithPadding 128 68) := by
  rw [biteUrnsCalldataMem_read128_68 hmem]
  have hbytes := biteUrnsIlkBytes_eq_toBytesBE (I := I) hsz36
  have hlen : (EVM.Word.toBytesBE (biteUrnsIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (biteUrnsIlkWord I)
  have haddrWord := biteUrns_addrWord I
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, addr,
    vatUrnsSelector, selectorBytes, hbytes, hlen, haddrWord, ABI.zeroBytes,
    word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.append_assoc]

/-! ## Item 2 — the guard + `STATICCALL` reach helpers

All lemmas start at the `EXTCODESIZE` guard pc `1383` and are stated *generically* over the
target-address word `target`, the shared calldata/return pointer `outPtr`, the pre-call memory
`mem`, its active-word count `aw`, the incoming return data `o`, and the incoming stack tail `R`.
`outPtr :: ⟨68⟩ :: outPtr :: ⟨64⟩` are the `STATICCALL` `inOffset/inSize/outOffset/outSize`. -/

/-- **codesize == 0** — the `EXTCODESIZE` guard reverts. -/
theorem RD.catBiteUrnsNoCode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {target outPtr aw : UInt256} {mem o : ByteArray} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1383⟩
      (target :: target :: outPtr :: ⟨68⟩ :: outPtr :: ⟨64⟩ :: R)
      mem aw o (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ target = ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) :
    RDrev catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) :=
  RD.solcExtcodesizeGuardMissing (pc := ⟨1383⟩) (okPc := ⟨1395⟩) rd hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons]; omega)

/-- **guard + `STATICCALL` (target has code).**  Steps the `EXTCODESIZE` guard and the `STATICCALL`,
    landing just after the call at pc `1399` with the success flag on top, and exposes the `Θ`-link
    as a `typedCallViaEVM` coupling (`callCoincides`) for the same opaque `(z, σ', o')`.  Generic
    over `args`/`mem`/`outPtr` via the encode coupling `hencode`. -/
theorem RD.catBiteUrnsStaticcall
    {cA gh bl σ σ₀ A I} {g : UInt256} {args : List Value}
    {target outPtr aw : UInt256} {mem o : ByteArray} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1383⟩
      (target :: target :: outPtr :: ⟨68⟩ :: outPtr :: ⟨64⟩ :: R)
      mem aw o (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hencode : config.externalABI.encode? "urns" args =
        some (mem.readWithPadding outPtr.toNat 68))
    (hov : R.length + 8 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o' : ByteArray) (A' : Substate) (awout : UInt256) (k' C' : ℕ),
      RD catBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1399⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (o'.write 0 mem outPtr.toNat (min (⟨64⟩ : UInt256) (UInt256.ofNat o'.size)).toNat)
        awout o' (cA', σ') k' C'
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 target) "urns" 0 args
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o') false
    ∧ o'.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1398⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1383⟩) (okPc := ⟨1395⟩) rd hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, o', A_in, callGas, k', C', hΘpack, rd1399, hosz⟩ :=
    RD.solcStaticcall rd1398 (by native_decide) hdepth (by omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o', A', _, k', C', rd1399, ?_, hosz⟩
  refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
    (callPerm := false) (targetWord := target)
    (mem := mem) (inOff := outPtr) (inSize := ⟨68⟩)
    (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
    rfl hencode ?_
  simpa [initState] using hΘ

/-- **depth-limit** — the `STATICCALL` returns `0` without invoking `Θ`. -/
theorem RD.catBiteUrnsDepthLimit
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {target outPtr aw : UInt256} {mem o : ByteArray} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1383⟩
      (target :: target :: outPtr :: ⟨68⟩ :: outPtr :: ⟨64⟩ :: R)
      mem aw o (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hov : R.length + 8 ≤ 1024) :
    ∃ (awout : UInt256) (k' C' : ℕ), RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1399⟩
      (⟨0⟩ :: R)
      (ByteArray.empty.write 0 mem outPtr.toNat
        (min (⟨64⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      awout ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨gasWord, _, _, rd1398⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1383⟩) (okPc := ⟨1395⟩) rd hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by simp only [List.length_cons]; omega)
  obtain ⟨k', C', rd1399⟩ :=
    RD.solcStaticcallDepthLimit rd1398 (by native_decide) hdepth (by omega)
  exact ⟨_, k', C', rd1399⟩

/-- **call failed** (`status = 0`) — the success guard bubbles the revert. -/
theorem RD.catBiteUrnsCallFailed
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1399⟩
      (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) :=
  RD.solcCallSuccessGuardMissing (pc := ⟨1399⟩) (okPc := ⟨1415⟩) rd rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

/-- **call succeeded** (`status ≠ 0`) — clear the success guard (one `POP`) and the three scratch
    `POP`s, landing at pc `1420` ready for the 2-word return decode. -/
theorem RD.catBiteUrnsCallSucceeded
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw status : UInt256} {d0 d1 d2 : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1399⟩
      (status :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hstatus : status ≠ ⟨0⟩)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1420⟩
      R mem aw o acc k' C' := by
  obtain ⟨_, _, rd1417⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨1399⟩) (okPc := ⟨1415⟩) rd hstatus
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)
  have rd1418 := RD.pop rd1417 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1419 := RD.pop rd1418 (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1420 := RD.pop rd1419 (by native_decide) (by omega)
  exact ⟨_, _, rd1420⟩

/-- **return too short** (`returndatasize < 64`) — the ABI-length guard reverts. -/
theorem RD.catBiteUrnsReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1420⟩
      R mem aw o acc k C)
    (hshort : o.size < 64) (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hMload64Cost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨64⟩ : UInt256) :: R → memoryExpansionCost s .MLOAD = 0)
    (hMload64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hov : R.length + 4 ≤ 1024) :
    RDrev catBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have rdPush64 := RD.push1 rd ⟨64⟩ (by native_decide) (by omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ aw rdPush64 (by native_decide) hMload64Cost
    hMload64Value hMload64Aw (by omega)
  have rdRds := RD.returndatasize rdMload64 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush64' := RD.push1 rdRds ⟨64⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush64' (by native_decide) (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' o.size hhi]
    exact hshort
  have rdIszero := RD.iszero rdLt (by native_decide) (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨1437⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]; decide
  have rdFallthrough := RD.jumpiNT rdPushOk (by native_decide) hcond
    (by simp only [List.length_cons]; omega)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

/-- **return decode OK** (`returndatasize ≥ 64`) — reads `ink = ret[0]` (offset `128`) and
    `art = ret[1]` (offset `160`) onto the stack, landing at pc `1447` with `art :: ink :: R`.
    The three `MLOAD` results are supplied as hypotheses (the trace agent computes them from the
    concrete post-call memory). -/
theorem RD.catBiteUrnsReturnDecodeOk
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw aw1 aw2 inkW artW : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1420⟩
      R mem aw o acc k C)
    (hlo : 64 ≤ o.size) (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hMload64Cost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨64⟩ : UInt256) :: R → memoryExpansionCost s .MLOAD = 0)
    (hMload64Aw : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size ∨ (⟨128⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32)))
        = inkW)
    (hMload128Cost : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = (⟨128⟩ : UInt256) :: ⟨128⟩ :: R → memoryExpansionCost s .MLOAD = 0)
    (hMload128Aw : UInt256.ofNat (MachineState.M aw.toNat 128 32) = aw1)
    (hMload160Value :
      (if (⟨160⟩ : UInt256).toNat ≥ mem.size ∨ (⟨160⟩ : UInt256) ≥ aw1 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨160⟩ : UInt256).toNat 32)))
        = artW)
    (hMload160Cost : ∀ s : State, s.machineState.activeWords = aw1 →
        s.machineState.stack = (⟨160⟩ : UInt256) :: inkW :: R → memoryExpansionCost s .MLOAD = 0)
    (hMload160Aw : UInt256.ofNat (MachineState.M aw1.toNat 160 32) = aw2)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1447⟩
      (artW :: inkW :: R) mem aw2 o acc k' C' := by
  have rdPush64 := RD.push1 rd ⟨64⟩ (by native_decide) (by omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ aw rdPush64 (by native_decide) hMload64Cost
    hMload64Value hMload64Aw (by omega)
  have rdRds := RD.returndatasize rdMload64 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush64' := RD.push1 rdRds ⟨64⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush64' (by native_decide) (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 (by native_decide) (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' o.size hhi]
    exact hlo
  have rdIszero := RD.iszero rdLt (by native_decide) (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨1437⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hlt]; decide
  have rdJumpi := RD.jumpiT rdPushOk (by native_decide) hcond (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop := RD.pop rdJumpdest (by native_decide) (by simp only [List.length_cons]; omega)
  have rdDup1 := RD.dup1 rdPop (by native_decide) (by omega)
  have rdMload128 := RD.mload 0 inkW aw1 rdDup1 (by native_decide) hMload128Cost
    hMload128Value hMload128Aw (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdMload128 ⟨32⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdSwap1 := RD.swap1 rdPush32 (by native_decide) (by simp only [List.length_cons]; omega)
  have rdSwap2 := RD.swap2 rdSwap1 (by native_decide) (by omega)
  have rdAdd := RD.add rdSwap2 (by native_decide) (by simp only [List.length_cons]; omega)
  have hadd : (⟨128⟩ : UInt256) + ⟨32⟩ = ⟨160⟩ := by decide
  rw [hadd] at rdAdd
  have rdMload160 := RD.mload 0 artW aw2 rdAdd (by native_decide) hMload160Cost
    hMload160Value hMload160Aw (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa using rdMload160⟩

end Benchmarks.Dss.Cat
