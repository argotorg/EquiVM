import Benchmarks.Dss.Clipper.RedoSuccessEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Reasoning.Theory

private theorem clipperDup16Xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP16, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        oo :: pp :: t)
    (hov : t.length + 17 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
       else .ok
        (stSwap s
          (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll ::
            mm :: nn :: oo :: pp :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP16, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup16 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
          nn :: oo :: pp :: t).length - 16 + 17 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

end Reasoning.Theory

namespace Reasoning.Reach

theorem RD.clipperDup16 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        oo :: pp :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP16, .none)) (hov : t.length + 17 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
        nn :: oo :: pp :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => Reasoning.Theory.clipperDup16Xstep hc hp hdec hs hov)

end Reasoning.Reach

namespace Benchmarks.Dss.Clipper

abbrev clipperRedoVatTarget (v : ClipperImmutables) : UInt256 :=
  UInt256.land solcAddrMask (EVM.Word.ofNat (↑v.vat : Nat))

abbrev clipperRedoVowTarget (σ : AccountMap) (ee : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (solcSlotWord σ ee ⟨2⟩)

abbrev clipperRedoKprTarget (kpr : UInt256) : UInt256 :=
  UInt256.land solcAddrMask kpr

abbrev clipperRedoSuckSelectorWord : UInt256 := ⟨0xf24e23eb⟩
abbrev clipperRedoSuckSelectorShifted : UInt256 :=
  UInt256.shiftLeft clipperRedoSuckSelectorWord ⟨224⟩

noncomputable def clipperRedoSuckSelectorMem (mem : ByteArray) : ByteArray :=
  clipperRedoSuckSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def clipperRedoSuckVowMem (σ : AccountMap) (ee : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  (clipperRedoVowTarget σ ee).toByteArray.write 0 (clipperRedoSuckSelectorMem mem) 132 32

noncomputable def clipperRedoSuckKprMem (σ : AccountMap) (ee : ExecutionEnv)
    (kpr : UInt256) (mem : ByteArray) : ByteArray :=
  (clipperRedoKprTarget kpr).toByteArray.write 0 (clipperRedoSuckVowMem σ ee mem) 164 32

noncomputable def clipperRedoSuckCalldataMem (σ : AccountMap) (ee : ExecutionEnv)
    (kpr coin : UInt256) (mem : ByteArray) : ByteArray :=
  coin.toByteArray.write 0 (clipperRedoSuckKprMem σ ee kpr mem) 196 32

theorem clipperRedoSuckSelectorMem_size {mem : ByteArray} (hmem : mem.size = 196) :
    (clipperRedoSuckSelectorMem mem).size = 196 := by
  unfold clipperRedoSuckSelectorMem
  exact toByteArray_write32_size_of_le mem clipperRedoSuckSelectorShifted
    128 196 196 hmem (by omega) (by omega)

theorem clipperRedoSuckVowMem_size (σ : AccountMap) (ee : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 196) :
    (clipperRedoSuckVowMem σ ee mem).size = 196 := by
  unfold clipperRedoSuckVowMem
  exact toByteArray_write32_size_of_le (clipperRedoSuckSelectorMem mem)
    (clipperRedoVowTarget σ ee) 132 196 196 (clipperRedoSuckSelectorMem_size hmem)
    (by rw [clipperRedoSuckSelectorMem_size hmem]; omega) (by omega)

theorem clipperRedoSuckKprMem_size (σ : AccountMap) (ee : ExecutionEnv)
    (kpr : UInt256) {mem : ByteArray} (hmem : mem.size = 196) :
    (clipperRedoSuckKprMem σ ee kpr mem).size = 196 := by
  unfold clipperRedoSuckKprMem
  exact toByteArray_write32_size_of_le (clipperRedoSuckVowMem σ ee mem)
    (clipperRedoKprTarget kpr) 164 196 196 (clipperRedoSuckVowMem_size σ ee hmem)
    (by rw [clipperRedoSuckVowMem_size σ ee hmem]; omega) (by omega)

theorem clipperRedoSuckCalldataMem_size (σ : AccountMap) (ee : ExecutionEnv)
    (kpr coin : UInt256) {mem : ByteArray} (hmem : mem.size = 196) :
    (clipperRedoSuckCalldataMem σ ee kpr coin mem).size = 228 := by
  unfold clipperRedoSuckCalldataMem
  exact toByteArray_write32_size_of_le (clipperRedoSuckKprMem σ ee kpr mem) coin
    196 196 228 (clipperRedoSuckKprMem_size σ ee kpr hmem)
    (by rw [clipperRedoSuckKprMem_size σ ee kpr hmem]) (by omega)

theorem clipperRedoSuckSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperRedoSuckSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold clipperRedoSuckSelectorMem
  rw [toByteArray_write_read_below_of_gap clipperRedoSuckSelectorShifted mem 128 64
    (by rw [hmem]; omega) (by omega) (by rw [hmem]; native_decide)]
  exact hread64

theorem clipperRedoSuckVowMem_read64 (σ : AccountMap) (ee : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperRedoSuckVowMem σ ee mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold clipperRedoSuckVowMem
  rw [toByteArray_write_read_below_of_gap (clipperRedoVowTarget σ ee)
    (clipperRedoSuckSelectorMem mem) 132 64
    (by rw [clipperRedoSuckSelectorMem_size hmem]; omega) (by omega)
    (by rw [clipperRedoSuckSelectorMem_size hmem]; native_decide)]
  exact clipperRedoSuckSelectorMem_read64 hmem hread64

theorem clipperRedoSuckKprMem_read64 (σ : AccountMap) (ee : ExecutionEnv)
    (kpr : UInt256) {mem : ByteArray} (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperRedoSuckKprMem σ ee kpr mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperRedoSuckKprMem
  rw [toByteArray_write_read_below_of_gap (clipperRedoKprTarget kpr)
    (clipperRedoSuckVowMem σ ee mem) 164 64
    (by rw [clipperRedoSuckVowMem_size σ ee hmem]; omega) (by omega)
    (by rw [clipperRedoSuckVowMem_size σ ee hmem]; native_decide)]
  exact clipperRedoSuckVowMem_read64 σ ee hmem hread64

theorem clipperRedoSuckCalldataMem_read64 (σ : AccountMap) (ee : ExecutionEnv)
    (kpr coin : UInt256) {mem : ByteArray} (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperRedoSuckCalldataMem σ ee kpr coin mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperRedoSuckCalldataMem
  rw [toByteArray_write_read_below_of_gap coin (clipperRedoSuckKprMem σ ee kpr mem)
    196 64 (by rw [clipperRedoSuckKprMem_size σ ee kpr hmem]; omega) (by omega)
    (by rw [clipperRedoSuckKprMem_size σ ee kpr hmem]; native_decide)]
  exact clipperRedoSuckKprMem_read64 σ ee kpr hmem hread64

theorem clipperRedoSuckCalldataMem_mload64 (σ : AccountMap) (ee : ExecutionEnv)
    (kpr coin : UInt256) {mem : ByteArray} (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperRedoSuckCalldataMem σ ee kpr coin mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperRedoSuckCalldataMem σ ee kpr coin mem).readWithPadding 64 32))) = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [clipperRedoSuckCalldataMem_size σ ee kpr coin hmem]; decide)
    (by decide) (clipperRedoSuckCalldataMem_read64 σ ee kpr coin hmem hread64)

theorem clipperRedoSuckCalldataMem_read128_100 (σ : AccountMap) (ee : ExecutionEnv)
    (kpr coin : UInt256) {mem : ByteArray} (hmem : mem.size = 196) :
    (clipperRedoSuckCalldataMem σ ee kpr coin mem).readWithPadding 128 100 =
      vatSuckSelector ++ (clipperRedoVowTarget σ ee).toByteArray ++
        (clipperRedoKprTarget kpr).toByteArray ++ coin.toByteArray := by
  set final := clipperRedoSuckCalldataMem σ ee kpr coin mem with hfinal
  have hfinalSize : final.size = 228 :=
    hfinal ▸ clipperRedoSuckCalldataMem_size σ ee kpr coin hmem
  have hselector : final.readWithPadding 128 4 = vatSuckSelector := by
    rw [hfinal]
    unfold clipperRedoSuckCalldataMem
    rw [toByteArray_write_read_below_len_of_gap coin (clipperRedoSuckKprMem σ ee kpr mem)
      196 128 4 (by rw [clipperRedoSuckKprMem_size σ ee kpr hmem]; omega)
      (by omega) (by omega) (by norm_num)
      (by rw [clipperRedoSuckKprMem_size σ ee kpr hmem]; native_decide)]
    unfold clipperRedoSuckKprMem
    rw [toByteArray_write_read_below_len_of_gap (clipperRedoKprTarget kpr)
      (clipperRedoSuckVowMem σ ee mem) 164 128 4
      (by rw [clipperRedoSuckVowMem_size σ ee hmem]; omega)
      (by omega) (by omega) (by norm_num)
      (by rw [clipperRedoSuckVowMem_size σ ee hmem]; native_decide)]
    unfold clipperRedoSuckVowMem
    rw [toByteArray_write_read_below_len_of_gap (clipperRedoVowTarget σ ee)
      (clipperRedoSuckSelectorMem mem) 132 128 4
      (by rw [clipperRedoSuckSelectorMem_size hmem]; omega)
      (by omega) (by omega) (by norm_num)
      (by rw [clipperRedoSuckSelectorMem_size hmem]; native_decide)]
    unfold clipperRedoSuckSelectorMem
    have hw := toByteArray_write_read_window_of_gap clipperRedoSuckSelectorShifted mem
      128 0 4 (by omega) (by omega) (by norm_num) (by rw [hmem]; native_decide)
    simp only [Nat.add_zero] at hw
    rw [hw]
    native_decide
  have hvow : final.readWithPadding 132 32 =
      (clipperRedoVowTarget σ ee).toByteArray := by
    rw [hfinal]
    unfold clipperRedoSuckCalldataMem
    rw [toByteArray_write_read_below_len_of_gap coin (clipperRedoSuckKprMem σ ee kpr mem)
      196 132 32 (by rw [clipperRedoSuckKprMem_size σ ee kpr hmem]; omega)
      (by omega) (by omega) (by norm_num)
      (by rw [clipperRedoSuckKprMem_size σ ee kpr hmem]; native_decide)]
    unfold clipperRedoSuckKprMem
    rw [toByteArray_write_read_below_len_of_gap (clipperRedoKprTarget kpr)
      (clipperRedoSuckVowMem σ ee mem) 164 132 32
      (by rw [clipperRedoSuckVowMem_size σ ee hmem]; omega)
      (by omega) (by omega) (by norm_num)
      (by rw [clipperRedoSuckVowMem_size σ ee hmem]; native_decide)]
    unfold clipperRedoSuckVowMem
    rw [toByteArray_write_read_back_of_gap (clipperRedoVowTarget σ ee)
      (clipperRedoSuckSelectorMem mem) 132
      (by rw [clipperRedoSuckSelectorMem_size hmem]; native_decide)]
  have hkpr : final.readWithPadding 164 32 =
      (clipperRedoKprTarget kpr).toByteArray := by
    rw [hfinal]
    unfold clipperRedoSuckCalldataMem
    rw [toByteArray_write_read_below_len_of_gap coin (clipperRedoSuckKprMem σ ee kpr mem)
      196 164 32 (by rw [clipperRedoSuckKprMem_size σ ee kpr hmem])
      (by omega) (by omega) (by norm_num)
      (by rw [clipperRedoSuckKprMem_size σ ee kpr hmem]; native_decide)]
    unfold clipperRedoSuckKprMem
    rw [toByteArray_write_read_back_of_gap (clipperRedoKprTarget kpr)
      (clipperRedoSuckVowMem σ ee mem) 164
      (by rw [clipperRedoSuckVowMem_size σ ee hmem]; native_decide)]
  have hcoin : final.readWithPadding 196 32 = coin.toByteArray := by
    rw [hfinal]
    unfold clipperRedoSuckCalldataMem
    rw [toByteArray_write_read_back_of_gap coin (clipperRedoSuckKprMem σ ee kpr mem) 196
      (by rw [clipperRedoSuckKprMem_size σ ee kpr hmem]; native_decide)]
  rw [readWithPadding_eq_extract' final 128 100 (by norm_num) (by norm_num)
    (by rw [hfinalSize])]
  have hselectorExt : final.extract 128 132 = vatSuckSelector := by
    rw [← readWithPadding_eq_extract' final 128 4 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hselector
  have hvowExt : final.extract 132 164 = (clipperRedoVowTarget σ ee).toByteArray := by
    rw [← readWithPadding_eq_extract' final 132 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hvow
  have hkprExt : final.extract 164 196 = (clipperRedoKprTarget kpr).toByteArray := by
    rw [← readWithPadding_eq_extract' final 164 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hkpr
  have hcoinExt : final.extract 196 228 = coin.toByteArray := by
    rw [← readWithPadding_eq_extract' final 196 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize])]
    exact hcoin
  rw [show final.extract 128 228 = final.extract 128 132 ++ final.extract 132 164 ++
      final.extract 164 196 ++ final.extract 196 228 by
    rw [show final.extract 128 228 = final.extract 128 132 ++ final.extract 132 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 132 228 = final.extract 132 164 ++ final.extract 164 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 164 228 = final.extract 164 196 ++ final.extract 196 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    simp]
  rw [hselectorExt, hvowExt, hkprExt, hcoinExt]

theorem clipperRedoAddressWord (w : UInt256) :
    EVM.word (AccountAddress.ofNat w.toNat).val = UInt256.land w solcAddrMask := by
  apply u256_inj
  rw [u256_land_toNat]
  unfold EVM.word EVM.uintN AccountAddress.ofNat
  simp only [UInt256.toNat, Fin.ofNat]
  rw [show (↑solcAddrMask.val : Nat) = 2 ^ 160 - 1 from by decide]
  rw [nat_land_mask_eq_mod]
  rw [show AccountAddress.size = 2 ^ 160 from by native_decide,
    show EVM.twoPow 256 = UInt256.size from by native_decide]

theorem clipperRedoSuckEncode_eq (v : ClipperImmutables) (σ : AccountMap)
    (ee : ExecutionEnv) (kpr coin : UInt256) {mem : ByteArray} (hmem : mem.size = 196) :
    (config v).externalABI.encode? "suck"
      [.address (AccountAddress.ofNat (clipperRedoVowTarget σ ee).toNat),
        .address (AccountAddress.ofNat kpr.toNat), .int (Int.ofNat coin.toNat)] =
      some ((clipperRedoSuckCalldataMem σ ee kpr coin mem).readWithPadding 128 100) := by
  rw [clipperRedoSuckCalldataMem_read128_100 σ ee kpr coin hmem]
  have hvowClean : UInt256.land (clipperRedoVowTarget σ ee) solcAddrMask =
      clipperRedoVowTarget σ ee := by
    have hcanon : (clipperRedoVowTarget σ ee).toNat < EVM.addressModulus := by
      unfold clipperRedoVowTarget
      rw [u256_land_comm]
      exact solcAddrMask_result_canonical (solcSlotWord σ ee ⟨2⟩)
    exact solcAddrMask_clean hcanon
  have hvowWord :
      EVM.word (AccountAddress.ofNat (clipperRedoVowTarget σ ee).toNat).val =
        clipperRedoVowTarget σ ee := by
    simpa [hvowClean] using clipperRedoAddressWord (clipperRedoVowTarget σ ee)
  have hkprWord : EVM.word (AccountAddress.ofNat kpr.toNat).val =
      clipperRedoKprTarget kpr := by
    simpa [clipperRedoKprTarget, u256_land_comm] using clipperRedoAddressWord kpr
  have hcoinWord : EVM.word coin.toNat = coin := u256_ofNat_toNat coin
  have hcoinLt : coin.toNat < EVM.twoPow 256 := by
    change coin.val.val < UInt256.size
    exact coin.val.isLt
  change externalABI.encode? "suck"
      [.address (AccountAddress.ofNat (clipperRedoVowTarget σ ee).toNat),
        .address (AccountAddress.ofNat kpr.toNat), .int (Int.ofNat coin.toNat)] =
    some (vatSuckSelector ++ UInt256.toByteArray (clipperRedoVowTarget σ ee) ++
      UInt256.toByteArray (clipperRedoKprTarget kpr) ++ UInt256.toByteArray coin)
  unfold externalABI ABI.encodeCallWithSelector? ABI.encodeABIValues?
  simp [ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr,
    uint256, uint256Int, selectorBytes, vatSuckSelector, hcoinLt, hcoinWord,
    hvowWord, hkprWord, word_toBytesBE_toByteArray_eq_toByteArray,
    ByteArray.append_assoc]

theorem clipperRedoVatPatchPayload7936 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    code.extract' 7936 7968 =
      ({ data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray } : ByteArray) := by
  rcases v.ilk_wf with ⟨bs, hilk, hlen⟩
  let ilkBytes : ByteArray :=
    { data := (EVM.Word.ofNat (fromBytesBigEndian bs)).toBytesBE.toArray }
  let vatBytes : ByteArray :=
    { data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray }
  have hsize : vatBytes.size = 32 := by
    simpa [vatBytes] using word_toBytesBE_toByteArray_size (EVM.Word.ofNat (↑v.vat : Nat))
  have hpost :
      PatchesWindowDisjoint32 7936 7968
        [(1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
          (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
          (8747, ilkBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse
    all_goals first | (unfold PatchWindowDisjoint32; omega) | cases hfalse
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre :=
      [(1463, vatBytes), (2437, vatBytes), (3145, vatBytes), (4318, vatBytes),
       (4441, vatBytes), (4751, vatBytes), (5115, vatBytes), (6295, vatBytes)])
    (post :=
      [(1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
       (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
       (8747, ilkBytes)])
    (off := 7936) (value := vatBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        hilk, hlen, List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperRedoVatPush32Decode7935 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    decode code (⟨7935⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (↑v.vat : Nat), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (by apply clipperRuntimePatchesWindowDisjoint32Bool v; native_decide)]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 7936 7968), 32)) =
    some (Operation.Push Operation.POp.PUSH32,
      some (EVM.Word.ofNat (↑v.vat : Nat), 32))
  rw [clipperRedoVatPatchPayload7936 v hpatch, uInt256OfByteArray_word_toBytesBE]

set_option maxHeartbeats 1000000 in
theorem RD.clipperRedoPayoutToSuckGuard {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {coin chost oldCoin chip tip feedPrice lot tab done topNew tic usr two kpr id ret sel :
      UInt256}
    {R : List UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨7932⟩
      (coin :: chost :: oldCoin :: chip :: tip :: feedPrice :: lot :: tab :: done :: topNew ::
        tic :: usr :: two :: kpr :: id :: ret :: sel :: R)
      mem (UInt256.ofNat 7) o (cA, σ) k C)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 50 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8079⟩
      (clipperRedoVatTarget v :: clipperRedoVatTarget v :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: clipperRedoSuckSelectorWord ::
        clipperRedoVatTarget v :: chost :: coin :: chip :: tip :: feedPrice :: lot :: tab ::
        done :: topNew :: tic :: usr :: two :: kpr :: id :: ret :: sel :: R)
      (clipperRedoSuckCalldataMem σ ee kpr coin mem) (UInt256.ofNat 8) o (cA, σ) k' C' := by
  let vatWord : UInt256 := EVM.Word.ofNat (↑v.vat : Nat)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))) = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hcallMload64 :=
    clipperRedoSuckCalldataMem_mload64 σ ee kpr coin hmem hread64
  have rdVatPre := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  have rdVat := RD.pushConst rdVatPre vatWord (width := 32) (op := .PUSH32)
    (by decide) (by simpa [vatWord] using clipperRedoVatPush32Decode7935 v hpatch) (by evm_ov)
  have rdVowSlotPre := evm_run rdVat with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push4 clipperRedoSuckSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨2⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdVowSlot⟩ := rdVowSlotPre.sload (by clipper_runtime_decode) (by evm_ov)
  have rd7995Raw := evm_run rdVowSlot with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨256⟩ (by clipper_runtime_decode) (by evm_ov),
    raw exp (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw div (by clipper_runtime_decode) (by evm_ov)]
  have hexp : UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ := by native_decide
  have hdiv : UInt256.div (solcSlotWord σ ee ⟨2⟩) ⟨1⟩ = solcSlotWord σ ee ⟨2⟩ := by
    apply u256_inj
    rw [udiv_toNat]
    exact Nat.div_one _
  have hpc7995 :
      (⟨7932⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 33 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + UInt256.ofNat 5 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨7995⟩ := by
    native_decide
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by native_decide
  have hvatEq :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) vatWord =
        clipperRedoVatTarget v := by
    rw [hmask]
  obtain ⟨_, _, rd7995⟩ : ∃ k C, RD code ee g s0 ⟨7995⟩
      (solcSlotWord σ ee ⟨2⟩ :: clipperRedoSuckSelectorWord ::
        clipperRedoVatTarget v :: chost :: coin :: chip :: tip :: feedPrice :: lot :: tab ::
        done :: topNew :: tic :: usr :: two :: kpr :: id :: ret :: sel :: R)
      mem (UInt256.ofNat 7) o (cA, σ) k C := by
    exact ⟨_, _, by
      simpa only [hexp, hdiv, hpc7995, hvatEq, solcSlotWord]
        using rd7995Raw⟩
  have rd8004Raw := evm_run rd7995 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov)]
  have hpc8004 :
      (⟨7995⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ = ⟨8004⟩ := by native_decide
  obtain ⟨_, _, rd8004⟩ : ∃ k C, RD code ee g s0 ⟨8004⟩
      (clipperRedoVowTarget σ ee :: clipperRedoSuckSelectorWord ::
        clipperRedoVatTarget v :: chost :: coin :: chip :: tip :: feedPrice :: lot :: tab ::
        done :: topNew :: tic :: usr :: two :: kpr :: id :: ret :: sel :: R)
      mem (UInt256.ofNat 7) o (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [hpc8004, clipperRedoVowTarget,
        show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by native_decide] using rd8004Raw⟩
  have rd8005 := RD.clipperDup16 rd8004 (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rdMemPre := evm_run rd8005 with [
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rdMem := rdMemPre.mload 0 ⟨128⟩ (UInt256.ofNat 7)
    (by clipper_runtime_decode) mem_cost hmload64 (by decide) (by evm_ov)
  have rdSelectorPre := evm_run rdMem with [
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨224⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have hselectorShift :
      UInt256.shiftLeft
          (UInt256.land (⟨4294967295⟩ : UInt256) clipperRedoSuckSelectorWord) ⟨224⟩ =
        clipperRedoSuckSelectorShifted := by native_decide
  have rdSelector := rdSelectorPre.mstore 0 (clipperRedoSuckSelectorMem mem)
    (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
    (by rw [hselectorShift]; rfl) (by decide) (by evm_ov)
  have rdVowPre := evm_run rdSelector with [
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have hvowClean :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (clipperRedoVowTarget σ ee) = clipperRedoVowTarget σ ee := by
    rw [hmask]
    have hcanon : (clipperRedoVowTarget σ ee).toNat < EVM.addressModulus := by
      unfold clipperRedoVowTarget
      rw [u256_land_comm]
      exact solcAddrMask_result_canonical (solcSlotWord σ ee ⟨2⟩)
    exact solcAddrMask_clean_left hcanon
  have rdVow := rdVowPre.mstore 0 (clipperRedoSuckVowMem σ ee mem)
    (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
    (by
      rw [hvowClean,
        show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat = 132 from by native_decide]
      rfl)
    (by decide) (by evm_ov)
  have rdKprPre := evm_run rdVow with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rdKpr := rdKprPre.mstore 0 (clipperRedoSuckKprMem σ ee kpr mem)
    (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
    (by
      rw [hmask,
        show ((⟨32⟩ : UInt256) + (⟨4⟩ + ⟨128⟩)).toNat = 164 from by native_decide]
      rfl)
    (by decide) (by evm_ov)
  have rdCoinPre := evm_run rdKpr with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rdCoin := rdCoinPre.mstore 3 (clipperRedoSuckCalldataMem σ ee kpr coin mem)
    (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
    (by
      rw [show ((⟨32⟩ : UInt256) + (⟨32⟩ + (⟨4⟩ + ⟨128⟩))).toNat = 196 from by
        native_decide]
      rfl)
    (by native_decide) (by evm_ov)
  have rdCallFramePre := evm_run rdCoin with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rdCallFrame := rdCallFramePre.mload 0 ⟨128⟩ (UInt256.ofNat 8)
    (by clipper_runtime_decode) mem_cost hcallMload64 (by decide) (by evm_ov)
  have rd8079 := evm_run rdCallFrame with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [vatWord, clipperRedoVatTarget, clipperRedoVowTarget,
      clipperRedoKprTarget, clipperRedoSuckSelectorWord, solcSlotWord,
      u256_land_comm] using rd8079⟩

theorem clipperRedoVatTargetAddress (v : ClipperImmutables) :
    AccountAddress.ofUInt256 (clipperRedoVatTarget v) = v.vat := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  have hvatWordToNat : (EVM.Word.ofNat (↑v.vat : Nat)).toNat = ↑v.vat := by
    simp [EVM.Word.ofNat, UInt256.ofNat, UInt256.toNat, Fin.ofNat]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le v.vat.isLt (by decide))
  have hclean :
      UInt256.land solcAddrMask (EVM.Word.ofNat (↑v.vat : Nat)) =
        EVM.Word.ofNat (↑v.vat : Nat) := by
    exact solcAddrMask_clean_left (w := EVM.Word.ofNat (↑v.vat : Nat)) (by
      rw [hvatWordToNat]
      simp [EVM.addressModulus, EVM.twoPow, AccountAddress.size])
  rw [clipperRedoVatTarget, hclean]
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat (EVM.Word.ofNat (↑v.vat : Nat))]
  simpa [EVM.Word.ofNat] using AccountAddress.ofUInt256_ofNat v.vat

theorem clipperRedoEVMAddressAccountAddress (a : AccountAddress) :
    EVM.address a = a := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])

theorem RD.clipperRedoSuckNoCode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {chost coin chip tip feedPrice lot tab done topNew tic usr two kpr id ret sel : UInt256}
    {R : List UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8079⟩
      (clipperRedoVatTarget v :: clipperRedoVatTarget v :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: clipperRedoSuckSelectorWord ::
        clipperRedoVatTarget v :: chost :: coin :: chip :: tip :: feedPrice :: lot :: tab ::
        done :: topNew :: tic :: usr :: two :: kpr :: id :: ret :: sel :: R)
      mem (UInt256.ofNat 8) o (cA, σ) k C)
    (hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ (clipperRedoVatTarget v) = ⟨0⟩)
    (hov : R.length + 50 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨8079⟩) (okPc := ⟨8091⟩)
    rd hcodeSizeVat
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperRedoSuckPostCall
    {cA0 cA gh bl σ₀ σStart σ} {ee : ExecutionEnv}
    {g : Sat256} {A : Substate} {k C : ℕ}
    {chost coin chip tip feedPrice lot tab done topNew tic usr two kpr id ret sel : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd : RD code ee g (initState cA0 gh bl σStart σ₀ g A ee) ⟨8079⟩
      (clipperRedoVatTarget v :: clipperRedoVatTarget v :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: clipperRedoSuckSelectorWord ::
        clipperRedoVatTarget v :: chost :: coin :: chip :: tip :: feedPrice :: lot :: tab ::
        done :: topNew :: tic :: usr :: two :: kpr :: id :: ret :: sel :: R)
      (clipperRedoSuckCalldataMem σ ee kpr coin mem)
      (UInt256.ofNat 8) rdata (cA, σ) k C)
    (hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ (clipperRedoVatTarget v) ≠ ⟨0⟩)
    (hdepth : ee.depth.val < 1024) (hperm : ee.perm = true)
    (hmem : mem.size = 196) (hov : R.length + 50 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code ee g (initState cA0 gh bl σStart σ₀ g A ee) ⟨8095⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperRedoSuckSelectorWord ::
          clipperRedoVatTarget v :: chost :: coin :: chip :: tip :: feedPrice :: lot :: tab ::
          done :: topNew :: tic :: usr :: two :: kpr :: id :: ret :: sel :: R)
        (clipperRedoSuckCalldataMem σ ee kpr coin mem) (UInt256.ofNat 8) out
        (cA', σ') k' C' ∧
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A ee with
          accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "suck" 0
        [.address (AccountAddress.ofNat (clipperRedoVowTarget σ ee).toNat),
          .address (AccountAddress.ofNat kpr.toNat), .int (Int.ofNat coin.toNat)]
        (z,
          { initState cA0 gh bl σStart σ₀ g A ee with
            accountMap := σ'
            substate := A'
            createdAccounts := cA' },
          out) true ∧
      out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd8094⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨8079⟩) (okPc := ⟨8091⟩)
      rd hcodeSizeVat
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperRedoJumpDest8091 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, out, A_in, callGas, k8095, C8095, hΘpack,
      rd8095raw, houtSize⟩ :=
    RD.call rd8094 (by clipper_runtime_decode) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k8095, C8095, ?_, ?_, houtSize⟩
  · have hmin :
        (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
        show (0 : Nat) ≤ (UInt256.ofNat out.size).val.val
        exact Nat.zero_le _
      simp [min, hle]
    have haw :
        UInt256.ofNat
          (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
            (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
            (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) =
          UInt256.ofNat 8 := by native_decide
    simpa [hmin, byteArray_write_len_zero, haw] using rd8095raw
  · let evmVat : EVM.State :=
      { initState cA0 gh bl σStart σ₀ g A ee with
        accountMap := σ, createdAccounts := cA }
    refine callCoincides (cfg := config v)
      (evm := evmVat) (name := "suck")
      (args :=
        [.address (AccountAddress.ofNat (clipperRedoVowTarget σ ee).toNat),
          .address (AccountAddress.ofNat kpr.toNat), .int (Int.ofNat coin.toNat)])
      (tgt := EVM.address v.vat) (targetWord := clipperRedoVatTarget v)
      (cA' := cA') (σ' := σ') (A' := A') (A_in := A_in)
      (z := z) (o := out) (g'' := g'') (callGas := callGas)
      (mem := clipperRedoSuckCalldataMem σ ee kpr coin mem)
      (inOff := ⟨128⟩) (inSize := ⟨100⟩) (callPerm := true)
      (fun h => absurd hdepth (by
        have hee : ee.depth = (1024 : Fin 1025) := by
          simpa [evmVat, initState] using h
        rw [hee]
        decide))
      ?_ ?_ ?_
    · rw [clipperRedoVatTargetAddress v]
      exact clipperRedoEVMAddressAccountAddress v.vat
    · simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        show (⟨100⟩ : UInt256).toNat = 100 from by decide] using
        clipperRedoSuckEncode_eq v σ ee kpr coin hmem
    · simpa [evmVat, initState, hperm] using hΘ

theorem RD.clipperRedoSuckCallFailure {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD code ee g s0 ⟨8095⟩ (⟨0⟩ :: R) mem aw out acc k C)
    (hout : out.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨8095⟩) (okPc := ⟨8111⟩)
    rd (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    hout hov

theorem RD.clipperRedoSuckCallSuccess {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {chost coin chip tip feedPrice lot tab done topNew tic usr two kpr id ret sel : UInt256}
    {R : List UInt256} {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8095⟩
      (⟨1⟩ :: ⟨228⟩ :: clipperRedoSuckSelectorWord :: clipperRedoVatTarget v ::
        chost :: coin :: chip :: tip :: feedPrice :: lot :: tab :: done :: topNew :: tic ::
        usr :: two :: kpr :: id :: ret :: sel :: R)
      mem aw out acc k C)
    (hov : R.length + 50 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8118⟩
      (coin :: chip :: tip :: feedPrice :: lot :: tab :: done :: topNew :: tic :: usr ::
        two :: kpr :: id :: ret :: sel :: R)
      mem aw out acc k' C' := by
  obtain ⟨_, _, rd8113⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨8095⟩) (okPc := ⟨8111⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (clipperRedoJumpDest8111 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd8113 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]⟩

end Benchmarks.Dss.Clipper
