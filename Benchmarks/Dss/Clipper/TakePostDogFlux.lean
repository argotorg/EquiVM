import Benchmarks.Dss.Clipper.TakeOweVatFlux
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperTakeIlkPatchPayload5046 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    code.extract' 5046 5078 =
      ({ data := (EVM.Word.ofNat (fromBytesBigEndian bs)).toBytesBE.toArray } :
        ByteArray) := by
  let ilkBytes : ByteArray :=
    { data := (EVM.Word.ofNat (fromBytesBigEndian bs)).toBytesBE.toArray }
  let vatBytes : ByteArray :=
    { data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray }
  have hsize : ilkBytes.size = 32 := by
    simpa [ilkBytes] using
      word_toBytesBE_toByteArray_size (EVM.Word.ofNat (fromBytesBigEndian bs))
  have hpost :
      PatchesWindowDisjoint32 5046 5078
        [(6800, ilkBytes), (8747, ilkBytes), (1463, vatBytes), (2437, vatBytes),
          (3145, vatBytes), (4318, vatBytes), (4441, vatBytes), (4751, vatBytes),
          (5115, vatBytes), (6295, vatBytes), (7936, vatBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | hfalse
    all_goals first | (unfold PatchWindowDisjoint32; omega) | cases hfalse
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre :=
      [(1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
        (4239, ilkBytes), (4866, ilkBytes)])
    (post :=
      [(6800, ilkBytes), (8747, ilkBytes), (1463, vatBytes), (2437, vatBytes),
        (3145, vatBytes), (4318, vatBytes), (4441, vatBytes), (4751, vatBytes),
        (5115, vatBytes), (6295, vatBytes), (7936, vatBytes)])
    (off := 5046) (value := ilkBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, hilk,
        hlen, List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperTakeIlkPush32Decode5045 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {bs : List UInt8} (hilk : v.ilk = .fixedBytes ⟨31, by decide⟩ bs)
    (hlen : bs.length = 32) :
    decode code (⟨5045⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (fromBytesBigEndian bs), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (clipperRuntimePatchesWindowDisjoint32Bool v (⟨5045⟩ : UInt256).toNat
      ((⟨5045⟩ : UInt256).toNat + 1) (by native_decide))]
  norm_num
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 5046 5078), 32)) =
    some (Operation.Push Operation.POp.PUSH32,
      some (EVM.Word.ofNat (fromBytesBigEndian bs), 32))
  rw [clipperTakeIlkPatchPayload5046 v hpatch hilk hlen]
  rw [uInt256OfByteArray_word_toBytesBE]

theorem clipperTakeVatPatchPayload5115 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    code.extract' 5115 5147 =
      ({ data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray } : ByteArray) := by
  rcases v.ilk_wf with ⟨bs, hilk, hlen⟩
  let ilkBytes : ByteArray :=
    { data := (EVM.Word.ofNat (fromBytesBigEndian bs)).toBytesBE.toArray }
  let vatBytes : ByteArray :=
    { data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray }
  have hsize : vatBytes.size = 32 := by
    simpa [vatBytes] using word_toBytesBE_toByteArray_size (EVM.Word.ofNat (↑v.vat : Nat))
  have hpost :
      PatchesWindowDisjoint32 5115 5147 [(6295, vatBytes), (7936, vatBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff] at hp
    rcases hp with rfl | rfl | hfalse
    · unfold PatchWindowDisjoint32; omega
    · unfold PatchWindowDisjoint32; omega
    · cases hfalse
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre :=
      [(1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
        (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
        (8747, ilkBytes), (1463, vatBytes), (2437, vatBytes), (3145, vatBytes),
        (4318, vatBytes), (4441, vatBytes), (4751, vatBytes)])
    (post := [(6295, vatBytes), (7936, vatBytes)])
    (off := 5115) (value := vatBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, hilk,
        hlen, List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize hpost (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperTakeVatPush32Decode5114 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    decode code (⟨5114⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (↑v.vat : Nat), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (clipperRuntimePatchesWindowDisjoint32Bool v (⟨5114⟩ : UInt256).toNat
      ((⟨5114⟩ : UInt256).toNat + 1) (by native_decide))]
  norm_num
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 5115 5147), 32)) =
    some (Operation.Push Operation.POp.PUSH32,
      some (EVM.Word.ofNat (↑v.vat : Nat), 32))
  rw [clipperTakeVatPatchPayload5115 v hpatch]
  rw [uInt256OfByteArray_word_toBytesBE]

theorem clipperTakeVatFluxCalldataMem_eq_writeCascade (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) (mem : ByteArray) :
    clipperTakeVatFluxCalldataMem v I who slice mem =
      writeCascade mem
        [(128, clipperTakeVatFluxSelectorShifted), (132, clipperTakeIlkWord v),
          (164, clipperTakeThisWord I), (196, UInt256.land solcAddrMask who),
          (228, slice)] := by
  rfl

theorem clipperTakeVatFluxCalldataMem_size_260 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).size = 260 := by
  rw [clipperTakeVatFluxCalldataMem_eq_writeCascade]
  exact writeCascade_size_of_base mem _ hmem (by norm_num [WriteGapsOk])
    (by norm_num [writeCascadeSize])

theorem clipperTakeVatFluxCalldataMem_read64_260 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [clipperTakeVatFluxCalldataMem_eq_writeCascade,
    writeCascade_read_preserved_of_base mem _ hmem (by norm_num [WindowDisjointFromWrites])]
  exact hread64

theorem clipperTakeVatFluxSelectorMem_size_260 {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperTakeVatFluxSelectorMem mem).size = 260 := by
  unfold clipperTakeVatFluxSelectorMem
  exact toByteArray_write32_size_of_le mem clipperTakeVatFluxSelectorShifted
    128 260 260 hmem (by rw [hmem]; omega) (by omega)

theorem clipperTakeVatFluxIlkMem_size_260 (v : ClipperImmutables) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperTakeVatFluxIlkMem v mem).size = 260 := by
  unfold clipperTakeVatFluxIlkMem
  exact toByteArray_write32_size_of_le (clipperTakeVatFluxSelectorMem mem)
    (clipperTakeIlkWord v) 132 260 260
    (clipperTakeVatFluxSelectorMem_size_260 hmem)
    (by rw [clipperTakeVatFluxSelectorMem_size_260 hmem]; omega) (by omega)

theorem clipperTakeVatFluxThisMem_size_260 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperTakeVatFluxThisMem I mem).size = 260 := by
  unfold clipperTakeVatFluxThisMem
  exact toByteArray_write32_size_of_le mem (clipperTakeThisWord I) 164 260 260 hmem
    (by rw [hmem]; omega) (by omega)

theorem clipperTakeVatFluxWhoMem_size_260 (who : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperTakeVatFluxWhoMem who mem).size = 260 := by
  unfold clipperTakeVatFluxWhoMem
  exact toByteArray_write32_size_of_le mem (UInt256.land solcAddrMask who)
    196 260 260 hmem (by rw [hmem]; omega) (by omega)

theorem clipperTakeVatFluxCalldataMem_read128_4_260 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 128 4 =
      vatFluxSelector := by
  have hIlk : (clipperTakeVatFluxIlkMem v mem).size = 260 :=
    clipperTakeVatFluxIlkMem_size_260 v hmem
  have hThis :
      (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem)).size = 260 :=
    clipperTakeVatFluxThisMem_size_260 I hIlk
  have hWho :
      (clipperTakeVatFluxWhoMem who
        (clipperTakeVatFluxThisMem I (clipperTakeVatFluxIlkMem v mem))).size = 260 :=
    clipperTakeVatFluxWhoMem_size_260 who hThis
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_below_len _ _ 228 128 4 (by rw [toByteArray_size])
    (by rw [hWho]; omega) (by omega) (by rw [hWho]; omega) (by norm_num) (by norm_num)]
  unfold clipperTakeVatFluxWhoMem
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (by rw [hThis]; omega) (by omega) (by rw [hThis]; omega) (by norm_num)
    (by norm_num)]
  unfold clipperTakeVatFluxThisMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [hIlk]; omega) (by omega) (by rw [hIlk]; omega) (by norm_num)
    (by norm_num)]
  unfold clipperTakeVatFluxIlkMem
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeVatFluxSelectorMem_size_260 hmem]; omega) (by omega)
    (by rw [clipperTakeVatFluxSelectorMem_size_260 hmem]; omega) (by norm_num)
    (by norm_num)]
  unfold clipperTakeVatFluxSelectorMem
  rw [toByteArray_write_read_window_of_gap clipperTakeVatFluxSelectorShifted mem
    128 0 4 (by norm_num) (by norm_num) (by norm_num) (by rw [hmem]; native_decide)]
  rw [toByteArray_eq_toBytesBE]
  native_decide

theorem clipperTakeVatFluxCalldataMem_read132_32_260 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 132 32 =
      UInt256.toByteArray (clipperTakeIlkWord v) := by
  have hIlk := clipperTakeVatFluxIlkMem_size_260 v hmem
  have hThis := clipperTakeVatFluxThisMem_size_260 I hIlk
  have hWho := clipperTakeVatFluxWhoMem_size_260 who hThis
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_below _ _ 228 132 (by rw [toByteArray_size])
    (by rw [hWho]; omega) (by omega)]
  unfold clipperTakeVatFluxWhoMem
  rw [write32_read_below _ _ 196 132 (by rw [toByteArray_size])
    (by rw [hThis]; omega) (by omega)]
  unfold clipperTakeVatFluxThisMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
    (by rw [hIlk]; omega) (by omega)]
  unfold clipperTakeVatFluxIlkMem
  rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
    (by rw [clipperTakeVatFluxSelectorMem_size_260 hmem]; omega)]
  exact toByteArray_extract_all _

theorem clipperTakeVatFluxCalldataMem_read164_32_260 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 164 32 =
      UInt256.toByteArray (clipperTakeThisWord I) := by
  have hIlk := clipperTakeVatFluxIlkMem_size_260 v hmem
  have hThis := clipperTakeVatFluxThisMem_size_260 I hIlk
  have hWho := clipperTakeVatFluxWhoMem_size_260 who hThis
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_below _ _ 228 164 (by rw [toByteArray_size])
    (by rw [hWho]; omega) (by omega)]
  unfold clipperTakeVatFluxWhoMem
  rw [write32_read_below _ _ 196 164 (by rw [toByteArray_size])
    (by rw [hThis]; omega) (by omega)]
  unfold clipperTakeVatFluxThisMem
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size]) (by rw [hIlk]; omega)]
  exact toByteArray_extract_all _

theorem clipperTakeVatFluxCalldataMem_read196_32_260 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 196 32 =
      UInt256.toByteArray (UInt256.land solcAddrMask who) := by
  have hIlk := clipperTakeVatFluxIlkMem_size_260 v hmem
  have hThis := clipperTakeVatFluxThisMem_size_260 I hIlk
  have hWho := clipperTakeVatFluxWhoMem_size_260 who hThis
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_below _ _ 228 196 (by rw [toByteArray_size])
    (by rw [hWho]; omega) (by omega)]
  unfold clipperTakeVatFluxWhoMem
  rw [write32_read_back _ _ 196 (by rw [toByteArray_size]) (by rw [hThis]; omega)]
  exact toByteArray_extract_all _

theorem clipperTakeVatFluxCalldataMem_read228_32_260 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 228 32 =
      UInt256.toByteArray slice := by
  have hIlk := clipperTakeVatFluxIlkMem_size_260 v hmem
  have hThis := clipperTakeVatFluxThisMem_size_260 I hIlk
  have hWho := clipperTakeVatFluxWhoMem_size_260 who hThis
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_back _ _ 228 (by rw [toByteArray_size]) (by rw [hWho]; omega)]
  exact toByteArray_extract_all _

theorem clipperTakeVatFluxCalldataMem_read128_132_260 (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 128 132 =
      vatFluxSelector ++ UInt256.toByteArray (clipperTakeIlkWord v) ++
        UInt256.toByteArray (clipperTakeThisWord I) ++
        UInt256.toByteArray (UInt256.land solcAddrMask who) ++
        UInt256.toByteArray slice := by
  rw [byteArray_readWithPadding_split _ 128 4 128 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatFluxCalldataMem_size_260 v I who slice hmem])]
  rw [byteArray_readWithPadding_split _ 132 32 96 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatFluxCalldataMem_size_260 v I who slice hmem])]
  rw [byteArray_readWithPadding_split _ 164 32 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatFluxCalldataMem_size_260 v I who slice hmem])]
  rw [byteArray_readWithPadding_split _ 196 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatFluxCalldataMem_size_260 v I who slice hmem])]
  rw [clipperTakeVatFluxCalldataMem_read128_4_260 v I who slice hmem,
    clipperTakeVatFluxCalldataMem_read132_32_260 v I who slice hmem,
    clipperTakeVatFluxCalldataMem_read164_32_260 v I who slice hmem,
    clipperTakeVatFluxCalldataMem_read196_32_260 v I who slice hmem,
    clipperTakeVatFluxCalldataMem_read228_32_260 v I who slice hmem]
  simp [ByteArray.append_assoc]

theorem clipperTakeVatFluxEncode_eq_260 (v : ClipperImmutables) (I : ExecutionEnv)
    (who slice : UInt256) {mem : ByteArray} (hmem : mem.size = 260) :
    (config v).externalABI.encode? "flux"
      [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
        .int (Int.ofNat slice.toNat)] =
      some ((clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 128 132) := by
  rw [clipperTakeVatFluxCalldataMem_read128_132_260 v I who slice hmem]
  let base : ByteArray := ByteArray.empty ++ ffi.ByteArray.zeroes 196
  have hbase : base.size = 196 := by
    simp [base, ByteArray_zeroes_size]
  have h := clipperTakeVatFluxEncode_eq v I who slice (mem := base) hbase
  rw [clipperTakeVatFluxCalldataMem_read128_132 v I who slice hbase] at h
  exact h

set_option maxHeartbeats 2000000 in
theorem RD.clipperTakePostDogFluxExtcodesizeGuard {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨5025⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      mem (UInt256.ofNat 9) rdata (cA, σ) k C)
    (htabNew : tabNew = ⟨0⟩)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    ∃ k' C', RD code ee g s0 ⟨5177⟩
      (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
        clipperTakeVatTarget v :: owe :: tabNew :: lotNew :: price :: tic :: packed ::
          stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      (clipperTakeVatFluxCalldataMem v ee packed lotNew mem)
      (UInt256.ofNat 9) rdata (cA, σ) k' C' := by
  rcases v.ilk_wf with ⟨ilkBs, hilk, hlen⟩
  let ilkWord : UInt256 := EVM.Word.ofNat (fromBytesBigEndian ilkBs)
  let vatWord : UInt256 := EVM.Word.ofNat (↑v.vat : Nat)
  have hbaseMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (mem := mem) (aw := UInt256.ofNat 9)
      (by rw [hmem]; decide) (by decide) hread64
  have hcallMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (clipperTakeVatFluxCalldataMem v ee packed lotNew mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperTakeVatFluxCalldataMem v ee packed lotNew mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
    mloadFreePtrValue (mem := clipperTakeVatFluxCalldataMem v ee packed lotNew mem)
      (aw := UInt256.ofNat 9)
      (by rw [clipperTakeVatFluxCalldataMem_size_260 v ee packed lotNew hmem]; decide)
      (by decide)
      (clipperTakeVatFluxCalldataMem_read64_260 v ee packed lotNew hmem hread64)
  have rd5030pre := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨5222⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd5031 := rd5030pre.jumpiNT (by clipper_runtime_decode) htabNew (by evm_ov)
  have rd5034pre := evm_run rd5031 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  have rd5035 := rd5034pre.mload 0 ⟨128⟩ (UInt256.ofNat 9)
    (by clipper_runtime_decode) mem_cost hbaseMload64 (by native_decide) (by evm_ov)
  have rd5044pre := evm_run rd5035 with [
    raw push4 clipperTakeVatFluxSelectorSeed (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨225⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.shiftLeft clipperTakeVatFluxSelectorSeed ⟨225⟩ =
    clipperTakeVatFluxSelectorShifted from by native_decide] at rd5044pre
  have rd5045 := rd5044pre.mstore 0 (clipperTakeVatFluxSelectorMem mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd5078 := rd5045.pushConst ilkWord (width := 32) (op := .PUSH32) (by decide)
    (by simpa [ilkWord] using clipperTakeIlkPush32Decode5045 v hpatch hilk hlen)
    (by evm_ov)
  have rd5082pre := evm_run rd5078 with [
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide] at rd5082pre
  have rd5083 := rd5082pre.mstore 0 (clipperTakeVatFluxIlkMem v mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost
    (by
      rw [show (⟨132⟩ : UInt256).toNat = 132 from by decide]
      simp [clipperTakeVatFluxIlkMem, clipperTakeIlkWord, hilk, ilkWord])
    (by native_decide) (by evm_ov)
  have rd5088pre := evm_run rd5083 with [
    raw address (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide] at rd5088pre
  have rd5089 := rd5088pre.mstore 0
    (clipperTakeVatFluxThisMem ee (clipperTakeVatFluxIlkMem v mem))
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd5104pre := evm_run rd5089 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup9 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd5104pre
  rw [show (⟨128⟩ : UInt256) + ⟨68⟩ = ⟨196⟩ from by native_decide] at rd5104pre
  have rd5105 := rd5104pre.mstore 0
    (clipperTakeVatFluxWhoMem packed
      (clipperTakeVatFluxThisMem ee (clipperTakeVatFluxIlkMem v mem)))
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd5111pre := evm_run rd5105 with [
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨100⟩ = ⟨228⟩ from by native_decide] at rd5111pre
  have rd5112 := rd5111pre.mstore 0
    (clipperTakeVatFluxCalldataMem v ee packed lotNew mem)
    (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost (by rfl)
    (by native_decide) (by evm_ov)
  have rd5113pre := evm_run rd5112 with [
    raw swap2 (by clipper_runtime_decode) (by evm_ov)]
  have rd5114 := rd5113pre.mload 0 ⟨128⟩ (UInt256.ofNat 9)
    (by clipper_runtime_decode) mem_cost hcallMload64 (by native_decide) (by evm_ov)
  have rd5147 := rd5114.pushConst vatWord (width := 32) (op := .PUSH32) (by decide)
    (by simpa [vatWord] using clipperTakeVatPush32Decode5114 v hpatch) (by evm_ov)
  have rd5177 := evm_run rd5147 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw push4 clipperTakeVatFluxSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨132⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨132⟩ = ⟨260⟩ from by native_decide] at rd5177
  rw [show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ = ⟨0⟩ from by native_decide]
    at rd5177
  rw [show (⟨0⟩ : UInt256) + ⟨132⟩ = ⟨132⟩ from by native_decide] at rd5177
  exact ⟨_, _, by simpa [clipperTakeVatTarget, vatWord, u256_land_comm] using rd5177⟩

theorem clipperTakeJumpDest5189 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨5189⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 6000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none => simp [hIlk]; native_decide
  | some bs => simp [hIlk]; native_decide

theorem clipperTakeJumpDest5209 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨5209⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 6000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none => simp [hIlk]; native_decide
  | some bs => simp [hIlk]; native_decide

theorem RD.clipperTakePostDogFluxNoCode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨5177⟩
      (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
        clipperTakeVatTarget v :: owe :: tabNew :: lotNew :: price :: tic :: packed ::
          stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      mem (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hcodeSizeVat : extCodeSizeWord σ (clipperTakeVatTarget v) = ⟨0⟩) :
    RDrev code g s0 := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨5177⟩) (okPc := ⟨5189⟩)
    rd hcodeSizeVat
    (by clipper_runtime_decode) (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakePostDogFluxPostCall {cA0 cA gh bl σ₀ σStart σ I}
    {g : Sat256} {A : Substate} {k C : ℕ}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {baseMem rdata : ByteArray} (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd : RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨5177⟩
      (clipperTakeVatTarget v :: clipperTakeVatTarget v :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨132⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
        clipperTakeVatTarget v :: owe :: tabNew :: lotNew :: price :: tic :: packed ::
          stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      (clipperTakeVatFluxCalldataMem v I packed lotNew baseMem)
      (UInt256.ofNat 9) rdata (cA, σ) k C)
    (hbaseMem : baseMem.size = 260)
    (hcodeSizeVat : extCodeSizeWord σ (clipperTakeVatTarget v) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true) :
    ∃ (cA_vat : Batteries.RBSet AccountAddress compare) (σ_vat : AccountMap)
      (zVat : Bool) (outVat : ByteArray) (A_vat : Substate) (k' C' : ℕ),
      RD code I g (initState cA0 gh bl σStart σ₀ g A I) ⟨5193⟩
        ((if zVat then ⟨1⟩ else ⟨0⟩) :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord ::
          clipperTakeVatTarget v :: owe :: tabNew :: lotNew :: price :: tic :: packed ::
            stopped :: dataLen :: dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
        (outVat.write 0 (clipperTakeVatFluxCalldataMem v I packed lotNew baseMem)
          128 (min (⟨0⟩ : UInt256) (UInt256.ofNat outVat.size)).toNat)
        (UInt256.ofNat
          (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
            (⟨128⟩ : UInt256).toNat (⟨132⟩ : UInt256).toNat)
            (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat))
        outVat (cA_vat, σ_vat) k' C' ∧
      typedCallViaEVM (config v)
        { initState cA0 gh bl σStart σ₀ g A I with
          accountMap := σ, createdAccounts := cA }
        (EVM.address v.vat) "flux" 0
        [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat packed.toNat),
          .int (Int.ofNat lotNew.toNat)]
        (zVat,
          { initState cA0 gh bl σStart σ₀ g A I with
            accountMap := σ_vat
            substate := A_vat
            createdAccounts := cA_vat },
          outVat) true ∧
      outVat.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd5192⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨5177⟩) (okPc := ⟨5189⟩)
      rd hcodeSizeVat
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperTakeJumpDest5189 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cA_vat, σ_vat, zVat, outVat, A_in, callGas, k5193, C5193, hΘpack,
      rd5193, houtVatSize⟩ :=
    RD.call rd5192 (by clipper_runtime_decode) hdepth (by evm_ov)
  obtain ⟨g'', A_vat, hΘ⟩ := hΘpack
  refine ⟨cA_vat, σ_vat, zVat, outVat, A_vat, k5193, C5193, rd5193, ?_,
    houtVatSize⟩
  let evmVat : EVM.State :=
    { initState cA0 gh bl σStart σ₀ g A I with
      accountMap := σ, createdAccounts := cA }
  refine callCoincides (cfg := config v) (evm := evmVat) (name := "flux")
    (args := [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat packed.toNat),
      .int (Int.ofNat lotNew.toNat)])
    (tgt := EVM.address v.vat) (targetWord := clipperTakeVatTarget v)
    (cA' := cA_vat) (σ' := σ_vat) (A' := A_vat) (A_in := A_in)
    (z := zVat) (o := outVat) (g'' := g'') (callGas := callGas)
    (mem := clipperTakeVatFluxCalldataMem v I packed lotNew baseMem)
    (inOff := ⟨128⟩) (inSize := ⟨132⟩) (callPerm := true)
    (fun h => absurd hdepth (by
      have hI : I.depth = (1024 : Fin 1025) := by
        simpa [evmVat, initState] using h
      rw [hI]
      decide)) ?_ ?_ ?_
  · rw [clipperTakeVatTargetAddress v]
    exact clipperTakeEVMAddressAccountAddress v.vat
  · simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      show (⟨132⟩ : UInt256).toNat = 132 from by decide] using
      clipperTakeVatFluxEncode_eq_260 v I packed lotNew hbaseMem
  · simpa [evmVat, initState, hperm] using hΘ

theorem RD.clipperTakePostDogFluxCallFailure {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD code ee g s0 ⟨5193⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨5193⟩) (okPc := ⟨5209⟩)
    rd (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    hosz hov

theorem RD.clipperTakePostDogFluxCallSuccessToRemove {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel :
      UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨5193⟩
      (⟨1⟩ :: ⟨260⟩ :: clipperTakeVatFluxSelectorWord :: clipperTakeVatTarget v ::
        owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
          dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      mem aw o acc k C) :
    ∃ k' C', RD code ee g s0 ⟨8274⟩
      (id :: ⟨5020⟩ :: owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped ::
        dataLen :: dataStart :: who :: max :: amt :: id :: [⟨502⟩, sel])
      mem aw o acc k' C' := by
  obtain ⟨_, _, rd5211⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨5193⟩) (okPc := ⟨5209⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (clipperTakeJumpDest5209 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5221pre := evm_run rd5211 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨5020⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup14 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8274⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rd5221pre.jump (by clipper_runtime_decode)
    (clipperYankJumpDest8274 v hpatch) (by evm_ov)⟩

theorem clipperEvalTakeVatFluxUsrArgsAtDigsRet (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) :
    evalExprs? (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog [ilkExpr v, thisAddr, .var "usr", .var "lot"] =
        .ok
          [v.ilk, .address evmDog.executionEnv.codeOwner,
            .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLoc I).toNat),
            .int (Int.ofNat lotNew.toNat)] := by
  rcases v.ilk_wf with ⟨bs, hilk, _hlen⟩
  have hilkEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmDog (ilkExpr v) = .ok v.ilk := by
    simp [ilkExpr, hilk, evalExpr?, pure]
  have hthisEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmDog thisAddr = .ok (.address evmDog.executionEnv.codeOwner) := by
    simp [thisAddr, evalExpr?, envValue, pure]
  have husrEval :
      evalExpr? (config v)
        (Frame.mk (contract v)
          (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew))
        evmDog (.var "usr") =
          .ok (.address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLoc I).toNat)) := by
    simp only [evalExpr?]
    rw [clipperTakeLocalsDigsRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsMoveRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsDogLoaded, store_get_ne _ _ (by decide),
      clipperTakeLocalsFluxBuyerRet, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabAssigned, store_get_ne _ _ (by decide),
      clipperTakeLocalsLotNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsTabNew, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTabSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsOweTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe, store_get_ne _ _ (by decide),
      clipperTakeLocalsOwe0, store_get_ne _ _ (by decide),
      clipperTakeLocalsSlice, store_get_ne _ _ (by decide),
      clipperTakeLocalsTab, store_get_ne _ _ (by decide),
      clipperTakeLocalsLot, store_get_ne _ _ (by decide),
      clipperTakeLocalsPrice, store_get_ne _ _ (by decide),
      clipperTakeLocalsDone, store_get_ne _ _ (by decide),
      clipperTakeLocalsSt, store_get_ne _ _ (by decide),
      clipperTakeLocalsTic, store_get_ne _ _ (by decide),
      clipperTakeLocalsUsr, store_get_self]
    rfl
  have hlotEval :=
    clipperEvalTakeVarLotAtDigsRet v evmLoc evmRead evmVat evmDog I price slice
      owe0 owe slice' tabNew lotNew
  simp only [evalExprs?, hilkEval, hthisEval, husrEval, hlotEval, EvalResult.bind,
    bind, pure]

theorem clipperTakePostDogTabZeroFluxNoCodeBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    (hlotNew : lotNew ≠ ⟨0⟩) (htabNew : tabNew = ⟨0⟩)
    (hnoVatCode :
      (UInt256.ofNat ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite
              (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ],
        .assign .storage lockedRef (.intLit 0) ]
      .reverted := by
  let digsRetFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
        slice' tabNew lotNew)
  have hlotCond := clipperEvalTakeLotEqZeroAtDigsRet_false v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew hlotNew
  have htabCond := clipperEvalTakeTabEqZeroAtDigsRet_true v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew htabNew
  have hflux :
      ExecBlock (config v) digsRetFrame evmDog
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet")
        .reverted := by
    have hguard := clipperEvalTakeVatCodeGuard_false v evmDog digsRetFrame.locals hnoVatCode
    simpa [checkedExternalCallStmts, digsRetFrame] using
      (ExecBlock.consRevert (ExecStmt.requireFalse hguard))
  have htabIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite (.binary .eq (.var "tab") (.intLit 0))
          (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
            [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
            [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
          [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
            .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
        .reverted := by
    exact ExecStmt.iteTrue (by simpa [digsRetFrame] using htabCond)
      (execBlockAppendReverted hflux)
  have hlotIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
        .reverted := by
    exact ExecStmt.iteFalse (by simpa [digsRetFrame] using hlotCond)
      (ExecBlock.consRevert htabIte)
  exact ExecBlock.consRevert hlotIte

theorem clipperTakePostDogTabZeroFluxCallFailureBlock (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog evmFlux : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256) {outFlux : ByteArray}
    (hlotNew : lotNew ≠ ⟨0⟩) (htabNew : tabNew = ⟨0⟩)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallFlux :
      typedCallViaEVM (config v) evmDog (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmDog.executionEnv.codeOwner,
          .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLoc I).toNat),
          .int (Int.ofNat lotNew.toNat)]
        (false, evmFlux, outFlux) true) :
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite
              (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ],
        .assign .storage lockedRef (.intLit 0) ]
      .reverted := by
  let digsRetFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
        slice' tabNew lotNew)
  have hlotCond := clipperEvalTakeLotEqZeroAtDigsRet_false v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew hlotNew
  have htabCond := clipperEvalTakeTabEqZeroAtDigsRet_true v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew htabNew
  have hargs := clipperEvalTakeVatFluxUsrArgsAtDigsRet v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew
  have hguard := clipperEvalTakeVatCodeGuard_true v evmDog digsRetFrame.locals hvatCode
  have hflux :
      ExecBlock (config v) digsRetFrame evmDog
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet")
        .reverted := by
    simpa [checkedExternalCallStmts, digsRetFrame] using
      (checkedExternalCallFailure hguard
        (clipperEvalVat v evmDog digsRetFrame.locals) hargs hcallFlux)
  have htabIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite (.binary .eq (.var "tab") (.intLit 0))
          (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
            [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
            [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
          [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
            .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
        .reverted := by
    exact ExecStmt.iteTrue (by simpa [digsRetFrame] using htabCond)
      (execBlockAppendReverted hflux)
  have hlotIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
        .reverted := by
    exact ExecStmt.iteFalse (by simpa [digsRetFrame] using hlotCond)
      (ExecBlock.consRevert htabIte)
  exact ExecBlock.consRevert hlotIte

set_option maxHeartbeats 1000000 in
theorem clipperTakePostDogTabZeroFluxRemoveSourceOk (v : ClipperImmutables)
    (evmLoc evmRead evmVat evmDog evmFlux : EVM.State) (I : ExecutionEnv)
    (price slice owe0 owe slice' tabNew lotNew : UInt256)
    {outFlux : ByteArray} {acc : Account}
    (hlotNew : lotNew ≠ ⟨0⟩) (htabNew : tabNew = ⟨0⟩)
    (hvatCode :
      0 <
        (UInt256.ofNat
          ((evmDog.lookupAccount v.vat).option 0 (fun acc => acc.code.size))).toNat)
    (hcallFlux :
      typedCallViaEVM (config v) evmDog (EVM.address v.vat) "flux" 0
        [v.ilk, .address evmDog.executionEnv.codeOwner,
          .address (AccountAddress.ofNat (clipperTakeSalesUsrEVMWord evmLoc I).toNat),
          .int (Int.ofNat lotNew.toNat)]
        (true, evmFlux, outFlux) true)
    (hacc : evmFlux.accountMap.find? evmFlux.executionEnv.codeOwner = some acc)
    (hlen : Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩)
    (heq :
      clipperYankArgWord I =
        Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
          (clipperYankActiveSlot
            (UInt256.sub
              (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩) ⟨1⟩))) :
    let lastIndex :=
      UInt256.sub (Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner ⟨11⟩) ⟨1⟩
    let evmRemove :=
      clipperYankDeleteSaleState (clipperYankRemovePopState evmFlux lastIndex) I
    let frameRemoveRet : Frame :=
      { contract := contract v,
        locals :=
          (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
            slice' tabNew lotNew).insert "_fluxUsrRet" .unit |>.insert
              "_removeRet2" .unit }
    ExecBlock (config v)
      (Frame.mk (contract v)
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew))
      evmDog
      [ .ite
          (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite
              (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ],
        .assign .storage lockedRef (.intLit 0) ]
      (.ok frameRemoveRet
        (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
  intro lastIndex evmRemove frameRemoveRet
  let digsRetFrame : Frame :=
    Frame.mk (contract v)
      (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
        slice' tabNew lotNew)
  let fluxRetFrame : Frame :=
    { contract := contract v,
      locals := digsRetFrame.locals.insert "_fluxUsrRet" .unit }
  have hlotCond := clipperEvalTakeLotEqZeroAtDigsRet_false v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew hlotNew
  have htabCond := clipperEvalTakeTabEqZeroAtDigsRet_true v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew htabNew
  have hargs := clipperEvalTakeVatFluxUsrArgsAtDigsRet v evmLoc evmRead evmVat
    evmDog I price slice owe0 owe slice' tabNew lotNew
  have hguard := clipperEvalTakeVatCodeGuard_true v evmDog digsRetFrame.locals hvatCode
  have hflux :
      ExecBlock (config v) digsRetFrame evmDog
        (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
          [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet")
        (.ok fluxRetFrame evmFlux) := by
    simpa [checkedExternalCallStmts, digsRetFrame, fluxRetFrame, collapseReturns] using
      (checkedExternalCallSuccess hguard
        (clipperEvalVat v evmDog digsRetFrame.locals) hargs hcallFlux
        (clipperTakeDecodeFluxVoid v outFlux))
  let move :=
    Solm.EVM.storageLoad evmFlux evmFlux.executionEnv.codeOwner
      (clipperYankActiveSlot lastIndex)
  have hremoveBody :
      ExecFuncBody (config v)
        { contract := contract v, locals := clipperYankRemoveStore I } evmFlux
        removeFunction.body
        (.returned
          { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move }
          evmRemove none) := by
    simpa [lastIndex, move, evmRemove] using
      clipperYankRemoveIdEqMoveSource v evmFlux I hacc hlen heq
  have hremoveArgs :
      evalExprs? (config v) fluxRetFrame evmFlux [.var "id"] =
        .ok [clipperYankArgValue I] := by
    have hid :=
      clipperEvalTakeVarIdAtDigsRet v evmLoc evmRead evmVat evmFlux I price slice
        owe0 owe slice' tabNew lotNew
    have hid' :
        evalExpr? (config v) fluxRetFrame evmFlux (.var "id") =
          .ok (clipperYankArgValue I) := by
      dsimp only [fluxRetFrame, digsRetFrame]
      simp only [evalExpr?]
      rw [store_get_ne
        (clipperTakeLocalsDigsRet evmLoc evmRead evmVat I price slice owe0 owe
          slice' tabNew lotNew)
        (k := "_fluxUsrRet") (a := "id") .unit (by decide)]
      simpa only [evalExpr?, clipperTakeIdValue, clipperYankArgValue,
        clipperTakeIdWord, clipperYankArgWord] using hid
    exact evalExprs?_singleton hid'
  have hremove :
      ExecStmt (config v) fluxRetFrame evmFlux
        (.internalCall "_remove" [.var "id"] "_removeRet2")
        (.ok frameRemoveRet evmRemove) := by
    simpa [resumeAfterInternalCall, fluxRetFrame, digsRetFrame, frameRemoveRet] using
      (internalCallFunctionReturn
        (cfg := config v) (caller := fluxRetFrame) (evm := evmFlux)
        (name := "_remove") (retVar := "_removeRet2") (args := [.var "id"])
        (argVals := [clipperYankArgValue I]) (callee := removeFunction)
        (locals := clipperYankRemoveStore I)
        (calleeSolm :=
          { contract := contract v, locals := clipperYankRemoveMoveStore I lastIndex move })
        (calleeEvm := evmRemove) (value := none) hremoveArgs
        (clipperYankRemoveLookup v) (clipperYankRemoveBind I) hremoveBody)
  have htabIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite (.binary .eq (.var "tab") (.intLit 0))
          (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
            [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
            [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
          [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
            .assign .storage (salesF (.var "id") "lot") (.var "lot") ])
        (.ok frameRemoveRet evmRemove) := by
    exact ExecStmt.iteTrue (by simpa [digsRetFrame] using htabCond)
      (execBlockAppendOk hflux (ExecBlock.consNormal hremove ExecBlock.nil))
  have hlotIte :
      ExecStmt (config v) digsRetFrame evmDog
        (.ite (.binary .eq (.var "lot") (.intLit 0))
          [ .internalCall "_remove" [.var "id"] "_removeRet" ]
          [ .ite (.binary .eq (.var "tab") (.intLit 0))
              (checkedExternalCallStmts (vatExpr v) "flux" (.intLit 0)
                [ilkExpr v, thisAddr, .var "usr", .var "lot"] "_fluxUsrRet" ++
                [ .internalCall "_remove" [.var "id"] "_removeRet2" ])
              [ .assign .storage (salesF (.var "id") "tab") (.var "tab"),
                .assign .storage (salesF (.var "id") "lot") (.var "lot") ] ])
        (.ok frameRemoveRet evmRemove) := by
    exact ExecStmt.iteFalse (by simpa [digsRetFrame] using hlotCond)
      (ExecBlock.consNormal htabIte ExecBlock.nil)
  have hzero :
      evalExpr? (config v) frameRemoveRet evmRemove (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure, frameRemoveRet]
  have hlocked : frameRemoveRet.locals.get? "locked" = none := by
    simp [frameRemoveRet]
  have hassign :
      assignStorageRef? (config v) frameRemoveRet evmRemove .storage lockedRef (.int 0) =
        .ok (frameRemoveRet,
          Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩) := by
    simpa [frameRemoveRet] using
      assign_clipperLocked v evmRemove frameRemoveRet.locals hlocked ⟨0⟩
  have hunlock :
      ExecStmt (config v) frameRemoveRet evmRemove
        (.assign .storage lockedRef (.intLit 0))
        (.ok frameRemoveRet
          (Solm.EVM.storageStore evmRemove evmRemove.executionEnv.codeOwner ⟨13⟩ ⟨0⟩)) := by
    exact ExecStmt.assign hzero hassign
  exact ExecBlock.consNormal hlotIte (ExecBlock.consNormal hunlock ExecBlock.nil)

end Benchmarks.Dss.Clipper
