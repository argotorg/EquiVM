import Reasoning.SolcRoutines
import Reasoning.ExternalCall
import Reasoning.EVMWord
import Reasoning.BytecodePatching
import Benchmarks.Dss.Clipper.Bytecode
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Initcode
import Reasoning.Memory
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.SolmBody
import Reasoning.Storage
import Mathlib.Tactic.IntervalCases

/-!
# MakerDAO/Sky DSS Clipper shared proof foundation

Contract-wide selector notation and constants for the optimized Clipper runtime.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables
set_option maxRecDepth 2000000
namespace Benchmarks.Dss.Clipper


/-- Clipper states in which the public `list()` getter's byte-level memory arithmetic for
the `active` array cannot overflow, and dynamic ABI calldata decoding stays in the modeled
legacy-solc signed-size domain.

The constant covers the largest pointer/length expression used by the generated getter and ABI
return code: a 128-byte base, 32-byte array length word, 64-byte ABI prefix, and two `32 * len`
byte spans. The second conjunct is model-specific: `ByteArray.readWithPadding` handles return
reads only below `2^64`, so the returned ABI byte length is bounded separately. The calldata
bound explains the apparent ABI mismatch: Clipper's solc 0.6.12 decoder emits a signed `SLT`
size guard, whereas the older solc 0.5 wrapper bytecode used elsewhere in this development has
only the ordinary unsigned head and v1 dynamic-offset/length checks. They differ only on enormous
lengths admitted by the unbounded model, not on concrete EVM calldata; this bound excludes exactly
that model-only region. -/
def clipperStorageWF (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  224 + 64 * (solcSlotWord σ I ⟨11⟩).toNat < UInt256.size ∧
    64 + 32 * (solcSlotWord σ I ⟨11⟩).toNat < 2 ^ 64 ∧
      I.calldata.size < 2 ^ 255
theorem clipperStorageWF_calldata_lt_sign {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    I.calldata.size < 2 ^ 255 := by
  simpa [clipperStorageWF] using hwf.2.2


/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev clipperSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩
/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true
/-- Function selectors in `(contract v).transitions` order. -/
def clipperSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x80, 0x33, 0xd5, 0x81]⟩  -- active(uint256)
  | 1 => ⟨#[0x15, 0x23, 0x25, 0x15]⟩  -- buf()
  | 2 => ⟨#[0x96, 0xf1, 0xb6, 0xbe]⟩  -- calc()
  | 3 => ⟨#[0xb6, 0x15, 0x00, 0xe4]⟩  -- chip()
  | 4 => ⟨#[0xba, 0x2c, 0xdc, 0x75]⟩  -- chost()
  | 5 => ⟨#[0x06, 0x66, 0x1a, 0xbd]⟩  -- count()
  | 6 => ⟨#[0x49, 0xed, 0x59, 0x31]⟩  -- cusp()
  | 7 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩  -- deny(address)
  | 8 => ⟨#[0xc3, 0xb3, 0xad, 0x7f]⟩  -- dog()
  | 9 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩  -- file(bytes32,uint256)
  | 10 => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ -- file(bytes32,address)
  | 11 => ⟨#[0x5c, 0x62, 0x2a, 0x0e]⟩ -- getStatus(uint256)
  | 12 => ⟨#[0xc5, 0xce, 0x28, 0x1e]⟩ -- ilk()
  | 13 => ⟨#[0x89, 0x8e, 0xb2, 0x67]⟩ -- kick(uint256,uint256,address,address)
  | 14 => ⟨#[0xcf, 0xdd, 0x33, 0x02]⟩ -- kicks()
  | 15 => ⟨#[0x0f, 0x56, 0x0c, 0xd7]⟩ -- list()
  | 16 => ⟨#[0xd8, 0x43, 0x41, 0x6d]⟩ -- redo(uint256,address)
  | 17 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 18 => ⟨#[0xb5, 0xf5, 0x22, 0xf7]⟩ -- sales(uint256)
  | 19 => ⟨#[0x2e, 0x77, 0x46, 0x8d]⟩ -- spotter()
  | 20 => ⟨#[0x75, 0xf1, 0x2b, 0x21]⟩ -- stopped()
  | 21 => ⟨#[0x13, 0xd8, 0xc8, 0x40]⟩ -- tail()
  | 22 => ⟨#[0x81, 0xa7, 0x94, 0xcb]⟩ -- take(uint256,uint256,uint256,address,bytes)
  | 23 => ⟨#[0x27, 0x55, 0xcd, 0x2d]⟩ -- tip()
  | 24 => ⟨#[0x0c, 0xbb, 0x58, 0x62]⟩ -- upchost()
  | 25 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | 26 => ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩ -- vow()
  | 27 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | _ => ⟨#[0x26, 0xe0, 0x27, 0xf1]⟩  -- yank(uint256)

/-- Function selectors as EVM words, in `(contract v).transitions` order. -/
def clipperSelNat : ℕ → UInt256
  | 0 => ⟨0x8033d581⟩  -- active(uint256)
  | 1 => ⟨0x15232515⟩  -- buf()
  | 2 => ⟨0x96f1b6be⟩  -- calc()
  | 3 => ⟨0xb61500e4⟩  -- chip()
  | 4 => ⟨0xba2cdc75⟩  -- chost()
  | 5 => ⟨0x06661abd⟩  -- count()
  | 6 => ⟨0x49ed5931⟩  -- cusp()
  | 7 => ⟨0x9c52a7f1⟩  -- deny(address)
  | 8 => ⟨0xc3b3ad7f⟩  -- dog()
  | 9 => ⟨0x29ae8114⟩  -- file(bytes32,uint256)
  | 10 => ⟨0xd4e8be83⟩ -- file(bytes32,address)
  | 11 => ⟨0x5c622a0e⟩ -- getStatus(uint256)
  | 12 => ⟨0xc5ce281e⟩ -- ilk()
  | 13 => ⟨0x898eb267⟩ -- kick(uint256,uint256,address,address)
  | 14 => ⟨0xcfdd3302⟩ -- kicks()
  | 15 => ⟨0x0f560cd7⟩ -- list()
  | 16 => ⟨0xd843416d⟩ -- redo(uint256,address)
  | 17 => ⟨0x65fae35e⟩ -- rely(address)
  | 18 => ⟨0xb5f522f7⟩ -- sales(uint256)
  | 19 => ⟨0x2e77468d⟩ -- spotter()
  | 20 => ⟨0x75f12b21⟩ -- stopped()
  | 21 => ⟨0x13d8c840⟩ -- tail()
  | 22 => ⟨0x81a794cb⟩ -- take(uint256,uint256,uint256,address,bytes)
  | 23 => ⟨0x2755cd2d⟩ -- tip()
  | 24 => ⟨0x0cbb5862⟩ -- upchost()
  | 25 => ⟨0x36569e77⟩ -- vat()
  | 26 => ⟨0x626cb3c5⟩ -- vow()
  | 27 => ⟨0xbf353dbb⟩ -- wards(address)
  | _ => ⟨0x26e027f1⟩  -- yank(uint256)

theorem clipperSelectorEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (i : ℕ) (hi : i < 29) :
    UInt256.eq (clipperSelNat i) (clipperSelWord I) =
      if (clipperSelBytes i == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases i <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)


theorem clipperPatchesStartAt (v : ClipperImmutables) :
    PatchesStartAt 1463 (patches v) := by
  unfold PatchesStartAt patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : Reasoning.Theory.wordBytes? v.ilk with
  | none => simp [hIlk]
  | some bs => simp [hIlk]

theorem clipperDecodeBeforeFirstPatch (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (pc : UInt256)
    (hwin : pc.toNat + 33 ≤ 1463) :
    decode code pc = decode clipperBytecode pc :=
  patchRuntime_decode_left hpatch (clipperPatchesStartAt v) pc hwin (by norm_num)

theorem clipperDecodeBeforeFirstPatchPrecise (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (pc : UInt256)
    (hpc : pc.toNat < 1463)
    (hwin : ∀ byte instr, clipperBytecode.get? pc.toNat = some byte →
      parseInstr byte = some instr → pc.toNat + 1 + argOnNBytesOfInstr instr ≤ 1463) :
    decode code pc = decode clipperBytecode pc :=
  patchRuntime_decode_left_precise hpatch (clipperPatchesStartAt v) pc hpc hwin
    (by norm_num)

theorem clipperDecodeBeforeFirstPatchOfDecode (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (pc : UInt256)
    (res : Operation × Option (UInt256 × Nat))
    (hdec : decode clipperBytecode pc = some res) (hpc : pc.toNat < 1463)
    (hwin : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ 1463) :
    decode code pc = some res :=
  patchRuntime_decode_left_of_decode hpatch (clipperPatchesStartAt v) pc res hdec hpc hwin
    (by norm_num)


theorem clipperPrefixBeforeFirstPatch (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    code.extract 0 1463 = clipperBytecode.extract 0 1463 :=
  patchRuntime_extract_left hpatch (clipperPatchesStartAt v) (by rfl)

theorem clipperCodeSize_ge_firstPatch (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    1463 ≤ code.size := by
  have hprefix := clipperPrefixBeforeFirstPatch v hpatch
  have hsz : (code.extract 0 1463).size = 1463 := by
    rw [hprefix]
    native_decide
  rw [ByteArray.size_extract] at hsz
  omega

theorem clipperJumpDestBeforeFirstPatch (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (pc : UInt256)
    (hpc : (D_J (clipperBytecode.extract 0 1463) 0).contains pc = true) :
    (D_J code 0).contains pc = true := by
  have hprefix := clipperPrefixBeforeFirstPatch v hpatch
  have hsplit := byteArray_eq_extract_prefix_suffix code 1463
    (clipperCodeSize_ge_firstPatch v hpatch)
  rw [hsplit, hprefix]
  exact Reasoning.Theory.D_J_contains_append_left
    (clipperBytecode.extract 0 1463) (code.extract 1463 code.size) pc hpc


theorem clipperStorageLocLoad_uint64 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint64Loc slot ⟨0, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (UInt256.ofNat (2 ^ 64 - 1))).toNat) := by
  simpa [uint64Loc, uint64Int] using
    storageLocLoad_uint_offset0 (evm := evm) (slot := slot)
      (size := ⟨8, by decide⟩) (width := ⟨64, by decide⟩)
      (hbound := by decide) (by decide) (by decide)

theorem clipperStorageLocLoad_uint192 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint192Loc slot ⟨8, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩)).toNat) := by
  have h := storageLocLoad_uint_offset (evm := evm) (slot := slot)
    (offset := ⟨8, by decide⟩) (size := ⟨24, by decide⟩)
    (width := ⟨192, by decide⟩) (hbound := by decide) (by decide) (by decide) (by decide)
  simpa [uint192Loc, uint192Int] using h


abbrev clipperActiveHashMem : ByteArray :=
  wordAt0Mem (⟨11⟩ : UInt256) solcFreePtrMem

theorem clipperActiveHashMem_size : clipperActiveHashMem.size = 96 := by
  simpa [clipperActiveHashMem] using
    wordAt0Mem_size_96 (mem := solcFreePtrMem) (⟨11⟩ : UInt256) solcFreePtrMem_size


theorem clipperActiveHashMem_read64 :
    clipperActiveHashMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  simpa [clipperActiveHashMem] using
    wordAt0Mem_read64 (⟨11⟩ : UInt256) solcFreePtrMem_size solcFreePtrMem_read64

theorem clipperActiveHashMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ clipperActiveHashMem.size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        (clipperActiveHashMem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact mloadFreePtrValue
    (mem := clipperActiveHashMem)
    (by rw [clipperActiveHashMem_size]; norm_num)
    clipperActiveHashMem_read64

theorem clipperActiveHashMem_keccak_slot :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (KEC (clipperActiveHashMem.readWithPadding (⟨0⟩ : UInt256).toNat
            (⟨32⟩ : UInt256).toNat))) =
      activeDataSlot := by
  simpa [clipperActiveHashMem, activeDataSlot,
    show (⟨0⟩ : UInt256).toNat = 0 from by decide,
    show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
    (wordAt0Mem_keccak_word (⟨11⟩ : UInt256) solcFreePtrMem).trans
      (keccakSlot_eq (UInt256.toByteArray (⟨11⟩ : UInt256)))


theorem clipperReturnWord476Wf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcReturnWordFromMemWf code (⟨476⟩ : UInt256) := by
  unfold solcReturnWordFromMemWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

theorem clipperReturnAddress716Wf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcReturnAddressFromMemWf code (⟨716⟩ : UInt256) := by
  unfold solcReturnAddressFromMemWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide


theorem clipperUint256GetterBodyCore (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot returnPc : UInt256}
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcWordSlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturnWf : solcReturnWordFromMemWf code returnPc)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody (config v) (contract v)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWord σ I slot).toNat))]))) :
    runtimeEquivalenceFor (config v) (contract v) σ σ₀ g A I := by
  have hword : solcSlotWord σ I slot = solcSlotWord σ I slot := rfl
  have hval :
      some [Value.int (Int.ofNat (solcSlotWord σ I slot).toNat)] =
        some [Value.int (Int.ofNat (solcSlotWord σ I slot).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (solcSlotWord σ I slot))
        (some [(.int (Int.ofNat (solcSlotWord σ I slot).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (solcSlotWord σ I slot))
  have hrd := RD.solcWordGetterExternal (code := code) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hret hreturnWf
  exact hrd.reEquivExecution hcode hdispatch hdecode hbody henc

theorem clipperAddressGetterBodyCore (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot returnPc : UInt256}
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcAddressSlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturnWf : solcReturnAddressFromMemWf code returnPc)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody (config v) (contract v)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (UInt256.land (solcSlotWord σ I slot) solcAddrMask).toNat))]))) :
    runtimeEquivalenceFor (config v) (contract v) σ σ₀ g A I := by
  have hword : solcSlotWord σ I slot = solcSlotWord σ I slot := rfl
  have hval :
      some [Value.address (AccountAddress.ofNat
          (UInt256.land (solcSlotWord σ I slot) solcAddrMask).toNat)] =
        some [Value.address (AccountAddress.ofNat
          (UInt256.land (solcSlotWord σ I slot) solcAddrMask).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray
          (UInt256.land (solcSlotWord σ I slot) solcAddrMask))
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (solcSlotWord σ I slot) solcAddrMask).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [addr] using solcAddressReturnEncoding rfl (solcSlotWord σ I slot))
  have hrd := RD.solcAddressGetterExternal (code := code) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hret hreturnWf
  exact hrd.reEquivExecution hcode hdispatch hdecode hbody henc

theorem clipperAddressConstGetterBodyCore (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine returnPc val : UInt256} {width : Nat}
    {op : Operation.POp}
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturnWf : solcReturnAddressFromMemWf code returnPc)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody (config v) (contract v)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat val.toNat))]))) :
    runtimeEquivalenceFor (config v) (contract v) σ σ₀ g A I := by
  have henc :
      returnEquiv (UInt256.toByteArray (UInt256.land val solcAddrMask))
        (some [(.address (AccountAddress.ofNat val.toNat))]) transition.returnType := by
    rw [hreturn]
    have hmasked :
        Value.address (AccountAddress.ofNat val.toNat) =
          .address (AccountAddress.ofNat (UInt256.land val solcAddrMask).toNat) := by
      rw [solcAddressValue_masked val]
      rw [u256_land_comm solcAddrMask val]
    exact returnEquiv_of_encode
      (by simpa [addr, hmasked] using solcAddressReturnEncoding rfl val)
  have hrd := solcAddressConstGetterExternal (code := code) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (val := val)
    (width := width) (op := op) hreach hentry hgetter hroutine hret hreturnWf
  exact hrd.reEquivExecution hcode hdispatch hdecode hbody henc

theorem clipperBytes32ConstGetterBodyCore (v : ClipperImmutables) {code : ByteArray}
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine returnPc val : UInt256} {width : Nat}
    {op : Operation.POp}
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturnWf : solcReturnWordFromMemWf code returnPc)
    (hreturn : transition.returnType = [bytes32])
    (hbody :
      ExecTransitionBody (config v) (contract v)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE val))]))) :
    runtimeEquivalenceFor (config v) (contract v) σ σ₀ g A I := by
  have henc :
      returnEquiv (UInt256.toByteArray val)
        (some [(.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE val))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [bytes32] using bytes32ReturnEncoding val)
  have hrd := RD.solcWordConstGetterExternal (code := code) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (val := val)
    (width := width) (op := op) hreach hentry hgetter hroutine hret hreturnWf
  exact hrd.reEquivExecution hcode hdispatch hdecode hbody henc

theorem clipperActiveDynamicLength (evm : EVM.State) :
    solidityDynamicLength? storageLayoutRaw evm { base := "active" } =
      .ok (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat := by
  have hloc : solidityAnchorWordLoc ⟨11⟩ = wordLoc ⟨11⟩ := rfl
  simp only [solidityDynamicLength?, solidityLengthLoc?, solidityAnchor?,
    storageLayoutRaw, hloc, Option.map_some, EvalResult.ofOption, EvalResult.bind, bind]
  rw [show wordLoc = uint256Loc from rfl, storageLocLoad_uint256]
  simp

theorem clipperActiveLength (evm : EVM.State) :
    solidityStorageLength? storageLayoutRaw { base := "active" } (.dynamicArray uint256St) evm =
      .ok (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat := by
  simpa only [solidityStorageLength?] using clipperActiveDynamicLength evm

end Benchmarks.Dss.Clipper
