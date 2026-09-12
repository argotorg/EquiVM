import Benchmarks.Dss.Clipper.KickInitEVM
import Benchmarks.Dss.Clipper.GetFeedPriceSuccessEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/-! `kick` enters the shared `getFeedPrice` routine with three active memory words.
The routine's two calldata stores grow that memory to six words, whereas `redo`
enters with seven words already active.  These lemmas record the `kick` memory
shape without changing the existing `redo` specialization. -/

theorem clipperKickSpotterIlksSelectorMem_size {mem : ByteArray}
    (hmem : mem.size = 96) :
    (clipperSpotterIlksSelectorMem mem).size = 160 := by
  unfold clipperSpotterIlksSelectorMem
  exact toByteArray_write32_size_of_ge mem clipperSpotterIlksSelectorShifted 128
    96 160 hmem (by omega) (by native_decide) (by native_decide)

theorem clipperKickSpotterIlksCalldataMem_size (ilk : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (clipperSpotterIlksCalldataMem ilk mem).size = 164 := by
  unfold clipperSpotterIlksCalldataMem
  rw [toByteArray_write32_size_of_le (clipperSpotterIlksSelectorMem mem) ilk 132
    160 164 (clipperKickSpotterIlksSelectorMem_size hmem)
      (by rw [clipperKickSpotterIlksSelectorMem_size hmem]; omega)
      (by native_decide)]

theorem clipperKickSpotterIlksCalldataMem_read64 (ilk : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperSpotterIlksCalldataMem ilk mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperSpotterIlksCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [clipperKickSpotterIlksSelectorMem_size hmem]; omega) (by omega),
    clipperSpotterIlksSelectorMem_read64 (by rw [hmem]) hread64]

theorem clipperKickSpotterIlksCalldataMem_read128_36 (ilk : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (clipperSpotterIlksCalldataMem ilk mem).readWithPadding 128 36 =
      spotterIlksSelector ++ ilk.toByteArray := by
  rw [byteArray_readWithPadding_split _ 128 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [clipperKickSpotterIlksCalldataMem_size ilk hmem])]
  have hleft :
      (clipperSpotterIlksCalldataMem ilk mem).readWithPadding 128 4 =
        spotterIlksSelector := by
    unfold clipperSpotterIlksCalldataMem
    rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
      (by rw [clipperKickSpotterIlksSelectorMem_size hmem]; omega)
      (by omega) (by rw [clipperKickSpotterIlksSelectorMem_size hmem]; omega)
      (by norm_num) (by norm_num)]
    unfold clipperSpotterIlksSelectorMem
    rw [toByteArray_write_read_window_of_gap clipperSpotterIlksSelectorShifted mem
      128 0 4 (by norm_num) (by norm_num) (by norm_num)
      (by rw [hmem]; exact lt_usize _ (by omega))]
    exact clipperSpotterIlksSelectorPrefix
  have hright :
      (clipperSpotterIlksCalldataMem ilk mem).readWithPadding 132 32 =
        ilk.toByteArray := by
    unfold clipperSpotterIlksCalldataMem
    rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
      (by rw [clipperKickSpotterIlksSelectorMem_size hmem]; omega)]
    rw [toByteArray_extract_all]
  rw [hleft, show 128 + 4 = 132 by norm_num, hright]

theorem clipperKickSpotterIlksEncode_eq (v : ClipperImmutables) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (config v).externalABI.encode? "spotterIlks" [v.ilk] =
      some ((clipperSpotterIlksCalldataMem (clipperIlkWord v) mem).readWithPadding
        128 36) := by
  rcases v.ilk_wf with ⟨bs, hilk, hlen⟩
  rw [hilk]
  have hilkWord :
      clipperIlkWord v = EVM.Word.ofNat (fromBytesBigEndian bs) := by
    simp [clipperIlkWord, hilk]
  rw [hilkWord]
  change (config v).externalABI.encode? "spotterIlks" [.fixedBytes ⟨31, by decide⟩ bs] =
    some ((clipperSpotterIlksCalldataMem (EVM.Word.ofNat (fromBytesBigEndian bs))
      mem).readWithPadding 128 36)
  rw [clipperKickSpotterIlksCalldataMem_read128_36 _ hmem]
  have hbytes :
      bs = EVM.Word.toBytesBE (EVM.Word.ofNat (fromBytesBigEndian bs)) := by
    have hword : ABI.bytesToWord bs = EVM.Word.ofNat (fromBytesBigEndian bs) := by
      unfold ABI.bytesToWord fromByteArrayBigEndian
      simp [byteArray_toList_eq, EVM.Word.ofNat]
    rw [← hword]
    exact (toBytesBE_bytesToWord_of_length hlen).symm
  have hwordBytes :
      (EVM.Word.ofNat (fromBytesBigEndian bs)).toByteArray =
        { data := bs.toArray } := by
    rw [← word_toBytesBE_toByteArray_eq_toByteArray
      (EVM.Word.ofNat (fromBytesBigEndian bs)), ← hbytes]
    apply ByteArray.ext
    simp
  have hbsByteArray : bs.toByteArray = { data := bs.toArray } := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [List.toList_data_toByteArray]
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width,
    spotterIlksSelector, selectorBytes, hlen, ABI.zeroBytes, hwordBytes, hbsByteArray]

set_option maxHeartbeats 1000000 in
theorem RD.clipperKickGetFeedPriceToSpotterIlksExtcodesizeGuard {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {sigma : AccountMap}
    {ret scratch lot tab : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {k C : Nat}
    (h : RD code ee g s0 ⟨8728⟩ (ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 3) rdata (cA, sigma) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 60 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8824⟩
      (clipperSpotterTarget sigma ee :: clipperSpotterTarget sigma ee ::
        ⟨0⟩ :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨64⟩ :: ⟨164⟩ ::
        clipperSpotterIlksSelectorWord :: clipperSpotterTarget sigma ee ::
        ⟨0⟩ :: ⟨0⟩ :: ret :: scratch :: lot :: tab :: R)
      (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem)
      (UInt256.ofNat 6) rdata (cA, sigma) k' C' := by
  rcases v.ilk_wf with ⟨ilkBs, hilk, hlen⟩
  let ilkWord : UInt256 := EVM.Word.ofNat (fromBytesBigEndian ilkBs)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding 64 32))) = ⟨128⟩ := by
    rw [hmem, hread64]
    native_decide
  have hselectorShift :
      UInt256.shiftLeft (⟨1823590043⟩ : UInt256) ⟨225⟩ =
        clipperSpotterIlksSelectorShifted := by native_decide
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hcallRead64 :
      (clipperSpotterIlksCalldataMem ilkWord mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    simpa [ilkWord] using clipperKickSpotterIlksCalldataMem_read64 ilkWord hmem hread64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (clipperSpotterIlksCalldataMem ilkWord mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((clipperSpotterIlksCalldataMem ilkWord mem).readWithPadding 64 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [clipperKickSpotterIlksCalldataMem_size ilkWord hmem]; omega)
      (by decide) hcallRead64
  obtain ⟨_, _, rdSpotter⟩ := (evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨3⟩ (by clipper_runtime_decode) (by evm_ov)]).sload
      (by clipper_runtime_decode) (by evm_ov)
  have rdSelector := evm_run rdSpotter with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 ⟨1823590043⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨225⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov)]
  rw [hselectorShift] at rdSelector
  have rdSelectorMem := evm_run rdSelector with [
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 6 (clipperSpotterIlksSelectorMem mem) (UInt256.ofNat 5)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rdIlk := rdSelectorMem.pushConst ilkWord (width := 32) (op := .PUSH32)
    (by decide)
    (by simpa [ilkWord] using clipperGetFeedPriceIlkPush32Decode8746 v hpatch hilk hlen)
    (by evm_ov)
  have rdCalldata := evm_run rdIlk with [
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3 (clipperSpotterIlksCalldataMem ilkWord mem) (UInt256.ofNat 6)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rdPreCall := evm_run rdCalldata with [
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by clipper_runtime_decode)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw push4 clipperSpotterIlksSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [clipperSpotterTarget, clipperSpotterIlksCalldataMem, clipperIlkWord,
      ilkWord, hilk, clipperSpotterIlksSelectorWord, haddrMask, u256_land_comm,
      show (⟨128⟩ : UInt256) + ⟨36⟩ = ⟨164⟩ from by native_decide,
      show UInt256.add (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩) ⟨36⟩ = ⟨36⟩
        from by native_decide] using rdPreCall⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperKickGetFeedPriceSpotterIlksNoCode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {sigma : AccountMap}
    {ret scratch lot tab : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {k C : Nat}
    (h : RD code ee g s0 ⟨8728⟩ (ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 3) rdata (cA, sigma) k C)
    (hcodeSize : extCodeSizeWord sigma (clipperSpotterTarget sigma ee) = ⟨0⟩)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 60 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, rd8824⟩ :=
    RD.clipperKickGetFeedPriceToSpotterIlksExtcodesizeGuard v hpatch h hmem hread64 hov
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨8824⟩) (okPc := ⟨8836⟩)
    rd8824 hcodeSize
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperKickGetFeedPriceSpotterIlksPostCall {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {s0 : State} {cA sigma I} {g : UInt256}
    {ret scratch lot tab : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {k C : Nat}
    (h : RD code I (Sat256.ofUInt256 g) s0 ⟨8728⟩
      (ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 3) rdata (cA, sigma) k C)
    (hcodeSize : extCodeSizeWord sigma (clipperSpotterTarget sigma I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 80 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (sigma' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k' C' : Nat),
      RD code I (Sat256.ofUInt256 g) s0 ⟨8840⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: clipperSpotterIlksSelectorWord ::
          clipperSpotterTarget sigma I :: ⟨0⟩ :: ⟨0⟩ :: ret :: scratch :: lot :: tab :: R)
        (clipperSpotterIlksPostCallMem v mem o) (UInt256.ofNat 6) o
        (cA', sigma') k' C'
    ∧ typedCallViaEVM (config v)
        {s0 with accountMap := sigma, createdAccounts := cA, executionEnv := I}
        (EVM.address (AccountAddress.ofUInt256 (clipperSpotterTarget sigma I)))
        "spotterIlks" 0 [v.ilk]
        (z, { {s0 with accountMap := sigma, createdAccounts := cA, executionEnv := I} with
              accountMap := sigma', substate := A', createdAccounts := cA' }, o) true
    ∧ o.size < UInt256.size := by
  obtain ⟨_, _, rd8824⟩ :=
    RD.clipperKickGetFeedPriceToSpotterIlksExtcodesizeGuard v hpatch h hmem hread64
      (by omega)
  obtain ⟨gasWord, _, _, rd8839⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨8824⟩) (okPc := ⟨8836⟩)
      rd8824 hcodeSize
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperGetFeedPriceJumpDest8836 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by simp only [List.length_cons]; omega)
  obtain ⟨cA', sigma', z, o, A_in, callGas, k8840, C8840, hThetaPack,
      rd8840raw, hosz⟩ :=
    RD.call rd8839 (by clipper_runtime_decode) hdepth (by evm_ov)
  obtain ⟨g'', A', hTheta⟩ := hThetaPack
  refine ⟨cA', sigma', z, o, A', k8840, C8840, ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          128 36) 128 64) = UInt256.ofNat 6 := by native_decide
    simpa [clipperSpotterIlksPostCallMem, clipperIlkWord] using haw ▸ rd8840raw
  · refine callCoincides (cfg := config v)
      (evm := {s0 with accountMap := sigma, createdAccounts := cA, executionEnv := I})
      (name := "spotterIlks") (args := [v.ilk])
      (tgt := EVM.address (AccountAddress.ofUInt256 (clipperSpotterTarget sigma I)))
      (targetWord := clipperSpotterTarget sigma I)
      (cA' := cA') (σ' := sigma') (A' := A') (A_in := A_in) (z := z)
      (o := o) (g'' := g'') (callGas := callGas)
      (mem := clipperSpotterIlksCalldataMem (clipperIlkWord v) mem)
      (inOff := ⟨128⟩) (inSize := ⟨36⟩) (callPerm := true)
      (fun hbad => absurd hdepth
        (by rw [show I.depth = (1024 : Fin 1025) from hbad]; decide))
      ?_ (by simpa using clipperKickSpotterIlksEncode_eq v hmem) ?_
    · apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])
    · simpa [hperm] using hTheta

theorem clipperKickSpotterIlksPostCallMem_size_ge
    (v : ClipperImmutables) {mem out : ByteArray}
    (hmem : mem.size = 96) (hout : out.size < UInt256.size) :
    164 ≤ (clipperSpotterIlksPostCallMem v mem out).size := by
  unfold clipperSpotterIlksPostCallMem
  have hbase :
      (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem).size = 164 :=
    clipperKickSpotterIlksCalldataMem_size (clipperIlkWord v) hmem
  by_cases hshort : out.size < 64
  · have hlen :
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
      umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
    rw [hlen]
    by_cases hzero : out.size = 0
    · rw [hzero, byteArray_write_len_zero, hbase]
    · by_cases hin : 128 + out.size ≤ 164
      · rw [write_eq_gen out
          (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem) 128 out.size
          hzero le_rfl (by rw [hbase]; exact hin)]
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract, hbase]
        omega
      · rw [write_eq_gen_extend out
          (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem) 128 out.size
          hzero le_rfl (by rw [hbase]; omega) (by rw [hbase]; omega)]
        rw [ByteArray.size_append,
          show ((clipperSpotterIlksCalldataMem (clipperIlkWord v) mem).extract
              0 128).size = 128 by rw [ByteArray.size_extract, hbase]; omega,
          show (out.extract 0 out.size).size = out.size by simp]
        omega
  · have hlo : 64 ≤ out.size := by omega
    have hlen :
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
      umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
    rw [hlen]
    rw [write_eq_gen_extend out
      (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem)
      128 64 (by omega) (by omega) (by rw [hbase]; omega) (by rw [hbase]; omega)]
    rw [ByteArray.size_append,
      show ((clipperSpotterIlksCalldataMem (clipperIlkWord v) mem).extract
          0 128).size = 128 by rw [ByteArray.size_extract, hbase]; omega,
      show (out.extract 0 64).size = 64 by rw [ByteArray.size_extract]; omega]
    omega

theorem clipperKickSpotterIlksPostCallMem_read64
    (v : ClipperImmutables) {mem out : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hout : out.size < UInt256.size) :
    (clipperSpotterIlksPostCallMem v mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperSpotterIlksPostCallMem
  have hbase :
      (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem).size = 164 :=
    clipperKickSpotterIlksCalldataMem_size (clipperIlkWord v) hmem
  have hbaseRead := clipperKickSpotterIlksCalldataMem_read64
    (clipperIlkWord v) hmem hread64
  by_cases hshort : out.size < 64
  · have hlen :
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
      umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
    rw [hlen]
    by_cases hzero : out.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact hbaseRead
    · rw [write_read_below_gen_extend out
        (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem)
        128 out.size 64 hzero le_rfl (by rw [hbase]; omega) (by omega)]
      exact hbaseRead
  · have hlo : 64 ≤ out.size := by omega
    have hlen :
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
      umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
    rw [hlen]
    rw [write_read_below_gen_extend out
      (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem)
      128 64 64 (by omega) (by omega) (by rw [hbase]; omega) (by omega)]
    exact hbaseRead

theorem clipperKickSpotterIlksPostCallMem_mload64
    (v : ClipperImmutables) {mem out : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperSpotterIlksPostCallMem v mem out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
        ((clipperSpotterIlksPostCallMem v mem out).readWithPadding 64 32))) = ⟨128⟩ := by
  exact mloadFreePtrValue
    (by have := clipperKickSpotterIlksPostCallMem_size_ge v hmem hout; omega)
    (by decide) (clipperKickSpotterIlksPostCallMem_read64 v hmem hread64 hout)

theorem clipperKickSpotterIlksPostCallMem_size_long
    (v : ClipperImmutables) {mem out : ByteArray}
    (hmem : mem.size = 96) (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperSpotterIlksPostCallMem v mem out).size = 192 := by
  unfold clipperSpotterIlksPostCallMem
  have hbase :
      (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem).size = 164 :=
    clipperKickSpotterIlksCalldataMem_size (clipperIlkWord v) hmem
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  rw [write_eq_gen_extend out
    (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem)
    128 64 (by omega) (by omega) (by rw [hbase]; omega) (by rw [hbase]; omega)]
  rw [ByteArray.size_append,
    show ((clipperSpotterIlksCalldataMem (clipperIlkWord v) mem).extract
        0 128).size = 128 by rw [ByteArray.size_extract, hbase]; omega,
    show (out.extract 0 64).size = 64 by rw [ByteArray.size_extract]; omega]

theorem byteArray_write_extend_read_first_word_back (src base : ByteArray)
    (destAddr len : Nat) (hlen : len ≠ 0) (hsrc : len ≤ src.size)
    (hword : 32 ≤ len) (hdest : destAddr ≤ base.size)
    (hext : base.size < destAddr + len) :
    (src.write 0 base destAddr len).readWithPadding destAddr 32 =
      src.extract 0 32 := by
  rw [write_eq_gen_extend src base destAddr len hlen hsrc hdest hext]
  have hprefix : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hsrcPrefix : (src.extract 0 len).size = len := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ destAddr (by
    rw [ByteArray.size_append, hprefix, hsrcPrefix]
    omega)]
  rw [extract_append_right_window (base.extract 0 destAddr) (src.extract 0 len)
    destAddr (destAddr + 32) (by rw [hprefix])]
  rw [show destAddr - (base.extract 0 destAddr).size = 0 by rw [hprefix]; omega]
  rw [show destAddr + 32 - (base.extract 0 destAddr).size = 32 by
    rw [hprefix]; omega]
  exact extract_prefix src len 0 32 hword

theorem clipperKickSpotterIlksPostCallMem_read128_long
    (v : ClipperImmutables) {mem out : ByteArray}
    (hmem : mem.size = 96) (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperSpotterIlksPostCallMem v mem out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold clipperSpotterIlksPostCallMem
  have hbase :
      (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem).size = 164 :=
    clipperKickSpotterIlksCalldataMem_size (clipperIlkWord v) hmem
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  exact byteArray_write_extend_read_first_word_back out
    (clipperSpotterIlksCalldataMem (clipperIlkWord v) mem)
    128 64 (by omega) (by omega) (by omega) (by rw [hbase]; omega)
      (by rw [hbase]; omega)

theorem clipperKickSpotterIlksPostCallMem_mload128_long
    (v : ClipperImmutables) {mem out : ByteArray}
    (hmem : mem.size = 96) (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (clipperSpotterIlksPostCallMem v mem out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
        ((clipperSpotterIlksPostCallMem v mem out).readWithPadding 128 32))) =
      clipperSpotterIlksPipWord out := by
  rw [clipperKickSpotterIlksPostCallMem_size_long v hmem hlo hout]
  rw [if_neg (by native_decide)]
  change UInt256.ofNat (fromByteArrayBigEndian
      ((clipperSpotterIlksPostCallMem v mem out).readWithPadding 128 32)) = _
  rw [clipperKickSpotterIlksPostCallMem_read128_long v hmem hlo hout]

end Benchmarks.Dss.Clipper
