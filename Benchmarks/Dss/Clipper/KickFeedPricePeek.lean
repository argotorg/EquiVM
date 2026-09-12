import Benchmarks.Dss.Clipper.KickFeedPriceEntry

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperKickPipPeekSelectorMem_size {mem : ByteArray}
    (hmem : mem.size = 192) :
    (clipperPipPeekSelectorMem mem).size = 192 := by
  rw [clipperPipPeekSelectorMem_size_of_ge (by rw [hmem]; omega), hmem]

theorem clipperKickPipPeekSelectorMem_read64 {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperPipPeekSelectorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ :=
  clipperPipPeekSelectorMem_read64 (by rw [hmem]; omega) hread64

theorem clipperKickPipPeekSelectorMem_mload64 {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperPipPeekSelectorMem mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
        ((clipperPipPeekSelectorMem mem).readWithPadding 64 32))) = ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [clipperKickPipPeekSelectorMem_size hmem]; omega)
    (by decide) (clipperKickPipPeekSelectorMem_read64 hmem hread64)

theorem clipperKickPipPeekPostCallMem_size {mem out : ByteArray}
    (hmem : mem.size = 192) (hout : out.size < UInt256.size) :
    (clipperPipPeekPostCallMem mem out).size = 192 := by
  unfold clipperPipPeekPostCallMem
  by_cases hshort : out.size < 64
  · have hlen :
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
      umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
    rw [hlen]
    by_cases hzero : out.size = 0
    · rw [hzero, byteArray_write_len_zero, hmem]
    · rw [write_eq_gen out mem 128 out.size hzero le_rfl (by rw [hmem]; omega)]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, hmem]
      omega
  · have hlo : 64 ≤ out.size := by omega
    have hlen :
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
      umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
    rw [hlen]
    rw [write_eq_gen out mem 128 64 (by omega) (by omega) (by rw [hmem])]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hmem]
    omega

theorem clipperKickPipPeekPostCallMem_read64 {mem out : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hout : out.size < UInt256.size) :
    (clipperPipPeekPostCallMem mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperPipPeekPostCallMem
  by_cases hshort : out.size < 64
  · have hlen :
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
      umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
    rw [hlen]
    by_cases hzero : out.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact hread64
    · rw [write_read_below_gen_extend out mem 128 out.size 64 hzero le_rfl
        (by rw [hmem]; omega) (by omega)]
      exact hread64
  · have hlo : 64 ≤ out.size := by omega
    have hlen :
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
      umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
    rw [hlen]
    rw [write_read_below_gen_extend out mem 128 64 64 (by omega) (by omega)
      (by rw [hmem]; omega) (by omega)]
    exact hread64

theorem clipperKickPipPeekPostCallMem_read128_long {mem out : ByteArray}
    (hmem : mem.size = 192) (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperPipPeekPostCallMem mem out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold clipperPipPeekPostCallMem
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  exact byteArray_write_read_first_word_back out mem 128 64
    (by omega) (by omega) (by omega) (by rw [hmem])

theorem clipperKickPipPeekPostCallMem_read160_long {mem out : ByteArray}
    (hmem : mem.size = 192) (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (clipperPipPeekPostCallMem mem out).readWithPadding 160 32 =
      out.extract 32 64 := by
  unfold clipperPipPeekPostCallMem
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  simpa [show 128 + 32 = 160 by norm_num] using
    byteArray_write_read_second_word_back out mem 128 64
      (by omega) (by omega) (by omega) (by rw [hmem])

theorem clipperKickPipPeekPostCallMem_mload64 {mem out : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperPipPeekPostCallMem mem out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
        ((clipperPipPeekPostCallMem mem out).readWithPadding 64 32))) = ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [clipperKickPipPeekPostCallMem_size hmem hout]; omega)
    (by decide) (clipperKickPipPeekPostCallMem_read64 hmem hread64 hout)

theorem clipperKickPipPeekPostCallMem_mload128_long {mem out : ByteArray}
    (hmem : mem.size = 192) (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (clipperPipPeekPostCallMem mem out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
        ((clipperPipPeekPostCallMem mem out).readWithPadding 128 32))) =
      clipperPipPeekValueWord out := by
  rw [clipperKickPipPeekPostCallMem_size hmem hout, if_neg (by native_decide)]
  rw [clipperKickPipPeekPostCallMem_read128_long hmem hlo hout]

theorem clipperKickPipPeekPostCallMem_mload160_long {mem out : ByteArray}
    (hmem : mem.size = 192) (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨160⟩ : UInt256).toNat ≥ (clipperPipPeekPostCallMem mem out).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
        ((clipperPipPeekPostCallMem mem out).readWithPadding 160 32))) =
      clipperPipPeekHasWord out := by
  rw [clipperKickPipPeekPostCallMem_size hmem hout, if_neg (by native_decide)]
  rw [clipperKickPipPeekPostCallMem_read160_long hmem hlo hout]

set_option maxHeartbeats 1000000 in
theorem RD.clipperKickGetFeedPriceSpotterIlksDecodeShortReverts
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {d0 d1 ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : Nat}
    (rd : RD code ee g s0 ⟨8861⟩ (d0 :: d1 :: ret :: scratch :: lot :: tab :: R)
      (clipperSpotterIlksPostCallMem v mem o) (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : o.size < 64) (hout : o.size < UInt256.size)
    (hov : R.length + 16 ≤ 1024) : RDrev code g s0 := by
  have hmload64 := clipperKickSpotterIlksPostCallMem_mload64
    v hmem hread64 hout
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      ulit_toNat' o.size hout]
    exact hshort
  have rdGuardPre := evm_run rd with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8878⟩ (by clipper_runtime_decode) (by evm_ov)]
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256)) =
        ⟨0⟩ := by rw [hlt]; decide
  have rdFallthrough := rdGuardPre.jumpiNT (by clipper_runtime_decode) hcond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by clipper_runtime_decode) (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperKickGetFeedPriceSpotterIlksDecodeOkToPipPeekExtcodesizeGuard
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {d0 d1 ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : Nat}
    (rd : RD code ee g s0 ⟨8861⟩ (d0 :: d1 :: ret :: scratch :: lot :: tab :: R)
      (clipperSpotterIlksPostCallMem v mem o) (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlo : 64 ≤ o.size) (hout : o.size < UInt256.size)
    (hov : R.length + 80 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8937⟩
      (clipperSpotterIlksPipTarget o :: clipperSpotterIlksPipTarget o ::
        ⟨0⟩ :: ⟨128⟩ :: ⟨4⟩ :: ⟨128⟩ :: ⟨64⟩ :: ⟨132⟩ ::
        clipperPipPeekSelectorWord :: clipperSpotterIlksPipTarget o ::
        ⟨0⟩ :: ⟨0⟩ :: clipperSpotterIlksPipWord o ::
        d1 :: ret :: scratch :: lot :: tab :: R)
      (clipperPipPeekSelectorMem (clipperSpotterIlksPostCallMem v mem o))
      (UInt256.ofNat 6) o acc k' C' := by
  have hpostRead64 := clipperKickSpotterIlksPostCallMem_read64
    v hmem hread64 hout
  have hpostSize := clipperKickSpotterIlksPostCallMem_size_long v hmem hlo hout
  have hmload64 := clipperKickSpotterIlksPostCallMem_mload64 v hmem hread64 hout
  have hmload128 := clipperKickSpotterIlksPostCallMem_mload128_long
    v hmem hlo hout
  have hmload64Selector :
      (if (⟨64⟩ : UInt256).toNat ≥
            (clipperPipPeekSelectorMem
              (clipperSpotterIlksPostCallMem v mem o)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
          ((clipperPipPeekSelectorMem
            (clipperSpotterIlksPostCallMem v mem o)).readWithPadding 64 32))) = ⟨128⟩ :=
    clipperKickPipPeekSelectorMem_mload64 hpostSize hpostRead64
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      ulit_toNat' o.size hout]
    exact hlo
  have hjumpCond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256)) ≠
        ⟨0⟩ := by rw [hlt]; decide
  have hselectorShift :
      UInt256.shiftLeft clipperPipPeekSelectorWord ⟨224⟩ =
        clipperPipPeekSelectorShifted := by rfl
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rdGuardPre := evm_run rd with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8878⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd8878 := rdGuardPre.jumpiT (by clipper_runtime_decode) hjumpCond
    (clipperGetFeedPriceJumpDest8878 v hpatch) (by evm_ov)
  have rdPip := evm_run rd8878 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 (clipperSpotterIlksPipWord o) (UInt256.ofNat 6)
      (by clipper_runtime_decode) mem_cost hmload128 (by decide) (by evm_ov)]
  have rdSelector := evm_run rdPip with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 clipperPipPeekSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨224⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov)]
  rw [hselectorShift] at rdSelector
  have rdSelectorMem := evm_run rdSelector with [
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0
      (clipperPipPeekSelectorMem (clipperSpotterIlksPostCallMem v mem o))
      (UInt256.ofNat 6) (by clipper_runtime_decode) mem_cost (by rfl)
      (by native_decide) (by evm_ov)]
  have rdPreExt := evm_run rdSelectorMem with [
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by clipper_runtime_decode)
      mem_cost hmload64Selector (by decide) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw push4 clipperPipPeekSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
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
    simpa [clipperSpotterIlksPipTarget, clipperPipPeekSelectorMem, haddrMask,
      u256_land_comm,
      show (⟨128⟩ : UInt256) + ⟨4⟩ = ⟨132⟩ from by native_decide,
      show UInt256.add (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩) ⟨4⟩ = ⟨4⟩
        from by native_decide] using rdPreExt⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperKickGetFeedPricePipPeekPostCall {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {s0 : State} {cA sigma I} {g : UInt256}
    {target pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : Nat}
    (rd : RD code I (Sat256.ofUInt256 g) s0 ⟨8937⟩
      (target :: target :: ⟨0⟩ :: ⟨128⟩ :: ⟨4⟩ :: ⟨128⟩ :: ⟨64⟩ ::
        ⟨132⟩ :: clipperPipPeekSelectorWord :: target :: ⟨0⟩ :: ⟨0⟩ ::
        pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 6) rdata (cA, sigma) k C)
    (hcodeSize : extCodeSizeWord sigma target ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hcalldata :
      (config v).externalABI.encode? "peek" [] = some (mem.readWithPadding 128 4))
    (htarget : AccountAddress.ofUInt256 target = clipperSpotterIlksPipAddress rdata)
    (hov : R.length + 80 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (sigma' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k' C' : Nat),
      RD code I (Sat256.ofUInt256 g) s0 ⟨8953⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨132⟩ :: clipperPipPeekSelectorWord ::
          target :: ⟨0⟩ :: ⟨0⟩ :: pipWord :: ret :: scratch :: lot :: tab :: R)
        (clipperPipPeekPostCallMem mem o) (UInt256.ofNat 6) o
        (cA', sigma') k' C'
    ∧ typedCallViaEVM (config v)
        {s0 with accountMap := sigma, createdAccounts := cA, executionEnv := I}
        (EVM.address (clipperSpotterIlksPipAddress rdata)) "peek" 0 []
        (z, { {s0 with accountMap := sigma, createdAccounts := cA, executionEnv := I} with
              accountMap := sigma', substate := A', createdAccounts := cA' }, o) true
    ∧ o.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd8952⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨8937⟩) (okPc := ⟨8949⟩)
      rd hcodeSize
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperGetFeedPriceJumpDest8949 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by simp only [List.length_cons]; omega)
  obtain ⟨cA', sigma', z, o, A_in, callGas, k8953, C8953, hThetaPack,
      rd8953raw, hosz⟩ :=
    RD.call rd8952 (by clipper_runtime_decode) hdepth
      (by simp only [List.length_cons]; omega)
  obtain ⟨g'', A', hTheta⟩ := hThetaPack
  refine ⟨cA', sigma', z, o, A', k8953, C8953, ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          128 4) 128 64) = UInt256.ofNat 6 := by native_decide
    simpa [clipperPipPeekPostCallMem] using haw ▸ rd8953raw
  · refine callCoincides (cfg := config v)
      (evm := {s0 with accountMap := sigma, createdAccounts := cA, executionEnv := I})
      (name := "peek") (args := [])
      (tgt := EVM.address (clipperSpotterIlksPipAddress rdata))
      (targetWord := target)
      (cA' := cA') (σ' := sigma') (A' := A') (A_in := A_in) (z := z)
      (o := o) (g'' := g'') (callGas := callGas) (mem := mem)
      (inOff := ⟨128⟩) (inSize := ⟨4⟩) (callPerm := true)
      (fun hbad => absurd hdepth
        (by rw [show I.depth = (1024 : Fin 1025) from hbad]; decide))
      ?_ (by simpa using hcalldata) ?_
    · rw [← htarget]
      apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt (by simp [EVM.twoPow, AccountAddress.size])
    · simpa [hperm] using hTheta

set_option maxHeartbeats 1000000 in
theorem RD.clipperKickGetFeedPricePipPeekDecodeShortReverts
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {d0 d1 pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : Nat}
    (rd : RD code ee g s0 ⟨8974⟩
      (d0 :: d1 :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : o.size < 64) (hout : o.size < UInt256.size)
    (hov : R.length + 16 ≤ 1024) : RDrev code g s0 := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding 64 32))) = ⟨128⟩ := by
    rw [hmem, hread64]
    native_decide
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      ulit_toNat' o.size hout]
    exact hshort
  have rdGuardPre := evm_run rd with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8991⟩ (by clipper_runtime_decode) (by evm_ov)]
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256)) =
        ⟨0⟩ := by rw [hlt]; decide
  have rdFallthrough := rdGuardPre.jumpiNT (by clipper_runtime_decode) hcond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by clipper_runtime_decode) (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperKickGetFeedPricePipPeekHasTrueToValBln
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {d0 d1 pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : Nat}
    (rd : RD code ee g s0 ⟨8974⟩
      (d0 :: d1 :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hread128 : mem.readWithPadding 128 32 = o.extract 0 32)
    (hread160 : mem.readWithPadding 160 32 = o.extract 32 64)
    (hlo : 64 ≤ o.size) (hout : o.size < UInt256.size)
    (hhas : clipperPipPeekHasWord o ≠ ⟨0⟩)
    (hov : R.length + 80 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9079⟩
      (clipperPipPeekHasWord o :: clipperPipPeekValueWord o :: pipWord ::
        ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 6) o acc k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding 64 32))) = ⟨128⟩ := by
    rw [hmem, hread64]
    native_decide
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding 128 32))) = clipperPipPeekValueWord o := by
    rw [hmem, if_neg (by native_decide), hread128]
  have hmload160 :
      (if (⟨160⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding 160 32))) = clipperPipPeekHasWord o := by
    rw [hmem, if_neg (by native_decide), hread160]
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      ulit_toNat' o.size hout]
    exact hlo
  have hjumpCond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256)) ≠
        ⟨0⟩ := by rw [hlt]; decide
  have rdGuardPre := evm_run rd with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8991⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd8991 := rdGuardPre.jumpiT (by clipper_runtime_decode) hjumpCond
    (clipperGetFeedPriceJumpDest8991 v hpatch) (by evm_ov)
  have rdHasCheck := evm_run rd8991 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 (clipperPipPeekValueWord o) (UInt256.ofNat 6)
      (by clipper_runtime_decode) mem_cost hmload128 (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 (clipperPipPeekHasWord o) (UInt256.ofNat 6)
      (by clipper_runtime_decode) mem_cost hmload160 (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9079⟩ (by clipper_runtime_decode) (by evm_ov)]
  exact ⟨_, _, rdHasCheck.jumpiT (by clipper_runtime_decode) hhas
    (clipperGetFeedPriceJumpDest9079 v hpatch) (by evm_ov)⟩

theorem clipperKickErrorStringMem0_size {mem : ByteArray} (hmem : mem.size = 192) :
    (solcErrorStringMem0 mem).size = 192 := by
  unfold solcErrorStringMem0
  exact toByteArray_write32_size_of_le mem solcErrorStringSelector 128
    192 192 hmem (by rw [hmem]; omega) (by native_decide)

theorem clipperKickErrorStringMem1_size {mem : ByteArray} (hmem : mem.size = 192) :
    (solcErrorStringMem1 mem).size = 192 := by
  unfold solcErrorStringMem1
  exact toByteArray_write32_size_of_le (solcErrorStringMem0 mem) ⟨32⟩ 132
    192 192 (clipperKickErrorStringMem0_size hmem)
      (by rw [clipperKickErrorStringMem0_size hmem]; omega) (by native_decide)

theorem clipperKickErrorStringMem2_size (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192) : (solcErrorStringMem2 len mem).size = 196 := by
  unfold solcErrorStringMem2
  exact toByteArray_write32_size_of_le (solcErrorStringMem1 mem) len 164
    192 196 (clipperKickErrorStringMem1_size hmem)
      (by rw [clipperKickErrorStringMem1_size hmem]; omega) (by native_decide)

theorem clipperKickErrorStringMem3_size (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192) : (solcErrorStringMem3 len word mem).size = 228 := by
  unfold solcErrorStringMem3
  exact toByteArray_write32_size_of_le (solcErrorStringMem2 len mem) word 196
    196 228 (clipperKickErrorStringMem2_size len hmem)
      (by rw [clipperKickErrorStringMem2_size len hmem]) (by native_decide)

theorem clipperKickErrorStringMem3_read64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [clipperKickErrorStringMem2_size len hmem]; native_decide)
      (by native_decide)
      (by rw [clipperKickErrorStringMem2_size len hmem]; exact lt_usize _ (by omega))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [clipperKickErrorStringMem1_size hmem]; omega) (by native_decide)
      (by rw [clipperKickErrorStringMem1_size hmem]; exact lt_usize _ (by omega))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [clipperKickErrorStringMem0_size hmem]; omega) (by native_decide)
      (by rw [clipperKickErrorStringMem0_size hmem]; exact lt_usize _ (by omega))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by native_decide)
      (by rw [hmem]; exact lt_usize _ (by omega))]
  exact hread64

theorem clipperKickErrorStringMem3_mload64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding 64 32))) = ⟨128⟩ :=
  mloadFreePtrValue (by rw [clipperKickErrorStringMem3_size len word hmem]; decide)
    (by decide) (clipperKickErrorStringMem3_read64 len word hmem hread64)

set_option maxHeartbeats 1000000 in
theorem RD.clipperKickGetFeedPricePipPeekHasFalseReverts
    {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {d0 d1 pipWord ret scratch lot tab : UInt256} {R : List UInt256}
    {mem o : ByteArray} {k C : Nat}
    (rd : RD code ee g s0 ⟨8974⟩
      (d0 :: d1 :: pipWord :: ret :: scratch :: lot :: tab :: R)
      mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hread128 : mem.readWithPadding 128 32 = o.extract 0 32)
    (hread160 : mem.readWithPadding 160 32 = o.extract 32 64)
    (hlo : 64 ≤ o.size) (hout : o.size < UInt256.size)
    (hhasFalse : clipperPipPeekHasWord o = ⟨0⟩)
    (hov : R.length + 80 ≤ 1024) : RDrev code g s0 := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding 64 32))) = ⟨128⟩ := by
    rw [hmem, hread64]
    native_decide
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding 128 32))) = clipperPipPeekValueWord o := by
    rw [hmem, if_neg (by native_decide), hread128]
  have hmload160 :
      (if (⟨160⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding 160 32))) = clipperPipPeekHasWord o := by
    rw [hmem, if_neg (by native_decide), hread160]
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      ulit_toNat' o.size hout]
    exact hlo
  have hjumpCond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨64⟩ : UInt256)) ≠
        ⟨0⟩ := by rw [hlt]; decide
  have rdGuardPre := evm_run rd with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw lt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8991⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd8991 := rdGuardPre.jumpiT (by clipper_runtime_decode) hjumpCond
    (clipperGetFeedPriceJumpDest8991 v hpatch) (by evm_ov)
  have rdHasCheck := evm_run rd8991 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 (clipperPipPeekValueWord o) (UInt256.ofNat 6)
      (by clipper_runtime_decode) mem_cost hmload128 (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 (clipperPipPeekHasWord o) (UInt256.ofNat 6)
      (by clipper_runtime_decode) mem_cost hmload160 (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9079⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rdRevert0 := rdHasCheck.jumpiNT (by clipper_runtime_decode) hhasFalse
    (by simp only [List.length_cons]; omega)
  let invalidPriceWord : UInt256 :=
    UInt256.shiftLeft ⟨98539532077487810267029201284522128899303115678565⟩ ⟨88⟩
  have hselector :
      UInt256.shiftLeft (⟨4594637⟩ : UInt256) ⟨229⟩ = solcErrorStringSelector := by rfl
  have hInvalidPrice :
      UInt256.shiftLeft ⟨98539532077487810267029201284522128899303115678565⟩ ⟨88⟩ =
        invalidPriceWord := by rfl
  have rdMload := evm_run rdRevert0 with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by clipper_runtime_decode)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rdSelector := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov)]
  rw [hselector] at rdSelector
  have rdPrefix := evm_run rdSelector with [
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 6)
      (by clipper_runtime_decode) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by clipper_runtime_decode) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨21⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨21⟩ mem) (UInt256.ofNat 7)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst
    (⟨98539532077487810267029201284522128899303115678565⟩ : UInt256)
    (width := 21) (op := .PUSH21) (by decide) (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 ⟨88⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov)]
  rw [hInvalidPrice] at rdWord
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨21⟩ invalidPriceWord mem)
      (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost (by rfl)
      (by native_decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by clipper_runtime_decode)
      mem_cost (clipperKickErrorStringMem3_mload64 ⟨21⟩ invalidPriceWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw rev 0 (by clipper_runtime_decode) mem_cost (by evm_ov)]

end Benchmarks.Dss.Clipper
