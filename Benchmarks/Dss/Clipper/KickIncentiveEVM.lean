import Benchmarks.Dss.Clipper.KickTailEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem RD.clipperKickIncentiveInactive {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {top id kpr usr lot tab sel : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨6203⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: top :: ⟨1⟩ :: id :: kpr :: usr :: lot :: tab ::
        ⟨476⟩ :: sel :: R)
      mem aw o acc k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨6394⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: top :: ⟨1⟩ :: id :: kpr :: usr :: lot :: tab ::
        ⟨476⟩ :: sel :: R)
      mem aw o acc k' C' := by
  have rd6216Pre := evm_run rd with [
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨6216⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd6216 := rd6216Pre.jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov)
  have rd6394Pre := evm_run rd6216 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨6394⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd6394 := rd6394Pre.jumpiT (by clipper_runtime_decode) (by decide)
    (clipperKickJumpDest6394 v hpatch) (by evm_ov)
  exact ⟨_, _, rd6394⟩

theorem RD.clipperKickIncentiveActive {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {chip tip top id kpr usr lot tab sel : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨6203⟩
      (⟨0⟩ :: chip :: tip :: top :: ⟨1⟩ :: id :: kpr :: usr :: lot :: tab ::
        ⟨476⟩ :: sel :: R)
      mem aw o acc k C)
    (hactive : tip ≠ ⟨0⟩ ∨ chip ≠ ⟨0⟩)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨6222⟩
      (⟨0⟩ :: chip :: tip :: top :: ⟨1⟩ :: id :: kpr :: usr :: lot :: tab ::
        ⟨476⟩ :: sel :: R)
      mem aw o acc k' C' := by
  have rd6216Pre := evm_run rd with [
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨6216⟩ (by clipper_runtime_decode) (by evm_ov)]
  by_cases htip : tip = ⟨0⟩
  · have hchip : chip ≠ ⟨0⟩ := hactive.resolve_left (fun hne => hne htip)
    subst tip
    have hchipPos : 0 < chip.toNat :=
      Nat.pos_of_ne_zero (fun h => hchip (uint256_toNat_eq_zero h))
    have hchipGt : UInt256.gt chip ⟨0⟩ = ⟨1⟩ := ugt_one (by simpa using hchipPos)
    have rd6216 := rd6216Pre.jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov)
    have rd6394Pre := evm_run rd6216 with [
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
      raw dup3 (by clipper_runtime_decode) (by evm_ov),
      raw gt (by clipper_runtime_decode) (by evm_ov),
      raw jumpdest (by clipper_runtime_decode) (by evm_ov),
      raw iszero (by clipper_runtime_decode) (by evm_ov),
      raw push2 ⟨6394⟩ (by clipper_runtime_decode) (by evm_ov)]
    rw [hchipGt] at rd6394Pre
    exact ⟨_, _, rd6394Pre.jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov)⟩
  · have hcond : UInt256.isZero (UInt256.isZero tip) = ⟨1⟩ := by
      rw [Reasoning.Theory.isZero_eq_zero_of_ne htip]
      decide
    rw [hcond] at rd6216Pre
    have rd6216 := rd6216Pre.jumpiT (by clipper_runtime_decode) (by decide)
      (clipperKickJumpDest6216 v hpatch) (by evm_ov)
    exact ⟨_, _, evm_run rd6216 with [
      raw jumpdest (by clipper_runtime_decode) (by evm_ov),
      raw iszero (by clipper_runtime_decode) (by evm_ov),
      raw push2 ⟨6394⟩ (by clipper_runtime_decode) (by evm_ov),
      raw jumpiNT (by clipper_runtime_decode) (by decide) (by evm_ov)]⟩

theorem RD.clipperKickIncentiveToWmul {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {chip tip top id kpr usr lot tab sel : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨6222⟩
      (⟨0⟩ :: chip :: tip :: top :: ⟨1⟩ :: id :: kpr :: usr :: lot :: tab ::
        ⟨476⟩ :: sel :: R)
      mem aw o acc k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8238⟩
      (chip :: tab :: ⟨6235⟩ :: tip :: ⟨6240⟩ :: ⟨0⟩ :: chip :: tip :: top ::
        ⟨1⟩ :: id :: kpr :: usr :: lot :: tab :: ⟨476⟩ :: sel :: R)
      mem aw o acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    raw push2 ⟨6240⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨6235⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup13 (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8238⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperRedoJumpDest8238 v hpatch) (by evm_ov)]⟩

theorem RD.clipperKickIncentiveWmulToCheckedAdd {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {chip tab tip keep : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8238⟩
      (chip :: tab :: ⟨6235⟩ :: tip :: ⟨6240⟩ :: keep :: R) mem aw o acc k C)
    (hmul : chip.toNat * tab.toNat < UInt256.size)
    (hov : R.length + 25 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨9258⟩
      (UInt256.div (UInt256.mul chip tab) ⟨1000000000000000000⟩ :: tip ::
        ⟨6240⟩ :: keep :: R)
      mem aw o acc k' C' := by
  obtain ⟨_, _, rd6235⟩ :=
    _root_.Benchmarks.Dss.Clipper.Reasoning.Reach.RD.clipperWmulRoutine
      v hpatch rd hmul (clipperKickJumpDest6235 v hpatch)
        (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd6235 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨9258⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperRedoJumpDest9258 v hpatch) (by evm_ov)]⟩

theorem RD.clipperKickIncentiveAddSuccess {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {chipCoin tip keep : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨9258⟩
      (chipCoin :: tip :: ⟨6240⟩ :: keep :: R) mem aw o acc k C)
    (hfit : tip.toNat + chipCoin.toNat < UInt256.size)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨6240⟩ ((tip + chipCoin) :: keep :: R) mem aw o acc k' C' := by
  exact RD.solcCheckedAddSuccess rd
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | clipper_runtime_decode)
    hfit (clipperKickJumpDest6240 v hpatch) (clipperJumpDest8722 v hpatch)
      (by simp only [List.length_cons]; omega)

/- The kick path reaches this call with 192 bytes of memory.  The selector and
   first address writes stay within that allocation; the remaining writes grow
   it to the same 228-byte calldata buffer used by redo. -/
theorem clipperKickSuckSelectorMem_size {mem : ByteArray} (hmem : mem.size = 192) :
    (clipperRedoSuckSelectorMem mem).size = 192 := by
  unfold clipperRedoSuckSelectorMem
  exact toByteArray_write32_size_of_le mem clipperRedoSuckSelectorShifted
    128 192 192 hmem (by omega) (by omega)

theorem clipperKickSuckVowMem_size (σ : AccountMap) (ee : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 192) :
    (clipperRedoSuckVowMem σ ee mem).size = 192 := by
  unfold clipperRedoSuckVowMem
  exact toByteArray_write32_size_of_le (clipperRedoSuckSelectorMem mem)
    (clipperRedoVowTarget σ ee) 132 192 192 (clipperKickSuckSelectorMem_size hmem)
    (by rw [clipperKickSuckSelectorMem_size hmem]; omega) (by omega)

theorem clipperKickSuckKprMem_size (σ : AccountMap) (ee : ExecutionEnv)
    (kpr : UInt256) {mem : ByteArray} (hmem : mem.size = 192) :
    (clipperRedoSuckKprMem σ ee kpr mem).size = 196 := by
  unfold clipperRedoSuckKprMem
  exact toByteArray_write32_size_of_le (clipperRedoSuckVowMem σ ee mem)
    (clipperRedoKprTarget kpr) 164 192 196 (clipperKickSuckVowMem_size σ ee hmem)
    (by rw [clipperKickSuckVowMem_size σ ee hmem]; omega) (by omega)

theorem clipperKickSuckCalldataMem_size (σ : AccountMap) (ee : ExecutionEnv)
    (kpr coin : UInt256) {mem : ByteArray} (hmem : mem.size = 192) :
    (clipperRedoSuckCalldataMem σ ee kpr coin mem).size = 228 := by
  unfold clipperRedoSuckCalldataMem
  exact toByteArray_write32_size_of_le (clipperRedoSuckKprMem σ ee kpr mem) coin
    196 196 228 (clipperKickSuckKprMem_size σ ee kpr hmem)
    (by rw [clipperKickSuckKprMem_size σ ee kpr hmem]) (by omega)

theorem clipperKickSuckSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperRedoSuckSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold clipperRedoSuckSelectorMem
  rw [toByteArray_write_read_below_of_gap clipperRedoSuckSelectorShifted mem 128 64
    (by rw [hmem]; omega) (by omega) (by rw [hmem]; native_decide)]
  exact hread64

theorem clipperKickSuckVowMem_read64 (σ : AccountMap) (ee : ExecutionEnv)
    {mem : ByteArray} (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperRedoSuckVowMem σ ee mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold clipperRedoSuckVowMem
  rw [toByteArray_write_read_below_of_gap (clipperRedoVowTarget σ ee)
    (clipperRedoSuckSelectorMem mem) 132 64
    (by rw [clipperKickSuckSelectorMem_size hmem]; omega) (by omega)
    (by rw [clipperKickSuckSelectorMem_size hmem]; native_decide)]
  exact clipperKickSuckSelectorMem_read64 hmem hread64

theorem clipperKickSuckKprMem_read64 (σ : AccountMap) (ee : ExecutionEnv)
    (kpr : UInt256) {mem : ByteArray} (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperRedoSuckKprMem σ ee kpr mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperRedoSuckKprMem
  rw [toByteArray_write_read_below_of_gap (clipperRedoKprTarget kpr)
    (clipperRedoSuckVowMem σ ee mem) 164 64
    (by rw [clipperKickSuckVowMem_size σ ee hmem]; omega) (by omega)
    (by rw [clipperKickSuckVowMem_size σ ee hmem]; native_decide)]
  exact clipperKickSuckVowMem_read64 σ ee hmem hread64

theorem clipperKickSuckCalldataMem_read64 (σ : AccountMap) (ee : ExecutionEnv)
    (kpr coin : UInt256) {mem : ByteArray} (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperRedoSuckCalldataMem σ ee kpr coin mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperRedoSuckCalldataMem
  rw [toByteArray_write_read_below_of_gap coin (clipperRedoSuckKprMem σ ee kpr mem)
    196 64 (by rw [clipperKickSuckKprMem_size σ ee kpr hmem]; omega) (by omega)
    (by rw [clipperKickSuckKprMem_size σ ee kpr hmem]; native_decide)]
  exact clipperKickSuckKprMem_read64 σ ee kpr hmem hread64

theorem clipperKickSuckCalldataMem_mload64 (σ : AccountMap) (ee : ExecutionEnv)
    (kpr coin : UInt256) {mem : ByteArray} (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperRedoSuckCalldataMem σ ee kpr coin mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((clipperRedoSuckCalldataMem σ ee kpr coin mem).readWithPadding 64 32))) = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [clipperKickSuckCalldataMem_size σ ee kpr coin hmem]; decide)
    (by decide) (clipperKickSuckCalldataMem_read64 σ ee kpr coin hmem hread64)

theorem clipperKickSuckCalldataMem_read128_100 (σ : AccountMap) (ee : ExecutionEnv)
    (kpr coin : UInt256) {mem : ByteArray} (hmem : mem.size = 192) :
    (clipperRedoSuckCalldataMem σ ee kpr coin mem).readWithPadding 128 100 =
      vatSuckSelector ++ (clipperRedoVowTarget σ ee).toByteArray ++
        (clipperRedoKprTarget kpr).toByteArray ++ coin.toByteArray := by
  set final := clipperRedoSuckCalldataMem σ ee kpr coin mem with hfinal
  have hfinalSize : final.size = 228 :=
    hfinal ▸ clipperKickSuckCalldataMem_size σ ee kpr coin hmem
  have hselector : final.readWithPadding 128 4 = vatSuckSelector := by
    rw [hfinal]
    unfold clipperRedoSuckCalldataMem
    rw [toByteArray_write_read_below_len_of_gap coin (clipperRedoSuckKprMem σ ee kpr mem)
      196 128 4 (by rw [clipperKickSuckKprMem_size σ ee kpr hmem]; omega)
      (by omega) (by omega) (by norm_num)
      (by rw [clipperKickSuckKprMem_size σ ee kpr hmem]; native_decide)]
    unfold clipperRedoSuckKprMem
    rw [toByteArray_write_read_below_len_of_gap (clipperRedoKprTarget kpr)
      (clipperRedoSuckVowMem σ ee mem) 164 128 4
      (by rw [clipperKickSuckVowMem_size σ ee hmem]; omega)
      (by omega) (by omega) (by norm_num)
      (by rw [clipperKickSuckVowMem_size σ ee hmem]; native_decide)]
    unfold clipperRedoSuckVowMem
    rw [toByteArray_write_read_below_len_of_gap (clipperRedoVowTarget σ ee)
      (clipperRedoSuckSelectorMem mem) 132 128 4
      (by rw [clipperKickSuckSelectorMem_size hmem]; omega)
      (by omega) (by omega) (by norm_num)
      (by rw [clipperKickSuckSelectorMem_size hmem]; native_decide)]
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
      196 132 32 (by rw [clipperKickSuckKprMem_size σ ee kpr hmem]; omega)
      (by omega) (by omega) (by norm_num)
      (by rw [clipperKickSuckKprMem_size σ ee kpr hmem]; native_decide)]
    unfold clipperRedoSuckKprMem
    rw [toByteArray_write_read_below_len_of_gap (clipperRedoKprTarget kpr)
      (clipperRedoSuckVowMem σ ee mem) 164 132 32
      (by rw [clipperKickSuckVowMem_size σ ee hmem]; omega)
      (by omega) (by omega) (by norm_num)
      (by rw [clipperKickSuckVowMem_size σ ee hmem]; native_decide)]
    unfold clipperRedoSuckVowMem
    rw [toByteArray_write_read_back_of_gap (clipperRedoVowTarget σ ee)
      (clipperRedoSuckSelectorMem mem) 132
      (by rw [clipperKickSuckSelectorMem_size hmem]; native_decide)]
  have hkpr : final.readWithPadding 164 32 =
      (clipperRedoKprTarget kpr).toByteArray := by
    rw [hfinal]
    unfold clipperRedoSuckCalldataMem
    rw [toByteArray_write_read_below_len_of_gap coin (clipperRedoSuckKprMem σ ee kpr mem)
      196 164 32 (by rw [clipperKickSuckKprMem_size σ ee kpr hmem])
      (by omega) (by omega) (by norm_num)
      (by rw [clipperKickSuckKprMem_size σ ee kpr hmem]; native_decide)]
    unfold clipperRedoSuckKprMem
    rw [toByteArray_write_read_back_of_gap (clipperRedoKprTarget kpr)
      (clipperRedoSuckVowMem σ ee mem) 164
      (by rw [clipperKickSuckVowMem_size σ ee hmem]; native_decide)]
  have hcoin : final.readWithPadding 196 32 = coin.toByteArray := by
    rw [hfinal]
    unfold clipperRedoSuckCalldataMem
    rw [toByteArray_write_read_back_of_gap coin (clipperRedoSuckKprMem σ ee kpr mem) 196
      (by rw [clipperKickSuckKprMem_size σ ee kpr hmem]; native_decide)]
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

theorem clipperKickSuckEncode_eq (v : ClipperImmutables) (σ : AccountMap)
    (ee : ExecutionEnv) (kpr coin : UInt256) {mem : ByteArray} (hmem : mem.size = 192) :
    (config v).externalABI.encode? "suck"
      [.address (AccountAddress.ofNat (clipperRedoVowTarget σ ee).toNat),
        .address (AccountAddress.ofNat kpr.toNat), .int (Int.ofNat coin.toNat)] =
      some ((clipperRedoSuckCalldataMem σ ee kpr coin mem).readWithPadding 128 100) := by
  rw [clipperKickSuckCalldataMem_read128_100 σ ee kpr coin hmem]
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

theorem clipperKickVatPatchPayload6295 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    code.extract' 6295 6327 =
      ({ data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray } : ByteArray) := by
  rcases v.ilk_wf with ⟨bs, hilk, hlen⟩
  let ilkBytes : ByteArray :=
    { data := (EVM.Word.ofNat (fromBytesBigEndian bs)).toBytesBE.toArray }
  let vatBytes : ByteArray :=
    { data := (EVM.Word.ofNat (↑v.vat : Nat)).toBytesBE.toArray }
  have hsize : vatBytes.size = 32 := by
    simpa [vatBytes] using word_toBytesBE_toByteArray_size (EVM.Word.ofNat (↑v.vat : Nat))
  exact patchRuntime_extract'_exact_split (template := clipperBytecode)
    (pre :=
      [(1510, ilkBytes), (1661, ilkBytes), (2221, ilkBytes), (2369, ilkBytes),
       (4239, ilkBytes), (4866, ilkBytes), (5046, ilkBytes), (6800, ilkBytes),
       (8747, ilkBytes),
       (1463, vatBytes), (2437, vatBytes), (3145, vatBytes), (4318, vatBytes),
       (4441, vatBytes), (4751, vatBytes), (5115, vatBytes)])
    (post := [(7936, vatBytes)]) (off := 6295) (value := vatBytes)
    (by
      simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        hilk, hlen, List.lookup_cons, ilkBytes, vatBytes] using hpatch)
    hsize (by simp [PatchesWindowDisjoint32, PatchWindowDisjoint32])
    (by norm_num) (by norm_num)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem clipperKickVatPush32Decode6294 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    decode code (⟨6294⟩ : UInt256) =
      some (.Push .PUSH32, some (EVM.Word.ofNat (↑v.vat : Nat), 32)) := by
  unfold decode
  rw [patchRuntime_get?_disjoint hpatch
    (by apply clipperRuntimePatchesWindowDisjoint32Bool v; native_decide)]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray (code.extract' 6295 6327), 32)) =
    some (Operation.Push Operation.POp.PUSH32,
      some (EVM.Word.ofNat (↑v.vat : Nat), 32))
  rw [clipperKickVatPatchPayload6295 v hpatch, uInt256OfByteArray_word_toBytesBE]

set_option maxHeartbeats 1000000 in
theorem RD.clipperKickIncentiveToSuckGuard {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {coin chip tip top id kpr usr lot tab sel : UInt256}
    {R : List UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨6240⟩
      (coin :: ⟨0⟩ :: chip :: tip :: top :: ⟨1⟩ :: id :: kpr :: usr :: lot :: tab ::
        ⟨476⟩ :: sel :: R)
      mem (UInt256.ofNat 6) o (cA, σ) k C)
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 50 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨6357⟩
      (clipperRedoVatTarget v :: clipperRedoVatTarget v :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: clipperRedoSuckSelectorWord ::
        clipperRedoVatTarget v :: coin :: chip :: tip :: top :: ⟨1⟩ :: id :: kpr :: usr ::
        lot :: tab :: ⟨476⟩ :: sel :: R)
      (clipperRedoSuckCalldataMem σ ee kpr coin mem) (UInt256.ofNat 8) o
      (cA, σ) k' C' := by
  let vatWord : UInt256 := EVM.Word.ofNat (↑v.vat : Nat)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 64 32))) = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hcallMload64 :=
    clipperKickSuckCalldataMem_mload64 σ ee kpr coin hmem hread64
  have rdVowSlotPre := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨2⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdVowSlot⟩ := rdVowSlotPre.sload (by clipper_runtime_decode) (by evm_ov)
  have rdMemPre := evm_run rdVowSlot with [
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov)]
  have rdMem := rdMemPre.mload 0 ⟨128⟩ (UInt256.ofNat 6)
    (by clipper_runtime_decode) mem_cost hmload64 (by decide) (by evm_ov)
  have rdSelectorPre := evm_run rdMem with [
    raw push4 clipperRedoSuckSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨224⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have hselectorShift :
      UInt256.shiftLeft clipperRedoSuckSelectorWord ⟨224⟩ =
        clipperRedoSuckSelectorShifted := by rfl
  have rdSelector := rdSelectorPre.mstore 0 (clipperRedoSuckSelectorMem mem)
    (UInt256.ofNat 6) (by clipper_runtime_decode) mem_cost
    (by rw [hselectorShift]; rfl) (by decide) (by evm_ov)
  have rdVowPre := evm_run rdSelector with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw mstore 0 (clipperRedoSuckVowMem σ ee mem) (UInt256.ofNat 6)
      (by clipper_runtime_decode) mem_cost (by
        simp [clipperRedoVowTarget, solcSlotWord,
          show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by native_decide, u256_land_comm]
        rfl) (by decide) (by evm_ov)]
  have rdKprPre := evm_run rdVowPre with [
    raw dup11 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨36⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov)]
  have rdKpr := rdKprPre.mstore 3 (clipperRedoSuckKprMem σ ee kpr mem)
    (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
    (by
      rw [show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 from by native_decide]
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by native_decide]
      unfold clipperRedoSuckKprMem clipperRedoKprTarget
      rw [u256_land_comm])
    (by native_decide) (by evm_ov)
  have rdCoinPre := evm_run rdKpr with [
    raw push1 ⟨68⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rdCoin := rdCoinPre.mstore 3 (clipperRedoSuckCalldataMem σ ee kpr coin mem)
    (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
    (by
      rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 from by native_decide]
      rfl)
    (by native_decide) (by evm_ov)
  have rdFramePre := evm_run rdCoin with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rdFrameMload := rdFramePre.mload 0 ⟨128⟩ (UInt256.ofNat 8)
    (by clipper_runtime_decode) mem_cost hcallMload64 (by decide) (by evm_ov)
  have rdFrame := evm_run rdFrameMload with [
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  change RD code ee g s0 ⟨6294⟩ _ _ _ _ _ _ _ at rdFrame
  have rdVat := RD.pushConst rdFrame vatWord (width := 32) (op := .PUSH32)
    (by decide) (by simpa [vatWord] using clipperKickVatPush32Decode6294 v hpatch) (by evm_ov)
  change RD code ee g s0 ⟨6327⟩ _ _ _ _ _ _ _ at rdVat
  have rdCallFrame := evm_run rdVat with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw push4 clipperRedoSuckSelectorWord (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨100⟩ (by clipper_runtime_decode) (by evm_ov),
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
  change RD code ee g s0 ⟨6357⟩ _ _ _ _ _ _ _ at rdCallFrame
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by native_decide
  have hsizeWord : UInt256.sub ⟨128⟩ ⟨128⟩ + (⟨100⟩ : UInt256) = ⟨100⟩ := by
    native_decide
  have hendWord : (⟨128⟩ : UInt256) + ⟨100⟩ = ⟨228⟩ := by native_decide
  rw [hmask, hsizeWord, hendWord] at rdCallFrame
  exact ⟨_, _, by
    simpa [vatWord, clipperRedoVatTarget, clipperRedoVowTarget,
      clipperRedoKprTarget, clipperRedoSuckSelectorWord, solcSlotWord,
      u256_land_comm]
      using rdCallFrame⟩

theorem RD.clipperKickSuckNoCode {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {coin chip tip top id kpr usr lot tab sel : UInt256}
    {R : List UInt256} {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨6357⟩
      (clipperRedoVatTarget v :: clipperRedoVatTarget v :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: clipperRedoSuckSelectorWord ::
        clipperRedoVatTarget v :: coin :: chip :: tip :: top :: ⟨1⟩ :: id :: kpr :: usr ::
        lot :: tab :: ⟨476⟩ :: sel :: R)
      mem (UInt256.ofNat 8) o (cA, σ) k C)
    (hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ (clipperRedoVatTarget v) = ⟨0⟩)
    (hov : R.length + 50 ≤ 1024) : RDrev code g s0 := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨6357⟩) (okPc := ⟨6369⟩)
    rd hcodeSizeVat
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.clipperKickSuckPostCall
    {cA0 cA gh bl σ₀ σStart σ} {ee : ExecutionEnv}
    {g : Sat256} {A : Substate} {k C : ℕ}
    {coin chip tip top id kpr usr lot tab sel : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (rd : RD code ee g (initState cA0 gh bl σStart σ₀ g A ee) ⟨6357⟩
      (clipperRedoVatTarget v :: clipperRedoVatTarget v :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: clipperRedoSuckSelectorWord ::
        clipperRedoVatTarget v :: coin :: chip :: tip :: top :: ⟨1⟩ :: id :: kpr :: usr ::
        lot :: tab :: ⟨476⟩ :: sel :: R)
      (clipperRedoSuckCalldataMem σ ee kpr coin mem)
      (UInt256.ofNat 8) rdata (cA, σ) k C)
    (hcodeSizeVat :
      Reasoning.Theory.extCodeSizeWord σ (clipperRedoVatTarget v) ≠ ⟨0⟩)
    (hdepth : ee.depth.val < 1024) (hperm : ee.perm = true)
    (hmem : mem.size = 192) (hov : R.length + 50 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code ee g (initState cA0 gh bl σStart σ₀ g A ee) ⟨6373⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: clipperRedoSuckSelectorWord ::
          clipperRedoVatTarget v :: coin :: chip :: tip :: top :: ⟨1⟩ :: id :: kpr :: usr ::
          lot :: tab :: ⟨476⟩ :: sel :: R)
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
  obtain ⟨gasWord, _, _, rd6372⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨6357⟩) (okPc := ⟨6369⟩)
      rd hcodeSizeVat
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (clipperKickJumpDest6369 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, out, A_in, callGas, k6373, C6373, hΘpack,
      rd6373raw, houtSize⟩ :=
    RD.call rd6372 (by clipper_runtime_decode) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k6373, C6373, ?_, ?_, houtSize⟩
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
    simpa [hmin, byteArray_write_len_zero, haw] using rd6373raw
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
        clipperKickSuckEncode_eq v σ ee kpr coin hmem
    · simpa [evmVat, initState, hperm] using hΘ

theorem RD.clipperKickSuckCallFailure {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD code ee g s0 ⟨6373⟩ (⟨0⟩ :: R) mem aw out acc k C)
    (hout : out.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨6373⟩) (okPc := ⟨6389⟩)
    rd (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    (by clipper_runtime_decode) (by clipper_runtime_decode)
    hout hov

theorem RD.clipperKickSuckCallSuccess {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {coin chip tip top id kpr usr lot tab sel : UInt256}
    {R : List UInt256} {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD code ee g s0 ⟨6373⟩
      (⟨1⟩ :: ⟨228⟩ :: clipperRedoSuckSelectorWord :: clipperRedoVatTarget v ::
        coin :: chip :: tip :: top :: ⟨1⟩ :: id :: kpr :: usr :: lot :: tab :: ⟨476⟩ ::
        sel :: R)
      mem aw out acc k C)
    (hov : R.length + 50 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨6394⟩
      (coin :: chip :: tip :: top :: ⟨1⟩ :: id :: kpr :: usr :: lot :: tab :: ⟨476⟩ ::
        sel :: R)
      mem aw out acc k' C' := by
  obtain ⟨_, _, rd6391⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨6373⟩) (okPc := ⟨6389⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by clipper_runtime_decode) (clipperKickJumpDest6389 v hpatch)
      (by clipper_runtime_decode) (by clipper_runtime_decode)
      (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd6391 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]⟩

end Benchmarks.Dss.Clipper
