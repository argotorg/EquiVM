import Benchmarks.Auction.UnpauseErrorStringDecoder

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 1000000
namespace Auction

theorem errorStringMemFree_mload64_of_aw (mem : ByteArray) (aw newFree : UInt256)
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size) :
    let memFree : ByteArray := (UInt256.toByteArray newFree).write 0 mem 64 32
    let awFree := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
    (if (⟨64⟩ : UInt256).toNat ≥ memFree.size ∨
        (⟨64⟩ : UInt256) ≥ awFree * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memFree.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      newFree := by
  intro memFree awFree
  apply mloadWordValue_of_readWithPadding
  · dsimp [memFree]
    have hgap : 64 - mem.size < USize.size :=
      lt_of_le_of_lt (Nat.sub_le _ _) (by native_decide : 64 < USize.size)
    have hsz := toByteArray_write_size_ge_off_add32 newFree mem 64 hgap
    change 64 < ((UInt256.toByteArray newFree).write 0 mem 64 32).size
    omega
  · intro h
    have hceil : (((⟨64⟩ : UInt256).toNat + 32 + 31) / 32) = 3 := by native_decide
    have hawNat : awFree.toNat = aw.toNat := by
      dsimp [awFree]
      rw [UInt256.toNat_ofNat_of_lt]
      · dsimp [MachineState.M]
        rw [hceil, max_eq_left haw3]
      · dsimp [MachineState.M]
        rw [hceil]
        exact max_lt aw.val.isLt (by norm_num [UInt256.size])
    have hmulNat : (awFree * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
      rw [umul_toNat]
      · rw [hawNat]
        rfl
      · simpa [hawNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hawMul
    have hle : (awFree * (⟨32⟩ : UInt256)).toNat ≤ 64 := by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using h
    rw [hmulNat] at hle
    omega
  · exact toByteArray_write_read_back_of_gap newFree mem 64
      (lt_of_le_of_lt (Nat.sub_le _ _) (by native_decide : 64 < USize.size))

-- LIBRARY CANDIDATE: generic `MLOAD 0x40` readback from a known word and active-word bound.
theorem mload64_of_readWithPadding_of_aw {mem : ByteArray} {aw val : UInt256}
    (hmem : 64 < mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray val)
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      val := by
  apply mloadWordValue_of_readWithPadding
  · simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hmem
  · intro h
    have hmulNat : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
      rw [umul_toNat]
      · rfl
      · simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hawMul
    have hle : (aw * (⟨32⟩ : UInt256)).toNat ≤ 64 := by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using h
    rw [hmulNat] at hle
    omega
  · simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hread

theorem auctionAwMstore32_bounds {aw addr : UInt256}
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size)
    (haddrLe : addr.toNat ≤ ABI.solcMaxU64 + 68) :
    let aw' := UInt256.ofNat (MachineState.M aw.toNat addr.toNat 32)
    3 ≤ aw'.toNat ∧ aw'.toNat * 32 < UInt256.size := by
  intro aw'
  let ceilA := (addr.toNat + 32 + 31) / 32
  have hceilMulLe : ceilA * 32 ≤ addr.toNat + 63 := by
    dsimp [ceilA]
    omega
  have hceilMulLt : ceilA * 32 < UInt256.size := by
    have hmax : addr.toNat + 63 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size] at haddrLe ⊢
      omega
    exact lt_of_le_of_lt hceilMulLe hmax
  have hceilLt : ceilA < UInt256.size := by
    nlinarith [hceilMulLt]
  have hMlt : MachineState.M aw.toNat addr.toNat 32 < UInt256.size := by
    dsimp [MachineState.M]
    exact max_lt aw.val.isLt (by simpa [ceilA] using hceilLt)
  have haw'Nat : aw'.toNat = MachineState.M aw.toNat addr.toNat 32 := by
    dsimp [aw']
    rw [UInt256.toNat_ofNat_of_lt hMlt]
  constructor
  · rw [haw'Nat]
    dsimp [MachineState.M]
    exact le_max_of_le_left haw3
  · rw [haw'Nat]
    dsimp [MachineState.M]
    rw [Nat.mul_comm, mul_max, Nat.mul_comm 32 aw.toNat, Nat.mul_comm 32 ceilA]
    exact max_lt hawMul (by simpa [ceilA] using hceilMulLt)

theorem auctionErrorStringEvent_aw_bounds {aw fmp : UInt256}
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size)
    (hfmpLe : fmp.toNat ≤ ABI.solcMaxU64) :
    let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
    let awEvent := UInt256.ofNat (MachineState.M aw64.toNat fmp.toNat 32)
    3 ≤ awEvent.toNat ∧ awEvent.toNat * 32 < UInt256.size := by
  intro aw64 awEvent
  have hceil64 : (((⟨64⟩ : UInt256).toNat + 32 + 31) / 32) = 3 := by
    native_decide
  have haw64Nat : aw64.toNat = aw.toNat := by
    dsimp [aw64]
    rw [UInt256.toNat_ofNat_of_lt]
    · dsimp [MachineState.M]
      rw [hceil64, max_eq_left haw3]
    · dsimp [MachineState.M]
      rw [hceil64]
      exact max_lt aw.val.isLt (by norm_num [UInt256.size])
  let ceilF := (fmp.toNat + 32 + 31) / 32
  have hceilMulLe : ceilF * 32 ≤ fmp.toNat + 63 := by
    dsimp [ceilF]
    omega
  have hceilMulLt : ceilF * 32 < UInt256.size := by
    have hmax : fmp.toNat + 63 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size] at hfmpLe ⊢
      omega
    exact lt_of_le_of_lt hceilMulLe hmax
  have hceilLt : ceilF < UInt256.size := by
    nlinarith [hceilMulLt]
  have hMlt : MachineState.M aw64.toNat fmp.toNat 32 < UInt256.size := by
    dsimp [MachineState.M]
    apply max_lt
    · rw [haw64Nat]
      exact aw.val.isLt
    · simpa [ceilF]
  have hawEventNat : awEvent.toNat = MachineState.M aw64.toNat fmp.toNat 32 := by
    dsimp [awEvent]
    rw [UInt256.toNat_ofNat_of_lt hMlt]
  constructor
  · rw [hawEventNat]
    dsimp [MachineState.M]
    exact le_max_of_le_left (by simpa [haw64Nat] using haw3)
  · rw [hawEventNat]
    dsimp [MachineState.M]
    rw [Nat.mul_comm, mul_max, Nat.mul_comm 32 aw64.toNat, Nat.mul_comm 32 ceilF]
    exact max_lt (by simpa [haw64Nat] using hawMul) (by simpa [ceilF] using hceilMulLt)

theorem auctionEventMemFrom_mload64_of_base {mem : ByteArray} {aw fmp : UInt256}
    (I : ExecutionEnv)
    (hmem : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fmp)
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size)
    (hfmpGe : 96 ≤ fmp.toNat) (hfmpLe : fmp.toNat ≤ ABI.solcMaxU64) :
    (if (⟨64⟩ : UInt256).toNat ≥ (auctionEventMemFrom mem I fmp).size ∨
        (⟨64⟩ : UInt256) ≥
          (UInt256.ofNat
            (MachineState.M
              (UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)).toNat
              fmp.toNat 32)) * ⟨32⟩ then
        ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((auctionEventMemFrom mem I fmp).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      fmp := by
  have hgap : fmp.toNat - mem.size < USize.size := by
    have hfmpU : fmp.toNat < USize.size :=
      lt_of_le_of_lt hfmpLe (by native_decide : ABI.solcMaxU64 < USize.size)
    exact lt_of_le_of_lt (Nat.sub_le _ _) hfmpU
  have hsizeEvent : 64 < (auctionEventMemFrom mem I fmp).size := by
    have hsz := toByteArray_write_size_ge_off_add32 (auctionSourceWord I) mem
      fmp.toNat hgap
    simp [auctionEventMemFrom]
    omega
  have hreadEvent :
      (auctionEventMemFrom mem I fmp).readWithPadding 64 32 =
        UInt256.toByteArray fmp := by
    have hpres := toByteArray_write_read_below_of_gap (auctionSourceWord I) mem
      fmp.toNat 64 hmem hfmpGe hgap
    rw [auctionEventMemFrom]
    rw [hpres]
    exact hread
  have hawEvent := auctionErrorStringEvent_aw_bounds (aw := aw) (fmp := fmp)
    haw3 hawMul hfmpLe
  exact mload64_of_readWithPadding_of_aw hsizeEvent hreadEvent
    (by simpa using hawEvent.1) (by simpa using hawEvent.2)

noncomputable def auctionPausablePausedMem0From (mem : ByteArray) (fmp : UInt256) :
    ByteArray :=
  (UInt256.toByteArray solcErrorStringSelector).write 0 mem fmp.toNat 32

noncomputable def auctionPausablePausedMem1From (mem : ByteArray) (fmp : UInt256) :
    ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0
    (auctionPausablePausedMem0From mem fmp) (fmp + (⟨4⟩ : UInt256)).toNat 32

noncomputable def auctionPausablePausedMem2From (mem : ByteArray) (fmp : UInt256) :
    ByteArray :=
  (UInt256.toByteArray (⟨16⟩ : UInt256)).write 0
    (auctionPausablePausedMem1From mem fmp) (fmp + (⟨36⟩ : UInt256)).toNat 32

noncomputable def auctionPausablePausedMem3From (mem : ByteArray) (fmp : UInt256) :
    ByteArray :=
  (UInt256.toByteArray auctionPausablePausedStringWord).write 0
    (auctionPausablePausedMem2From mem fmp) (fmp + (⟨68⟩ : UInt256)).toNat 32

def auctionPausablePausedAw64From (aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)

def auctionPausablePausedAw0From (aw fmp : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (auctionPausablePausedAw64From aw).toNat fmp.toNat 32)

def auctionPausablePausedAw1From (aw fmp : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (auctionPausablePausedAw0From aw fmp).toNat
      (fmp + (⟨4⟩ : UInt256)).toNat 32)

def auctionPausablePausedAw2From (aw fmp : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (auctionPausablePausedAw1From aw fmp).toNat
      (fmp + (⟨36⟩ : UInt256)).toNat 32)

def auctionPausablePausedAw3From (aw fmp : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (auctionPausablePausedAw2From aw fmp).toNat
      (fmp + (⟨68⟩ : UInt256)).toNat 32)

theorem auctionPausablePausedAw3From_bounds {aw fmp : UInt256}
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size)
    (hfmpLe : fmp.toNat ≤ ABI.solcMaxU64) :
    3 ≤ (auctionPausablePausedAw3From aw fmp).toNat ∧
      (auctionPausablePausedAw3From aw fmp).toNat * 32 < UInt256.size := by
  have haddr64 : (⟨64⟩ : UInt256).toNat ≤ ABI.solcMaxU64 + 68 := by
    native_decide
  have haw64 := auctionAwMstore32_bounds (aw := aw) (addr := (⟨64⟩ : UInt256))
    haw3 hawMul haddr64
  have hfmpAddr : fmp.toNat ≤ ABI.solcMaxU64 + 68 := by
    omega
  have haw0 := auctionAwMstore32_bounds
    (aw := auctionPausablePausedAw64From aw) (addr := fmp)
    (by simpa [auctionPausablePausedAw64From] using haw64.1)
    (by simpa [auctionPausablePausedAw64From] using haw64.2)
    hfmpAddr
  have hfmp4 : (fmp + (⟨4⟩ : UInt256)).toNat ≤ ABI.solcMaxU64 + 68 := by
    have hnat : (fmp + (⟨4⟩ : UInt256)).toNat = fmp.toNat + 4 := by
      rw [uadd_toNat]
      rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      rw [Nat.mod_eq_of_lt]
      norm_num [ABI.solcMaxU64, UInt256.size] at hfmpLe ⊢
      omega
    rw [hnat]
    omega
  have haw1 := auctionAwMstore32_bounds
    (aw := auctionPausablePausedAw0From aw fmp) (addr := fmp + (⟨4⟩ : UInt256))
    (by simpa [auctionPausablePausedAw0From] using haw0.1)
    (by simpa [auctionPausablePausedAw0From] using haw0.2)
    hfmp4
  have hfmp36 : (fmp + (⟨36⟩ : UInt256)).toNat ≤ ABI.solcMaxU64 + 68 := by
    have hnat : (fmp + (⟨36⟩ : UInt256)).toNat = fmp.toNat + 36 := by
      rw [uadd_toNat]
      rw [show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      rw [Nat.mod_eq_of_lt]
      norm_num [ABI.solcMaxU64, UInt256.size] at hfmpLe ⊢
      omega
    rw [hnat]
    omega
  have haw2 := auctionAwMstore32_bounds
    (aw := auctionPausablePausedAw1From aw fmp) (addr := fmp + (⟨36⟩ : UInt256))
    (by simpa [auctionPausablePausedAw1From] using haw1.1)
    (by simpa [auctionPausablePausedAw1From] using haw1.2)
    hfmp36
  have hfmp68 : (fmp + (⟨68⟩ : UInt256)).toNat ≤ ABI.solcMaxU64 + 68 := by
    have hnat : (fmp + (⟨68⟩ : UInt256)).toNat = fmp.toNat + 68 := by
      rw [uadd_toNat]
      rw [show (⟨68⟩ : UInt256).toNat = 68 from by decide]
      rw [Nat.mod_eq_of_lt]
      norm_num [ABI.solcMaxU64, UInt256.size] at hfmpLe ⊢
      omega
    rw [hnat]
    omega
  have haw3' := auctionAwMstore32_bounds
    (aw := auctionPausablePausedAw2From aw fmp) (addr := fmp + (⟨68⟩ : UInt256))
    (by simpa [auctionPausablePausedAw2From] using haw2.1)
    (by simpa [auctionPausablePausedAw2From] using haw2.2)
    hfmp68
  simpa [auctionPausablePausedAw3From] using haw3'

theorem auctionPausablePausedMem3From_mload64_of_base {mem : ByteArray}
    {aw fmp : UInt256}
    (hmem : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fmp)
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size)
    (hfmpGe : 96 ≤ fmp.toNat) (hfmpLe : fmp.toNat ≤ ABI.solcMaxU64) :
    (if (⟨64⟩ : UInt256).toNat ≥ (auctionPausablePausedMem3From mem fmp).size ∨
        (⟨64⟩ : UInt256) ≥ auctionPausablePausedAw3From aw fmp * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionPausablePausedMem3From mem fmp).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      fmp := by
  let mem0 := auctionPausablePausedMem0From mem fmp
  let mem1 := auctionPausablePausedMem1From mem fmp
  let mem2 := auctionPausablePausedMem2From mem fmp
  let mem3 := auctionPausablePausedMem3From mem fmp
  have hfmpU : fmp.toNat < USize.size :=
    lt_of_le_of_lt hfmpLe (by native_decide : ABI.solcMaxU64 < USize.size)
  have hgap0 : fmp.toNat - mem.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) hfmpU
  have hsz0 : fmp.toNat + 32 ≤ mem0.size := by
    dsimp [mem0, auctionPausablePausedMem0From]
    exact toByteArray_write_size_ge_off_add32 solcErrorStringSelector mem fmp.toNat hgap0
  have hmem0 : 96 ≤ mem0.size := by
    omega
  have hread0 : mem0.readWithPadding 64 32 = UInt256.toByteArray fmp := by
    have hpres := toByteArray_write_read_below_of_gap solcErrorStringSelector mem
      fmp.toNat 64 hmem hfmpGe hgap0
    dsimp [mem0, auctionPausablePausedMem0From]
    rw [hpres]
    exact hread
  have hfmp4Nat : (fmp + (⟨4⟩ : UInt256)).toNat = fmp.toNat + 4 := by
    rw [uadd_toNat]
    rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    rw [Nat.mod_eq_of_lt]
    norm_num [ABI.solcMaxU64, UInt256.size] at hfmpLe ⊢
    omega
  have hoff1Le : (fmp + (⟨4⟩ : UInt256)).toNat ≤ mem0.size := by
    rw [hfmp4Nat]
    omega
  have hgap1 : (fmp + (⟨4⟩ : UInt256)).toNat - mem0.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le hoff1Le]
    exact USize.size_pos
  have hsz1 : (fmp + (⟨4⟩ : UInt256)).toNat + 32 ≤ mem1.size := by
    dsimp [mem1, auctionPausablePausedMem1From, mem0]
    exact toByteArray_write_size_ge_off_add32 (⟨32⟩ : UInt256)
      (auctionPausablePausedMem0From mem fmp) (fmp + (⟨4⟩ : UInt256)).toNat hgap1
  have hmem1 : 96 ≤ mem1.size := by
    rw [hfmp4Nat] at hsz1
    omega
  have hread1 : mem1.readWithPadding 64 32 = UInt256.toByteArray fmp := by
    have hbelow : 64 + 32 ≤ (fmp + (⟨4⟩ : UInt256)).toNat := by
      rw [hfmp4Nat]
      omega
    have hpres := toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256)
      (auctionPausablePausedMem0From mem fmp) (fmp + (⟨4⟩ : UInt256)).toNat 64
      hmem0 hbelow hgap1
    dsimp [mem1, auctionPausablePausedMem1From]
    rw [hpres]
    exact hread0
  have hfmp36Nat : (fmp + (⟨36⟩ : UInt256)).toNat = fmp.toNat + 36 := by
    rw [uadd_toNat]
    rw [show (⟨36⟩ : UInt256).toNat = 36 from by decide]
    rw [Nat.mod_eq_of_lt]
    norm_num [ABI.solcMaxU64, UInt256.size] at hfmpLe ⊢
    omega
  have hoff2Le : (fmp + (⟨36⟩ : UInt256)).toNat ≤ mem1.size := by
    rw [hfmp36Nat]
    rw [hfmp4Nat] at hsz1
    omega
  have hgap2 : (fmp + (⟨36⟩ : UInt256)).toNat - mem1.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le hoff2Le]
    exact USize.size_pos
  have hsz2 : (fmp + (⟨36⟩ : UInt256)).toNat + 32 ≤ mem2.size := by
    dsimp [mem2, auctionPausablePausedMem2From, mem1]
    exact toByteArray_write_size_ge_off_add32 (⟨16⟩ : UInt256)
      (auctionPausablePausedMem1From mem fmp) (fmp + (⟨36⟩ : UInt256)).toNat hgap2
  have hmem2 : 96 ≤ mem2.size := by
    rw [hfmp36Nat] at hsz2
    omega
  have hread2 : mem2.readWithPadding 64 32 = UInt256.toByteArray fmp := by
    have hbelow : 64 + 32 ≤ (fmp + (⟨36⟩ : UInt256)).toNat := by
      rw [hfmp36Nat]
      omega
    have hpres := toByteArray_write_read_below_of_gap (⟨16⟩ : UInt256)
      (auctionPausablePausedMem1From mem fmp) (fmp + (⟨36⟩ : UInt256)).toNat 64
      hmem1 hbelow hgap2
    dsimp [mem2, auctionPausablePausedMem2From]
    rw [hpres]
    exact hread1
  have hfmp68Nat : (fmp + (⟨68⟩ : UInt256)).toNat = fmp.toNat + 68 := by
    rw [uadd_toNat]
    rw [show (⟨68⟩ : UInt256).toNat = 68 from by decide]
    rw [Nat.mod_eq_of_lt]
    norm_num [ABI.solcMaxU64, UInt256.size] at hfmpLe ⊢
    omega
  have hoff3Le : (fmp + (⟨68⟩ : UInt256)).toNat ≤ mem2.size := by
    rw [hfmp68Nat]
    rw [hfmp36Nat] at hsz2
    omega
  have hgap3 : (fmp + (⟨68⟩ : UInt256)).toNat - mem2.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le hoff3Le]
    exact USize.size_pos
  have hsz3 : (fmp + (⟨68⟩ : UInt256)).toNat + 32 ≤ mem3.size := by
    dsimp [mem3, auctionPausablePausedMem3From, mem2]
    exact toByteArray_write_size_ge_off_add32 auctionPausablePausedStringWord
      (auctionPausablePausedMem2From mem fmp) (fmp + (⟨68⟩ : UInt256)).toNat hgap3
  have hsize3 : 64 < mem3.size := by
    rw [hfmp68Nat] at hsz3
    omega
  have hread3 : mem3.readWithPadding 64 32 = UInt256.toByteArray fmp := by
    have hbelow : 64 + 32 ≤ (fmp + (⟨68⟩ : UInt256)).toNat := by
      rw [hfmp68Nat]
      omega
    have hpres := toByteArray_write_read_below_of_gap auctionPausablePausedStringWord
      (auctionPausablePausedMem2From mem fmp) (fmp + (⟨68⟩ : UInt256)).toNat 64
      hmem2 hbelow hgap3
    dsimp [mem3, auctionPausablePausedMem3From]
    rw [hpres]
    exact hread2
  have hawErr := auctionPausablePausedAw3From_bounds (aw := aw) (fmp := fmp)
    haw3 hawMul hfmpLe
  exact mload64_of_readWithPadding_of_aw (mem := mem3)
    (aw := auctionPausablePausedAw3From aw fmp) (val := fmp)
    hsize3 hread3 hawErr.1 hawErr.2

set_option maxHeartbeats 10000000 in
theorem auctionCreateAuction_errorStringDecoderCopyToReturnAllocFail {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw fmp off len : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨6037⟩
      (len :: ⟨0xffffffffffffffff⟩ :: (fmp + off) :: off ::
        UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem aw o acc k C)
    (hguard :
      UInt256.lor
          (UInt256.gt
            (fmp +
              UInt256.land (UInt256.lnot (⟨31⟩ : UInt256))
                ((((off + len) + ⟨32⟩ : UInt256) + ⟨31⟩)))
            (⟨0xffffffffffffffff⟩ : UInt256))
          (UInt256.lt
            (fmp +
              UInt256.land (UInt256.lnot (⟨31⟩ : UInt256))
                ((((off + len) + ⟨32⟩ : UInt256) + ⟨31⟩)))
            fmp) ≠
        ⟨0⟩)
    (hov : R.length + 16 ≤ 1024) :
    RDrev auctionBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let max64 : UInt256 := ⟨0xffffffffffffffff⟩
  let payloadLen : UInt256 := (off + len) + ⟨32⟩
  let roundedLen : UInt256 :=
    UInt256.land (UInt256.lnot (⟨31⟩ : UInt256)) (payloadLen + ⟨31⟩)
  let newFree : UInt256 := fmp + roundedLen
  have hguardRev : UInt256.lor (UInt256.lt newFree fmp) (UInt256.gt newFree max64) ≠
      ⟨0⟩ := by
    intro h
    apply hguard
    rw [← u256_lor_comm] at h
    simpa [newFree, roundedLen, payloadLen, max64] using h
  have hguard' : UInt256.isZero (UInt256.lor (UInt256.lt newFree fmp)
      (UInt256.gt newFree max64)) = ⟨0⟩ := by
    exact isZero_eq_zero_of_ne hguardRev
  have rd5868₀ := evm_run rd with [
    push2 ⟨6051⟩, push1 ⟨32⟩, dup3, dup7, add, add, dup8, push2 ⟨5868⟩,
    jump (by jump_dest)]
  have rd5868 : ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I)
      ⟨5868⟩
      (fmp :: payloadLen :: ⟨6051⟩ :: len :: max64 :: (fmp + off) :: off ::
        UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem aw o acc k' C' := by
    exact ⟨_, _, by simpa [payloadLen, max64] using rd5868₀⟩
  obtain ⟨_, _, rd5868⟩ := rd5868
  have rd5869 := RD.jumpdest rd5868 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5871 := RD.push1 rd5869 ⟨31⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5872 := RD.dup3 rd5871 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5873 := RD.add rd5872 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5875 := RD.push1 rd5873 ⟨31⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5876 := RD.not rd5875 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5877 := RD.and rd5876 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5878 := RD.dup2 rd5877 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5879 := RD.add rd5878 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5888 := RD.pushConst rd5879 max64 (width := 8) (op := .PUSH8)
    (by decide) (by native_decide) (by simp only [List.length_cons]; omega)
  have rd5889 := RD.dup2 rd5888 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5890 := RD.gt rd5889 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5891 := RD.dup3 rd5890 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5892 := RD.dup3 rd5891 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5893 := RD.lt rd5892 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5894 := RD.lor rd5893 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5895₀ := RD.iszero rd5894 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd5895 := rd5895₀
  rw [hguard'] at rd5895
  have rd5898 := evm_run rd5895 with [push2 ⟨5918⟩, jumpiNT (by decide)]
  have hsel : UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
      ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ := by
    decide
  let panicSelector : UInt256 :=
    ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩
  let mem0 := (UInt256.toByteArray panicSelector).write 0 mem 0 32
  let aw0 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
  have rd5907₀ := evm_run rd5898 with [push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl]
  have rd5907 := rd5907₀
  rw [hsel] at rd5907
  have rd5909 := evm_run rd5907 with [
    push0,
    raw mstore (Cₘ aw0 - Cₘ aw) mem0 aw0 (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw0])
      (by rfl) (by rfl) (by simp only [List.length_cons]; omega)]
  let mem1 := (UInt256.toByteArray (⟨65⟩ : UInt256)).write 0 mem0 4 32
  let aw1 := UInt256.ofNat (MachineState.M aw0.toNat 4 32)
  have rd5917 := evm_run rd5909 with [
    push1 ⟨65⟩, push1 ⟨4⟩,
    raw mstore (Cₘ aw1 - Cₘ aw0) mem1 aw1 (by native_decide)
      (fun s haw hstk => by
        have h4 : (⟨4⟩ : UInt256).toNat = 4 := by decide
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw1, h4])
      (by rfl) (by rfl) (by simp only [List.length_cons]; omega),
    push1 ⟨36⟩, push0]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M aw1.toNat 0 36)) - Cₘ aw1)
    rd5917 (by decide)
    (fun s haw hstk => by
      have h36 : (⟨36⟩ : UInt256).toNat = 36 := by decide
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw1, h36])
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringDecodedToPause {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw ptr : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3143⟩
      (ptr :: R) mem aw o acc k C)
    (hptr : ptr ≠ ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3655⟩
      (⟨2850⟩ :: ptr :: R) mem aw o acc k' C' := by
  have rd3148 := evm_run rd with [jumpdest, dup1, push2 ⟨3154⟩]
  have rd3154 := RD.jumpiT rd3148 (by native_decide) hptr (by jump_dest)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd3154 with [
    jumpdest, push2 ⟨2850⟩, push2 ⟨3655⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringDecodedNullRevert {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3143⟩
      (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 8 ≤ 1024) :
    RDrev auctionBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  have rd3165 := evm_run rd with [
    jumpdest, dup1, push2 ⟨3154⟩, jumpiNT (by decide), pop,
    push2 ⟨3164⟩, jump (by jump_dest), jumpdest]
  exact auctionCreateAuction_mintCallFailureBubbleRevertTail
    (mem := mem) (aw := aw) rd3165 hosz hov

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringPauseReturnTail {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw ptr : UInt256} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨2850⟩
      [ptr, ⟨1163⟩, ⟨413⟩, auctionSelWord I] mem aw o acc k C) :
    RDret auctionBytecode g (initState cA gh bl σInit σ₀ g A I) acc ByteArray.empty := by
  have rd1163 := evm_run rd with [jumpdest, pop, jump (by jump_dest), jumpdest]
  have rd413 := evm_run rd1163 with [jump (by jump_dest), jumpdest]
  exact rd413.stop (by native_decide) (by evm_ov)

set_option maxHeartbeats 10000000 in
theorem auctionPauseRoutine_revert_paused_from_mem {cA accA gh bl σInit σ σ₀ A I}
    {g : Sat256}
    {mem rdata : ByteArray} {aw fmp : UInt256} {k C : ℕ} {ret : UInt256}
    {R : List UInt256}
    (hperm : I.perm = true)
    (hnz : auctionPausedWord σ I ≠ ⟨0⟩)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        fmp)
    (hmload64Err :
      (if (⟨64⟩ : UInt256).toNat ≥ (auctionPausablePausedMem3From mem fmp).size ∨
          (⟨64⟩ : UInt256) ≥ auctionPausablePausedAw3From aw fmp * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((auctionPausablePausedMem3From mem fmp).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        fmp)
    (hlen100 : UInt256.sub ((⟨100⟩ : UInt256) + fmp) fmp = ⟨100⟩)
    (hov : R.length + 8 ≤ 1024)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3655⟩
      (ret :: R) mem aw rdata (accA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  have rd3663₀ := evm_run h with [jumpdest, push1 ⟨51⟩]
  obtain ⟨_, _, rd3659₀⟩ := rd3663₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3659⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3659⟩
      (auctionSlotWord ⟨51⟩ σ I :: ret :: R) mem aw rdata (accA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3659₀⟩
  have rd3663 := evm_run rd3659 with [push1 ⟨255⟩, and, iszero]
  have hmask : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) = auctionPausedWord σ I := by
    rw [auctionPausedWord, u256_land_comm]
  have hcond : UInt256.isZero (UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I)) = ⟨0⟩ := by
    exact isZero_eq_zero_of_ne (by simpa [hmask] using hnz)
  have rd3667 := evm_run rd3663 with [
    push2 ⟨3725⟩, jumpiNT hcond]
  let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd3670 := evm_run rd3667 with [
    push1 ⟨64⟩,
    raw mload (Cₘ aw64 - Cₘ aw) fmp aw64 (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw64])
      hmload64 (by rfl) (by simp only [List.length_cons]; omega)]
  have rd3674 := rd3670.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by native_decide) (by evm_ov)
  let mem0 := auctionPausablePausedMem0From mem fmp
  let aw0 := UInt256.ofNat (MachineState.M aw64.toNat fmp.toNat 32)
  let mem1 := auctionPausablePausedMem1From mem fmp
  let aw1 := UInt256.ofNat (MachineState.M aw0.toNat (fmp + (⟨4⟩ : UInt256)).toNat 32)
  let mem2 := auctionPausablePausedMem2From mem fmp
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat (fmp + (⟨36⟩ : UInt256)).toNat 32)
  let mem3 := auctionPausablePausedMem3From mem fmp
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (fmp + (⟨68⟩ : UInt256)).toNat 32)
  have rd3693 := evm_run rd3674 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore (Cₘ aw0 - Cₘ aw64) mem0 aw0
      (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw0])
      (by rfl) (by rfl) (by simp only [List.length_cons]; omega),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore (Cₘ aw1 - Cₘ aw0) mem1 aw1
      (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw1])
      (by rfl) (by rfl) (by simp only [List.length_cons]; omega),
    push1 ⟨16⟩, push1 ⟨36⟩, dup3, add,
    raw mstore (Cₘ aw2 - Cₘ aw1) mem2 aw2
      (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2])
      (by rfl) (by rfl) (by simp only [List.length_cons]; omega)]
  have rd3710 := rd3693.pushConst auctionPausablePausedRawStringWord
    (width := 16) (op := .PUSH16) (by decide) (by native_decide) (by evm_ov)
  have rd3713₀ := evm_run rd3710 with [push1 ⟨130⟩, shl]
  have hword :
      UInt256.shiftLeft auctionPausablePausedRawStringWord ⟨130⟩ =
        auctionPausablePausedStringWord := by
    native_decide
  have rd3713 := rd3713₀
  rw [hword] at rd3713
  have rd3721₀ := evm_run rd3713 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore (Cₘ aw3 - Cₘ aw2) mem3 aw3
      (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw3])
      (by rfl) (by rfl) (by simp only [List.length_cons]; omega),
    push1 ⟨100⟩, add]
  have rd3721 := rd3721₀
  have rd994 := evm_run rd3721 with [push2 ⟨994⟩, jump (by jump_dest)]
  let aw64Err := UInt256.ofNat (MachineState.M aw3.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload (Cₘ aw64Err - Cₘ aw3) fmp aw64Err (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw64Err])
      (by
        simpa [mem3, aw3, aw2, aw1, aw0, aw64, auctionPausablePausedAw3From,
          auctionPausablePausedAw2From, auctionPausablePausedAw1From,
          auctionPausablePausedAw0From, auctionPausablePausedAw64From] using hmload64Err)
      (by rfl)
      (by simp only [List.length_cons]; omega),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [hlen100] at rd1001
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M aw64Err.toNat fmp.toNat (⟨100⟩ : UInt256).toNat)) -
      Cₘ aw64Err)
    rd1001 (by decide)
    (fun s haws hstks => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw64Err])
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem auctionPauseRoutine_success_from_mem {cA accA gh bl σInit σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw fmp : UInt256} {k C : ℕ} {ret : UInt256}
    {R : List UInt256}
    (hperm : I.perm = true)
    (hzero : auctionPausedWord σ I = ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        fmp)
    (hmload64Event :
      (if (⟨64⟩ : UInt256).toNat ≥ (auctionEventMemFrom mem I fmp).size ∨
          (⟨64⟩ : UInt256) ≥
            (UInt256.ofNat
              (MachineState.M
                (UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)).toNat
                fmp.toNat 32)) * ⟨32⟩ then
          ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((auctionEventMemFrom mem I fmp).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        fmp)
    (hlen32 : UInt256.sub ((⟨32⟩ : UInt256) + fmp) fmp = ⟨32⟩)
    (hov : R.length + 8 ≤ 1024)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3655⟩
      (ret :: R) mem aw rdata (accA, σ) k C) :
    ∃ mem' aw' k' C',
      RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R mem' aw' rdata
        (accA, auctionPausePostMap σ I) k' C' := by
  have rd3663₀ := evm_run h with [jumpdest, push1 ⟨51⟩]
  obtain ⟨_, _, rd3659₀⟩ := rd3663₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3659⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3659⟩
      (auctionSlotWord ⟨51⟩ σ I :: ret :: R) mem aw rdata (accA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3659₀⟩
  have rd3663 := evm_run rd3659 with [push1 ⟨255⟩, and, iszero]
  have hmask : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) = auctionPausedWord σ I := by
    rw [auctionPausedWord, u256_land_comm]
  have hcond : UInt256.isZero (UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I)) ≠ ⟨0⟩ := by
    rw [hmask, hzero]
    decide
  have rd3725 := evm_run rd3663 with [
    push2 ⟨3725⟩, jumpiT hcond (by jump_dest), jumpdest]
  have rd3734₀ := evm_run rd3725 with [push1 ⟨51⟩, dup1]
  obtain ⟨_, _, rd3730₀⟩ := rd3734₀.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3730⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3730⟩
      (auctionSlotWord ⟨51⟩ σ I :: ⟨51⟩ :: ret :: R) mem aw rdata (accA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3730₀⟩
  have rd3737₀ := evm_run rd3730 with [push1 ⟨255⟩, not, and, push1 ⟨1⟩]
  have rd3737₁ := rd3737₀
  have hland : UInt256.land (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨51⟩ σ I) =
      UInt256.land (auctionSlotWord ⟨51⟩ σ I) (UInt256.lnot ⟨255⟩) := by
    exact u256_land_comm (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨51⟩ σ I)
  rw [hland] at rd3737₁
  have rd3737₂ := RD.lor rd3737₁ (by native_decide) (by evm_ov)
  have hlor :
      UInt256.lor ⟨1⟩
          (UInt256.land (auctionSlotWord ⟨51⟩ σ I) (UInt256.lnot ⟨255⟩)) =
        auctionPausedSetTrueWord (auctionSlotWord ⟨51⟩ σ I) := by
    unfold auctionPausedSetTrueWord
    exact u256_lor_comm ⟨1⟩
      (UInt256.land (auctionSlotWord ⟨51⟩ σ I) (UInt256.lnot ⟨255⟩))
  rw [hlor] at rd3737₂
  have rd3738 := evm_run rd3737₂ with [swap1]
  obtain ⟨_, _, rd3739₀⟩ := rd3738.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3739⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3739⟩ (ret :: R) mem aw rdata
      (accA, auctionPausePostMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionPausePostMap] using rd3739₀⟩
  have rd3772 := rd3739.pushConst auctionPausedTopic (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd2971 := evm_run rd3772 with [push2 ⟨2971⟩, caller, swap1, jump (by jump_dest)]
  let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd2988₀ := evm_run rd2971 with [
    jumpdest, push1 ⟨64⟩,
    raw mload (Cₘ aw64 - Cₘ aw) fmp aw64 (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw64])
      hmload64 (by rfl) (by simp only [List.length_cons]; omega),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2, and, dup2]
  have rd2988 := rd2988₀
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  rw [haddrMask] at rd2988
  have hcaller : UInt256.land (UInt256.ofNat I.source.val) solcAddrMask = auctionSourceWord I := by
    rw [u256_land_comm]
    simpa [auctionSourceWord] using solcAddrMask_clean_left (auctionSourceWord_canonical I)
  rw [hcaller] at rd2988
  let awEvent := UInt256.ofNat (MachineState.M aw64.toNat fmp.toNat 32)
  have rd2991 := evm_run rd2988 with [
    raw mstore (Cₘ awEvent - Cₘ aw64) (auctionEventMemFrom mem I fmp) awEvent
      (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awEvent])
      (by rfl) (by rfl) (by simp only [List.length_cons]; omega)]
  let aw64Event := UInt256.ofNat (MachineState.M awEvent.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd2998₀ := evm_run rd2991 with [
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload (Cₘ aw64Event - Cₘ awEvent) fmp aw64Event (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw64Event])
      (by simpa [aw64, awEvent] using hmload64Event) (by rfl)
      (by simp only [List.length_cons]; omega),
    dup1, swap2, sub, swap1]
  have rd2998 := rd2998₀
  rw [hlen32] at rd2998
  let awLog :=
    UInt256.ofNat
      (MachineState.M aw64Event.toNat fmp.toNat
        (⟨32⟩ : UInt256).toNat)
  have rd2999 := RD.log1 (Cₘ awLog - Cₘ aw64Event) awLog rd2998 (by decide) hperm
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awLog])
    (by rfl) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, _, _, evm_run rd2999 with [jump hret]⟩

end Auction
