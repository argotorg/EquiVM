import Reasoning.WordArithmetic

/-!
# Storage word loops

Index, memory, and account-map facts for sequential storage clearing and copying.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace Reasoning.Theory

def clearDataWordsLoopIndex (idx : UInt256) : Nat → UInt256
  | 0 => idx
  | n + 1 => (⟨1⟩ : UInt256) + clearDataWordsLoopIndex idx n

theorem clearDataWordsLoopIndex_zero_ofNat :
    ∀ i, clearDataWordsLoopIndex ⟨0⟩ i = UInt256.ofNat i
  | 0 => rfl
  | i + 1 => by
      simp [clearDataWordsLoopIndex, clearDataWordsLoopIndex_zero_ofNat i,
        u256_one_add_ofNat]

theorem clearDataWordsLoopIndex_succ_base (idx : UInt256) :
    ∀ i, clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) i =
      (⟨1⟩ : UInt256) + clearDataWordsLoopIndex idx i
  | 0 => rfl
  | i + 1 => by
      simp [clearDataWordsLoopIndex, clearDataWordsLoopIndex_succ_base idx i]

def longDataWordsLoopIndex (idx : UInt256) : Nat → UInt256
  | 0 => idx
  | n + 1 => (⟨32⟩ : UInt256) + longDataWordsLoopIndex idx n

def longDataWordsLoopSlot (slot : UInt256) : Nat → UInt256
  | 0 => slot
  | n + 1 => (⟨1⟩ : UInt256) + longDataWordsLoopSlot slot n

def longDataWordsLoopStride (stride : UInt256) : Nat → UInt256
  | 0 => stride
  | n + 1 => (⟨32⟩ : UInt256) + longDataWordsLoopStride stride n

def longDataWordsLoopAw (aw ptr stride : UInt256) : Nat → UInt256
  | 0 => aw
  | n + 1 =>
      UInt256.ofNat
        (MachineState.M
          (longDataWordsLoopAw aw ptr stride n).toNat
          (ptr + longDataWordsLoopStride stride n).toNat 32)

def longDataWordsLoopWord (mem : ByteArray) (ptr stride : UInt256) (n : Nat) :
    UInt256 :=
  if (ptr + longDataWordsLoopStride stride n).toNat ≥ mem.size then
    ⟨0⟩
  else
    UInt256.ofNat (fromByteArrayBigEndian
      (mem.readWithPadding (ptr + longDataWordsLoopStride stride n).toNat 32))

def longDataWordsForwardFrom (owner : AccountAddress) (τ : AccountMap)
    (slot stride ptr aw : UInt256) (mem : ByteArray) : Nat → AccountMap
  | 0 => τ
  | n + 1 =>
      longDataWordsForwardFrom owner
        (sstoreAccountMap owner τ slot (longDataWordsLoopWord mem ptr stride 0))
        ((⟨1⟩ : UInt256) + slot) ((⟨32⟩ : UInt256) + stride) ptr
        (UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32)) mem n

theorem longDataWordsForwardFrom_absent_same {owner : AccountAddress} {τ : AccountMap}
    {slot stride ptr aw : UInt256} {mem : ByteArray} :
    ∀ fuel, τ.get? owner = none →
      longDataWordsForwardFrom owner τ slot stride ptr aw mem fuel = τ
  | 0, _hmissing => rfl
  | fuel + 1, hmissing => by
      simp [longDataWordsForwardFrom, sstoreAccountMap_absent_same hmissing]
      exact longDataWordsForwardFrom_absent_same (owner := owner) (τ := τ)
        (slot := (⟨1⟩ : UInt256) + slot) (stride := (⟨32⟩ : UInt256) + stride)
        (ptr := ptr) (aw := UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32))
        (mem := mem) fuel hmissing

theorem clearDataWordsLoopIndex_ofNat (i : Nat) :
    ∀ j, clearDataWordsLoopIndex (UInt256.ofNat i) j = UInt256.ofNat (i + j)
  | 0 => by simp [clearDataWordsLoopIndex]
  | j + 1 => by
      simp [clearDataWordsLoopIndex, clearDataWordsLoopIndex_ofNat i j,
        u256_one_add_ofNat]
      congr 1

theorem longDataWordsLoopIndex_zero_ofNat :
    ∀ i, longDataWordsLoopIndex ⟨0⟩ i = UInt256.ofNat (32 * i)
  | 0 => rfl
  | i + 1 => by
      simp [longDataWordsLoopIndex, longDataWordsLoopIndex_zero_ofNat i,
        u256_32_add_ofNat]
      congr 1

theorem longDataWordsLoopStride_32_ofNat :
    ∀ i, longDataWordsLoopStride ⟨32⟩ i = UInt256.ofNat (32 * (i + 1))
  | 0 => rfl
  | i + 1 => by
      simp [longDataWordsLoopStride, longDataWordsLoopStride_32_ofNat i,
        u256_32_add_ofNat]
      congr 1

theorem longDataWordsLoopIndex_succ_base (idx : UInt256) :
    ∀ i, longDataWordsLoopIndex ((⟨32⟩ : UInt256) + idx) i =
      (⟨32⟩ : UInt256) + longDataWordsLoopIndex idx i
  | 0 => rfl
  | i + 1 => by
      simp [longDataWordsLoopIndex, longDataWordsLoopIndex_succ_base idx i]

theorem longDataWordsLoopSlot_succ_base (slot : UInt256) :
    ∀ i, longDataWordsLoopSlot ((⟨1⟩ : UInt256) + slot) i =
      (⟨1⟩ : UInt256) + longDataWordsLoopSlot slot i
  | 0 => rfl
  | i + 1 => by
      simp [longDataWordsLoopSlot, longDataWordsLoopSlot_succ_base slot i]

theorem longDataWordsLoopStride_succ_base (stride : UInt256) :
    ∀ i, longDataWordsLoopStride ((⟨32⟩ : UInt256) + stride) i =
      (⟨32⟩ : UInt256) + longDataWordsLoopStride stride i
  | 0 => rfl
  | i + 1 => by
      simp [longDataWordsLoopStride, longDataWordsLoopStride_succ_base stride i]

theorem longDataWordsLoopAw_succ_base (aw ptr stride : UInt256) :
    ∀ i, longDataWordsLoopAw
        (UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32))
        ptr ((⟨32⟩ : UInt256) + stride) i =
      longDataWordsLoopAw aw ptr stride (i + 1)
  | 0 => rfl
  | i + 1 => by
      simp [longDataWordsLoopAw, longDataWordsLoopAw_succ_base aw ptr stride i,
        longDataWordsLoopStride, longDataWordsLoopStride_succ_base]

theorem longDataWordsLoopWord_succ_base (mem : ByteArray) (ptr stride : UInt256) :
    ∀ i, longDataWordsLoopWord mem
        ptr ((⟨32⟩ : UInt256) + stride) i =
      longDataWordsLoopWord mem ptr stride (i + 1)
  | 0 => by
      simp [longDataWordsLoopWord, longDataWordsLoopStride]
  | i + 1 => by
      simp [longDataWordsLoopWord,
        longDataWordsLoopStride, longDataWordsLoopStride_succ_base]

def longDataTailMaskedWord (word len : UInt256) : UInt256 :=
  UInt256.land word
    (UInt256.lnot
      (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
        (UInt256.mul ⟨8⟩ (UInt256.land len ⟨31⟩))))

theorem longDataTailMaskedWord_padded {len word : UInt256} {bytes : List UInt8}
    (hbytesLen : bytes.length = len.toNat % 32)
    (hword :
      word = UInt256.ofNat
        (fromBytesBigEndian (bytes ++ List.replicate (32 - bytes.length) 0))) :
    longDataTailMaskedWord word len = word := by
  let remWord := UInt256.land len ⟨31⟩
  have hremNat : remWord.toNat = bytes.length := by
    dsimp [remWord]
    rw [u256_land_31_toNat, hbytesLen]
  have hremLt : remWord.toNat < 32 := by
    rw [hremNat]
    rw [hbytesLen]
    exact Nat.mod_lt _ (by decide : 0 < 32)
  have hmask := shortPackedHeader_mask_of_short (len := remWord) hremLt
  have hwordZero :
      word.toNat % 2 ^ (256 - 8 * bytes.length) = 0 := by
    subst word
    have hbe :
        fromBytesBigEndian (bytes ++ List.replicate (32 - bytes.length) 0) =
          fromBytesBigEndian bytes * 2 ^ (8 * (32 - bytes.length)) := by
      exact fromBytesBigEndian_append_zeros bytes (32 - bytes.length)
    have hlt :
        fromBytesBigEndian (bytes ++ List.replicate (32 - bytes.length) 0) <
          UInt256.size := by
      unfold fromBytesBigEndian Function.comp
      have hbound := EVM.fromBytes'_le
        (bs := (bytes ++ List.replicate (32 - bytes.length) (0 : UInt8)).reverse)
      rw [List.length_reverse, List.length_append, List.length_replicate] at hbound
      have hlen32 : bytes.length + (32 - bytes.length) = 32 := by
        rw [hbytesLen]
        have hlt := Nat.mod_lt len.toNat (by decide : 0 < 32)
        omega
      simpa [hlen32, UInt256.size] using hbound
    rw [ulit_toNat' _ hlt, hbe]
    have hpowEq : 8 * (32 - bytes.length) = 256 - 8 * bytes.length := by
      have hle : bytes.length ≤ 32 := by
        rw [hbytesLen]
        exact Nat.le_of_lt (Nat.mod_lt _ (by decide : 0 < 32))
      omega
    rw [← hpowEq]
    rw [Nat.mul_comm]
    exact Nat.mul_mod_right (2 ^ (8 * (32 - bytes.length))) (fromBytesBigEndian bytes)
  unfold longDataTailMaskedWord
  rw [show UInt256.land len ⟨31⟩ = remWord from rfl]
  rw [hmask]
  rw [hremNat]
  exact u256_land_high_mask_eq_self word (by omega) hwordZero

section

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

theorem sstoreZero_clearDataWordsForwardFrom_comm
    (owner : AccountAddress) (σ : AccountMap) (base idx slot : UInt256) :
    ∀ fuel,
      sstoreAccountMap owner
          (clearDataWordsForwardFrom owner σ base idx fuel) slot ⟨0⟩ =
        clearDataWordsForwardFrom owner
          (sstoreAccountMap owner σ slot ⟨0⟩) base idx fuel
  | 0 => rfl
  | n + 1 => by
      simp [clearDataWordsForwardFrom]
      have ih := sstoreZero_clearDataWordsForwardFrom_comm
        owner (sstoreAccountMap owner σ (base + idx) ⟨0⟩)
        base ((⟨1⟩ : UInt256) + idx) slot n
      have hcomm₀ :
          sstoreAccountMap owner
              (sstoreAccountMap owner σ (base + idx) ⟨0⟩) slot ⟨0⟩ =
            sstoreAccountMap owner
              (sstoreAccountMap owner σ slot ⟨0⟩) (base + idx) ⟨0⟩ := by
        by_cases hne : slot ≠ base + idx
        · exact (sstoreAccountMap_comm σ owner slot ⟨0⟩ (base + idx) ⟨0⟩ hne).symm
        · have heq : slot = base + idx := by exact Classical.not_not.mp hne
          subst slot
          rfl
      have hcomm := congrArg
        (fun accounts => clearDataWordsForwardFrom owner accounts base
          ((⟨1⟩ : UInt256) + idx) n) hcomm₀
      exact Eq.trans ih hcomm

end

theorem clearDataWordsForwardFrom_split
    {owner : AccountAddress} {τ : AccountMap} {base idx : UInt256} :
    ∀ (pref tail : Nat),
      clearDataWordsForwardFrom owner τ base idx (pref + tail) =
        clearDataWordsForwardFrom owner
          (clearDataWordsForwardFrom owner τ base (clearDataWordsLoopIndex idx pref) tail)
          base idx pref
  | 0, tail => by
      simp [clearDataWordsForwardFrom, clearDataWordsLoopIndex]
  | pref + 1, tail => by
      have hfuel : pref + 1 + tail = pref + tail + 1 := by omega
      rw [hfuel]
      simp [clearDataWordsForwardFrom]
      have ih := clearDataWordsForwardFrom_split
        (owner := owner) (τ := sstoreAccountMap owner τ (base + idx) ⟨0⟩)
        (base := base) (idx := ((⟨1⟩ : UInt256) + idx)) pref tail
      have hcomm := sstoreZero_clearDataWordsForwardFrom_comm
        owner τ base (clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) pref)
        (base + idx) tail
      have htail := congrArg
        (fun accounts => clearDataWordsForwardFrom owner accounts base
          ((⟨1⟩ : UInt256) + idx) pref) hcomm.symm
      have hidxLoop :
          clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) pref =
            clearDataWordsLoopIndex idx (pref + 1) := by
        rw [clearDataWordsLoopIndex_succ_base]
        rfl
      exact Eq.trans ih (by simpa [hidxLoop] using htail)

theorem clearDataWordsForwardFrom_succ_last {base : UInt256}
    {owner : AccountAddress} {τ : AccountMap} :
    ∀ (i fuel : Nat),
      clearDataWordsForwardFrom owner τ base
          (UInt256.ofNat i) (fuel + 1) =
        sstoreAccountMap owner
          (clearDataWordsForwardFrom owner τ base
            (UInt256.ofNat i) fuel)
          (base + UInt256.ofNat (i + fuel)) ⟨0⟩
  | i, 0 => by
      simp [clearDataWordsForwardFrom]
  | i, fuel + 1 => by
      have ih := clearDataWordsForwardFrom_succ_last (base := base)
        (owner := owner)
        (τ := sstoreAccountMap owner τ (base + UInt256.ofNat i) ⟨0⟩)
        (i := i + 1) (fuel := fuel)
      simpa [clearDataWordsForwardFrom, u256_one_add_ofNat,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

theorem clearDataWordsForwardFrom_shift_ofNat {base : UInt256}
    {owner : AccountAddress} {σ : AccountMap} :
    ∀ (offset : Nat) (idx : UInt256) (fuel : Nat),
      offset + fuel < 2 ^ 251 →
      clearDataWordsForwardFrom owner σ
          (base + UInt256.ofNat offset) idx fuel =
        clearDataWordsForwardFrom owner σ
          base (UInt256.ofNat offset + idx) fuel
  | offset, idx, 0, _hbound => by
      simp [clearDataWordsForwardFrom]
  | offset, idx, fuel + 1, hbound => by
      simp [clearDataWordsForwardFrom]
      have hslot :
          (base + UInt256.ofNat offset) + idx =
            base + (UInt256.ofNat offset + idx) := by
        exact u256_add_assoc base (UInt256.ofNat offset) idx
      have htail := clearDataWordsForwardFrom_shift_ofNat (base := base)
        (owner := owner)
        (σ := sstoreAccountMap owner σ
          ((base + UInt256.ofNat offset) + idx) ⟨0⟩)
        offset ((⟨1⟩ : UInt256) + idx) fuel (by omega)
      have hidx :
          UInt256.ofNat offset + ((⟨1⟩ : UInt256) + idx) =
            (⟨1⟩ : UInt256) + (UInt256.ofNat offset + idx) := by
        rw [u256_add_comm (UInt256.ofNat offset) ((⟨1⟩ : UInt256) + idx)]
        rw [u256_add_assoc]
        rw [u256_add_comm idx (UInt256.ofNat offset)]
      simpa [hslot, hidx] using htail

theorem longDataWordsLoopSlot_ofNat {slot : UInt256} :
    ∀ i, longDataWordsLoopSlot slot i =
      slot + UInt256.ofNat i
  | 0 => by
      rw [longDataWordsLoopSlot]
      change slot = slot + (⟨0⟩ : UInt256)
      rw [uint256_add_zero_right]
  | i + 1 => by
      rw [longDataWordsLoopSlot, longDataWordsLoopSlot_ofNat i]
      rw [u256_add_comm (⟨1⟩ : UInt256) (slot + UInt256.ofNat i)]
      rw [u256_add_assoc]
      rw [u256_add_comm (UInt256.ofNat i) (⟨1⟩ : UInt256)]
      rw [u256_one_add_ofNat]

theorem longDataWordsLoopReadAddr_toNat {len : UInt256} {i : Nat}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hi : i < len.toNat / 32) :
    ((⟨128⟩ : UInt256) + longDataWordsLoopStride ⟨32⟩ i).toNat =
      160 + 32 * i := by
  rw [longDataWordsLoopStride_32_ofNat]
  rw [uadd_toNat]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
  have hstrideLt : 32 * (i + 1) < UInt256.size := by
    have hle : 32 * (i + 1) ≤ len.toNat := by
      have hlt : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
      have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) := Nat.mul_le_mul_left 32 hlt
      have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
      exact le_trans hmul hdiv
    exact lt_of_le_of_lt hle len.val.isLt
  rw [ulit_toNat' _ hstrideLt]
  have hsumLt : 128 + 32 * (i + 1) < UInt256.size := by
    have hle : 32 * (i + 1) ≤ len.toNat := by
      have hlt : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
      have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) := Nat.mul_le_mul_left 32 hlt
      have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
      exact le_trans hmul hdiv
    have hmax : 128 + ABI.solcMaxU64 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    omega
  rw [Nat.mod_eq_of_lt hsumLt]
  omega

theorem longDataLoopContinue (len : UInt256) {i : Nat}
    (hi : i < len.toNat / 32) :
    UInt256.isZero
      (UInt256.lt (longDataWordsLoopIndex ⟨0⟩ i)
        (UInt256.land len (UInt256.lnot ⟨31⟩))) = ⟨0⟩ := by
  have hidxLt : 32 * i < UInt256.size := by
    have hle : 32 * (len.toNat / 32) ≤ len.toNat := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
    have hlt : 32 * i < 32 * (len.toNat / 32) := by nlinarith
    exact lt_of_lt_of_le hlt (le_trans hle (Nat.le_of_lt len.val.isLt))
  have hidxNat : (longDataWordsLoopIndex ⟨0⟩ i).toNat = 32 * i := by
    rw [longDataWordsLoopIndex_zero_ofNat]
    exact ulit_toNat' _ hidxLt
  have hltWord :
      UInt256.lt (longDataWordsLoopIndex ⟨0⟩ i)
        (UInt256.land len (UInt256.lnot ⟨31⟩)) = ⟨1⟩ := by
    apply ult_one
    rw [hidxNat, longDataCutoff_toNat]
    nlinarith
  rw [hltWord]
  decide

theorem longDataLoopDone (len : UInt256) :
    UInt256.lt (longDataWordsLoopIndex ⟨0⟩ (len.toNat / 32))
      (UInt256.land len (UInt256.lnot ⟨31⟩)) = ⟨0⟩ := by
  have hidxLt : 32 * (len.toNat / 32) < UInt256.size := by
    have hle : 32 * (len.toNat / 32) ≤ len.toNat := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
    exact lt_of_le_of_lt hle len.val.isLt
  have hidxNat :
      (longDataWordsLoopIndex ⟨0⟩ (len.toNat / 32)).toNat =
        32 * (len.toNat / 32) := by
    rw [longDataWordsLoopIndex_zero_ofNat]
    exact ulit_toNat' _ hidxLt
  apply ult_zero
  rw [hidxNat, longDataCutoff_toNat]
  exact Nat.le_of_eq (Nat.mul_comm _ _)

section

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

/-- General append/split for the forward zeroing fold: running `fuel + tail` clears is running
    `tail` more clears from the advanced cursor after the first `fuel`. -/
theorem clearDataWordsForwardFrom_append_gen (owner : AccountAddress) (base : UInt256) :
    ∀ (fuel : Nat) (τ : AccountMap) (idx : UInt256) (tail : Nat),
      clearDataWordsForwardFrom owner τ base idx (fuel + tail) =
        clearDataWordsForwardFrom owner
          (clearDataWordsForwardFrom owner τ base idx fuel) base
          (UInt256.ofNat fuel + idx) tail
  | 0, τ, idx, tail => by
      simp only [Nat.zero_add, clearDataWordsForwardFrom]
      rw [show (UInt256.ofNat 0 + idx) = idx from by
        apply u256_inj; rw [uadd_toNat]
        simp only [show (UInt256.ofNat 0).toNat = 0 from rfl, Nat.zero_add]
        exact Nat.mod_eq_of_lt idx.val.isLt]
  | fuel + 1, τ, idx, tail => by
      have key : fuel + 1 + tail = (fuel + tail) + 1 := by omega
      rw [key, clearDataWordsForwardFrom,
        clearDataWordsForwardFrom_append_gen owner base fuel
          (sstoreAccountMap owner τ (base + idx) ⟨0⟩) ((⟨1⟩ : UInt256) + idx) tail]
      conv_rhs => rw [clearDataWordsForwardFrom]
      rw [show UInt256.ofNat (fuel + 1) + idx = UInt256.ofNat fuel + ((⟨1⟩ : UInt256) + idx) from by
        rw [← u256_one_add_ofNat, u256_add_comm (⟨1⟩ : UInt256) (UInt256.ofNat fuel), uadd_assoc]]

/-- Peel the final store off a `⟨0⟩`-based clear run: `n+1` clears equal `n` clears followed by a
    single `sstore` of `⟨0⟩` at `base + n`. -/
theorem clearDataWordsForwardFrom_append (owner : AccountAddress) (τ : AccountMap)
    (base : UInt256) (n : Nat) :
    clearDataWordsForwardFrom owner τ base ⟨0⟩ (n + 1) =
      sstoreAccountMap owner (clearDataWordsForwardFrom owner τ base ⟨0⟩ n)
        (base + UInt256.ofNat n) ⟨0⟩ := by
  rw [clearDataWordsForwardFrom_append_gen owner base n τ ⟨0⟩ 1]
  rw [show (UInt256.ofNat n + (⟨0⟩ : UInt256)) = UInt256.ofNat n from by
    apply u256_inj; rw [uadd_toNat]
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.add_zero]
    exact Nat.mod_eq_of_lt (UInt256.ofNat n).val.isLt]
  rw [clearDataWordsForwardFrom, clearDataWordsForwardFrom]

end

/-- The EVM stores the short word at `slot` **then** clears the keccak-data words; the Solm write
    clears **then** stores. Since the slots are disjoint, the resulting account maps are equal. -/
theorem clearDataWordsForwardFrom_sstore_comm (cO : AccountAddress) (K slot sw : UInt256) :
    ∀ (n : Nat) (σ : AccountMap), (∀ i, i < n → slot ≠ K + UInt256.ofNat i) →
      clearDataWordsForwardFrom cO (sstoreAccountMap cO σ slot sw) K ⟨0⟩ n =
        sstoreAccountMap cO (clearDataWordsForwardFrom cO σ K ⟨0⟩ n) slot sw
  | 0, σ, _ => rfl
  | n + 1, σ, hdisj => by
      rw [clearDataWordsForwardFrom_append cO (sstoreAccountMap cO σ slot sw) K n,
        clearDataWordsForwardFrom_append cO σ K n]
      rw [clearDataWordsForwardFrom_sstore_comm cO K slot sw n σ
        (fun i hi => hdisj i (by omega))]
      exact sstoreAccountMap_comm (clearDataWordsForwardFrom cO σ K ⟨0⟩ n)
        cO slot sw (K + UInt256.ofNat n) ⟨0⟩ (hdisj n (by omega))

end Reasoning.Theory

/-! ## Clearing prefixes and repeated stores -/

namespace Reasoning.Theory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

theorem sstoreZero_clearDataWordsForwardFrom_absorb_first
    {owner : AccountAddress} {τ : AccountMap} {base idx : UInt256} (fuel : Nat) :
    sstoreAccountMap owner
        (clearDataWordsForwardFrom owner τ base idx (fuel + 1)) (base + idx) ⟨0⟩ =
      clearDataWordsForwardFrom owner τ base idx (fuel + 1) := by
  simp [clearDataWordsForwardFrom]
  have hcomm := sstoreZero_clearDataWordsForwardFrom_comm
    owner (sstoreAccountMap owner τ (base + idx) ⟨0⟩)
    base ((⟨1⟩ : UInt256) + idx) (base + idx) fuel
  have hself := sstoreAccountMap_self_update
    τ owner (base + idx) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)
  have htailSelf := congrArg
    (fun accounts => clearDataWordsForwardFrom owner accounts base
      ((⟨1⟩ : UInt256) + idx) fuel) hself
  exact Eq.trans hcomm (Eq.symm htailSelf)

theorem clearDataWordsForwardFrom_double_prefix
    {owner : AccountAddress} {τ : AccountMap} {base idx : UInt256} :
    ∀ oldFuel newFuel : Nat, oldFuel ≤ newFuel →
      clearDataWordsForwardFrom owner
          (clearDataWordsForwardFrom owner τ base idx oldFuel) base idx newFuel =
        clearDataWordsForwardFrom owner τ base idx newFuel
  | 0, newFuel, _hle => by
      simp [clearDataWordsForwardFrom]
  | oldFuel + 1, 0, hle => by
      omega
  | oldFuel + 1, newFuel + 1, hle => by
      simp [clearDataWordsForwardFrom]
      have hcomm := sstoreZero_clearDataWordsForwardFrom_comm
        owner (sstoreAccountMap owner τ (base + idx) ⟨0⟩)
        base ((⟨1⟩ : UInt256) + idx) (base + idx) oldFuel
      have hself := sstoreAccountMap_self_update
        τ owner (base + idx) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)
      have htailSelf := congrArg
        (fun accounts => clearDataWordsForwardFrom owner accounts base
          ((⟨1⟩ : UInt256) + idx) oldFuel) hself
      have hbase := Eq.trans hcomm (Eq.symm htailSelf)
      have hcong := congrArg
        (fun accounts => clearDataWordsForwardFrom owner accounts base
          ((⟨1⟩ : UInt256) + idx) newFuel) hbase
      have htail := clearDataWordsForwardFrom_double_prefix
        (owner := owner) (τ := sstoreAccountMap owner τ (base + idx) ⟨0⟩)
        (base := base) (idx := ((⟨1⟩ : UInt256) + idx))
        oldFuel newFuel (by omega)
      exact Eq.trans hcong htail

end Reasoning.Theory
