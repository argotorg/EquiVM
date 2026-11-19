import Benchmarks.Midnight.MulticallEntry
import Benchmarks.Midnight.PackedWrites
import Benchmarks.Midnight.RuntimeBlocks_078

/-! A checked reference to the calldata array of fixed-size collateral records. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: a dynamic tuple offset passes the signed header-extent guard.
theorem collateralArrayOffsetCheck {bytes : ByteArray} {base relative : UInt256}
    (hs : bytes.size < 2^255)
    (hb : base.toNat + relative.toNat + 32 ≤ bytes.size) :
    UInt256.isZero (UInt256.slt relative
      (UInt256.sub (UInt256.ofNat bytes.size) base + UInt256.lnot (UInt256.ofNat 30))) = ⟨0⟩ := by
  have hs' : (UInt256.ofNat bytes.size).toNat = bytes.size :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hd : (UInt256.sub (UInt256.ofNat bytes.size) base).toNat = bytes.size - base.toNat := by
    rw [usub_toNat (by rw [hs']; omega), hs']
  have hn : (UInt256.sub (UInt256.ofNat bytes.size) base +
      UInt256.lnot (UInt256.ofNat 30)).toNat = bytes.size - base.toNat - 31 := by
    rw [wordAddLnot30, usub_toNat (by rw [hd]; change 31 ≤ _; omega), hd]
    rfl
  have he : UInt256.sub (UInt256.ofNat bytes.size) base + UInt256.lnot (UInt256.ofNat 30) =
      UInt256.ofNat (bytes.size - base.toNat - 31) := by
    apply u256_inj
    rw [hn, UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)]
  rw [he, slt_lit_one_low (by omega) (by omega)]
  rfl

-- LIBRARY CANDIDATE: bounded fixed-stride calldata arrays pass the signed end check.
theorem collateralArrayExtentCheck {bytes : ByteArray} {head count : UInt256}
    (hs : bytes.size < 2^255) (hn : count.toNat < 2^64)
    (hb : head.toNat + 32 + 128 * count.toNat ≤ bytes.size) :
    UInt256.sgt (UInt256.ofNat 32 + head)
      (UInt256.sub (UInt256.ofNat bytes.size) (UInt256.shiftLeft count ⟨7⟩)) = ⟨0⟩ := by
  have hshift : (UInt256.shiftLeft count ⟨7⟩).toNat = 128 * count.toNat := by
    rw [shiftLeft_toNat_of_noOverflow _ _ (by decide) (by
      change count.toNat * 128 < 2^256; omega)]
    change count.toNat * 128 = 128 * count.toNat
    omega
  have hs' : (UInt256.ofNat bytes.size).toNat = bytes.size :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hp : (UInt256.ofNat 32 + head).toNat = head.toNat + 32 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat _ 32 (by change _ < 2^256; omega)]
  have he : (UInt256.sub (UInt256.ofNat bytes.size) (UInt256.shiftLeft count ⟨7⟩)).toNat =
      bytes.size - 128 * count.toNat := by
    rw [usub_toNat (by rw [hs', hshift]; omega), hs', hshift]
  unfold UInt256.sgt UInt256.sgtBool
  rw [if_neg (by rw [hp]; omega), if_neg (by rw [he]; omega)]
  rw [decide_eq_false (by
    change ¬ (UInt256.sub (UInt256.ofNat bytes.size) (UInt256.shiftLeft count ⟨7⟩)).toNat <
      (UInt256.ofNat 32 + head).toNat
    rw [hp, he]; omega)]
  rfl

theorem midnightCollateralArrayReference {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw base field ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hs : I.calldata.size < 2^255)
    (hb : base.toNat < 2^128)
    (ho : (calldataWord I.calldata field.toNat).toNat < 2^64)
    (hn : (calldataWord I.calldata (base + calldataWord I.calldata field.toNat).toNat).toNat < 2^64)
    (he : (base + calldataWord I.calldata field.toNat).toNat + 32 + 128 *
      (calldataWord I.calldata (base + calldataWord I.calldata field.toNat).toNat).toNat ≤
        I.calldata.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨20488⟩ (base :: field :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ret
      (calldataWord I.calldata (base + calldataWord I.calldata field.toNat).toNat ::
        (UInt256.ofNat 32 + (base + calldataWord I.calldata field.toNat)) :: R)
      mem aw rdata σ k' C' := by
  have hp : (base + calldataWord I.calldata field.toNat).toNat =
      base.toNat + (calldataWord I.calldata field.toNat).toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
  have rd1 := midnightBlocks.midnight_block_20488_fallthrough
    (by simp only [List.length_cons]; omega)
    (collateralArrayOffsetCheck (base := base) (relative := calldataWord I.calldata field.toNat)
      hs (by rw [hp] at he; omega)) rd
  simp only [midnightBlocks.midnight_block_20488_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_20506_fallthrough
    (by simp only [List.length_cons]; omega)
    (ugt_zero (by
      change (calldataWord I.calldata
        (base + calldataWord I.calldata field.toNat).toNat).toNat ≤ 2^64 - 1
      omega)) rd1
  simp only [midnightBlocks.midnight_block_20506_fallthrough_stack] at rd2
  have rd3 := midnightBlocks.midnight_block_20524_fallthrough (by omega)
    (collateralArrayExtentCheck hs hn he) rd2
  have rd4 := midnightBlocks.midnight_block_20540
    (by simp only [midnightBlocks.midnight_block_20524_fallthrough_stack, List.length_cons]; omega)
    hret rd3
  exact ⟨_, _, by omega, rd4⟩

theorem midnightCalldataCollateralIndex {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr count index ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024) (hi : index.toNat < count.toNat)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨20541⟩ (ptr :: count :: index :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ret
      ((UInt256.shiftLeft index ⟨7⟩ + ptr) :: R) mem aw rdata σ k' C' := by
  have hc : UInt256.isZero (UInt256.lt index count) = ⟨0⟩ := by
    rw [ult_one hi]
    rfl
  have rd1 := midnightBlocks.midnight_block_20541_fallthrough
    (by simp only [List.length_cons]; omega) hc rd
  have rd2 := midnightBlocks.midnight_block_20551 (by omega) hret rd1
  exact ⟨_, _, by omega, rd2⟩

-- LIBRARY CANDIDATE: natural position of a bounded fixed-stride calldata element.
theorem calldataCollateralIndex_toNat {ptr index : UInt256}
    (hi : index.toNat < 2^64) (hp : ptr.toNat + 128 * index.toNat < UInt256.size) :
    (UInt256.shiftLeft index ⟨7⟩ + ptr).toNat = ptr.toNat + 128 * index.toNat := by
  have hh : (UInt256.shiftLeft index ⟨7⟩).toNat = 128 * index.toNat := by
    rw [shiftLeft_toNat_of_noOverflow _ _ (by decide) (by
      change index.toNat * 128 < UInt256.size; omega)]
    change index.toNat * 128 = 128 * index.toNat
    omega
  rw [uadd_toNat, hh, Nat.add_comm, Nat.mod_eq_of_lt hp]

end Benchmarks.Midnight
