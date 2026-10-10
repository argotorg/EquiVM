import Benchmarks.UniswapV3.Pool.WordArrayUpdate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a Solidity memory array, including its length header.
def dynamicWordArrayWords (ws : List UInt256) : List UInt256 :=
  UInt256.ofNat ws.length :: ws

abbrev DynamicWordArrayMemory (mem : ByteArray) (p : UInt256) (ws : List UInt256) : Prop :=
  WordArrayMemory mem p (dynamicWordArrayWords ws)

def wordArrayElement (p : UInt256) (i : Nat) : UInt256 :=
  p + UInt256.ofNat (32 * (i + 1))

theorem wordArrayElement_toNat (p : UInt256) (i : Nat)
    (hb : p.toNat + 32 * (i + 1) < UInt256.size) :
    (wordArrayElement p i).toNat = p.toNat + 32 * (i + 1) :=
  uadd_word_ofNat_toNat p _ hb

theorem wordArrayElement_raw (p : UInt256) (i : Nat)
    (hb : p.toNat + 32 * (i + 1) < UInt256.size) :
    (UInt256.ofNat 32 + UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat i)) + p =
      wordArrayElement p i := by
  have hi : i < UInt256.size := by omega
  have hm : (UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat i)).toNat = 32 * i := by
    rw [u256_mul_toNat, ulit_toNat' i hi]
    change (32 * i) % UInt256.size = 32 * i
    exact Nat.mod_eq_of_lt (by omega)
  have hs : (UInt256.ofNat 32 + UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat i)).toNat =
      32 * (i + 1) := by
    rw [uadd_toNat, hm]
    change (32 + 32 * i) % UInt256.size = _
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  apply u256_inj
  rw [uadd_toNat, hs, wordArrayElement_toNat p i hb, Nat.mod_eq_of_lt (by omega)]
  omega

theorem DynamicWordArrayMemory.header {mem : ByteArray} {p : UInt256} {ws : List UInt256}
    (hm : DynamicWordArrayMemory mem p ws)
    (hb : p.toNat + 32 * (ws.length + 1) < UInt256.size) :
    memLoad p mem = UInt256.ofNat ws.length := by
  have h := hm.load 0 (by simp [dynamicWordArrayWords]) hb
  change memLoad (p + (⟨0⟩ : UInt256)) mem = UInt256.ofNat ws.length at h
  simpa only [u256_add_zero] using h

theorem DynamicWordArrayMemory.element {mem : ByteArray} {p : UInt256} {ws : List UInt256}
    (hm : DynamicWordArrayMemory mem p ws) (i : Nat) (hi : i < ws.length)
    (hb : p.toNat + 32 * (ws.length + 1) < UInt256.size) :
    memLoad (wordArrayElement p i) mem = ws[i] :=
  hm.load (i + 1) (by simp only [dynamicWordArrayWords, List.length_cons]; omega) hb

theorem DynamicWordArrayMemory.update {mem : ByteArray} {p : UInt256} {ws : List UInt256}
    (hm : DynamicWordArrayMemory mem p ws) (i : Nat) (value : UInt256) :
    DynamicWordArrayMemory (writeWord mem (p.toNat + 32 * (i + 1)) value) p
      (ws.set i value) := by
  simpa only [DynamicWordArrayMemory, dynamicWordArrayWords, List.length_set,
    List.set_cons_succ] using
    hm.write (i + 1) value

end Benchmarks.UniswapV3.Pool
