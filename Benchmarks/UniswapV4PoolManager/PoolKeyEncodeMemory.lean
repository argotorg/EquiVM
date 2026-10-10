import Benchmarks.UniswapV4PoolManager.PoolKeyView
import Benchmarks.UniswapV4PoolManager.WordCallMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- The compiler interleaves the struct reads and stores while building a hook payload.
def poolKeyPrefixMemory (mem : ByteArray) (free keyPtr selector sender : UInt256) : ByteArray :=
  let m0 := writeWord mem (free+UInt256.ofNat 32).toNat selector
  let m1 := writeWord m0 (free+UInt256.ofNat 36).toNat sender
  let m2 := writeWord m1 (free+UInt256.ofNat 68).toNat (UInt256.land (memLoad keyPtr m1) solcAddrMask)
  let m3 := writeWord m2 ((free+UInt256.ofNat 68)+UInt256.ofNat 32).toNat
    (UInt256.land (memLoad (keyPtr+UInt256.ofNat 32) m2) solcAddrMask)
  let m4 := writeWord m3 ((free+UInt256.ofNat 68)+UInt256.ofNat 64).toNat
    (UInt256.land (memLoad (keyPtr+UInt256.ofNat 64) m3) (UInt256.ofNat 16777215))
  writeWord m4 ((free+UInt256.ofNat 68)+UInt256.ofNat 96).toNat
    (UInt256.signextend (UInt256.ofNat 2) (memLoad (keyPtr+UInt256.ofNat 96) m4))

def poolKeyPrefixWords (sender : UInt256) (key : PoolKeyWords) : List UInt256 :=
  [sender, key.currency0, key.currency1, key.fee, key.tickSpacing]

theorem poolKeyPrefixMemory_eq {mem : ByteArray} {free keyPtr selector sender : UInt256} {key : PoolKeyWords}
    (hv : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+196 < UInt256.size) :
    poolKeyPrefixMemory mem free keyPtr selector sender =
      wordCallMemory mem (free.toNat+32) selector (poolKeyPrefixWords sender key) := by
  have h32 := uadd_word_ofNat_toNat free 32 (by omega : free.toNat+32 < UInt256.size)
  have h36 := uadd_word_ofNat_toNat free 36 (by omega : free.toNat+36 < UInt256.size)
  have h68 := uadd_word_ofNat_toNat free 68 (by omega : free.toNat+68 < UInt256.size)
  have h100 : ((free+UInt256.ofNat 68)+UInt256.ofNat 32).toNat = free.toNat+100 := by
    rw [uadd_word_ofNat_toNat _ 32 (by rw [h68]; omega), h68]
  have h132 : ((free+UInt256.ofNat 68)+UInt256.ofNat 64).toNat = free.toNat+132 := by
    rw [uadd_word_ofNat_toNat _ 64 (by rw [h68]; omega), h68]
  have h164 : ((free+UInt256.ofNat 68)+UInt256.ofNat 96).toNat = free.toNat+164 := by
    rw [uadd_word_ofNat_toNat _ 96 (by rw [h68]; omega), h68]
  let m1 := writeWord (writeWord mem (free+UInt256.ofNat 32).toNat selector)
    (free+UInt256.ofNat 36).toNat sender
  have hv1 : PoolKeyView m1 keyPtr key :=
    (hv.writeWord _ _ (.inl (by rw [h32]; omega))).writeWord _ _ (.inl (by rw [h36]; omega))
  have h0 : UInt256.land (memLoad keyPtr m1) solcAddrMask = key.currency0 := by
    rw [hv1.slice.word_load (i := 0) (word := key.currency0) rfl (by omega)]
    exact solcAddrMask_clean hc.1
  let m2 := writeWord m1 (free+UInt256.ofNat 68).toNat key.currency0
  have hv2 : PoolKeyView m2 keyPtr key := hv1.writeWord _ _ (.inl (by rw [h68]; omega))
  have h1 : UInt256.land (memLoad (keyPtr+UInt256.ofNat 32) m2) solcAddrMask = key.currency1 := by
    rw [hv2.load (i := 1) (word := key.currency1) rfl]
    exact solcAddrMask_clean hc.2.1
  let m3 := writeWord m2 ((free+UInt256.ofNat 68)+UInt256.ofNat 32).toNat key.currency1
  have hv3 : PoolKeyView m3 keyPtr key := hv2.writeWord _ _ (.inl (by rw [h100]; omega))
  have h2 : UInt256.land (memLoad (keyPtr+UInt256.ofNat 64) m3) (UInt256.ofNat 16777215) = key.fee := by
    rw [hv3.load (i := 2) (word := key.fee) rfl]
    exact u256LandMaskCleanOfToNat _ _ rfl hc.2.2.1
  let m4 := writeWord m3 ((free+UInt256.ofNat 68)+UInt256.ofNat 64).toNat key.fee
  have hv4 : PoolKeyView m4 keyPtr key := hv3.writeWord _ _ (.inl (by rw [h132]; omega))
  have h3 : UInt256.signextend (UInt256.ofNat 2) (memLoad (keyPtr+UInt256.ofNat 96) m4) = key.tickSpacing := by
    rw [hv4.load (i := 3) (word := key.tickSpacing) rfl]
    exact (signextend24_eq_iff _).mpr hc.2.2.2.1
  dsimp only [m1, m2, m3, m4] at h0 h1 h2 h3
  simp only [poolKeyPrefixMemory, h0, h1, h2, h3]
  simp only [h32, h36, h68, h100, h132, h164, wordCallMemory, poolKeyPrefixWords,
    wordSequenceMemory, Nat.add_assoc]

theorem poolKeyPrefixMemory_view {mem : ByteArray} {free keyPtr selector sender : UInt256} {key : PoolKeyWords}
    (hv : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+196 < UInt256.size) :
    PoolKeyView (poolKeyPrefixMemory mem free keyPtr selector sender) keyPtr key := by
  rw [poolKeyPrefixMemory_eq hv hc hb hf]
  refine ⟨(hv.slice.writeWord (free.toNat+32) selector (.inl ?_)).wordSequence
    (free.toNat+36) _ ?_, hv.fits⟩
  all_goals
    simp only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil]
    omega

theorem poolKeyPrefixMemory_hook {mem : ByteArray} {free keyPtr selector sender : UInt256} {key : PoolKeyWords}
    (hv : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+196 < UInt256.size) :
    UInt256.land (memLoad (keyPtr+UInt256.ofNat 128)
      (poolKeyPrefixMemory mem free keyPtr selector sender)) solcAddrMask = key.hooks := by
  rw [(poolKeyPrefixMemory_view hv hc hb hf).load (i := 4) (word := key.hooks) rfl]
  exact solcAddrMask_clean hc.2.2.2.2

end Benchmarks.UniswapV4PoolManager
