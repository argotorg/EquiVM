import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolKeyPrefixActiveWords (aw free ptr : UInt256) : UInt256 :=
  let a0 := M aw (UInt256.ofNat 64) ⟨32⟩
  let a1 := M a0 (free+UInt256.ofNat 32) ⟨32⟩
  let a2 := M a1 (free+UInt256.ofNat 36) ⟨32⟩
  let a3 := M a2 ptr ⟨32⟩
  let a4 := M a3 (free+UInt256.ofNat 68) ⟨32⟩
  let a5 := M a4 (ptr+UInt256.ofNat 32) ⟨32⟩
  let a6 := M a5 ((free+UInt256.ofNat 68)+UInt256.ofNat 32) ⟨32⟩
  let a7 := M a6 (ptr+UInt256.ofNat 64) ⟨32⟩
  let a8 := M a7 ((free+UInt256.ofNat 68)+UInt256.ofNat 64) ⟨32⟩
  let a9 := M a8 (ptr+UInt256.ofNat 96) ⟨32⟩
  let a10 := M a9 ((free+UInt256.ofNat 68)+UInt256.ofNat 96) ⟨32⟩
  M a10 (ptr+UInt256.ofNat 128) ⟨32⟩

theorem poolKeyPrefixActiveWords_le {aw free ptr : UInt256}
    (haw : aw.toNat ≤ 2048) (hf : free.toNat ≤ 1024) (hp : ptr.toNat ≤ 1024) :
    (poolKeyPrefixActiveWords aw free ptr).toNat ≤ 2048 := by
  unfold poolKeyPrefixActiveWords
  repeat' apply memoryWords_le
  · exact haw
  all_goals
    simp only [uadd_toNat, UInt256.size,
      show (⟨32⟩ : UInt256).toNat = 32 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl,
      show (UInt256.ofNat 36).toNat = 36 from rfl,
      show (UInt256.ofNat 64).toNat = 64 from rfl,
      show (UInt256.ofNat 68).toNat = 68 from rfl,
      show (UInt256.ofNat 96).toNat = 96 from rfl,
      show (UInt256.ofNat 128).toNat = 128 from rfl] <;> omega

end Benchmarks.UniswapV4PoolManager
