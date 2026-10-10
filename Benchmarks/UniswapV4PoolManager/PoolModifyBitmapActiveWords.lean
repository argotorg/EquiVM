import Benchmarks.UniswapV4PoolManager.PoolModifyBitmapsTrace
import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem tickBitmapActiveWords_eq_self {aw : UInt256} (ha : 2 ≤ aw.toNat) :
    tickBitmapActiveWords aw = aw := by
  have h0 : M aw ⟨0⟩ ⟨32⟩ = aw := memoryWords_eq_self (by change 0+32 ≤ _*32; omega)
  have h32 : M aw (UInt256.ofNat 32) ⟨32⟩ = aw := memoryWords_eq_self (by change 32+32 ≤ _*32; omega)
  have h64 : M aw ⟨0⟩ (UInt256.ofNat 64) = aw := memoryWords_eq_self (by change 0+64 ≤ _*32; omega)
  simp only [tickBitmapActiveWords, h0, h32, h64]

theorem poolModifyFlipEnterActiveWords_eq_self {aw params ptr : UInt256} (upper flipped : Bool)
    (h5 : 5 ≤ aw.toNat) (hf : ptr.toNat+128 < UInt256.size)
    (hc : ptr.toNat+128 ≤ aw.toNat*32)
    (hp : (params+UInt256.ofNat 128).toNat+32 ≤ aw.toNat*32) :
    poolModifyFlipEnterActiveWords aw params ptr upper flipped = aw := by
  have h64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have hptr : M aw ptr ⟨32⟩ = aw := memoryWords_eq_self (by change ptr.toNat+32 ≤ _*32; omega)
  have hptr64 : M aw (ptr+UInt256.ofNat 64) ⟨32⟩ = aw :=
    memoryWords_eq_self (by change (ptr+UInt256.ofNat 64).toNat+32 ≤ _*32; rw [h64]; omega)
  have hparams : M aw (params+UInt256.ofNat 128) ⟨32⟩ = aw := memoryWords_eq_self hp
  have h128 : M aw (UInt256.ofNat 128) ⟨32⟩ = aw := memoryWords_eq_self (by change 128+32 ≤ _*32; omega)
  cases upper <;> cases flipped <;>
    simp only [poolModifyFlipEnterActiveWords, Bool.false_eq_true, if_false, if_true,
      hptr, hptr64, hparams, h128]

theorem poolModifyFlipActiveWords_eq_self {aw params ptr : UInt256} (upper flipped : Bool)
    (h5 : 5 ≤ aw.toNat) (hf : ptr.toNat+128 < UInt256.size)
    (hc : ptr.toNat+128 ≤ aw.toNat*32)
    (hp : (params+UInt256.ofNat 128).toNat+32 ≤ aw.toNat*32) :
    poolModifyFlipActiveWords aw params ptr upper flipped = aw := by
  simp only [poolModifyFlipActiveWords,
    poolModifyFlipEnterActiveWords_eq_self upper flipped h5 hf hc hp,
    tickBitmapActiveWords_eq_self (by omega : 2 ≤ aw.toNat), ite_self]

theorem poolModifyBitmapsActiveWords_eq_self {aw params ptr : UInt256} (fl fu : Bool)
    (h5 : 5 ≤ aw.toNat) (hf : ptr.toNat+128 < UInt256.size)
    (hc : ptr.toNat+128 ≤ aw.toNat*32)
    (hp : (params+UInt256.ofNat 128).toNat+32 ≤ aw.toNat*32) :
    poolModifyBitmapsActiveWords aw params ptr fl fu = aw := by
  rw [poolModifyBitmapsActiveWords,
    poolModifyFlipActiveWords_eq_self false fl h5 hf hc hp,
    poolModifyFlipActiveWords_eq_self true fu h5 hf hc hp]

end Benchmarks.UniswapV4PoolManager
