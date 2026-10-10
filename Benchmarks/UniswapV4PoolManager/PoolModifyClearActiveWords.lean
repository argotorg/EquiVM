import Benchmarks.UniswapV4PoolManager.PoolModifyClearsTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem poolModifyClearActiveWords_eq_self {aw ptr : UInt256} (upper flipped : Bool)
    (h5 : 5 ≤ aw.toNat) (hfit : ptr.toNat+128 < UInt256.size)
    (hactive : ptr.toNat+128 ≤ aw.toNat*32) :
    poolModifyClearActiveWords aw ptr upper flipped = aw := by
  have h64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have hptr : M aw ptr ⟨32⟩ = aw := memoryWords_eq_self (by change ptr.toNat+32 ≤ _*32; omega)
  have hptr64 : M aw (ptr+UInt256.ofNat 64) ⟨32⟩ = aw :=
    memoryWords_eq_self (by change (ptr+UInt256.ofNat 64).toNat+32 ≤ _*32; rw [h64]; omega)
  cases upper <;> cases flipped <;>
    simp only [poolModifyClearActiveWords, Bool.false_eq_true, if_false, if_true,
      hptr, hptr64, tickClearActiveWords_eq_self h5]

theorem poolModifyClearsActiveWords_eq_self {aw ptr : UInt256} (delta : Int) (fl fu : Bool)
    (h5 : 5 ≤ aw.toNat) (hfit : ptr.toNat+128 < UInt256.size)
    (hactive : ptr.toNat+128 ≤ aw.toNat*32) :
    poolModifyClearsActiveWords aw ptr delta fl fu = aw := by
  simp only [poolModifyClearsActiveWords,
    poolModifyClearActiveWords_eq_self false fl h5 hfit hactive,
    poolModifyClearActiveWords_eq_self true fu h5 hfit hactive, ite_self]

end Benchmarks.UniswapV4PoolManager
