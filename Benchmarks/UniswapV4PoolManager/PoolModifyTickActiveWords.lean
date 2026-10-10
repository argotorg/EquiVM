import Benchmarks.UniswapV4PoolManager.PoolModifyTwoTicksTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem tickLowerUpdateActiveWords_eq_self {aw ptr : UInt256}
    (h5 : 5 ≤ aw.toNat) (hf : ptr.toNat+128 < UInt256.size) (hc : ptr.toNat+128 ≤ aw.toNat*32) :
    tickLowerUpdateActiveWords aw ptr = aw := by
  have h32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have h128 : M aw (UInt256.ofNat 128) ⟨32⟩ = aw :=
    memoryWords_eq_self (by change 128+32 ≤ _*32; omega)
  have hs0 : M aw ⟨0⟩ ⟨32⟩ = aw := memoryWords_eq_self (by change 0+32 ≤ _*32; omega)
  have hs32 : M aw (UInt256.ofNat 32) ⟨32⟩ = aw := memoryWords_eq_self (by change 32+32 ≤ _*32; omega)
  have hs64 : M aw ⟨0⟩ (UInt256.ofNat 64) = aw := memoryWords_eq_self (by change 0+64 ≤ _*32; omega)
  have hp : M aw ptr ⟨32⟩ = aw := memoryWords_eq_self (by change ptr.toNat+32 ≤ _*32; omega)
  have hp32 : M aw (ptr+UInt256.ofNat 32) ⟨32⟩ = aw :=
    memoryWords_eq_self (by change (ptr+UInt256.ofNat 32).toNat+32 ≤ _*32; rw [h32]; omega)
  simp only [tickLowerUpdateActiveWords, h128, hp32, hp, hs0, hs32, hs64]

theorem tickUpperUpdateActiveWords_eq_self {aw ptr : UInt256} (packed : UInt256)
    (h5 : 5 ≤ aw.toNat) (hf : ptr.toNat+128 < UInt256.size) (hc : ptr.toNat+128 ≤ aw.toNat*32) :
    tickUpperUpdateActiveWords aw ptr packed = aw := by
  have h64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have h96 := uadd_word_ofNat_toNat ptr 96 (by omega)
  have h128 : M aw (UInt256.ofNat 128) ⟨32⟩ = aw :=
    memoryWords_eq_self (by change 128+32 ≤ _*32; omega)
  have hp64 : M aw (ptr+UInt256.ofNat 64) ⟨32⟩ = aw :=
    memoryWords_eq_self (by change (ptr+UInt256.ofNat 64).toNat+32 ≤ _*32; rw [h64]; omega)
  have hp96 : M aw (ptr+UInt256.ofNat 96) ⟨32⟩ = aw :=
    memoryWords_eq_self (by change (ptr+UInt256.ofNat 96).toNat+32 ≤ _*32; rw [h96]; omega)
  simp only [tickUpperUpdateActiveWords, h128, ite_self, hp96, hp64]

theorem poolModifyTwoTicksActiveWords_eq_self {aw ptr : UInt256} (id : UInt256)
    (p : PoolModifyParams) (evm : State) (h5 : 5 ≤ aw.toNat)
    (hf : ptr.toNat+128 < UInt256.size) (hc : ptr.toNat+128 ≤ aw.toNat*32) :
    poolModifyTwoTicksActiveWords aw ptr id p evm = aw := by
  rw [poolModifyTwoTicksActiveWords, tickLowerUpdateActiveWords_eq_self h5 hf hc,
    tickUpperUpdateActiveWords_eq_self _ h5 hf hc]

end Benchmarks.UniswapV4PoolManager
