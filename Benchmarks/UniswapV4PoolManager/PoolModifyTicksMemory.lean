import Benchmarks.UniswapV4PoolManager.PoolModifyTicksTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyTickOutput

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem poolModifyBitmapsMemory_size (mem : ByteArray) (id : UInt256) (p : PoolModifyParams) (fl fu : Bool)
    (hm : 64 ≤ mem.size) : (poolModifyBitmapsMemory mem id p fl fu).size = mem.size := by
  unfold poolModifyBitmapsMemory
  rw [poolModifyFlipMemory_size _ _ _ _ _ (by rw [poolModifyFlipMemory_size _ _ _ _ _ hm]; exact hm),
    poolModifyFlipMemory_size _ _ _ _ _ hm]

theorem poolModifyBitmapsMemory_loadWord (mem : ByteArray) (id : UInt256) (p : PoolModifyParams) (fl fu : Bool)
    (read : UInt256) (hlo : 64 ≤ read.toNat) (hin : read.toNat+32 ≤ mem.size) :
    memLoad read (poolModifyBitmapsMemory mem id p fl fu) = memLoad read mem := by
  unfold poolModifyBitmapsMemory
  rw [poolModifyFlipMemory_loadWord _ _ _ _ _ _ hlo
      (by rw [poolModifyFlipMemory_size _ _ _ _ _ (by omega)]; exact hin),
    poolModifyFlipMemory_loadWord _ _ _ _ _ _ hlo hin]

theorem poolModifyTwoTicksMemory_span (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State)
    (hf : ptr.toNat+128 < UInt256.size) : ptr.toNat+128 ≤ (poolModifyTwoTicksMemory mem ptr id p evm).size :=
  tickUpperResultMemory_span _ _ _ _ (by omega)

theorem poolModifyTicksMemory_size_ge (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State)
    (hm : 64 ≤ mem.size) : mem.size ≤ (poolModifyTicksMemory mem ptr id p evm).size := by
  have hs := poolModifyTwoTicksMemory_size_ge mem ptr id p evm hm
  unfold poolModifyTicksMemory poolModifyTicksActiveMemory
  split_ifs
  · rw [poolModifyBitmapsMemory_size _ _ _ _ _ (by omega)]
    exact hs
  · exact Nat.le_refl _

theorem poolModifyTicksMemory_load_before (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State)
    (read : UInt256) (hlo : 64 ≤ read.toNat) (hin : read.toNat+32 ≤ mem.size)
    (hbefore : read.toNat+32 ≤ ptr.toNat) (hfit : ptr.toNat+128 < UInt256.size) :
    memLoad read (poolModifyTicksMemory mem ptr id p evm) = memLoad read mem := by
  have hs := poolModifyTwoTicksMemory_size_ge mem ptr id p evm (by omega)
  unfold poolModifyTicksMemory poolModifyTicksActiveMemory
  split_ifs
  · rw [poolModifyBitmapsMemory_loadWord _ _ _ _ _ read hlo (by omega)]
    exact poolModifyTwoTicksMemory_loadWord mem ptr id p evm read hlo hin hbefore hfit
  · rfl

theorem poolModifyTicksMemory_lowerFlipped (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State)
    (hp : 64 ≤ ptr.toNat) (hf : ptr.toNat+128 < UInt256.size) (hz : memLoad ptr mem = ⟨0⟩) :
    memLoad ptr (poolModifyTicksMemory mem ptr id p evm) = UInt256.fromBool (poolModifyTicksFlipped evm id p false) := by
  by_cases hd : p.delta ≠ 0
  · rw [poolModifyTicksMemory, if_pos hd, poolModifyTicksActiveMemory,
      poolModifyBitmapsMemory_loadWord _ _ _ _ _ ptr hp (by have := poolModifyTwoTicksMemory_span mem ptr id p evm hf; omega),
      poolModifyTwoTicksMemory_lowerFlipped mem ptr id p evm hp hf]
    simp only [poolModifyTicksFlipped, if_pos hd, Bool.false_eq_true, if_false]
  · rw [poolModifyTicksMemory, if_neg hd, poolModifyTicksFlipped, if_neg hd]
    exact hz

theorem poolModifyTicksMemory_upperFlipped (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State)
    (hp : 64 ≤ ptr.toNat) (hf : ptr.toNat+128 < UInt256.size)
    (hz : memLoad (ptr+UInt256.ofNat 64) mem = ⟨0⟩) :
    memLoad (ptr+UInt256.ofNat 64) (poolModifyTicksMemory mem ptr id p evm) =
      UInt256.fromBool (poolModifyTicksFlipped evm id p true) := by
  have h64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  by_cases hd : p.delta ≠ 0
  · rw [poolModifyTicksMemory, if_pos hd, poolModifyTicksActiveMemory,
      poolModifyBitmapsMemory_loadWord _ _ _ _ _ (ptr+UInt256.ofNat 64) (by omega)
        (by have := poolModifyTwoTicksMemory_span mem ptr id p evm hf; omega),
      poolModifyTwoTicksMemory_upperFlipped mem ptr id p evm]
    simp only [poolModifyTicksFlipped, if_pos hd, if_true]
  · rw [poolModifyTicksMemory, if_neg hd, poolModifyTicksFlipped, if_neg hd]
    exact hz

end Benchmarks.UniswapV4PoolManager
