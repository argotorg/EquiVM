import Benchmarks.UniswapV4PoolManager.ReturnDataMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: the unchecked cursor used by Solidity's return-data bytes allocation.
def returnDataEnd (ptr : UInt256) (out : ByteArray) : UInt256 :=
  ptr+UInt256.land (UInt256.ofNat out.size+⟨63⟩) (UInt256.lnot ⟨31⟩)

theorem returnDataEnd_toNat (ptr : UInt256) (out : ByteArray)
    (hf : ptr.toNat+out.size+63 < UInt256.size) :
    (returnDataEnd ptr out).toNat = ptr.toNat+(out.size+63)/32*32 := by
  unfold returnDataEnd
  rw [uadd_toNat, solcReturnDataRounded_toNat out.size (by omega), Nat.mod_eq_of_lt (by omega)]

theorem returnDataEnd_bounds (ptr : UInt256) (out : ByteArray)
    (hf : ptr.toNat+out.size+63 < UInt256.size) :
    ptr.toNat+32+out.size ≤ (returnDataEnd ptr out).toNat ∧
      (returnDataEnd ptr out).toNat ≤ ptr.toNat+out.size+63 := by
  rw [returnDataEnd_toNat _ _ hf]
  omega

end Benchmarks.UniswapV4PoolManager
