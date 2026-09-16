import Examples.UniswapV2Pair.ConstructorDomainHashRuntime
import Examples.UniswapV2Pair.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000

def constructorStoredAccountMap (σ : AccountMap) (I : ExecutionEnv) (domainHash : UInt256) :
    AccountMap :=
  let σD := sstoreAccountMap I.codeOwner σ ⟨3⟩ domainHash
  sstoreAccountMap I.codeOwner σD ⟨5⟩
    (setAddressOffset0Word (uniswapSlotWord ⟨5⟩ σD I) (uniswapSourceWord I))

set_option maxHeartbeats 1000000 in
theorem RD.uniswapConstructorStoreAndReturn {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {domainHash : UInt256} {mem : ByteArray} {R : List UInt256} {k C : Nat}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd225 : RD uniswapV2PairInitcode I g s0 ⟨225⟩ (domainHash :: ⟨128⟩ :: R)
      mem ⟨14⟩ ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) (hov : R.length + 8 ≤ 1024) :
    RDret uniswapV2PairInitcode g s0 (cA, constructorStoredAccountMap σ I domainHash)
      uniswapV2PairBytecode := by
  have rd227 := evm_run rd225 with [push1 ⟨3⟩]
  obtain ⟨_, _, rd228⟩ := rd227.sstore hperm (by native_decide) (by evm_ov)
  have rd232 := evm_run rd228 with [pop, push1 ⟨5⟩, dup1]
  obtain ⟨_, _, rd233⟩ := rd232.sload (by native_decide) (by evm_ov)
  have rd246 := evm_run rd233 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not, and,
    caller, or, swap1]
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  rw [hmask] at rd246
  have hstored : UInt256.lor (uniswapSourceWord I)
      (UInt256.land (UInt256.lnot solcAddrMask)
        (uniswapSlotWord ⟨5⟩ (sstoreAccountMap I.codeOwner σ ⟨3⟩ domainHash) I)) =
      setAddressOffset0Word (uniswapSlotWord ⟨5⟩ (sstoreAccountMap I.codeOwner σ ⟨3⟩ domainHash) I)
        (uniswapSourceWord I) := by
    rw [setAddressOffset0Word, solcAddrMask_clean (uniswapSourceWord_canonical I),
      u256_lor_comm, u256_land_comm]
  dsimp only [uniswapSourceWord, solcSourceWord, uniswapSlotWord] at hstored
  rw [hstored] at rd246
  obtain ⟨_, _, rd247⟩ := rd246.sstore hperm (by native_decide) (by evm_ov)
  have rd256 := evm_run rd247 with [push2 ⟨8833⟩, dup1, push2 ⟨261⟩, push1 ⟨0⟩]
  have rd257 := RD.codecopyAny rd256 (by native_decide) (by evm_ov)
  have rd259 := evm_run rd257 with [push1 ⟨0⟩]
  apply RD.ret 0 uniswapV2PairBytecode rd259 (by native_decide) ?_ ?_ (by evm_ov)
  · intro s haw hstk
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    native_decide
  · change (uniswapV2PairInitcode.write 261 mem 0 8833).readWithPadding 0 8833 = _
    rw [write0_read_back_from_gen _ _ _ _ (by decide) (by native_decide) (by decide)]
    native_decide

end UniswapV2Pair
