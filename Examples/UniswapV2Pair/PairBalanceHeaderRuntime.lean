import Examples.UniswapV2Pair.PairBalanceCallRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev PairBalanceCallSite.headerPc : PairBalanceCallSite → UInt256
  | .burn0 => ⟨4640⟩
  | .burn1 => ⟨4754⟩
  | .swap0 => ⟨2092⟩
  | .swap1 => ⟨2206⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPairBalanceHeaderStored
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {site : PairBalanceCallSite}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw ptr : UInt256} {R : List UInt256} {k C : Nat}
    (rd : RD uniswapV2PairBytecode I g s0 site.headerPc R mem aw rdata acc k C)
    (hin : 96 ≤ mem.size) (hgap : ptr.toNat - mem.size < USize.size) (hlo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hawLo : 96 ≤ aw.toNat * 32)
    (hfit : ptr.toNat + 67 < UInt256.size) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 (site.headerPc + ⟨22⟩) (ptr :: ptr :: R)
      (balanceDynamicCalldataMem mem ptr (UInt256.ofNat I.codeOwner.val))
      (balanceDynamicCalldataWords aw ptr) rdata acc k' C' := by
  have h64c : (⟨64⟩ : UInt256).toNat + 32 ≤ aw.toNat * 32 := hawLo
  have hload : memoryWordLoad mem aw ⟨64⟩ = ptr :=
    mloadWordValue_of_readWithPadding (by change 64 < mem.size; omega)
      (UInt256_mload_haw_of_cover aw ⟨64⟩ haw h64c) hread
  have haw64 : memoryWordActiveWords aw ⟨64⟩ = aw := UInt256_M_same_of_cover aw ⟨64⟩ haw h64c
  obtain ⟨hm64, hw64⟩ := balanceDynamicCalldataMem_mload64 aw ptr (UInt256.ofNat I.codeOwner.val)
    hin hlo hgap hfit haw hread
  cases site
  all_goals
    have rd3 := evm_run rd with [push1 ⟨64⟩, dup1]
    have rd4 := RD.mloadWord rd3 (by native_decide) hload (by simp only [List.length_cons]; omega)
    rw [haw64] at rd4
    have rd13 := evm_run rd4 with [push4 balanceOfSelectorWord, push1 ⟨224⟩, shl, dup2]
    have rd14 := RD.mstoreWord rd13 (by native_decide) (by simp only [List.length_cons]; omega)
    have rd19 := evm_run rd14 with [address, push1 ⟨4⟩, dup3, add]
    have rd20 := RD.mstoreWord rd19 (by native_decide) (by simp only [List.length_cons]; omega)
    have rd21 := evm_run rd20 with [swap1]
    have rd22 := RD.mloadWord rd21 (by native_decide) hm64 (by simp only [List.length_cons]; omega)
    rw [hw64] at rd22
    exact ⟨_, _, rd22⟩

end UniswapV2Pair
