import Benchmarks.Morpho.MetaMorphoV1_1.MaxWithdrawConversionSimulation

/-! The complete internal withdrawal limit, including accrued fees and available liquidity. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem maxWithdrawFinalReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {assets remaining total supply ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hfit : remaining.toNat ≤ assets.toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12234⟩
      ([assets, remaining, ⟨12410⟩, total, supply, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
      ([total, supply, UInt256.sub assets remaining] ++ R) mem aw' rdata σ k' C' := by
  obtain ⟨k1, C1, h1⟩ := checkedSubReturn v
    (by simp only [List.append, List.length_cons]; omega) hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  exact metaMorphoV1_1_block_12410_packed (immWords := wordsOf (immStore v))
    (by simp only [List.append]; omega) hret h1

theorem maxWithdrawFunctionSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner : AccountAddress} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 38 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hmem : 96 ≤ mem.size)
    (hs : SourceState s0 I σ evm) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨15882⟩
      (UInt256.ofNat owner.toNat :: ret :: R) mem aw rdata σ k C) :
    (ExecFuncBody config (maxWithdrawFrame (immStore v) owner ptr) evm
      allocatedMaxWithdrawFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (final : Frame) (assets supply total cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      memLoad ⟨64⟩ mem' = cursor ∧ 96 ≤ cursor.toNat ∧ 96 ≤ mem'.size ∧
      ExecFuncBody config (maxWithdrawFrame (immStore v) owner ptr) evm
        allocatedMaxWithdrawFunction.body
        (.returned final evm'
          [.tuple [uint256Value assets, uint256Value supply, uint256Value total],
            uint256Value cursor]) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
        ([total, supply, assets] ++ R) mem' aw' out evm'.accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15882_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  rcases accruedAssetsSimulation v
      (by simp only [List.length_cons]; omega) hcalldata hfree hlo hmem hs
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1 with
    ⟨hbad, hrev⟩ | ⟨evm1, final1, lost, total, shares, ptr1, mem1, out1,
      hs1, hstore1, hfree1, hlo1, hmem1, hsource1, aw2, k2, C2, h2⟩
  · exact .inl ⟨maxWithdrawAccrualReverts v hbad, hrev⟩
  rcases maxWithdrawConversionSimulation v (by simp only [List.length_cons]; omega)
      (maxWithdrawAccruedLocals v owner ptr lost total shares ptr1
        (codeOwnerStorageWord I evm1.accountMap ⟨2⟩)) hs1 h2 with
    ⟨hbad, hrev⟩ | ⟨locals2, assets2, hl2, hprefix2, aw3, k3, C3, h3⟩
  · exact .inl ⟨ExecFuncBody.execBlockRevert
      (maxWithdrawAccrualPrefix v hsource1 (hs1.storageRead ⟨2⟩) hbad), hrev⟩
  rcases simulateWithdrawFunctionSimulation v
      (by simp only [List.append, List.length_cons]; omega)
      hcalldata ((maxWithdrawBalanceMemory_free owner hmem1).trans hfree1) hlo1
      (by rw [maxWithdrawBalanceMemory_size owner hmem1]; exact hmem1) hs1 h3 with
    ⟨hbad, hrev⟩ | ⟨evm2, final2, remaining, cursor, mem2, out2, hs2, hstore2,
      hsource2, hfree2, hlo2, hmem2, aw4, k4, C4, h4⟩
  · exact .inl ⟨ExecFuncBody.execBlockRevert
      (maxWithdrawAccrualPrefix v hsource1 (hs1.storageRead ⟨2⟩)
        (hprefix2 _ (maxWithdrawSimulateReverts v hl2 hbad))), hrev⟩
  have hl3 := hl2.reader (remaining := remaining) (cursor := cursor)
  have hr := cursorResultFrame_value ⟨contract, locals2, immStore v⟩ "__c4"
    (uint256Value remaining) cursor (by decide)
  by_cases hfit : remaining.toNat ≤ assets2.toNat
  · exact .inr ⟨evm2, _, UInt256.sub assets2 remaining, _, total, cursor, mem2, out2,
      hs2, accountStorageStateEq_trans hstore1 hstore2, hfree2, hlo2, hmem2,
      ExecFuncBody.execBlockRet
        (maxWithdrawAccrualPrefix v hsource1 (hs1.storageRead ⟨2⟩)
          (hprefix2 _ (maxWithdrawSimulatePrefix v hl2 hsource2
            (maxWithdrawReturnSource hl3 hr hfit)))),
      maxWithdrawFinalReturn v (by omega) hfit hret h4⟩
  · exact .inl ⟨ExecFuncBody.execBlockRevert
      (maxWithdrawAccrualPrefix v hsource1 (hs1.storageRead ⟨2⟩)
        (hprefix2 _ (maxWithdrawSimulatePrefix v hl2 hsource2
          (maxWithdrawReturnReverts hl3 hr (Nat.lt_of_not_ge hfit))))),
      checkedSubRevert v (by simp only [List.append, List.length_cons]; omega)
        (Nat.lt_of_not_ge hfit) h4⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
