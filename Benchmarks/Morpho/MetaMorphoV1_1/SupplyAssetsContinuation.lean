import Benchmarks.Morpho.MetaMorphoV1_1.SupplyAssetsSource
import Benchmarks.Morpho.MetaMorphoV1_1.HeapWordWindow
import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.SharesToAssetsDownRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_062

/-! Shared supply-assets simulation after hashing the market parameters. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem supplyAssetsAfterHashSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params morpho ret sharesRet : UInt256} {R T : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 27 ≤ 1024)
    (hsharesStack : T.length + 15 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hmem : ptr.toNat ≤ mem.size) (hparamslo : 96 ≤ params.toNat)
    (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hbytes : mem.readWithPadding params.toNat 160 = p.bytes)
    (hloads : MarketParamsLoads mem params p) (hs : SourceState s0 I σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hsharesRet : (D_J (deployedRuntime v) 0).contains sharesRet = true)
    (hnext : ∀ (shares : UInt256) (mem' : ByteArray) (aw' : UInt256) (out : ByteArray)
      (σ' : AccountMap) (k' C' : Nat),
      RD (deployedRuntime v) I g s0 sharesRet (shares :: T) mem' aw' out σ' k' C' →
      ∃ aw'' k'' C'', RD (deployedRuntime v) I g s0 ⟨16911⟩
        ([morpho, params, ⟨12507⟩, shares, ret] ++ R) mem' aw'' out σ' k'' C'')
    (rd : RD (deployedRuntime v) I g s0 ⟨14078⟩
      ([morpho, p.id, UInt256.ofNat I.codeOwner.val, sharesRet] ++ T)
      mem aw rdata σ k C) :
    (ExecFuncBody config
      (supplyAssetsFrame (immStore v) (AccountAddress.ofNat morpho.toNat) I.codeOwner p ptr)
      evm allocatedSupplyAssetsFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (value cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      ExecFuncBody config
        (supplyAssetsFrame (immStore v) (AccountAddress.ofNat morpho.toNat) I.codeOwner p ptr)
        evm allocatedSupplyAssetsFunction.body
        (.returned frame' evm' (some [uint256Value value, uint256Value cursor])) ∧
      memLoad ⟨64⟩ mem' = cursor ∧ 96 ≤ cursor.toNat ∧ cursor.toNat < 2 ^ 64 ∧
      cursor.toNat ≤ mem'.size ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
        (value :: R) mem' aw' out evm'.accountMap k' C' := by
  let frame0 := supplyAssetsFrame (immStore v) (AccountAddress.ofNat morpho.toNat)
    I.codeOwner p ptr
  let frame1 := supplyAssetsIdFrame frame0 p
  have hid := supplyAssetsIdPrefix evm (immStore v) (AccountAddress.ofNat morpho.toNat)
    I.codeOwner p ptr
  have hargs1 := supplyAssetsSharesArgs evm (immStore v) (AccountAddress.ofNat morpho.toNat)
    I.codeOwner p ptr
  have huser : AccountAddress.ofNat (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner := by
    rw [UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le I.codeOwner.isLt (by decide))]
    exact accountAddress_ofNat_toNat I.codeOwner
  rcases supplySharesAllocationSimulation v (immStore v)
      hsharesStack hcalldata hfree hlo hsharesRet hs rd with
    ⟨hbad, hrev⟩ | ⟨evm1, final1, shares, ptr1, mem1, aw2, out1, k2, C2,
      hsource1, hs1, hstore1, hfree1, hlo1, hhi1, hmem1, hprefix1, hmono1, h2⟩
  · simp only [huser] at hbad
    refine .inl ⟨ExecFuncBody.execBlockRevert (hid.run ?_), hrev⟩
    rw [allocatedSupplyAssetsFunction_body]
    exact ExecBlock.consRevert (supplySharesReaderRevert hargs1 hbad)
  simp only [huser] at hsource1
  have hcall1 := supplySharesReaderCall (ret := slotsAndCursorName) hargs1 hsource1
  let frame2 := supplyAssetsSharesFrame frame1 shares ptr1
  have hargs2 := supplyAssetsBalancesArgs evm1 (immStore v) (AccountAddress.ofNat morpho.toNat)
    I.codeOwner p ptr shares ptr1
  have hsrcfit : params.toNat + 160 < UInt256.size :=
    lt_of_le_of_lt hparams ptr.val.isLt
  have hbytes1 : mem1.readWithPadding params.toNat 160 = p.bytes := by
    rw [memoryPrefix_read_words hprefix1 5 params.toNat hparamslo hparams (by omega)]
    exact hbytes
  have hloads1 : MarketParamsLoads mem1 params p :=
    hloads.prefix hprefix1 hparamslo (by omega) hparams hsrcfit
  obtain ⟨aw3, k3, C3, h3⟩ := hnext shares mem1 aw2 out1 evm1.accountMap k2 C2 h2
  rcases marketBalancesSimulation v p (by simp only [List.append, List.length_cons]; omega)
      hfree1 hlo1 hhi1 hmem1 hparamslo (by omega) hbytes1 hloads1 hs1
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3 with
    ⟨hbad, hrev⟩ | ⟨market, evm2, result, out2, hs2, hstore2, hsource2, aw4, k4, C4, h4⟩
  · refine .inl ⟨ExecFuncBody.execBlockRevert (hid.run ?_), hrev⟩
    rw [allocatedSupplyAssetsFunction_body]
    apply cursorCallPrefix (by decide) hcall1
    exact ExecBlock.consRevert (marketBalancesReaderRevert hargs2 hbad)
  have hcall2 := marketBalancesReaderCall (ret := slotsAndCursorName) hargs2 hsource2
  let frame3 := supplyAssetsBalancesFrame frame2
    (marketUpdatedBalancesValue market result.supplyAssets result.supplyShares result.borrowAssets)
    result.cursor
  have hcontract3 : frame3.contract = contract := rfl
  have hshares3 : frame3.locals.get? "supplyShares" = some (uint256Value shares) := by
    rw [show frame3 = cursorResultFrame frame2 "__c2" _ result.cursor from rfl,
      cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact cursorResultFrame_value _ _ _ _ (by decide)
  have hcursor3 : frame3.locals.get? cursorName = some (uint256Value result.cursor) :=
    cursorResultFrame_cursor _ _ _ _
  have hbalances3 : frame3.locals.get? "__c2" =
      some (marketUpdatedBalancesValue market result.supplyAssets result.supplyShares
        result.borrowAssets) := cursorResultFrame_value _ _ _ _ (by decide)
  obtain ⟨aw5, k5, C5, h5⟩ := metaMorphoV1_1_block_12507_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
  by_cases hfit : assetsDownFits shares result.supplyAssets result.supplyShares
  · obtain ⟨k6, C6, h6⟩ := assetsDownReturn v
      (by simp only [List.append]; omega) hfit hret h5
    refine .inr ⟨evm2,
      supplyAssetsReturnFrame frame3 shares result.supplyAssets result.supplyShares,
      _, result.cursor, result.memory, out2, hs2,
      accountStorageStateEq_trans hstore1 hstore2, ExecFuncBody.execBlockRet (hid.run ?_),
      result.free, result.lower, result.upper, result.size, aw5, k6, C6, h6⟩
    rw [allocatedSupplyAssetsFunction_body]
    apply cursorCallPrefix (by decide) hcall1
    apply cursorCallPrefix (by decide) hcall2
    exact supplyAssetsReturn hcontract3 hshares3 hcursor3 hbalances3 hfit
  · refine .inl ⟨ExecFuncBody.execBlockRevert (hid.run ?_),
      assetsDownRevert v (by simp only [List.append]; omega) hfit h5⟩
    rw [allocatedSupplyAssetsFunction_body]
    apply cursorCallPrefix (by decide) hcall1
    apply cursorCallPrefix (by decide) hcall2
    apply (supplyAssetsTotalsPrefix hbalances3).run
    exact ExecBlock.consRevert (supplyAssetsConversionReverts hcontract3 hshares3 hfit)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
