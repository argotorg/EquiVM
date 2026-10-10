import Benchmarks.Morpho.MetaMorphoV1_1.SetCapEnableRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyAssetsContinuation

/-! Reusing the supply-assets reader through the cap setter's return trampoline. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem setCapSupplyAssetsSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params previous cap id ret slot : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 34 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hmem : ptr.toNat ≤ mem.size) (hparamslo : 96 ≤ params.toNat)
    (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hbytes : mem.readWithPadding params.toNat 160 = p.bytes)
    (hloads : MarketParamsLoads mem params p) (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨14078⟩
      ([UInt256.ofNat v.MORPHO.val, p.id, UInt256.ofNat I.codeOwner.val, ⟨13739⟩,
        params, ⟨12507⟩, UInt256.ofNat v.MORPHO.val, ⟨12515⟩,
        previous, ⟨13745⟩, ⟨13750⟩, cap, id, ret, slot] ++ R) mem aw rdata σ k C) :
    (ExecFuncBody config (supplyAssetsFrame (immStore v) v.MORPHO I.codeOwner p ptr)
      evm allocatedSupplyAssetsFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (value cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      ExecFuncBody config (supplyAssetsFrame (immStore v) v.MORPHO I.codeOwner p ptr)
        evm allocatedSupplyAssetsFunction.body
        (.returned frame' evm' (some [uint256Value value, uint256Value cursor])) ∧
      memLoad ⟨64⟩ mem' = cursor ∧ 96 ≤ cursor.toNat ∧ cursor.toNat < 2 ^ 64 ∧
      cursor.toNat ≤ mem'.size ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12515⟩
        ([value, previous, ⟨13745⟩, ⟨13750⟩, cap, id, ret, slot] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  have haddr : AccountAddress.ofNat (UInt256.ofNat v.MORPHO.val).toNat = v.MORPHO := by
    rw [UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le v.MORPHO.isLt (by decide))]
    exact accountAddress_ofNat_toNat v.MORPHO
  have h := supplyAssetsAfterHashSimulation v p
    (ret := ⟨12515⟩) (sharesRet := ⟨13739⟩)
    (R := [previous, ⟨13745⟩, ⟨13750⟩, cap, id, ret, slot] ++ R)
    (T := [params, ⟨12507⟩, UInt256.ofNat v.MORPHO.val, ⟨12515⟩,
      previous, ⟨13745⟩, ⟨13750⟩, cap, id, ret, slot] ++ R)
    (by change R.length + 7 + 27 ≤ 1024; omega)
    (by change R.length + 11 + 15 ≤ 1024; omega)
    hcalldata hfree hlo hmem hparamslo hparams hbytes hloads hs
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest)
    (fun shares mem' aw' out σ' k' C' hshares ↦ by
      exact metaMorphoV1_1_block_13739_packed
        (immWords := wordsOf (immStore v))
        (by change R.length + 8 + 5 ≤ 1024; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hshares) rd
  simpa only [haddr] using h

end Benchmarks.Morpho.MetaMorphoV1_1
