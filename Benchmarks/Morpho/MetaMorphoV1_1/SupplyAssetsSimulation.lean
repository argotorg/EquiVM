import Benchmarks.Morpho.MetaMorphoV1_1.SupplyAssetsContinuation

/-! Expected supply assets in the accrued-fee loop, using the actual two reader calls. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem supplyAssetsSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params morpho ret a b c : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 31 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hmem : ptr.toNat ≤ mem.size) (hparamslo : 96 ≤ params.toNat)
    (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hbytes : mem.readWithPadding params.toNat 160 = p.bytes)
    (hloads : MarketParamsLoads mem params p) (hs : SourceState s0 I σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12483⟩
      ([params, ret, a, b, c, morpho] ++ R) mem aw rdata σ k C) :
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
        ([value, a, b, c, morpho] ++ R) mem' aw' out evm'.accountMap k' C' := by
  have hhash : keccakWord params (UInt256.ofNat 160) mem = p.id := by
    simp only [keccakWord, show (UInt256.ofNat 160).toNat = 160 from rfl, hbytes,
      MarketParamsData.id, uInt256OfByteArray_eq]
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12483_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_12483_stack, hhash] at h1
  apply supplyAssetsAfterHashSimulation v p
    (R := [a, b, c, morpho] ++ R)
    (T := [⟨12507⟩, params, ret, a, b, c, morpho] ++ R)
    (by change R.length + 4 + 27 ≤ 1024; omega)
    (by change R.length + 7 + 15 ≤ 1024; omega)
    hcalldata hfree hlo hmem hparamslo hparams hbytes hloads hs hret
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) ?_ h1
  intro shares mem' aw' out σ' k' C' hshares
  exact metaMorphoV1_1_block_12500_packed
    (immWords := wordsOf (immStore v)) (by simpa using (show R.length + 10 ≤ 1024 by omega))
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hshares

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
