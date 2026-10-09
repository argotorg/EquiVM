import Benchmarks.CompoundIII.Comet.DispatchLast

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- The final SUB-based selector comparison enters the withdrawal wrapper at pc 778. -/
theorem cometWithExtendedAssetListReachWithdrawBody {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) (hcode : I.code = deployedRuntime v)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 67)) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨778⟩ []
      solcFreePtrMem (M ⟨0⟩ ⟨64⟩ ⟨32⟩) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨4093572003⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xf3 0xfe 0xf3 0xa3 ⟨4093572003⟩ (by decide +kernel)
      (by simpa only [cometWithExtendedAssetListSelBytes] using hsel)
  obtain ⟨_, _, r1⟩ := cometDispatchLastSelector v hcode hsz hsize
    (by rw [hword]; native_decide)
  have r2 := cometWithExtendedAssetList_block_768_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by rw [hword]; exact u256_sub_self _) r1
  exact ⟨_, _, r2⟩

end Benchmarks.CompoundIII.Comet
