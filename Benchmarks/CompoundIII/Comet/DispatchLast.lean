import Benchmarks.CompoundIII.Comet.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- Selectors tested by the EQ chain before the final SUB-based dispatcher branch. -/
def cometDispatchPrefixSelectors : List UInt256 :=
  [⟨70124239⟩,⟨151187884⟩,⟨197425873⟩,⟨204737060⟩,⟨404098525⟩,⟨412857073⟩,⟨480214969⟩,⟨525948093⟩,⟨599290589⟩,⟨614716962⟩,⟨641995544⟩,⟨709414674⟩,⟨731029629⟩,⟨755328779⟩,⟨772061415⟩,⟨806251499⟩,⟨826074471⟩,⟨840395849⟩,⟨927746484⟩,⟨950698303⟩,⟨993782830⟩,⟨1100443145⟩,⟨1110625635⟩,⟨1134440005⟩,⟨1153557995⟩,⟨1153654023⟩,⟨1157571613⟩,⟨1507858365⟩,⟨1519696081⟩,⟨1736444767⟩,⟨1889567281⟩,⟨2031398087⟩,⟨2059964113⟩,⟨2125926705⟩,⟨2152589087⟩,⟨2189815616⟩,⟨2371715404⟩,⟨2419208567⟩,⟨2453775713⟩,⟨2472862090⟩,⟨2492599498⟩,⟨2661915226⟩,⟨2678602586⟩,⟨2683660280⟩,⟨2707768185⟩,⟨2711744323⟩,⟨2758797371⟩,⟨2780102521⟩,⟨2835717307⟩,⟨2879910238⟩,⟨2903799676⟩,⟨3219561613⟩,⟨3253611544⟩,⟨3283311230⟩,⟨3285110738⟩,⟨3311251043⟩,⟨3321501135⟩,⟨3368549995⟩,⟨3454435393⟩,⟨3638949393⟩,⟨3646256541⟩,⟨3695885053⟩,⟨3815960634⟩,⟨3833100637⟩,⟨3840337785⟩,⟨3889878717⟩,⟨4072275384⟩]

theorem cometDispatchLastSelector {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hm : cometDispatchPrefixSelectors.all (fun w ↦ UInt256.eq w (solcSelectorWord I) == ⟨0⟩) = true) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨768⟩ [solcSelectorWord I]
      solcFreePtrMem (M ⟨0⟩ ⟨64⟩ ⟨32⟩) ByteArray.empty σ k C := by
  have hmiss (w : UInt256) (hw : w ∈ cometDispatchPrefixSelectors) :
      UInt256.eq w (solcSelectorWord I) = ⟨0⟩ := by
    simpa only [beq_iff_eq] using List.all_eq_true.mp hm w hw
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := cometWithExtendedAssetList_block_0_taken
    (immWords := wordsOf (immStore v))
    (by decide) (by rw [lt_four_eq_zero_of_ge hsz hsize]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd0
  have rd2 := cometWithExtendedAssetList_block_24_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨70124239⟩ (by decide)) rd1
  have rd3 := cometWithExtendedAssetList_block_42_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨151187884⟩ (by decide)) rd2
  have rd4 := cometWithExtendedAssetList_block_53_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨197425873⟩ (by decide)) rd3
  have rd5 := cometWithExtendedAssetList_block_64_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨204737060⟩ (by decide)) rd4
  have rd6 := cometWithExtendedAssetList_block_75_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨404098525⟩ (by decide)) rd5
  have rd7 := cometWithExtendedAssetList_block_86_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨412857073⟩ (by decide)) rd6
  have rd8 := cometWithExtendedAssetList_block_97_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨480214969⟩ (by decide)) rd7
  have rd9 := cometWithExtendedAssetList_block_108_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨525948093⟩ (by decide)) rd8
  have rd10 := cometWithExtendedAssetList_block_119_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨599290589⟩ (by decide)) rd9
  have rd11 := cometWithExtendedAssetList_block_130_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨614716962⟩ (by decide)) rd10
  have rd12 := cometWithExtendedAssetList_block_141_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨641995544⟩ (by decide)) rd11
  have rd13 := cometWithExtendedAssetList_block_152_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨709414674⟩ (by decide)) rd12
  have rd14 := cometWithExtendedAssetList_block_163_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨731029629⟩ (by decide)) rd13
  have rd15 := cometWithExtendedAssetList_block_174_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨755328779⟩ (by decide)) rd14
  have rd16 := cometWithExtendedAssetList_block_185_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨772061415⟩ (by decide)) rd15
  have rd17 := cometWithExtendedAssetList_block_196_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨806251499⟩ (by decide)) rd16
  have rd18 := cometWithExtendedAssetList_block_207_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨826074471⟩ (by decide)) rd17
  have rd19 := cometWithExtendedAssetList_block_218_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨840395849⟩ (by decide)) rd18
  have rd20 := cometWithExtendedAssetList_block_229_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨927746484⟩ (by decide)) rd19
  have rd21 := cometWithExtendedAssetList_block_240_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨950698303⟩ (by decide)) rd20
  have rd22 := cometWithExtendedAssetList_block_251_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨993782830⟩ (by decide)) rd21
  have rd23 := cometWithExtendedAssetList_block_262_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨1100443145⟩ (by decide)) rd22
  have rd24 := cometWithExtendedAssetList_block_273_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨1110625635⟩ (by decide)) rd23
  have rd25 := cometWithExtendedAssetList_block_284_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨1134440005⟩ (by decide)) rd24
  have rd26 := cometWithExtendedAssetList_block_295_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨1153557995⟩ (by decide)) rd25
  have rd27 := cometWithExtendedAssetList_block_306_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨1153654023⟩ (by decide)) rd26
  have rd28 := cometWithExtendedAssetList_block_317_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨1157571613⟩ (by decide)) rd27
  have rd29 := cometWithExtendedAssetList_block_328_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨1507858365⟩ (by decide)) rd28
  have rd30 := cometWithExtendedAssetList_block_339_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨1519696081⟩ (by decide)) rd29
  have rd31 := cometWithExtendedAssetList_block_350_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨1736444767⟩ (by decide)) rd30
  have rd32 := cometWithExtendedAssetList_block_361_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨1889567281⟩ (by decide)) rd31
  have rd33 := cometWithExtendedAssetList_block_372_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2031398087⟩ (by decide)) rd32
  have rd34 := cometWithExtendedAssetList_block_383_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2059964113⟩ (by decide)) rd33
  have rd35 := cometWithExtendedAssetList_block_394_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2125926705⟩ (by decide)) rd34
  have rd36 := cometWithExtendedAssetList_block_405_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2152589087⟩ (by decide)) rd35
  have rd37 := cometWithExtendedAssetList_block_416_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2189815616⟩ (by decide)) rd36
  have rd38 := cometWithExtendedAssetList_block_427_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2371715404⟩ (by decide)) rd37
  have rd39 := cometWithExtendedAssetList_block_438_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2419208567⟩ (by decide)) rd38
  have rd40 := cometWithExtendedAssetList_block_449_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2453775713⟩ (by decide)) rd39
  have rd41 := cometWithExtendedAssetList_block_460_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2472862090⟩ (by decide)) rd40
  have rd42 := cometWithExtendedAssetList_block_471_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2492599498⟩ (by decide)) rd41
  have rd43 := cometWithExtendedAssetList_block_482_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2661915226⟩ (by decide)) rd42
  have rd44 := cometWithExtendedAssetList_block_493_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2678602586⟩ (by decide)) rd43
  have rd45 := cometWithExtendedAssetList_block_504_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2683660280⟩ (by decide)) rd44
  have rd46 := cometWithExtendedAssetList_block_515_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2707768185⟩ (by decide)) rd45
  have rd47 := cometWithExtendedAssetList_block_526_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2711744323⟩ (by decide)) rd46
  have rd48 := cometWithExtendedAssetList_block_537_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2758797371⟩ (by decide)) rd47
  have rd49 := cometWithExtendedAssetList_block_548_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2780102521⟩ (by decide)) rd48
  have rd50 := cometWithExtendedAssetList_block_559_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2835717307⟩ (by decide)) rd49
  have rd51 := cometWithExtendedAssetList_block_570_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2879910238⟩ (by decide)) rd50
  have rd52 := cometWithExtendedAssetList_block_581_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨2903799676⟩ (by decide)) rd51
  have rd53 := cometWithExtendedAssetList_block_592_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨3219561613⟩ (by decide)) rd52
  have rd54 := cometWithExtendedAssetList_block_603_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨3253611544⟩ (by decide)) rd53
  have rd55 := cometWithExtendedAssetList_block_614_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨3283311230⟩ (by decide)) rd54
  have rd56 := cometWithExtendedAssetList_block_625_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨3285110738⟩ (by decide)) rd55
  have rd57 := cometWithExtendedAssetList_block_636_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨3311251043⟩ (by decide)) rd56
  have rd58 := cometWithExtendedAssetList_block_647_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨3321501135⟩ (by decide)) rd57
  have rd59 := cometWithExtendedAssetList_block_658_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨3368549995⟩ (by decide)) rd58
  have rd60 := cometWithExtendedAssetList_block_669_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨3454435393⟩ (by decide)) rd59
  have rd61 := cometWithExtendedAssetList_block_680_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨3638949393⟩ (by decide)) rd60
  have rd62 := cometWithExtendedAssetList_block_691_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨3646256541⟩ (by decide)) rd61
  have rd63 := cometWithExtendedAssetList_block_702_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨3695885053⟩ (by decide)) rd62
  have rd64 := cometWithExtendedAssetList_block_713_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨3815960634⟩ (by decide)) rd63
  have rd65 := cometWithExtendedAssetList_block_724_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨3833100637⟩ (by decide)) rd64
  have rd66 := cometWithExtendedAssetList_block_735_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨3840337785⟩ (by decide)) rd65
  have rd67 := cometWithExtendedAssetList_block_746_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨3889878717⟩ (by decide)) rd66
  have rd68 := cometWithExtendedAssetList_block_757_fallthrough
    (immWords := wordsOf (immStore v)) (by simp) (by simpa only [solcSelectorWord] using hmiss ⟨4072275384⟩ (by decide)) rd67
  exact ⟨_, _, rd68⟩

end Benchmarks.CompoundIII.Comet
