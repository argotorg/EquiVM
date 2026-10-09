import Benchmarks.CompoundIII.Comet.Common
import Reasoning.ABIViews
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_001
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_002
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_003
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_004
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_005
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_006
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_007

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometFallbackDispatchLong {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 68 → (cometWithExtendedAssetListSelBytes i == I.calldata.extract 0 4) = false) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨14⟩ []
      solcFreePtrMem (M ⟨0⟩ ⟨64⟩ ⟨32⟩) ByteArray.empty σ k C := by
  have r0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have r1 := cometWithExtendedAssetList_block_0_taken (immWords := wordsOf (immStore v))
    (by decide) (by rw [lt_four_eq_zero_of_ge hsz hsize]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r0
  have hn0 : solcSelectorWord I ≠ UInt256.ofNat 70124239 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x04) (c1 := 0x2e) (c2 := 0x02) (c3 := 0xcf) (by decide +kernel)
      (hnm 0 (by decide))
  have r2 := cometWithExtendedAssetList_block_24_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn0.symm) r1
  have hn1 : solcSelectorWord I ≠ UInt256.ofNat 151187884 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x09) (c1 := 0x02) (c2 := 0xf1) (c3 := 0xac) (by decide +kernel)
      (hnm 1 (by decide))
  have r3 := cometWithExtendedAssetList_block_42_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn1.symm) r2
  have hn2 : solcSelectorWord I ≠ UInt256.ofNat 197425873 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x0b) (c1 := 0xc4) (c2 := 0x7a) (c3 := 0xd1) (by decide +kernel)
      (hnm 2 (by decide))
  have r4 := cometWithExtendedAssetList_block_53_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn2.symm) r3
  have hn3 : solcSelectorWord I ≠ UInt256.ofNat 204737060 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x0c) (c1 := 0x34) (c2 := 0x0a) (c3 := 0x24) (by decide +kernel)
      (hnm 3 (by decide))
  have r5 := cometWithExtendedAssetList_block_64_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn3.symm) r4
  have hn4 : solcSelectorWord I ≠ UInt256.ofNat 404098525 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x18) (c1 := 0x16) (c2 := 0x0d) (c3 := 0xdd) (by decide +kernel)
      (hnm 4 (by decide))
  have r6 := cometWithExtendedAssetList_block_75_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn4.symm) r5
  have hn5 : solcSelectorWord I ≠ UInt256.ofNat 412857073 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x18) (c1 := 0x9b) (c2 := 0xb2) (c3 := 0xf1) (by decide +kernel)
      (hnm 5 (by decide))
  have r7 := cometWithExtendedAssetList_block_86_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn5.symm) r6
  have hn6 : solcSelectorWord I ≠ UInt256.ofNat 480214969 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x1c) (c1 := 0x9f) (c2 := 0x7f) (c3 := 0xb9) (by decide +kernel)
      (hnm 6 (by decide))
  have r8 := cometWithExtendedAssetList_block_97_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn6.symm) r7
  have hn7 : solcSelectorWord I ≠ UInt256.ofNat 525948093 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x1f) (c1 := 0x59) (c2 := 0x54) (c3 := 0xbd) (by decide +kernel)
      (hnm 7 (by decide))
  have r9 := cometWithExtendedAssetList_block_108_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn7.symm) r8
  have hn8 : solcSelectorWord I ≠ UInt256.ofNat 599290589 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x23) (c1 := 0xb8) (c2 := 0x72) (c3 := 0xdd) (by decide +kernel)
      (hnm 8 (by decide))
  have r10 := cometWithExtendedAssetList_block_119_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn8.symm) r9
  have hn9 : solcSelectorWord I ≠ UInt256.ofNat 614716962 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x24) (c1 := 0xa3) (c2 := 0xd6) (c3 := 0x22) (by decide +kernel)
      (hnm 9 (by decide))
  have r11 := cometWithExtendedAssetList_block_130_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn9.symm) r10
  have hn10 : solcSelectorWord I ≠ UInt256.ofNat 641995544 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x26) (c1 := 0x44) (c2 := 0x13) (c3 := 0x18) (by decide +kernel)
      (hnm 10 (by decide))
  have r12 := cometWithExtendedAssetList_block_141_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn10.symm) r11
  have hn11 : solcSelectorWord I ≠ UInt256.ofNat 709414674 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x2a) (c1 := 0x48) (c2 := 0xcf) (c3 := 0x12) (by decide +kernel)
      (hnm 11 (by decide))
  have r13 := cometWithExtendedAssetList_block_152_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn11.symm) r12
  have hn12 : solcSelectorWord I ≠ UInt256.ofNat 731029629 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x2b) (c1 := 0x92) (c2 := 0xa0) (c3 := 0x7d) (by decide +kernel)
      (hnm 12 (by decide))
  have r14 := cometWithExtendedAssetList_block_163_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn12.symm) r13
  have hn13 : solcSelectorWord I ≠ UInt256.ofNat 755328779 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x2d) (c1 := 0x05) (c2 := 0x67) (c3 := 0x0b) (by decide +kernel)
      (hnm 13 (by decide))
  have r15 := cometWithExtendedAssetList_block_174_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn13.symm) r14
  have hn14 : solcSelectorWord I ≠ UInt256.ofNat 772061415 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x2e) (c1 := 0x04) (c2 := 0xb8) (c3 := 0xe7) (by decide +kernel)
      (hnm 14 (by decide))
  have r16 := cometWithExtendedAssetList_block_185_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn14.symm) r15
  have hn15 : solcSelectorWord I ≠ UInt256.ofNat 806251499 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x30) (c1 := 0x0e) (c2 := 0x6b) (c3 := 0xeb) (by decide +kernel)
      (hnm 15 (by decide))
  have r17 := cometWithExtendedAssetList_block_196_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn15.symm) r16
  have hn16 : solcSelectorWord I ≠ UInt256.ofNat 826074471 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x31) (c1 := 0x3c) (c2 := 0xe5) (c3 := 0x67) (by decide +kernel)
      (hnm 16 (by decide))
  have r18 := cometWithExtendedAssetList_block_207_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn16.symm) r17
  have hn17 : solcSelectorWord I ≠ UInt256.ofNat 840395849 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x32) (c1 := 0x17) (c2 := 0x6c) (c3 := 0x49) (by decide +kernel)
      (hnm 17 (by decide))
  have r19 := cometWithExtendedAssetList_block_218_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn17.symm) r18
  have hn18 : solcSelectorWord I ≠ UInt256.ofNat 927746484 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x37) (c1 := 0x4c) (c2 := 0x49) (c3 := 0xb4) (by decide +kernel)
      (hnm 18 (by decide))
  have r20 := cometWithExtendedAssetList_block_229_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn18.symm) r19
  have hn19 : solcSelectorWord I ≠ UInt256.ofNat 950698303 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x38) (c1 := 0xaa) (c2 := 0x81) (c3 := 0x3f) (by decide +kernel)
      (hnm 19 (by decide))
  have r21 := cometWithExtendedAssetList_block_240_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn19.symm) r20
  have hn20 : solcSelectorWord I ≠ UInt256.ofNat 993782830 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x3b) (c1 := 0x3b) (c2 := 0xec) (c3 := 0x2e) (by decide +kernel)
      (hnm 20 (by decide))
  have r22 := cometWithExtendedAssetList_block_251_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn20.symm) r21
  have hn21 : solcSelectorWord I ≠ UInt256.ofNat 1100443145 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x41) (c1 := 0x97) (c2 := 0x6e) (c3 := 0x09) (by decide +kernel)
      (hnm 21 (by decide))
  have r23 := cometWithExtendedAssetList_block_262_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn21.symm) r22
  have hn22 : solcSelectorWord I ≠ UInt256.ofNat 1110625635 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x42) (c1 := 0x32) (c2 := 0xcd) (c3 := 0x63) (by decide +kernel)
      (hnm 22 (by decide))
  have r24 := cometWithExtendedAssetList_block_273_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn22.symm) r23
  have hn23 : solcSelectorWord I ≠ UInt256.ofNat 1134440005 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x43) (c1 := 0x9e) (c2 := 0x2e) (c3 := 0x45) (by decide +kernel)
      (hnm 23 (by decide))
  have r25 := cometWithExtendedAssetList_block_284_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn23.symm) r24
  have hn24 : solcSelectorWord I ≠ UInt256.ofNat 1153557995 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x44) (c1 := 0xc1) (c2 := 0xe5) (c3 := 0xeb) (by decide +kernel)
      (hnm 24 (by decide))
  have r26 := cometWithExtendedAssetList_block_295_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn24.symm) r25
  have hn25 : solcSelectorWord I ≠ UInt256.ofNat 1153654023 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x44) (c1 := 0xc3) (c2 := 0x5d) (c3 := 0x07) (by decide +kernel)
      (hnm 25 (by decide))
  have r27 := cometWithExtendedAssetList_block_306_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn25.symm) r26
  have hn26 : solcSelectorWord I ≠ UInt256.ofNat 1157571613 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x44) (c1 := 0xff) (c2 := 0x24) (c3 := 0x1d) (by decide +kernel)
      (hnm 26 (by decide))
  have r28 := cometWithExtendedAssetList_block_317_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn26.symm) r27
  have hn27 : solcSelectorWord I ≠ UInt256.ofNat 1507858365 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x59) (c1 := 0xe0) (c2 := 0x17) (c3 := 0xbd) (by decide +kernel)
      (hnm 27 (by decide))
  have r29 := cometWithExtendedAssetList_block_328_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn27.symm) r28
  have hn28 : solcSelectorWord I ≠ UInt256.ofNat 1519696081 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x5a) (c1 := 0x94) (c2 := 0xb8) (c3 := 0xd1) (by decide +kernel)
      (hnm 28 (by decide))
  have r30 := cometWithExtendedAssetList_block_339_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn28.symm) r29
  have hn29 : solcSelectorWord I ≠ UInt256.ofNat 1736444767 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x67) (c1 := 0x80) (c2 := 0x0b) (c3 := 0x5f) (by decide +kernel)
      (hnm 29 (by decide))
  have r31 := cometWithExtendedAssetList_block_350_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn29.symm) r30
  have hn30 : solcSelectorWord I ≠ UInt256.ofNat 1889567281 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x70) (c1 := 0xa0) (c2 := 0x82) (c3 := 0x31) (by decide +kernel)
      (hnm 30 (by decide))
  have r32 := cometWithExtendedAssetList_block_361_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn30.symm) r31
  have hn31 : solcSelectorWord I ≠ UInt256.ofNat 2031398087 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x79) (c1 := 0x14) (c2 := 0xac) (c3 := 0xc7) (by decide +kernel)
      (hnm 31 (by decide))
  have r33 := cometWithExtendedAssetList_block_372_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn31.symm) r32
  have hn32 : solcSelectorWord I ≠ UInt256.ofNat 2059964113 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x7a) (c1 := 0xc8) (c2 := 0x8e) (c3 := 0xd1) (by decide +kernel)
      (hnm 32 (by decide))
  have r34 := cometWithExtendedAssetList_block_383_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn32.symm) r33
  have hn33 : solcSelectorWord I ≠ UInt256.ofNat 2125926705 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x7e) (c1 := 0xb7) (c2 := 0x11) (c3 := 0x31) (by decide +kernel)
      (hnm 33 (by decide))
  have r35 := cometWithExtendedAssetList_block_394_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn33.symm) r34
  have hn34 : solcSelectorWord I ≠ UInt256.ofNat 2152589087 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x80) (c1 := 0x4d) (c2 := 0xe7) (c3 := 0x1f) (by decide +kernel)
      (hnm 34 (by decide))
  have r36 := cometWithExtendedAssetList_block_405_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn34.symm) r35
  have hn35 : solcSelectorWord I ≠ UInt256.ofNat 2189815616 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x82) (c1 := 0x85) (c2 := 0xef) (c3 := 0x40) (by decide +kernel)
      (hnm 35 (by decide))
  have r37 := cometWithExtendedAssetList_block_416_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn35.symm) r36
  have hn36 : solcSelectorWord I ≠ UInt256.ofNat 2371715404 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x8d) (c1 := 0x5d) (c2 := 0x81) (c3 := 0x4c) (by decide +kernel)
      (hnm 36 (by decide))
  have r38 := cometWithExtendedAssetList_block_427_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn36.symm) r37
  have hn37 : solcSelectorWord I ≠ UInt256.ofNat 2419208567 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x90) (c1 := 0x32) (c2 := 0x31) (c3 := 0x77) (by decide +kernel)
      (hnm 37 (by decide))
  have r39 := cometWithExtendedAssetList_block_438_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn37.symm) r38
  have hn38 : solcSelectorWord I ≠ UInt256.ofNat 2453775713 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x92) (c1 := 0x41) (c2 := 0xa5) (c3 := 0x61) (by decide +kernel)
      (hnm 39 (by decide))
  have r40 := cometWithExtendedAssetList_block_449_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn38.symm) r39
  have hn39 : solcSelectorWord I ≠ UInt256.ofNat 2472862090 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x93) (c1 := 0x64) (c2 := 0xe1) (c3 := 0x8a) (by decide +kernel)
      (hnm 40 (by decide))
  have r41 := cometWithExtendedAssetList_block_460_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn39.symm) r40
  have hn40 : solcSelectorWord I ≠ UInt256.ofNat 2492599498 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x94) (c1 := 0x92) (c2 := 0x0c) (c3 := 0xca) (by decide +kernel)
      (hnm 41 (by decide))
  have r42 := cometWithExtendedAssetList_block_471_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn40.symm) r41
  have hn41 : solcSelectorWord I ≠ UInt256.ofNat 2661915226 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x9e) (c1 := 0xa9) (c2 := 0x9a) (c3 := 0x5a) (by decide +kernel)
      (hnm 42 (by decide))
  have r43 := cometWithExtendedAssetList_block_482_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn41.symm) r42
  have hn42 : solcSelectorWord I ≠ UInt256.ofNat 2678602586 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x9f) (c1 := 0xa8) (c2 := 0x3b) (c3 := 0x5a) (by decide +kernel)
      (hnm 43 (by decide))
  have r44 := cometWithExtendedAssetList_block_493_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn42.symm) r43
  have hn43 : solcSelectorWord I ≠ UInt256.ofNat 2683660280 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0x9f) (c1 := 0xf5) (c2 := 0x67) (c3 := 0xf8) (by decide +kernel)
      (hnm 44 (by decide))
  have r45 := cometWithExtendedAssetList_block_504_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn43.symm) r44
  have hn44 : solcSelectorWord I ≠ UInt256.ofNat 2707768185 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xa1) (c1 := 0x65) (c2 := 0x43) (c3 := 0x79) (by decide +kernel)
      (hnm 45 (by decide))
  have r46 := cometWithExtendedAssetList_block_515_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn44.symm) r45
  have hn45 : solcSelectorWord I ≠ UInt256.ofNat 2711744323 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xa1) (c1 := 0xa1) (c2 := 0xef) (c3 := 0x43) (by decide +kernel)
      (hnm 46 (by decide))
  have r47 := cometWithExtendedAssetList_block_526_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn45.symm) r46
  have hn46 : solcSelectorWord I ≠ UInt256.ofNat 2758797371 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xa4) (c1 := 0x6f) (c2 := 0xe8) (c3 := 0x3b) (by decide +kernel)
      (hnm 47 (by decide))
  have r48 := cometWithExtendedAssetList_block_537_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn46.symm) r47
  have hn47 : solcSelectorWord I ≠ UInt256.ofNat 2780102521 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xa5) (c1 := 0xb4) (c2 := 0xff) (c3 := 0x79) (by decide +kernel)
      (hnm 48 (by decide))
  have r49 := cometWithExtendedAssetList_block_548_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn47.symm) r48
  have hn48 : solcSelectorWord I ≠ UInt256.ofNat 2835717307 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xa9) (c1 := 0x05) (c2 := 0x9c) (c3 := 0xbb) (by decide +kernel)
      (hnm 49 (by decide))
  have r50 := cometWithExtendedAssetList_block_559_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn48.symm) r49
  have hn49 : solcSelectorWord I ≠ UInt256.ofNat 2879910238 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xab) (c1 := 0xa7) (c2 := 0xf1) (c3 := 0x5e) (by decide +kernel)
      (hnm 50 (by decide))
  have r51 := cometWithExtendedAssetList_block_570_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn49.symm) r50
  have hn50 : solcSelectorWord I ≠ UInt256.ofNat 2903799676 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xad) (c1 := 0x14) (c2 := 0x77) (c3 := 0x7c) (by decide +kernel)
      (hnm 51 (by decide))
  have r52 := cometWithExtendedAssetList_block_581_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn50.symm) r51
  have hn51 : solcSelectorWord I ≠ UInt256.ofNat 3219561613 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xbf) (c1 := 0xe6) (c2 := 0x9c) (c3 := 0x8d) (by decide +kernel)
      (hnm 52 (by decide))
  have r53 := cometWithExtendedAssetList_block_592_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn51.symm) r52
  have hn52 : solcSelectorWord I ≠ UInt256.ofNat 3253611544 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xc1) (c1 := 0xee) (c2 := 0x2c) (c3 := 0x18) (by decide +kernel)
      (hnm 53 (by decide))
  have r54 := cometWithExtendedAssetList_block_603_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn52.symm) r53
  have hn53 : solcSelectorWord I ≠ UInt256.ofNat 3283311230 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xc3) (c1 := 0xb3) (c2 := 0x5a) (c3 := 0x7e) (by decide +kernel)
      (hnm 54 (by decide))
  have r55 := cometWithExtendedAssetList_block_614_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn53.symm) r54
  have hn54 : solcSelectorWord I ≠ UInt256.ofNat 3285110738 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xc3) (c1 := 0xce) (c2 := 0xcf) (c3 := 0xd2) (by decide +kernel)
      (hnm 38 (by decide))
  have r56 := cometWithExtendedAssetList_block_625_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn54.symm) r55
  have hn55 : solcSelectorWord I ≠ UInt256.ofNat 3311251043 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xc5) (c1 := 0x5d) (c2 := 0xae) (c3 := 0x63) (by decide +kernel)
      (hnm 55 (by decide))
  have r57 := cometWithExtendedAssetList_block_636_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn55.symm) r56
  have hn56 : solcSelectorWord I ≠ UInt256.ofNat 3321501135 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xc5) (c1 := 0xfa) (c2 := 0x15) (c3 := 0xcf) (by decide +kernel)
      (hnm 56 (by decide))
  have r58 := cometWithExtendedAssetList_block_647_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn56.symm) r57
  have hn57 : solcSelectorWord I ≠ UInt256.ofNat 3368549995 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xc8) (c1 := 0xc7) (c2 := 0xfe) (c3 := 0x6b) (by decide +kernel)
      (hnm 57 (by decide))
  have r59 := cometWithExtendedAssetList_block_658_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn57.symm) r58
  have hn58 : solcSelectorWord I ≠ UInt256.ofNat 3454435393 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xcd) (c1 := 0xe6) (c2 := 0x80) (c3 := 0x41) (by decide +kernel)
      (hnm 58 (by decide))
  have r60 := cometWithExtendedAssetList_block_669_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn58.symm) r59
  have hn59 : solcSelectorWord I ≠ UInt256.ofNat 3638949393 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xd8) (c1 := 0xe5) (c2 := 0xf6) (c3 := 0x11) (by decide +kernel)
      (hnm 59 (by decide))
  have r61 := cometWithExtendedAssetList_block_680_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn59.symm) r60
  have hn60 : solcSelectorWord I ≠ UInt256.ofNat 3646256541 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xd9) (c1 := 0x55) (c2 := 0x75) (c3 := 0x9d) (by decide +kernel)
      (hnm 60 (by decide))
  have r62 := cometWithExtendedAssetList_block_691_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn60.symm) r61
  have hn61 : solcSelectorWord I ≠ UInt256.ofNat 3695885053 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xdc) (c1 := 0x4a) (c2 := 0xba) (c3 := 0xfd) (by decide +kernel)
      (hnm 61 (by decide))
  have r63 := cometWithExtendedAssetList_block_702_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn61.symm) r62
  have hn62 : solcSelectorWord I ≠ UInt256.ofNat 3815960634 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xe3) (c1 := 0x72) (c2 := 0xf0) (c3 := 0x3a) (by decide +kernel)
      (hnm 62 (by decide))
  have r64 := cometWithExtendedAssetList_block_713_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn62.symm) r63
  have hn63 : solcSelectorWord I ≠ UInt256.ofNat 3833100637 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xe4) (c1 := 0x78) (c2 := 0x79) (c3 := 0x5d) (by decide +kernel)
      (hnm 63 (by decide))
  have r65 := cometWithExtendedAssetList_block_724_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn63.symm) r64
  have hn64 : solcSelectorWord I ≠ UInt256.ofNat 3840337785 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xe4) (c1 := 0xe6) (c2 := 0xe7) (c3 := 0x79) (by decide +kernel)
      (hnm 64 (by decide))
  have r66 := cometWithExtendedAssetList_block_735_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn64.symm) r65
  have hn65 : solcSelectorWord I ≠ UInt256.ofNat 3889878717 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xe7) (c1 := 0xda) (c2 := 0xd6) (c3 := 0xbd) (by decide +kernel)
      (hnm 65 (by decide))
  have r67 := cometWithExtendedAssetList_block_746_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn65.symm) r66
  have hn66 : solcSelectorWord I ≠ UInt256.ofNat 4072275384 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xf2) (c1 := 0xb9) (c2 := 0xfd) (c3 := 0xb8) (by decide +kernel)
      (hnm 66 (by decide))
  have r68 := cometWithExtendedAssetList_block_757_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_eq_of_ne hn66.symm) r67
  have hn67 : solcSelectorWord I ≠ UInt256.ofNat 4093572003 :=
    selectorWord_ne_of_selector_false hsz
      (c0 := 0xf3) (c1 := 0xfe) (c2 := 0xf3) (c3 := 0xa3) (by decide +kernel)
      (hnm 67 (by decide))
  have r69 := cometWithExtendedAssetList_block_768_taken
    (immWords := wordsOf (immStore v)) (by decide)
    (by exact u256_sub_ne_zero_of_ne hn67.symm)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r68
  exact ⟨_, _, r69⟩

theorem cometFallbackDispatch {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 68 → (cometWithExtendedAssetListSelBytes i == I.calldata.extract 0 4) = false) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨18418⟩ [⟨22⟩]
      solcFreePtrMem (M ⟨0⟩ ⟨64⟩ ⟨32⟩) ByteArray.empty σ k C := by
  have h14 : ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨14⟩ []
      solcFreePtrMem (M ⟨0⟩ ⟨64⟩ ⟨32⟩) ByteArray.empty σ k C := by
    by_cases hsz : 4 ≤ I.calldata.size
    · exact cometFallbackDispatchLong v hcode hsize hsz hnm
    · have hshort : I.calldata.size < 4 := by omega
      have r0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
      have r1 := cometWithExtendedAssetList_block_0_fallthrough
        (immWords := wordsOf (immStore v)) (by decide)
        (isZero_eq_zero_of_ne (lt_four_ne_zero_of_lt hshort)) r0
      exact ⟨_, _, r1⟩
  obtain ⟨k, C, r1⟩ := h14
  have r2 := cometWithExtendedAssetList_block_14 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  exact ⟨_, _, r2⟩

end Benchmarks.CompoundIII.Comet
