import Benchmarks.UniswapV3Pool.Uint128
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

noncomputable def ticksScratchReturnMem1 (scratch : ByteArray) (gross : UInt256) :
    ByteArray :=
  writeCascade scratch [(128, gross)]

noncomputable def ticksScratchReturnMem2 (scratch : ByteArray) (gross net : UInt256) :
    ByteArray :=
  writeCascade scratch [(128, gross), (160, net)]

noncomputable def ticksScratchReturnMem3 (scratch : ByteArray) (gross net fee0 : UInt256) :
    ByteArray :=
  writeCascade scratch [(128, gross), (160, net), (192, fee0)]

noncomputable def ticksScratchReturnMem4
    (scratch : ByteArray) (gross net fee0 fee1 : UInt256) : ByteArray :=
  writeCascade scratch [(128, gross), (160, net), (192, fee0), (224, fee1)]

noncomputable def ticksScratchReturnMem5
    (scratch : ByteArray) (gross net fee0 fee1 tick : UInt256) : ByteArray :=
  writeCascade scratch
    [(128, gross), (160, net), (192, fee0), (224, fee1), (256, tick)]

noncomputable def ticksScratchReturnMem6
    (scratch : ByteArray) (gross net fee0 fee1 tick secondsLiq : UInt256) :
    ByteArray :=
  writeCascade scratch
    [(128, gross), (160, net), (192, fee0), (224, fee1), (256, tick),
      (288, secondsLiq)]

noncomputable def ticksScratchReturnMem7
    (scratch : ByteArray) (gross net fee0 fee1 tick secondsLiq secondsOut : UInt256) :
    ByteArray :=
  writeCascade scratch
    [(128, gross), (160, net), (192, fee0), (224, fee1), (256, tick),
      (288, secondsLiq), (320, secondsOut)]

noncomputable def ticksScratchReturnMem
    (scratch : ByteArray) (gross net fee0 fee1 tick secondsLiq secondsOut initialized : UInt256) :
    ByteArray :=
  writeCascade scratch
    [(128, gross), (160, net), (192, fee0), (224, fee1), (256, tick),
      (288, secondsLiq), (320, secondsOut), (352, initialized)]

theorem ticksScratchReturnMem1_eq (scratch : ByteArray) (gross : UInt256) :
    ticksScratchReturnMem1 scratch gross = writeWord scratch 128 gross := by
  rfl

theorem ticksScratchReturnMem2_eq (scratch : ByteArray) (gross net : UInt256) :
    ticksScratchReturnMem2 scratch gross net =
      writeWord (ticksScratchReturnMem1 scratch gross) 160 net := by
  rfl

theorem ticksScratchReturnMem3_eq (scratch : ByteArray) (gross net fee0 : UInt256) :
    ticksScratchReturnMem3 scratch gross net fee0 =
      writeWord (ticksScratchReturnMem2 scratch gross net) 192 fee0 := by
  rfl

theorem ticksScratchReturnMem4_eq
    (scratch : ByteArray) (gross net fee0 fee1 : UInt256) :
    ticksScratchReturnMem4 scratch gross net fee0 fee1 =
      writeWord (ticksScratchReturnMem3 scratch gross net fee0) 224 fee1 := by
  rfl

theorem ticksScratchReturnMem5_eq
    (scratch : ByteArray) (gross net fee0 fee1 tick : UInt256) :
    ticksScratchReturnMem5 scratch gross net fee0 fee1 tick =
      writeWord (ticksScratchReturnMem4 scratch gross net fee0 fee1) 256 tick := by
  rfl

theorem ticksScratchReturnMem6_eq
    (scratch : ByteArray) (gross net fee0 fee1 tick secondsLiq : UInt256) :
    ticksScratchReturnMem6 scratch gross net fee0 fee1 tick secondsLiq =
      writeWord (ticksScratchReturnMem5 scratch gross net fee0 fee1 tick) 288 secondsLiq := by
  rfl

theorem ticksScratchReturnMem7_eq
    (scratch : ByteArray) (gross net fee0 fee1 tick secondsLiq secondsOut : UInt256) :
    ticksScratchReturnMem7 scratch gross net fee0 fee1 tick secondsLiq secondsOut =
      writeWord (ticksScratchReturnMem6 scratch gross net fee0 fee1 tick secondsLiq) 320
        secondsOut := by
  rfl

theorem ticksScratchReturnMem_eq
    (scratch : ByteArray) (gross net fee0 fee1 tick secondsLiq secondsOut initialized : UInt256) :
    ticksScratchReturnMem scratch gross net fee0 fee1 tick secondsLiq secondsOut initialized =
      writeWord (ticksScratchReturnMem7 scratch gross net fee0 fee1 tick secondsLiq secondsOut)
        352 initialized := by
  rfl

theorem ticksScratchReturnMem1_size {scratch : ByteArray} (gross : UInt256)
    (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem1 scratch gross).size = 160 := by
  unfold ticksScratchReturnMem1
  exact writeCascade_size_of_base scratch _ hscratch
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem ticksScratchReturnMem2_size {scratch : ByteArray} (gross net : UInt256)
    (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem2 scratch gross net).size = 192 := by
  unfold ticksScratchReturnMem2
  exact writeCascade_size_of_base scratch _ hscratch
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem ticksScratchReturnMem3_size {scratch : ByteArray} (gross net fee0 : UInt256)
    (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem3 scratch gross net fee0).size = 224 := by
  unfold ticksScratchReturnMem3
  exact writeCascade_size_of_base scratch _ hscratch
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem ticksScratchReturnMem4_size {scratch : ByteArray}
    (gross net fee0 fee1 : UInt256) (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem4 scratch gross net fee0 fee1).size = 256 := by
  unfold ticksScratchReturnMem4
  exact writeCascade_size_of_base scratch _ hscratch
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem ticksScratchReturnMem5_size {scratch : ByteArray}
    (gross net fee0 fee1 tick : UInt256) (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem5 scratch gross net fee0 fee1 tick).size = 288 := by
  unfold ticksScratchReturnMem5
  exact writeCascade_size_of_base scratch _ hscratch
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem ticksScratchReturnMem6_size {scratch : ByteArray}
    (gross net fee0 fee1 tick secondsLiq : UInt256) (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem6 scratch gross net fee0 fee1 tick secondsLiq).size = 320 := by
  unfold ticksScratchReturnMem6
  exact writeCascade_size_of_base scratch _ hscratch
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem ticksScratchReturnMem7_size {scratch : ByteArray}
    (gross net fee0 fee1 tick secondsLiq secondsOut : UInt256)
    (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem7 scratch gross net fee0 fee1 tick secondsLiq secondsOut).size =
      352 := by
  unfold ticksScratchReturnMem7
  exact writeCascade_size_of_base scratch _ hscratch
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem ticksScratchReturnMem_size {scratch : ByteArray}
    (gross net fee0 fee1 tick secondsLiq secondsOut initialized : UInt256)
    (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem scratch gross net fee0 fee1 tick secondsLiq secondsOut
      initialized).size = 384 := by
  unfold ticksScratchReturnMem
  exact writeCascade_size_of_base scratch _ hscratch
    (by
      norm_num [WriteGapsOk]
      all_goals native_decide)
    (by norm_num [writeCascadeSize])

theorem ticksScratchReturnMem_read64 {scratch : ByteArray}
    (gross net fee0 fee1 tick secondsLiq secondsOut initialized : UInt256)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (ticksScratchReturnMem scratch gross net fee0 fee1 tick secondsLiq secondsOut
      initialized).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold ticksScratchReturnMem
  rw [writeCascade_read_preserved_of_base scratch _ hscratch
    (by
      norm_num [WindowDisjointFromWrites]
      all_goals native_decide)]
  exact hread64

theorem ticksScratchReturnMem_mload64 {scratch : ByteArray}
    (gross net fee0 fee1 tick secondsLiq secondsOut initialized : UInt256)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (ticksScratchReturnMem scratch gross net fee0 fee1 tick secondsLiq secondsOut
            initialized).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((ticksScratchReturnMem scratch gross net fee0 fee1 tick secondsLiq secondsOut
          initialized).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by
      rw [ticksScratchReturnMem_size gross net fee0 fee1 tick secondsLiq secondsOut
        initialized hscratch]
      decide)
    (by decide)
    (ticksScratchReturnMem_read64 gross net fee0 fee1 tick secondsLiq secondsOut initialized
      hscratch hread64)

theorem ticksScratchReturnMem_read128 {scratch : ByteArray}
    (gross net fee0 fee1 tick secondsLiq secondsOut initialized : UInt256)
    (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem scratch gross net fee0 fee1 tick secondsLiq secondsOut
      initialized).readWithPadding 128 32 =
      UInt256.toByteArray gross := by
  unfold ticksScratchReturnMem
  exact writeCascade_read_word_of_head_of_base scratch (base := 96) (off := 128)
    gross [(160, net), (192, fee0), (224, fee1), (256, tick), (288, secondsLiq),
      (320, secondsOut), (352, initialized)] hscratch (by native_decide)
    (by
      norm_num [WindowDisjointFromWrites])

set_option maxHeartbeats 1000000 in
theorem ticksScratchReturnMem_read160 {scratch : ByteArray}
    (gross net fee0 fee1 tick secondsLiq secondsOut initialized : UInt256)
    (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem scratch gross net fee0 fee1 tick secondsLiq secondsOut
      initialized).readWithPadding 160 32 =
      UInt256.toByteArray net := by
  unfold ticksScratchReturnMem
  change (writeCascade (ticksScratchReturnMem1 scratch gross)
      [(160, net), (192, fee0), (224, fee1), (256, tick), (288, secondsLiq),
        (320, secondsOut), (352, initialized)]).readWithPadding 160 32 =
    UInt256.toByteArray net
  exact writeCascade_read_word_of_head_of_base (ticksScratchReturnMem1 scratch gross)
    (base := 160) (off := 160) net [(192, fee0), (224, fee1), (256, tick),
      (288, secondsLiq), (320, secondsOut), (352, initialized)]
    (ticksScratchReturnMem1_size gross hscratch) (by native_decide)
    (by
      norm_num [WindowDisjointFromWrites])

theorem ticksScratchReturnMem_read192 {scratch : ByteArray}
    (gross net fee0 fee1 tick secondsLiq secondsOut initialized : UInt256)
    (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem scratch gross net fee0 fee1 tick secondsLiq secondsOut
      initialized).readWithPadding 192 32 =
      UInt256.toByteArray fee0 := by
  unfold ticksScratchReturnMem
  change (writeCascade (ticksScratchReturnMem2 scratch gross net)
      [(192, fee0), (224, fee1), (256, tick), (288, secondsLiq), (320, secondsOut),
        (352, initialized)]).readWithPadding 192 32 =
    UInt256.toByteArray fee0
  exact writeCascade_read_word_of_head_of_base (ticksScratchReturnMem2 scratch gross net)
    (base := 192) (off := 192) fee0 [(224, fee1), (256, tick), (288, secondsLiq),
      (320, secondsOut), (352, initialized)]
    (ticksScratchReturnMem2_size gross net hscratch) (by native_decide)
    (by
      norm_num [WindowDisjointFromWrites])

theorem ticksScratchReturnMem_read224 {scratch : ByteArray}
    (gross net fee0 fee1 tick secondsLiq secondsOut initialized : UInt256)
    (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem scratch gross net fee0 fee1 tick secondsLiq secondsOut
      initialized).readWithPadding 224 32 =
      UInt256.toByteArray fee1 := by
  unfold ticksScratchReturnMem
  change (writeCascade (ticksScratchReturnMem3 scratch gross net fee0)
      [(224, fee1), (256, tick), (288, secondsLiq), (320, secondsOut),
        (352, initialized)]).readWithPadding 224 32 =
    UInt256.toByteArray fee1
  exact writeCascade_read_word_of_head_of_base (ticksScratchReturnMem3 scratch gross net fee0)
    (base := 224) (off := 224) fee1 [(256, tick), (288, secondsLiq), (320, secondsOut),
      (352, initialized)]
    (ticksScratchReturnMem3_size gross net fee0 hscratch) (by native_decide)
    (by
      norm_num [WindowDisjointFromWrites])

theorem ticksScratchReturnMem_read256 {scratch : ByteArray}
    (gross net fee0 fee1 tick secondsLiq secondsOut initialized : UInt256)
    (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem scratch gross net fee0 fee1 tick secondsLiq secondsOut
      initialized).readWithPadding 256 32 =
      UInt256.toByteArray tick := by
  unfold ticksScratchReturnMem
  change (writeCascade (ticksScratchReturnMem4 scratch gross net fee0 fee1)
      [(256, tick), (288, secondsLiq), (320, secondsOut),
        (352, initialized)]).readWithPadding 256 32 =
    UInt256.toByteArray tick
  exact writeCascade_read_word_of_head_of_base
    (ticksScratchReturnMem4 scratch gross net fee0 fee1) (base := 256) (off := 256)
    tick [(288, secondsLiq), (320, secondsOut), (352, initialized)]
    (ticksScratchReturnMem4_size gross net fee0 fee1 hscratch) (by native_decide)
    (by
      norm_num [WindowDisjointFromWrites])

theorem ticksScratchReturnMem_read288 {scratch : ByteArray}
    (gross net fee0 fee1 tick secondsLiq secondsOut initialized : UInt256)
    (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem scratch gross net fee0 fee1 tick secondsLiq secondsOut
      initialized).readWithPadding 288 32 =
      UInt256.toByteArray secondsLiq := by
  unfold ticksScratchReturnMem
  change (writeCascade (ticksScratchReturnMem5 scratch gross net fee0 fee1 tick)
      [(288, secondsLiq), (320, secondsOut), (352, initialized)]).readWithPadding
        288 32 =
    UInt256.toByteArray secondsLiq
  exact writeCascade_read_word_of_head_of_base
    (ticksScratchReturnMem5 scratch gross net fee0 fee1 tick) (base := 288) (off := 288)
    secondsLiq [(320, secondsOut), (352, initialized)]
    (ticksScratchReturnMem5_size gross net fee0 fee1 tick hscratch) (by native_decide)
    (by
      norm_num [WindowDisjointFromWrites])

theorem ticksScratchReturnMem_read320 {scratch : ByteArray}
    (gross net fee0 fee1 tick secondsLiq secondsOut initialized : UInt256)
    (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem scratch gross net fee0 fee1 tick secondsLiq secondsOut
      initialized).readWithPadding 320 32 =
      UInt256.toByteArray secondsOut := by
  unfold ticksScratchReturnMem
  change (writeCascade (ticksScratchReturnMem6 scratch gross net fee0 fee1 tick secondsLiq)
      [(320, secondsOut), (352, initialized)]).readWithPadding 320 32 =
    UInt256.toByteArray secondsOut
  exact writeCascade_read_word_of_head_of_base
    (ticksScratchReturnMem6 scratch gross net fee0 fee1 tick secondsLiq) (base := 320)
    (off := 320) secondsOut [(352, initialized)]
    (ticksScratchReturnMem6_size gross net fee0 fee1 tick secondsLiq hscratch)
    (by native_decide)
    (by
      norm_num [WindowDisjointFromWrites])

theorem ticksScratchReturnMem_read352 {scratch : ByteArray}
    (gross net fee0 fee1 tick secondsLiq secondsOut initialized : UInt256)
    (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem scratch gross net fee0 fee1 tick secondsLiq secondsOut
      initialized).readWithPadding 352 32 =
      UInt256.toByteArray initialized := by
  unfold ticksScratchReturnMem
  change (writeCascade
      (ticksScratchReturnMem7 scratch gross net fee0 fee1 tick secondsLiq secondsOut)
      [(352, initialized)]).readWithPadding 352 32 =
    UInt256.toByteArray initialized
  exact writeCascade_read_word_of_head_of_base
    (ticksScratchReturnMem7 scratch gross net fee0 fee1 tick secondsLiq secondsOut)
    (base := 352) (off := 352) initialized []
    (ticksScratchReturnMem7_size gross net fee0 fee1 tick secondsLiq secondsOut hscratch)
    (by native_decide)
    (by
      norm_num [WindowDisjointFromWrites])

theorem ticksScratchReturnMem_read128_256 {scratch : ByteArray}
    (gross net fee0 fee1 tick secondsLiq secondsOut initialized : UInt256)
    (hscratch : scratch.size = 96) :
    (ticksScratchReturnMem scratch gross net fee0 fee1 tick secondsLiq secondsOut
      initialized).readWithPadding 128 256 =
      UInt256.toByteArray gross ++ UInt256.toByteArray net ++ UInt256.toByteArray fee0 ++
        UInt256.toByteArray fee1 ++ UInt256.toByteArray tick ++
          UInt256.toByteArray secondsLiq ++ UInt256.toByteArray secondsOut ++
            UInt256.toByteArray initialized := by
  let mem := ticksScratchReturnMem scratch gross net fee0 fee1 tick secondsLiq secondsOut
    initialized
  have hsize : mem.size = 384 := by
    simpa [mem] using
      ticksScratchReturnMem_size gross net fee0 fee1 tick secondsLiq secondsOut initialized
        hscratch
  have h128 : mem.readWithPadding 128 32 = UInt256.toByteArray gross := by
    simpa [mem] using
      ticksScratchReturnMem_read128 gross net fee0 fee1 tick secondsLiq secondsOut initialized
        hscratch
  have h160 : mem.readWithPadding 160 32 = UInt256.toByteArray net := by
    simpa [mem] using
      ticksScratchReturnMem_read160 gross net fee0 fee1 tick secondsLiq secondsOut initialized
        hscratch
  have h192 : mem.readWithPadding 192 32 = UInt256.toByteArray fee0 := by
    simpa [mem] using
      ticksScratchReturnMem_read192 gross net fee0 fee1 tick secondsLiq secondsOut initialized
        hscratch
  have h224 : mem.readWithPadding 224 32 = UInt256.toByteArray fee1 := by
    simpa [mem] using
      ticksScratchReturnMem_read224 gross net fee0 fee1 tick secondsLiq secondsOut initialized
        hscratch
  have h256 : mem.readWithPadding 256 32 = UInt256.toByteArray tick := by
    simpa [mem] using
      ticksScratchReturnMem_read256 gross net fee0 fee1 tick secondsLiq secondsOut initialized
        hscratch
  have h288 : mem.readWithPadding 288 32 = UInt256.toByteArray secondsLiq := by
    simpa [mem] using
      ticksScratchReturnMem_read288 gross net fee0 fee1 tick secondsLiq secondsOut initialized
        hscratch
  have h320 : mem.readWithPadding 320 32 = UInt256.toByteArray secondsOut := by
    simpa [mem] using
      ticksScratchReturnMem_read320 gross net fee0 fee1 tick secondsLiq secondsOut initialized
        hscratch
  have h352 : mem.readWithPadding 352 32 = UInt256.toByteArray initialized := by
    simpa [mem] using
      ticksScratchReturnMem_read352 gross net fee0 fee1 tick secondsLiq secondsOut initialized
        hscratch
  change mem.readWithPadding 128 256 = _
  rw [byteArray_readWithPadding_split mem 128 32 224 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h128]
  rw [byteArray_readWithPadding_split mem 160 32 192 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h160]
  rw [byteArray_readWithPadding_split mem 192 32 160 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h192]
  rw [byteArray_readWithPadding_split mem 224 32 128 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h224]
  rw [byteArray_readWithPadding_split mem 256 32 96 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h256]
  rw [byteArray_readWithPadding_split mem 288 32 64 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h288]
  rw [byteArray_readWithPadding_split mem 320 32 32 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by omega), h320, h352]
  simp only [ByteArray.append_assoc]

theorem ticksScratch_mload64 {scratch : ByteArray}
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ scratch.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        (scratch.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [hscratch]; decide) (by decide) hread64

end Benchmarks.UniswapV3Pool
