import Benchmarks.Midnight.PositionViewValues
import Benchmarks.Midnight.MemoryWords
import Benchmarks.Midnight.WordTuple
import Benchmarks.Midnight.RuntimeBlocks_008
import Benchmarks.Midnight.RuntimeBlocks_013

variable {fork : Ethereum.Fork}

/-! The position-view ABI encoder for three uint128 return values. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightReturnThree128 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root a b c : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 9 ≤ 1024)
    (hroot : root.toNat < 2 ^ 64) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (ha : a.toNat < 2 ^ 128) (hb : b.toNat < 2 ^ 128) (hc : c.toNat < 2 ^ 128)
    (rd : RD fork midnightBytecode I g s0 ⟨2594⟩ (c :: b :: a :: ⟨1184⟩ :: R) mem aw rdata σ k C) :
    RDret fork midnightBytecode g s0 σ (wordArrayBytes [a, b, c]) := by
  have rd1 := midnightBlocks.midnight_block_2594 hstack (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_2594_stack, hfree] at rd1
  have hr := midnightBlocks.midnight_block_1184 (by omega) rd1
  have h32 : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2 ^ 256; omega)
  have h64 : (root + UInt256.ofNat 64).toNat = root.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2 ^ 256; omega)
  have h96 : (root + UInt256.ofNat 96).toNat = root.toNat + 96 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2 ^ 256; omega)
  have hlen : (UInt256.sub (root + UInt256.ofNat 96) root).toNat = 96 := by
    rw [usub_toNat (by rw [h96]; omega), h96]
    omega
  have hm : midnightBlocks.midnight_block_2594_memory (mem := mem) (x0 := c) (x1 := b) (x2 := a) =
      writeWordArray mem root.toNat [a, b, c] := by
    simp only [midnightBlocks.midnight_block_2594_memory, uint128Mask_computed,
      u256_land_comm, uint128Mask_clean ha, uint128Mask_clean hb, uint128Mask_clean hc,
      hfree, h32, h64]
    simp only [writeWordArray, Reasoning.Theory.writeWord, Nat.add_assoc]
  rw [hm, hlen] at hr
  have hread := (MemoryWords.of_writeWordArray mem root.toNat [a, b, c]
    (by change root.toNat + 96 < 2 ^ 256; omega) (by simp)).read
  exact hread ▸ hr

theorem threeUint128ReturnEncoding (a b c : UInt256)
    (ha : a.toNat < 2 ^ 128) (hb : b.toNat < 2 ^ 128) (hc : c.toNat < 2 ^ 128) :
    encodeReturnValues? [.elem (.int packedUInt128Int), .elem (.int packedUInt128Int),
      .elem (.int packedUInt128Int)] [.int a.toNat, .int b.toNat, .int c.toNat] =
      some (wordArrayBytes [a, b, c]) := by
  apply uintWordTupleReturnEncoding [(⟨128, by decide⟩, a), (⟨128, by decide⟩, b), (⟨128, by decide⟩, c)]
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

end Benchmarks.Midnight
