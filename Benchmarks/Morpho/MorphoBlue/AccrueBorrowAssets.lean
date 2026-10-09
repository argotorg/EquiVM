import Benchmarks.Morpho.MorphoBlue.Uint128Arithmetic
import Benchmarks.Morpho.MorphoBlue.MarketWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def accrueBorrowAssetsAccounts (σ : AccountMap) (I : ExecutionEnv) (id interest : UInt256) : AccountMap :=
  storeMarketFieldAccounts σ I id ⟨2, by decide⟩ (marketFieldWord σ I id 2 + interest)

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {id interest : UInt256} {R : List UInt256}

theorem morphoAccrueBorrowReachAdd (hstack : R.length + 18 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13574)
      ([interest, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, id, UInt256.ofNat 32,
        solcAddrMask, interest, UInt256.ofNat 3] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12664)
      ([marketFieldWord σ ee id 2, interest, UInt256.ofNat 13601, uint128Mask, marketFieldSlot id 2,
        solcSlotWordAt (marketFieldSlot id 2) σ ee, UInt256.ofNat 0, UInt256.ofNat 64,
        uint128Mask, id, UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 3] ++ R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13574_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) = solcMappingSlot ⟨3⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    ([UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) uint128Mask,
      interest, UInt256.ofNat 13601, uint128Mask,
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1,
      solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee,
      UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, id, UInt256.ofNat 32,
      solcAddrMask, interest, UInt256.ofNat 3] ++ R)
    (twoWordHashMem id (UInt256.ofNat 3) mem) _ _ _ _ _ at rd1
  rw [hh] at rd1
  exact ⟨aw1, k1, C1, rd1⟩

theorem morphoAccrueBorrowAddOk (hstack : R.length + 18 ≤ 1024)
    (hi : interest.toNat < 2 ^ 128)
    (hsum : (marketFieldWord σ ee id 2).toNat + interest.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13574)
      ([interest, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, id, UInt256.ofNat 32,
        solcAddrMask, interest, UInt256.ofNat 3] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13601)
      ([marketFieldWord σ ee id 2 + interest, uint128Mask, marketFieldSlot id 2,
        solcSlotWordAt (marketFieldSlot id 2) σ ee, UInt256.ofNat 0, UInt256.ofNat 64,
        uint128Mask, id, UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 3] ++ R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueBorrowReachAdd (v := v) hstack h
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedAdd128Ok (v := v)
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (halfWord_bound _ _) hi hsum rd1
  exact ⟨aw1, k2, C2, rd2⟩

theorem morphoAccrueBorrowAddReverts (hstack : R.length + 18 ≤ 1024)
    (hi : interest.toNat < 2 ^ 128)
    (hover : 2 ^ 128 ≤ (marketFieldWord σ ee id 2).toNat + interest.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13574)
      ([interest, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, id, UInt256.ofNat 32,
        solcAddrMask, interest, UInt256.ofNat 3] ++ R) mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueBorrowReachAdd (v := v) hstack h
  exact morphoCheckedAdd128Reverts (v := v) (by simp only [List.append, List.length_cons]; omega)
    (halfWord_bound _ _) hi hover rd1

theorem morphoAccrueBorrowStore (hstack : R.length + 13 ≤ 1024) (hp : ee.perm = true)
    (hc : (marketFieldWord σ ee id 2 + interest).toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13601)
      ([marketFieldWord σ ee id 2 + interest, uint128Mask, marketFieldSlot id 2,
        solcSlotWordAt (marketFieldSlot id 2) σ ee, UInt256.ofNat 0, UInt256.ofNat 64,
        uint128Mask, id, UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 3] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([interest, UInt256.ofNat 13650, UInt256.lnot uint128Mask, UInt256.ofNat 0, UInt256.ofNat 64,
        uint128Mask, id, UInt256.ofNat 32, solcAddrMask, interest, UInt256.ofNat 3] ++ R)
      mem aw rdata (accrueBorrowAssetsAccounts σ ee id interest) k' C' := by
  obtain ⟨k1, C1, rd1⟩ := morphoBlocks.morpho_block_13601 (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega) hp
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have hclean : UInt256.land (marketFieldWord σ ee id 2 + interest) uint128Mask =
      marketFieldWord σ ee id 2 + interest := halfWord_low_clean _ hc
  dsimp only [morphoBlocks.morpho_block_13601_stack] at rd1
  rw [hclean] at rd1
  exact ⟨k1, C1, rd1⟩

theorem morphoAccrueBorrowStoreStatic {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256}
    (hstack : R.length + 12 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13601)
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)
      mem aw rdata σ k C) : RDstatic (deployedRuntime v) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13601⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13602⟩ : UInt256), UInt8.ofNat 22, .AND, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13603⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480), 32), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13636⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap4 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13637⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13638⟩ : UInt256), UInt8.ofNat 22, .AND, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13639⟩ : UInt256), UInt8.ofNat 23, .OR, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13640⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  exact r8.sstoreStatic hperm (by
    immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
      (⟨13641⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)

end Routines
end Benchmarks.Morpho.MorphoBlue
