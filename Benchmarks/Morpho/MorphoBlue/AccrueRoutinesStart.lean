import Benchmarks.Morpho.MorphoBlue.AccrueSourceStart
import Benchmarks.Morpho.MorphoBlue.ArithmeticRoutines
import Benchmarks.Morpho.MorphoBlue.MarketParamsMemory
import Benchmarks.Morpho.MorphoBlue.MarketStorageBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {ptr ret : UInt256} {R : List UInt256}

theorem morphoAccrueReachSub (p : MarketParamsWords) (hstack : R.length + 15 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13166) (ptr :: p.id :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12833)
      ([UInt256.ofNat ee.header.timestamp, marketFieldWord σ ee p.id 4, UInt256.ofNat 13222,
        p.id, UInt256.ofNat 32, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64,
        uint128Mask, ret, ptr] ++ R)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13166_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _
    ([UInt256.ofNat ee.header.timestamp,
      UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem p.id (UInt256.ofNat 3) mem) + UInt256.ofNat 2) σ ee) uint128Mask,
      UInt256.ofNat 13222, p.id, UInt256.ofNat 32, UInt256.ofNat 3, UInt256.ofNat 0,
      UInt256.ofNat 64, uint128Mask, ret, ptr] ++ R)
    (twoWordHashMem p.id (UInt256.ofNat 3) mem) _ _ _ _ _ at rd1
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) = solcMappingSlot ⟨3⟩ p.id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  rw [hh] at rd1
  exact ⟨aw1, k1, C1, rd1⟩

theorem morphoAccrueUnderflow (p : MarketParamsWords) (hstack : R.length + 15 ≤ 1024)
    (hunder : (UInt256.ofNat ee.header.timestamp).toNat < (marketFieldWord σ ee p.id 4).toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13166) (ptr :: p.id :: ret :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueReachSub (v := v) p hstack h
  exact morphoCheckedSubReverts (v := v)
    (by simp only [List.append, List.length_cons]; omega) hunder rd1

theorem morphoAccrueReachElapsed (p : MarketParamsWords) (hstack : R.length + 15 ≤ 1024)
    (htime : (marketFieldWord σ ee p.id 4).toNat ≤ (UInt256.ofNat ee.header.timestamp).toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13166) (ptr :: p.id :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13222)
      ([accrueElapsed σ ee p, p.id, UInt256.ofNat 32, UInt256.ofNat 3, UInt256.ofNat 0,
        UInt256.ofNat 64, uint128Mask, ret, ptr] ++ R)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueReachSub (v := v) p hstack h
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedSubOk (v := v)
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) htime rd1
  exact ⟨aw1, k2, C2, rd2⟩

theorem morphoAccrueZeroElapsed (p : MarketParamsWords) (hstack : R.length + 15 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (htime : (marketFieldWord σ ee p.id 4).toNat ≤ (UInt256.ofNat ee.header.timestamp).toNat)
    (hz : accrueElapsed σ ee p = ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13166) (ptr :: p.id :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret R
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueReachElapsed (v := v) p hstack htime h
  have rd2 := morphoBlocks.morpho_block_13222_taken (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega) (by rw [hz]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  exact ⟨aw1, _, _, morphoBlocks.morpho_block_13937 (immWords := wordsOf (immStore v))
    (by omega) hvalid rd2⟩

theorem morphoAccrueReachIrm (p : MarketParamsWords) (hstack : R.length + 15 ≤ 1024)
    (htime : (marketFieldWord σ ee p.id 4).toNat ≤ (UInt256.ofNat ee.header.timestamp).toNat)
    (hn : accrueElapsed σ ee p ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13166) (ptr :: p.id :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13229)
      ([accrueElapsed σ ee p, p.id, UInt256.ofNat 32, UInt256.ofNat 3, UInt256.ofNat 0,
        UInt256.ofNat 64, uint128Mask, ret, ptr] ++ R)
      (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueReachElapsed (v := v) p hstack htime h
  exact ⟨aw1, _, _, morphoBlocks.morpho_block_13222_fallthrough
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega) (isZero_eq_zero_of_ne hn) rd1⟩



theorem morphoAccrueNoIrmBranch (p : MarketParamsWords) (hc : p.Canonical)
    {elapsed : UInt256} (hstack : R.length + 13 ≤ 1024) (hi0 : p.irm = ⟨0⟩)
    (hm : p.InMemory ptr mem)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13229)
      ([elapsed, p.id, UInt256.ofNat 32, UInt256.ofNat 3, UInt256.ofNat 0,
        UInt256.ofNat 64, uint128Mask, ret, ptr] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13263)
      ([p.irm, elapsed, solcAddrMask, p.id, UInt256.ofNat 32, UInt256.ofNat 3,
        UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret, ptr] ++ R) mem aw' rdata σ k' C' := by
  have hi : memLoad (ptr + UInt256.ofNat 96) mem = p.irm := by
    simpa only [MarketParamsWords.word] using hm ⟨3, by decide⟩
  have hclean : UInt256.land p.irm (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = p.irm :=
    solcAddrMask_clean hc.2.2.2
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13229_fallthrough_packed (immWords := wordsOf (immStore v))
    hstack (by rw [hi, hclean, hi0]; rfl) h
  refine ⟨aw1, k1, C1, ?_⟩
  simpa only [morphoBlocks.morpho_block_13229_fallthrough_stack, hi,
    hclean] using rd1

theorem morphoAccrueHasIrmBranch (p : MarketParamsWords) (hc : p.Canonical)
    {elapsed : UInt256} (hstack : R.length + 13 ≤ 1024) (hin : p.irm ≠ ⟨0⟩)
    (hm : p.InMemory ptr mem)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13229)
      ([elapsed, p.id, UInt256.ofNat 32, UInt256.ofNat 3, UInt256.ofNat 0,
        UInt256.ofNat 64, uint128Mask, ret, ptr] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13321)
      ([p.irm, elapsed, solcAddrMask, p.id, UInt256.ofNat 32, UInt256.ofNat 3,
        UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret, ptr] ++ R) mem aw' rdata σ k' C' := by
  have hi : memLoad (ptr + UInt256.ofNat 96) mem = p.irm := by
    simpa only [MarketParamsWords.word] using hm ⟨3, by decide⟩
  have hclean : UInt256.land p.irm (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = p.irm :=
    solcAddrMask_clean hc.2.2.2
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13229_taken_packed (immWords := wordsOf (immStore v))
    hstack (by rw [hi, hclean]; exact hin)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  refine ⟨aw1, k1, C1, ?_⟩
  simpa only [morphoBlocks.morpho_block_13229_taken_stack, hi,
    hclean] using rd1

theorem morphoAccrueStoreTimestamp (id : UInt256) {x0 x1 x2 : UInt256}
    (hstack : R.length + 11 ≤ 1024) (hp : ee.perm = true)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13263)
      ([x0, x1, x2, id, UInt256.ofNat 32, UInt256.ofNat 3, UInt256.ofNat 0,
        UInt256.ofNat 64, uint128Mask, ret, ptr] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret R
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' rdata
      (storeMarketFieldAccounts σ ee id ⟨4, by decide⟩
        (halfWord false (UInt256.ofNat ee.header.timestamp))) k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13263_packed
    (immWords := wordsOf (immStore v)) hstack hp hvalid h
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) = solcMappingSlot ⟨3⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _ R (twoWordHashMem id (UInt256.ofNat 3) mem) _ _
    (sstoreAccountMap ee.codeOwner σ
      (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 2)
      (setUint128LowWord (solcSlotWordAt
        (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 2) σ ee)
        (halfWord false (UInt256.ofNat ee.header.timestamp)))) _ _ at rd1
  rw [hh] at rd1
  exact ⟨aw1, k1, C1, rd1⟩

-- Static execution stops at the timestamp write, after the shared load/mask prefix.
theorem morphoAccrueTimestampStatic {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256}
    (hstack : R.length + 11 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13263)
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: R)
      mem aw rdata σ k C) : RDstatic (deployedRuntime v) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13263⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.pop (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13264⟩ : UInt256), UInt8.ofNat 80, .POP, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pop (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13265⟩ : UInt256), UInt8.ofNat 80, .POP, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.pop (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13266⟩ : UInt256), UInt8.ofNat 80, .POP, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13267⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 2), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.swap6 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13269⟩ : UInt256), UInt8.ofNat 149, .SWAP6, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.swap7 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13270⟩ : UInt256), UInt8.ofNat 150, .SWAP7, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap8 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13271⟩ : UInt256), UInt8.ofNat 151, .SWAP8, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.pop (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13272⟩ : UInt256), UInt8.ofNat 80, .POP, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.dup4 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13273⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r11 := RD.genMstore r10 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13274⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r12 := RD.genMstore r11 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13275⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r13 := RD.genKeccak256 r12 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13276⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.add (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13277⟩ : UInt256), UInt8.ofNat 1, .ADD, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13278⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.timestamp (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13279⟩ : UInt256), UInt8.ofNat 66, .TIMESTAMP, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13280⟩ : UInt256), UInt8.ofNat 22, .AND, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.pushConst (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13281⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480), 32), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13314⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sload r19 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13315⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13316⟩ : UInt256), UInt8.ofNat 22, .AND, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13317⟩ : UInt256), UInt8.ofNat 23, .OR, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨13318⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  exact r23.sstoreStatic hperm (by
    immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
      (⟨13319⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)

end Routines
end Benchmarks.Morpho.MorphoBlue
