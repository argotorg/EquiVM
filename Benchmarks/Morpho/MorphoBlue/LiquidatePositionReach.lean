import Benchmarks.Morpho.MorphoBlue.LiquidateMathRefine
import Benchmarks.Morpho.MorphoBlue.RepayPositionRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidateUpdateTail (id assets seized shares srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  [shares, id, srcOff, len, UInt256.ofNat 0, assets, seized, UInt256.ofNat 128] ++ R

def liquidatePositionStoreTail (σ : AccountMap) (ee : ExecutionEnv) (id assets seized shares account srcOff len : UInt256)
    (R : List UInt256) : List UInt256 :=
  [uint128Mask, positionSlot id account + UInt256.ofNat 1,
    solcSlotWordAt (positionSlot id account + UInt256.ofNat 1) σ ee] ++
    liquidateUpdateTail id assets seized shares srcOff len R

def liquidateMarketTail (id assets seized shares srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  UInt256.lnot uint128Mask :: liquidateUpdateTail id assets seized shares srcOff len R

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem out : ByteArray} {aw id assets seized shares account srcOff len value : UInt256} {σ : AccountMap}
  {k C : Nat} {R : List UInt256}

theorem morphoLiquidatePositionReachCast (hstack : R.length + 30 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2105)
      (assets :: liquidateFinishMathTail id seized shares srcOff len R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([shares, UInt256.ofNat 2115] ++ liquidateUpdateTail id assets seized shares srcOff len R) mem aw out σ k' C' := by
  exact ⟨_, _, morphoBlocks.morpho_block_2105 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 9 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h⟩

theorem morphoLiquidatePositionReachSub (hstack : R.length + 30 ≤ 1024)
    (ha : account.toNat < EVM.addressModulus) (haccount : calldataWord ee.calldata 164 = account)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2115)
      (shares :: liquidateUpdateTail id assets seized shares srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12846)
      ([positionFieldWord σ ee id account 1, shares, UInt256.ofNat 2197] ++
        liquidatePositionStoreTail σ ee id assets seized shares account srcOff len R)
      (supplyPositionMem id account mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_2115_packed (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 12 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have haddr : UInt256.land (uInt256OfByteArray (ee.calldata.readBytes (UInt256.ofNat 164).toNat 32))
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = account := by
    change UInt256.land (calldataWord ee.calldata 164) solcAddrMask = account
    rw [haccount, solcAddrMask_clean ha]
  let m1 := twoWordHashMem id (UInt256.ofNat 2) mem
  have hh1 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1 = solcMappingSlot ⟨2⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  let m2 := twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1) m1
  have hm2 : m2 = supplyPositionMem id account mem := by dsimp only [m2]; rw [hh1]; rfl
  have hh2 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (supplyPositionMem id account mem) =
      positionSlot id account := twoWordHashMem_solcMappingSlot_any _ _ _
  dsimp only [morphoBlocks.morpho_block_2115_stack, morphoBlocks.morpho_block_2115_memory] at rd1
  rw [haddr] at rd1
  change RD _ _ _ _ _
    ([UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1) σ ee) uint128Mask,
      shares, UInt256.ofNat 2197, uint128Mask,
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1,
      solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1) σ ee] ++
      liquidateUpdateTail id assets seized shares srcOff len R) m2 _ _ _ _ _ at rd1
  rw [hm2, hh2] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoLiquidatePositionStore (hstack : R.length + 30 ≤ 1024) (hperm : ee.perm = true)
    (hc : value.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2197)
      (value :: liquidatePositionStoreTail σ ee id assets seized shares account srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([shares, UInt256.ofNat 2249, UInt256.ofNat 2342] ++ liquidateMarketTail id assets seized shares srcOff len R)
      mem aw' out (storePositionPackedAccounts σ ee id account false value) k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_2197_packed (immWords := wordsOf (immStore v))
    (by change R.length + 7 + 6 ≤ 1024; omega) hperm (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _ _ _ _ _
    (sstoreAccountMap ee.codeOwner σ (positionSlot id account + UInt256.ofNat 1)
      (UInt256.lor (UInt256.land (solcSlotWordAt (positionSlot id account + UInt256.ofNat 1) σ ee)
        (UInt256.lnot uint128Mask)) (UInt256.land value uint128Mask))) _ _ at rd1
  have hc' : UInt256.land value uint128Mask = value := halfWord_low_clean value hc
  rw [hc'] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Reach

theorem morphoLiquidatePositionStatic {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw value mask slot old : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2197) ([value, mask, slot, old] ++ R)
      mem aw out σ k C) : RDstatic (deployedRuntime v) g s0 := by
  change RD _ _ _ _ _ (value :: mask :: slot :: old :: R) _ _ _ _ _ _ at h
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨2197⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨2198⟩ : UInt256), UInt8.ofNat 22, .AND, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨2199⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480), 32), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨2232⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap4 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨2233⟩ : UInt256), UInt8.ofNat 147, .SWAP4, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨2234⟩ : UInt256), UInt8.ofNat 22, .AND, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨2235⟩ : UInt256), UInt8.ofNat 23, .OR, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨2236⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  exact r8.sstoreStatic hperm (by
    immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
      (⟨2237⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MorphoBlue
