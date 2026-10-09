import Benchmarks.Morpho.MorphoBlue.RepayMathRefine
import Benchmarks.Morpho.MorphoBlue.SupplyPositionRefine
import Benchmarks.Morpho.MorphoBlue.Uint128Subtraction
import Benchmarks.Morpho.MorphoBlue.PositionPackedWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def repayPositionStoreTail (σ : AccountMap) (ee : ExecutionEnv) (id assets shares account srcOff len : UInt256)
    (R : List UInt256) : List UInt256 :=
  [uint128Mask, positionSlot id account + UInt256.ofNat 1, uint128Mask,
    solcSlotWordAt (positionSlot id account + UInt256.ofNat 1) σ ee,
    UInt256.ofNat 3, id, account, srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32,
    shares, assets, solcAddrMask] ++ R

def repayMarketTail (id assets shares account srcOff len : UInt256) (R : List UInt256) : List UInt256 :=
  [uint128Mask, UInt256.lnot uint128Mask, UInt256.ofNat 3, id, account, srcOff, len,
    UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32, shares, assets, solcAddrMask] ++ R

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem out : ByteArray} {aw id assets shares account srcOff len value : UInt256} {σ : AccountMap}
  {k C : Nat} {R : List UInt256}

theorem morphoRepayPositionReachCast (hstack : R.length + 28 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10609)
      (repayUpdateTail id assets shares account srcOff len R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([shares, UInt256.ofNat 10618] ++ repayUpdateTail id assets shares account srcOff len R) mem aw out σ k' C' := by
  have rd := morphoBlocks.morpho_block_10609 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 13 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact ⟨_, _, rd⟩

theorem morphoRepayPositionReachSub (hstack : R.length + 28 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10618)
      (shares :: repayUpdateTail id assets shares account srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12846)
      ([positionFieldWord σ ee id account 1, shares, UInt256.ofNat 10657] ++
        repayPositionStoreTail σ ee id assets shares account srcOff len R)
      (supplyPositionMem id account mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_10618_packed (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 16 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  let m1 := twoWordHashMem id (UInt256.ofNat 2) mem
  have hh1 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1 = solcMappingSlot ⟨2⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  let m2 := twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1) m1
  have hm2 : m2 = supplyPositionMem id account mem := by dsimp only [m2]; rw [hh1]; rfl
  have hh2 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (supplyPositionMem id account mem) =
      positionSlot id account := twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    ([UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1) σ ee) uint128Mask,
      shares, UInt256.ofNat 10657, uint128Mask,
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1, uint128Mask,
      solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2 + UInt256.ofNat 1) σ ee,
      UInt256.ofNat 3, id, account, srcOff, len, UInt256.ofNat 0, UInt256.ofNat 128, UInt256.ofNat 32,
      shares, assets, solcAddrMask] ++ R) m2 _ _ _ _ _ at rd1
  rw [hm2, hh2] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoRepayPositionStore (hstack : R.length + 28 ≤ 1024) (hperm : ee.perm = true)
    (hc : value.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10657)
      (value :: repayPositionStoreTail σ ee id assets shares account srcOff len R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([shares, UInt256.ofNat 10709, UInt256.ofNat 10736] ++ repayMarketTail id assets shares account srcOff len R)
      mem aw' out (storePositionPackedAccounts σ ee id account false value) k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_10657_packed (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 15 ≤ 1024; omega) hperm
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _ _ _ _ _
    (sstoreAccountMap ee.codeOwner σ (positionSlot id account + UInt256.ofNat 1)
      (UInt256.lor (UInt256.land (solcSlotWordAt (positionSlot id account + UInt256.ofNat 1) σ ee)
        (UInt256.lnot uint128Mask)) (UInt256.land value uint128Mask))) _ _ at rd1
  have hc' : UInt256.land value uint128Mask = value := halfWord_low_clean value hc
  rw [hc'] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Reach

theorem morphoRepayPositionStatic {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw value mask slot old : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10657) ([value, mask, slot, mask, old] ++ R)
      mem aw out σ k C) : RDstatic (deployedRuntime v) g s0 := by
  change RD _ _ _ _ _ (value :: mask :: slot :: mask :: old :: R) _ _ _ _ _ _ at h
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v), (⟨10657⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.and (by immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v), (⟨10658⟩ : UInt256), UInt8.ofNat 22, .AND, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v), (⟨10659⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480), 32), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v), (⟨10692⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap5 (by immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v), (⟨10693⟩ : UInt256), UInt8.ofNat 148, .SWAP5, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.and (by immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v), (⟨10694⟩ : UInt256), UInt8.ofNat 22, .AND, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.or (by immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v), (⟨10695⟩ : UInt256), UInt8.ofNat 23, .OR, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap1 (by immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v), (⟨10696⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  exact r8.sstoreStatic hperm (by
    immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
      (⟨10697⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MorphoBlue
