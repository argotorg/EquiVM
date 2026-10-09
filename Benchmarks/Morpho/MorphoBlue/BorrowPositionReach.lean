import Benchmarks.Morpho.MorphoBlue.BorrowMathRefine
import Benchmarks.Morpho.MorphoBlue.HealthyPriceReach
import Benchmarks.Morpho.MorphoBlue.Uint128Arithmetic
import Benchmarks.Morpho.MorphoBlue.PositionPackedWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def borrowPositionStoreTail (σ : AccountMap) (ee : ExecutionEnv) (id assets shares account receiver : UInt256)
    (R : List UInt256) : List UInt256 :=
  [uint128Mask, positionSlot id account + UInt256.ofNat 1, shares, UInt256.ofNat 3, UInt256.ofNat 32,
    solcSlotWordAt (positionSlot id account + UInt256.ofNat 1) σ ee,
    account, UInt256.ofNat 3, UInt256.ofNat 0, uint128Mask, id, account, receiver, UInt256.ofNat 128,
    solcAddrMask, assets, receiver, UInt256.ofNat 32, shares, assets] ++ R

def borrowMarketTail (id assets shares account receiver : UInt256) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat 3, UInt256.ofNat 32, UInt256.lnot uint128Mask, account, UInt256.ofNat 3, UInt256.ofNat 0,
    uint128Mask, id, account, receiver, UInt256.ofNat 128, solcAddrMask, assets, receiver,
    UInt256.ofNat 32, shares, assets] ++ R

section Reach
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem out : ByteArray} {aw id assets shares account receiver value : UInt256} {σ : AccountMap}
  {k C : Nat} {R : List UInt256}

theorem morphoBorrowPositionReachCast (hstack : R.length + 32 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8538)
      (borrowUpdateTail id assets shares account receiver R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([shares, UInt256.ofNat 8547] ++ borrowUpdateTail id assets shares account receiver R) mem aw out σ k' C' := by
  have rd := morphoBlocks.morpho_block_8538 (immWords := wordsOf (immStore v))
    (by change R.length + 8 + 9 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact ⟨_, _, rd⟩

theorem morphoBorrowPositionReachAdd (hstack : R.length + 32 ≤ 1024)
    (hc : account.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8547)
      (shares :: borrowUpdateTail id assets shares account receiver R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12664)
      ([positionFieldWord σ ee id account 1, shares, UInt256.ofNat 8596] ++
        borrowPositionStoreTail σ ee id assets shares account receiver R)
      (supplyPositionMem id account mem) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_8547_packed (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 22 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_8547_stack, morphoBlocks.morpho_block_8547_memory] at rd1
  have hmask : UInt256.land account solcAddrMask = account := solcAddrMask_clean hc
  rw [hmask] at rd1
  have hh1 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 2) mem) =
      solcMappingSlot ⟨2⟩ id := twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    ([UInt256.land (solcSlotWordAt (UInt256.ofNat 1 + keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 2) mem))
        (twoWordHashMem id (UInt256.ofNat 2) mem))) σ ee) uint128Mask,
      shares, UInt256.ofNat 8596, uint128Mask,
      UInt256.ofNat 1 + keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 2) mem))
          (twoWordHashMem id (UInt256.ofNat 2) mem)),
      shares, UInt256.ofNat 3, UInt256.ofNat 32,
      solcSlotWordAt (UInt256.ofNat 1 + keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 2) mem))
          (twoWordHashMem id (UInt256.ofNat 2) mem))) σ ee,
      account, UInt256.ofNat 3, UInt256.ofNat 0, uint128Mask, id, account, receiver, UInt256.ofNat 128,
      solcAddrMask, assets, receiver, UInt256.ofNat 32, shares, assets] ++ R)
    (twoWordHashMem account (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 2) mem))
      (twoWordHashMem id (UInt256.ofNat 2) mem)) _ _ _ _ _ at rd1
  rw [hh1] at rd1
  change RD _ _ _ _ _
    ([UInt256.land (solcSlotWordAt (UInt256.ofNat 1 + keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (supplyPositionMem id account mem)) σ ee) uint128Mask,
      shares, UInt256.ofNat 8596, uint128Mask,
      UInt256.ofNat 1 + keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (supplyPositionMem id account mem),
      shares, UInt256.ofNat 3, UInt256.ofNat 32,
      solcSlotWordAt (UInt256.ofNat 1 + keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (supplyPositionMem id account mem)) σ ee,
      account, UInt256.ofNat 3, UInt256.ofNat 0, uint128Mask, id, account, receiver, UInt256.ofNat 128,
      solcAddrMask, assets, receiver, UInt256.ofNat 32, shares, assets] ++ R)
    (supplyPositionMem id account mem) _ _ _ _ _ at rd1
  rw [supplyPositionMem_hash, u256_add_comm (UInt256.ofNat 1)] at rd1
  exact ⟨a1, k1, C1, rd1⟩

theorem morphoBorrowPositionStore (hstack : R.length + 32 ≤ 1024) (hperm : ee.perm = true)
    (hc : value.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8596)
      (value :: borrowPositionStoreTail σ ee id assets shares account receiver R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([shares, UInt256.ofNat 8645] ++ borrowMarketTail id assets shares account receiver R)
      mem aw' out (storePositionPackedAccounts σ ee id account false value) k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_8596_packed (immWords := wordsOf (immStore v))
    (by change R.length + 14 + 8 ≤ 1024; omega) hperm
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _ _ _ _ _
    (sstoreAccountMap ee.codeOwner σ (positionSlot id account + UInt256.ofNat 1)
      (UInt256.lor (UInt256.land (solcSlotWordAt (positionSlot id account + UInt256.ofNat 1) σ ee)
        (UInt256.lnot uint128Mask)) (UInt256.land value uint128Mask))) _ _ at rd1
  have hc' : UInt256.land value uint128Mask = value := halfWord_low_clean value hc
  rw [hc'] at rd1
  exact ⟨a1, k1, C1, rd1⟩

end Reach
theorem morphoBorrowPositionStatic {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw value mask slot x y z old : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8596) ([value, mask, slot, x, y, z, old] ++ R)
      mem aw out σ k C) : RDstatic (deployedRuntime v) g s0 := by
  change RD _ _ _ _ _ (value :: mask :: slot :: x :: y :: z :: old :: R) _ _ _ _ _ _ at h
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8596⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8597⟩ : UInt256), UInt8.ofNat 22, .AND, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8598⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907852929702298719625575994209400481361428480), 32), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r4 := r3.dup1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8631⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.swap7 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8632⟩ : UInt256), UInt8.ofNat 150, .SWAP7, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8633⟩ : UInt256), UInt8.ofNat 22, .AND, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8634⟩ : UInt256), UInt8.ofNat 23, .OR, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8635⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  exact r8.sstoreStatic hperm (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8636⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MorphoBlue
