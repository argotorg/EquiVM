import Benchmarks.UniswapV3Pool.BurnPositionUpdateTokensOwedPacking
import Benchmarks.UniswapV3Pool.BurnPositionUpdateTokensOwedStore
import Benchmarks.UniswapV3Pool.BurnPositionUpdateSlowPostReturn

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

abbrev burnTickGetBelow0Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  if tickSpacingSint24Value (slot0TickRawWord σ I) >=
      tickSpacingSint24Value (burnTickLowerWord I) then
    burnTickGetLowerFeeGrowthOutside0Word σ I
  else
    UInt256.sub (solcSlotWord σ I ⟨1⟩) (burnTickGetLowerFeeGrowthOutside0Word σ I)

abbrev burnTickGetBelow1Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  if tickSpacingSint24Value (slot0TickRawWord σ I) >=
      tickSpacingSint24Value (burnTickLowerWord I) then
    burnTickGetLowerFeeGrowthOutside1Word σ I
  else
    UInt256.sub (solcSlotWord σ I ⟨2⟩) (burnTickGetLowerFeeGrowthOutside1Word σ I)

abbrev burnTickGetAbove0Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  if tickSpacingSint24Value (slot0TickRawWord σ I) <
      tickSpacingSint24Value (burnTickUpperWord I) then
    burnTickGetUpperFeeGrowthOutside0Word σ I
  else
    UInt256.sub (solcSlotWord σ I ⟨1⟩) (burnTickGetUpperFeeGrowthOutside0Word σ I)

abbrev burnTickGetAbove1Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  if tickSpacingSint24Value (slot0TickRawWord σ I) <
      tickSpacingSint24Value (burnTickUpperWord I) then
    burnTickGetUpperFeeGrowthOutside1Word σ I
  else
    UInt256.sub (solcSlotWord σ I ⟨2⟩) (burnTickGetUpperFeeGrowthOutside1Word σ I)

abbrev burnTickGetInside0Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (UInt256.sub (solcSlotWord σ I ⟨1⟩) (burnTickGetBelow0Word σ I))
    (burnTickGetAbove0Word σ I)

abbrev burnTickGetInside1Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (UInt256.sub (solcSlotWord σ I ⟨2⟩) (burnTickGetBelow1Word σ I))
    (burnTickGetAbove1Word σ I)

theorem solcSlotWord_eq_of_accountMapEquiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) (I : ExecutionEnv) (slot : UInt256) :
    solcSlotWord σ I slot = solcSlotWord τ I slot := by
  have hslot := accountMapEquiv_storage_findD h I.codeOwner slot (⟨0⟩ : UInt256)
  simpa [solcSlotWord] using hslot

theorem sstoreAccountMap_find?_same_exists
    {σ : AccountMap} {addr : AccountAddress} {slot val : UInt256}
    (h : ∃ acc, σ.find? addr = some acc) :
    ∃ acc, (sstoreAccountMap addr σ slot val).find? addr = some acc := by
  rcases h with ⟨acc, hacc⟩
  refine ⟨if val == default then {acc with storage := acc.storage.erase slot}
    else {acc with storage := acc.storage.insert slot val}, ?_⟩
  simp only [sstoreAccountMap, hacc, Option.option]
  rw [accountMap_find_insert_self]

theorem storageStore_codeOwner_find?_exists
    {evm : EVM.State} (h : ∃ acc, evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (slot val : UInt256) :
    ∃ acc,
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val).accountMap.find?
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val).executionEnv.codeOwner =
        some acc := by
  simpa [storageStore_accountMap, storageStore_executionEnv] using
    sstoreAccountMap_find?_same_exists (σ := evm.accountMap)
      (addr := evm.executionEnv.codeOwner) (slot := slot) (val := val) h

theorem accountMap_find?_codeOwner_exists_of_burnUnlockedByte_ne_zero
    {σ : AccountMap} {I : ExecutionEnv} (h : burnUnlockedByte σ I ≠ ⟨0⟩) :
    ∃ acc, σ.find? I.codeOwner = some acc := by
  by_cases hmissing : σ.find? I.codeOwner = none
  · exfalso
    apply h
    simp [burnUnlockedByte, solcSlotWord, hmissing, burnUint8Mask, burnUnlockedShift,
      Option.option]
    native_decide
  · cases hfind : σ.find? I.codeOwner with
    | none => exact False.elim (hmissing hfind)
    | some acc => exact ⟨acc, rfl⟩

theorem slot0TickRawWord_eq_of_accountMapEquiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) (I : ExecutionEnv) :
    slot0TickRawWord σ I = slot0TickRawWord τ I := by
  rw [slot0TickRawWord, slot0SlotWord, solcSlotWord_eq_of_accountMapEquiv h I ⟨0⟩]

theorem slot0TickReturnWord_eq_of_accountMapEquiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) (I : ExecutionEnv) :
    slot0TickReturnWord σ I = slot0TickReturnWord τ I := by
  rw [slot0TickReturnWord, slot0SlotWord, solcSlotWord_eq_of_accountMapEquiv h I ⟨0⟩]

theorem burnTickGetLowerFeeGrowthOutside0Word_eq_of_accountMapEquiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) (I : ExecutionEnv) :
    burnTickGetLowerFeeGrowthOutside0Word σ I =
      burnTickGetLowerFeeGrowthOutside0Word τ I := by
  rw [burnTickGetLowerFeeGrowthOutside0Word,
    solcSlotWord_eq_of_accountMapEquiv h I (burnTickGetLowerBaseSlot I + ⟨1⟩)]

theorem burnTickGetLowerFeeGrowthOutside1Word_eq_of_accountMapEquiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) (I : ExecutionEnv) :
    burnTickGetLowerFeeGrowthOutside1Word σ I =
      burnTickGetLowerFeeGrowthOutside1Word τ I := by
  rw [burnTickGetLowerFeeGrowthOutside1Word,
    solcSlotWord_eq_of_accountMapEquiv h I (burnTickGetLowerBaseSlot I + ⟨2⟩)]

theorem burnTickGetUpperFeeGrowthOutside0Word_eq_of_accountMapEquiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) (I : ExecutionEnv) :
    burnTickGetUpperFeeGrowthOutside0Word σ I =
      burnTickGetUpperFeeGrowthOutside0Word τ I := by
  rw [burnTickGetUpperFeeGrowthOutside0Word,
    solcSlotWord_eq_of_accountMapEquiv h I (burnTickGetUpperBaseSlot I + ⟨1⟩)]

theorem burnTickGetUpperFeeGrowthOutside1Word_eq_of_accountMapEquiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) (I : ExecutionEnv) :
    burnTickGetUpperFeeGrowthOutside1Word σ I =
      burnTickGetUpperFeeGrowthOutside1Word τ I := by
  rw [burnTickGetUpperFeeGrowthOutside1Word,
    solcSlotWord_eq_of_accountMapEquiv h I (burnTickGetUpperBaseSlot I + ⟨2⟩)]

theorem burnTickGetBelow0Word_eq_of_accountMapEquiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) (I : ExecutionEnv) :
    burnTickGetBelow0Word σ I = burnTickGetBelow0Word τ I := by
  unfold burnTickGetBelow0Word
  rw [slot0TickRawWord_eq_of_accountMapEquiv h I]
  rw [burnTickGetLowerFeeGrowthOutside0Word_eq_of_accountMapEquiv h I]
  rw [solcSlotWord_eq_of_accountMapEquiv h I ⟨1⟩]

theorem burnTickGetBelow1Word_eq_of_accountMapEquiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) (I : ExecutionEnv) :
    burnTickGetBelow1Word σ I = burnTickGetBelow1Word τ I := by
  unfold burnTickGetBelow1Word
  rw [slot0TickRawWord_eq_of_accountMapEquiv h I]
  rw [burnTickGetLowerFeeGrowthOutside1Word_eq_of_accountMapEquiv h I]
  rw [solcSlotWord_eq_of_accountMapEquiv h I ⟨2⟩]

theorem burnTickGetAbove0Word_eq_of_accountMapEquiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) (I : ExecutionEnv) :
    burnTickGetAbove0Word σ I = burnTickGetAbove0Word τ I := by
  unfold burnTickGetAbove0Word
  rw [slot0TickRawWord_eq_of_accountMapEquiv h I]
  rw [burnTickGetUpperFeeGrowthOutside0Word_eq_of_accountMapEquiv h I]
  rw [solcSlotWord_eq_of_accountMapEquiv h I ⟨1⟩]

theorem burnTickGetAbove1Word_eq_of_accountMapEquiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) (I : ExecutionEnv) :
    burnTickGetAbove1Word σ I = burnTickGetAbove1Word τ I := by
  unfold burnTickGetAbove1Word
  rw [slot0TickRawWord_eq_of_accountMapEquiv h I]
  rw [burnTickGetUpperFeeGrowthOutside1Word_eq_of_accountMapEquiv h I]
  rw [solcSlotWord_eq_of_accountMapEquiv h I ⟨2⟩]

theorem burnTickGetInside0Word_eq_of_accountMapEquiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) (I : ExecutionEnv) :
    burnTickGetInside0Word σ I = burnTickGetInside0Word τ I := by
  rw [burnTickGetInside0Word, solcSlotWord_eq_of_accountMapEquiv h I ⟨1⟩,
    burnTickGetBelow0Word_eq_of_accountMapEquiv h I,
    burnTickGetAbove0Word_eq_of_accountMapEquiv h I]

theorem burnTickGetInside1Word_eq_of_accountMapEquiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) (I : ExecutionEnv) :
    burnTickGetInside1Word σ I = burnTickGetInside1Word τ I := by
  rw [burnTickGetInside1Word, solcSlotWord_eq_of_accountMapEquiv h I ⟨2⟩,
    burnTickGetBelow1Word_eq_of_accountMapEquiv h I,
    burnTickGetAbove1Word_eq_of_accountMapEquiv h I]

theorem burnPositionUpdateSourceTokensOwed0Int_eq_of_accountMapEquiv
    {σ τ : AccountMap} (h : accountMapEquiv σ τ) (I : ExecutionEnv)
    (feeGrowthInside0X128 : Int) :
    burnPositionUpdateSourceTokensOwed0Int σ I feeGrowthInside0X128 =
      burnPositionUpdateSourceTokensOwed0Int τ I feeGrowthInside0X128 := by
  unfold burnPositionUpdateSourceTokensOwed0Int
  rw [burnPositionUpdateSourceFeeGrowthInside0LastInt,
    solcSlotWord_eq_of_accountMapEquiv h I
      (positionsBase (burnPositionKeyKey I) + ⟨1⟩)]
  rw [burnPositionUpdateSourceLiquidityInt,
    solcSlotWord_eq_of_accountMapEquiv h I (positionsBase (burnPositionKeyKey I))]

theorem burnPositionUpdateSourceTokensOwed1Int_eq_of_accountMapEquiv
    {σ τ : AccountMap} (h : accountMapEquiv σ τ) (I : ExecutionEnv)
    (feeGrowthInside1X128 : Int) :
    burnPositionUpdateSourceTokensOwed1Int σ I feeGrowthInside1X128 =
      burnPositionUpdateSourceTokensOwed1Int τ I feeGrowthInside1X128 := by
  unfold burnPositionUpdateSourceTokensOwed1Int
  rw [burnPositionUpdateSourceFeeGrowthInside1LastInt,
    solcSlotWord_eq_of_accountMapEquiv h I
      (positionsBase (burnPositionKeyKey I) + ⟨2⟩)]
  rw [burnPositionUpdateSourceLiquidityInt,
    solcSlotWord_eq_of_accountMapEquiv h I (positionsBase (burnPositionKeyKey I))]

theorem burnTickGetBelow0Int_eq_word (σ : AccountMap) (I : ExecutionEnv) :
    burnTickGetBelow0Int σ I = Int.ofNat (burnTickGetBelow0Word σ I).toNat := by
  unfold burnTickGetBelow0Int burnTickGetBelow0Word
  split
  · rfl
  · exact burnWordSubInt_ofNat_toNat_eq (solcSlotWord σ I ⟨1⟩)
      (burnTickGetLowerFeeGrowthOutside0Word σ I)

theorem burnTickGetBelow1Int_eq_word (σ : AccountMap) (I : ExecutionEnv) :
    burnTickGetBelow1Int σ I = Int.ofNat (burnTickGetBelow1Word σ I).toNat := by
  unfold burnTickGetBelow1Int burnTickGetBelow1Word
  split
  · rfl
  · exact burnWordSubInt_ofNat_toNat_eq (solcSlotWord σ I ⟨2⟩)
      (burnTickGetLowerFeeGrowthOutside1Word σ I)

theorem burnTickGetAbove0Int_eq_word (σ : AccountMap) (I : ExecutionEnv) :
    burnTickGetAbove0Int σ I = Int.ofNat (burnTickGetAbove0Word σ I).toNat := by
  unfold burnTickGetAbove0Int burnTickGetAbove0Word
  split
  · rfl
  · exact burnWordSubInt_ofNat_toNat_eq (solcSlotWord σ I ⟨1⟩)
      (burnTickGetUpperFeeGrowthOutside0Word σ I)

theorem burnTickGetAbove1Int_eq_word (σ : AccountMap) (I : ExecutionEnv) :
    burnTickGetAbove1Int σ I = Int.ofNat (burnTickGetAbove1Word σ I).toNat := by
  unfold burnTickGetAbove1Int burnTickGetAbove1Word
  split
  · rfl
  · exact burnWordSubInt_ofNat_toNat_eq (solcSlotWord σ I ⟨2⟩)
      (burnTickGetUpperFeeGrowthOutside1Word σ I)

theorem burnTickGetInside0Value_eq_word (σ : AccountMap) (I : ExecutionEnv) :
    burnTickGetInside0Value σ I = .int (Int.ofNat (burnTickGetInside0Word σ I).toNat) := by
  simp only [burnTickGetInside0Value, burnTickGetInside0Int]
  rw [burnTickGetBelow0Int_eq_word σ I, burnTickGetAbove0Int_eq_word σ I]
  change
    Value.int
      (burnWordSubInt
        (burnWordSubInt (Int.ofNat (solcSlotWord σ I ⟨1⟩).toNat)
          (Int.ofNat (burnTickGetBelow0Word σ I).toNat))
        (Int.ofNat (burnTickGetAbove0Word σ I).toNat)) =
      Value.int (Int.ofNat (burnTickGetInside0Word σ I).toNat)
  rw [burnWordSubInt_ofNat_toNat_eq (solcSlotWord σ I ⟨1⟩)
    (burnTickGetBelow0Word σ I)]
  rw [burnWordSubInt_ofNat_toNat_eq
    (UInt256.sub (solcSlotWord σ I ⟨1⟩) (burnTickGetBelow0Word σ I))
    (burnTickGetAbove0Word σ I)]

theorem burnTickGetInside1Value_eq_word (σ : AccountMap) (I : ExecutionEnv) :
    burnTickGetInside1Value σ I = .int (Int.ofNat (burnTickGetInside1Word σ I).toNat) := by
  simp only [burnTickGetInside1Value, burnTickGetInside1Int]
  rw [burnTickGetBelow1Int_eq_word σ I, burnTickGetAbove1Int_eq_word σ I]
  change
    Value.int
      (burnWordSubInt
        (burnWordSubInt (Int.ofNat (solcSlotWord σ I ⟨2⟩).toNat)
          (Int.ofNat (burnTickGetBelow1Word σ I).toNat))
        (Int.ofNat (burnTickGetAbove1Word σ I).toNat)) =
      Value.int (Int.ofNat (burnTickGetInside1Word σ I).toNat)
  rw [burnWordSubInt_ofNat_toNat_eq (solcSlotWord σ I ⟨2⟩)
    (burnTickGetBelow1Word σ I)]
  rw [burnWordSubInt_ofNat_toNat_eq
    (UInt256.sub (solcSlotWord σ I ⟨2⟩) (burnTickGetBelow1Word σ I))
    (burnTickGetAbove1Word σ I)]

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnFeeGrowthInsideEntryReturnConcrete {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord ee) <
        tickSpacingSint24Value (burnTickUpperWord ee))
    (h : RD code ee g s0 ⟨21387⟩
      (solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        burnPositionBaseSlotWord σ ee :: slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee ::
        burnTickLowerCleanWord ee :: ret :: R)
      (burnPositionKeyMappingMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 82 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨19510⟩
      (burnTickGetInside1Word σ ee :: burnTickGetInside0Word σ ee ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        burnPositionBaseSlotWord σ ee :: slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee ::
        burnTickLowerCleanWord ee :: ret :: R)
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  let tail : List UInt256 :=
    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
    solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
    burnPositionBaseSlotWord σ ee :: slot0TickReturnWord σ ee ::
    UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
    UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
    UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
    UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
    burnAmountCleanWord ee :: burnTickUpperCleanWord ee ::
    burnTickLowerCleanWord ee :: ret :: R
  by_cases hCurrentBelow :
      tickSpacingSint24Value (slot0TickRawWord σ ee) <
        tickSpacingSint24Value (burnTickLowerWord ee)
  · obtain ⟨_, _, hrdLower⟩ :=
      uniswapV3PoolBurnFeeGrowthInsideLowerBelowToUpperJoin
        (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
        (ret := ret) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
        hpatch hCurrentBelow h (by omega)
    have hCurrentUpper :
        tickSpacingSint24Value (slot0TickRawWord σ ee) <
          tickSpacingSint24Value (burnTickUpperWord ee) :=
      lt_trans hCurrentBelow htickLt
    obtain ⟨_, _, hrdUpper⟩ :=
      uniswapV3PoolBurnFeeGrowthInsideUpperInsideFromJoin
        (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
        (ret := ret) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
        hpatch hCurrentUpper hrdLower (by omega)
    obtain ⟨_, _, hrdReturn⟩ :=
      uniswapV3PoolBurnFeeGrowthInsideJoinReturn (v := v) (code := code)
        (ee := ee) (g := g) (s0 := s0) (ret := ⟨19510⟩)
        (rdata := rdata) (acc := (cA, σ)) hpatch
        (uniswapV3PoolJumpDestPatched19510 hpatch) hrdUpper
        (by simp only [List.length_cons] at hov ⊢; omega)
    have hnotGeLower :
        ¬ tickSpacingSint24Value (slot0TickRawWord σ ee) >=
          tickSpacingSint24Value (burnTickLowerWord ee) := by
      exact not_le_of_gt hCurrentBelow
    exact ⟨_, _, by simpa [tail, burnTickGetInside1Word, burnTickGetInside0Word,
      burnTickGetBelow1Word, burnTickGetBelow0Word, burnTickGetAbove1Word,
      burnTickGetAbove0Word, hnotGeLower, hCurrentUpper,
      burnTickGetLowerFeeGrowthOutside0Word, burnTickGetLowerFeeGrowthOutside1Word,
      burnTickGetUpperFeeGrowthOutside0Word, burnTickGetUpperFeeGrowthOutside1Word,
      burnTickGetLowerBaseSlot, burnTickGetUpperBaseSlot, burnTickGetLowerKey,
      burnTickGetUpperKey, burnTickLowerFeeGrowthOutside0Word,
      burnTickLowerFeeGrowthOutside1Word, burnTickUpperFeeGrowthOutside0Word,
      burnTickUpperFeeGrowthOutside1Word, burnTickLowerFeeGrowthOutside0Slot,
      burnTickLowerFeeGrowthOutside1Slot, burnTickUpperFeeGrowthOutside0Slot,
      burnTickUpperFeeGrowthOutside1Slot, burnTickLowerFeeGrowthBaseSlot,
      burnTickUpperFeeGrowthBaseSlot, burnTickLowerFeeGrowthKey,
      burnTickUpperFeeGrowthKey, burnTickLowerFeeGrowthCompareWord,
      burnTickUpperFeeGrowthCompareWord, ticksBase, mapSlot, solcMappingSlot,
      keyValueToWord, wordOfInt_sint24Value_eq_signextend_two,
      signextend_two_tickSpacing_idempotent, u256_add_comm] using hrdReturn⟩
  · obtain ⟨_, _, hrdLower⟩ :=
      uniswapV3PoolBurnFeeGrowthInsideLowerNotBelowToUpperJoin
        (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
        (ret := ret) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
        hpatch hCurrentBelow h (by omega)
    have hgeLower :
        tickSpacingSint24Value (slot0TickRawWord σ ee) >=
          tickSpacingSint24Value (burnTickLowerWord ee) := by
      exact le_of_not_gt hCurrentBelow
    by_cases hCurrentUpper :
        tickSpacingSint24Value (slot0TickRawWord σ ee) <
          tickSpacingSint24Value (burnTickUpperWord ee)
    · obtain ⟨_, _, hrdUpper⟩ :=
        uniswapV3PoolBurnFeeGrowthInsideUpperInsideFromJoin
          (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
          (ret := ret) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
          hpatch hCurrentUpper hrdLower (by omega)
      obtain ⟨_, _, hrdReturn⟩ :=
        uniswapV3PoolBurnFeeGrowthInsideJoinReturn (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ret := ⟨19510⟩)
          (rdata := rdata) (acc := (cA, σ)) hpatch
          (uniswapV3PoolJumpDestPatched19510 hpatch) hrdUpper
          (by simp only [List.length_cons] at hov ⊢; omega)
      exact ⟨_, _, by simpa [tail, burnTickGetInside1Word, burnTickGetInside0Word,
        burnTickGetBelow1Word, burnTickGetBelow0Word, burnTickGetAbove1Word,
        burnTickGetAbove0Word, hgeLower, hCurrentUpper,
        burnTickGetLowerFeeGrowthOutside0Word, burnTickGetLowerFeeGrowthOutside1Word,
        burnTickGetUpperFeeGrowthOutside0Word, burnTickGetUpperFeeGrowthOutside1Word,
        burnTickGetLowerBaseSlot, burnTickGetUpperBaseSlot, burnTickGetLowerKey,
        burnTickGetUpperKey, burnTickLowerFeeGrowthOutside0Word,
        burnTickLowerFeeGrowthOutside1Word, burnTickUpperFeeGrowthOutside0Word,
        burnTickUpperFeeGrowthOutside1Word, burnTickLowerFeeGrowthOutside0Slot,
        burnTickLowerFeeGrowthOutside1Slot, burnTickUpperFeeGrowthOutside0Slot,
        burnTickUpperFeeGrowthOutside1Slot, burnTickLowerFeeGrowthBaseSlot,
        burnTickUpperFeeGrowthBaseSlot, burnTickLowerFeeGrowthKey,
        burnTickUpperFeeGrowthKey, burnTickLowerFeeGrowthCompareWord,
        burnTickUpperFeeGrowthCompareWord, ticksBase, mapSlot, solcMappingSlot,
        keyValueToWord, wordOfInt_sint24Value_eq_signextend_two,
        signextend_two_tickSpacing_idempotent, u256_add_comm] using hrdReturn⟩
    · obtain ⟨_, _, hrdUpper⟩ :=
        uniswapV3PoolBurnFeeGrowthInsideUpperNotInsideFromJoin
          (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
          (ret := ret) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
          hpatch hCurrentUpper hrdLower (by omega)
      obtain ⟨_, _, hrdReturn⟩ :=
        uniswapV3PoolBurnFeeGrowthInsideJoinReturn (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ret := ⟨19510⟩)
          (rdata := rdata) (acc := (cA, σ)) hpatch
          (uniswapV3PoolJumpDestPatched19510 hpatch) hrdUpper
          (by simp only [List.length_cons] at hov ⊢; omega)
      exact ⟨_, _, by simpa [tail, burnTickGetInside1Word, burnTickGetInside0Word,
        burnTickGetBelow1Word, burnTickGetBelow0Word, burnTickGetAbove1Word,
        burnTickGetAbove0Word, hgeLower, hCurrentUpper,
        burnTickGetLowerFeeGrowthOutside0Word, burnTickGetLowerFeeGrowthOutside1Word,
        burnTickGetUpperFeeGrowthOutside0Word, burnTickGetUpperFeeGrowthOutside1Word,
        burnTickGetLowerBaseSlot, burnTickGetUpperBaseSlot, burnTickGetLowerKey,
        burnTickGetUpperKey, burnTickLowerFeeGrowthOutside0Word,
        burnTickLowerFeeGrowthOutside1Word, burnTickUpperFeeGrowthOutside0Word,
        burnTickUpperFeeGrowthOutside1Word, burnTickLowerFeeGrowthOutside0Slot,
        burnTickLowerFeeGrowthOutside1Slot, burnTickUpperFeeGrowthOutside0Slot,
        burnTickUpperFeeGrowthOutside1Slot, burnTickLowerFeeGrowthBaseSlot,
        burnTickUpperFeeGrowthBaseSlot, burnTickLowerFeeGrowthKey,
        burnTickUpperFeeGrowthKey, burnTickLowerFeeGrowthCompareWord,
        burnTickUpperFeeGrowthCompareWord, ticksBase, mapSlot, solcMappingSlot,
        keyValueToWord, wordOfInt_sint24Value_eq_signextend_two,
        signextend_two_tickSpacing_idempotent, u256_add_comm] using hrdReturn⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnZeroDeltaPositionUpdateToMulDivReturnConcrete
    {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hperm : ee.perm = true)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord ee) <
        tickSpacingSint24Value (burnTickUpperWord ee))
    (hzero : burnAmountCleanWord ee = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee)) ≠ ⟨0⟩)
    (hprod0 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub (burnTickGetInside0Word σ ee)
            (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed
            (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee))) = ⟨0⟩)
    (hprod1 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub (burnTickGetInside1Word σ ee)
            (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee + (⟨2⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed
            (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee))) = ⟨0⟩)
    (h : RD code ee g s0 ⟨21387⟩
      (solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        burnPositionBaseSlotWord σ ee :: slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee ::
        burnTickLowerCleanWord ee :: ret :: R)
      (burnPositionKeyMappingMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 82 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21861⟩
      (UInt256.div
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub (burnTickGetInside1Word σ ee)
              (solcSlotWord σ ee
                (burnPositionBaseSlotWord σ ee + (⟨2⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed
              (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee))))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ::
        UInt256.div
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub (burnTickGetInside0Word σ ee)
              (solcSlotWord σ ee
                (burnPositionBaseSlotWord σ ee + (⟨1⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed
              (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee))))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ::
        burnPositionUpdateSlot0Packed
          (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee)) ::
        burnPositionKeyNewFreePtrWord ::
        burnTickGetInside1Word σ ee :: burnTickGetInside0Word σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        burnPositionBaseSlotWord σ ee :: ⟨19527⟩ ::
        burnTickGetInside1Word σ ee :: burnTickGetInside0Word σ ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        burnPositionBaseSlotWord σ ee :: slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee ::
        burnTickLowerCleanWord ee :: ret :: R)
      (burnPositionUpdateMem5 σ ee
        (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee))
        (burnPositionBaseSlotWord σ ee))
      (UInt256.ofNat 22) rdata
      (cA, sstoreAccountMap ee.codeOwner
        (sstoreAccountMap ee.codeOwner σ
          (burnPositionBaseSlotWord σ ee + (⟨1⟩ : UInt256))
          (burnTickGetInside0Word σ ee))
        (burnPositionBaseSlotWord σ ee + (⟨2⟩ : UInt256))
        (burnTickGetInside1Word σ ee)) k' C' := by
  let inside1 := burnTickGetInside1Word σ ee
  let inside0 := burnTickGetInside0Word σ ee
  let posBase := burnPositionBaseSlotWord σ ee
  let delta := UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee))
  let postFreeR : List UInt256 :=
    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
    burnAmountCleanWord ee :: burnTickUpperCleanWord ee ::
    burnTickLowerCleanWord ee :: ret :: R
  let tail : List UInt256 :=
    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
    solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
    posBase :: slot0TickReturnWord σ ee ::
    delta ::
    UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
    UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
    UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ :: postFreeR
  obtain ⟨_, _, hrdReturn⟩ :=
    uniswapV3PoolBurnFeeGrowthInsideEntryReturnConcrete
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (ret := ret) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch htickLt h (by omega)
  obtain ⟨_, _, hrdEntry⟩ :=
    uniswapV3PoolBurnFeeGrowthInsideEnterPositionUpdate
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0)
      (z0 := ⟨0⟩) (z1 := ⟨0⟩) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase := posBase) (tick := slot0TickReturnWord σ ee)
      (delta := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR)
      hpatch
      (by simpa [inside1, inside0, posBase, delta] using hrdReturn)
      (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdSlot0⟩ :=
    uniswapV3PoolBurnPositionUpdateLoadSlot0
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdEntry (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdPacked⟩ :=
    uniswapV3PoolBurnPositionUpdateStoreSlot0Packed
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (pos0 := solcSlotWord σ ee posBase)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdSlot0 (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdFee0⟩ :=
    uniswapV3PoolBurnPositionUpdateStoreFeeGrowthInside0Last
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch (by simpa [inside1, inside0, posBase, delta] using hrdPacked)
      (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdFee1⟩ :=
    uniswapV3PoolBurnPositionUpdateStoreFeeGrowthInside1Last
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdFee0 (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdTokens0⟩ :=
    uniswapV3PoolBurnPositionUpdateStoreTokensOwed0
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdFee1 (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdTokens1⟩ :=
    uniswapV3PoolBurnPositionUpdateStoreTokensOwed1
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdTokens0 (by simp [postFreeR] at hov ⊢; omega)
  have hdelta : UInt256.signextend ⟨15⟩ delta = ⟨0⟩ := by
    dsimp [delta]
    rw [hzero]
    native_decide
  obtain ⟨_, _, hrdFallthrough⟩ :=
    uniswapV3PoolBurnPositionUpdateLiquidityDeltaZeroFallthrough
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hdelta hrdTokens1 (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdNonzero⟩ :=
    uniswapV3PoolBurnPositionUpdateLiquidityNonzeroJump
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hliq hrdFallthrough (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdReload⟩ :=
    uniswapV3PoolBurnPositionUpdateReloadLiquidity
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdNonzero (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrd13017⟩ :=
    uniswapV3PoolBurnPositionUpdateStartMulDiv0
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdReload (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrd21861⟩ :=
    uniswapV3PoolBurnPositionUpdateMulDivsProd1ZeroStoreFeeGrowthLast
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hperm hrd13017
      (by simpa [inside0, posBase] using hprod0)
      (by simpa [inside1, posBase] using hprod1)
      hdelta (by simp [postFreeR] at hov ⊢; omega)
  exact ⟨_, _, by simpa [inside1, inside0, posBase, delta, postFreeR, tail] using hrd21861⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnZeroDeltaPositionUpdateToMulDivReturnConcreteSlowToken1
    {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hperm : ee.perm = true)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord ee) <
        tickSpacingSint24Value (burnTickUpperWord ee))
    (hzero : burnAmountCleanWord ee = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee)) ≠ ⟨0⟩)
    (hprod0 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub (burnTickGetInside0Word σ ee)
            (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee + (⟨1⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed
            (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee))) = ⟨0⟩)
    (hprod1 :
      uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub (burnTickGetInside1Word σ ee)
            (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee + (⟨2⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed
            (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee))) ≠ ⟨0⟩)
    (hden :
      UInt256.gt (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
        (uniswapV3PoolFullMathMulDivProd1
          (UInt256.sub (burnTickGetInside1Word σ ee)
            (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee + (⟨2⟩ : UInt256))))
          (burnPositionUpdateSlot0Packed
            (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee)))) ≠ ⟨0⟩)
    (h : RD code ee g s0 ⟨21387⟩
      (solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        burnPositionBaseSlotWord σ ee :: slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee ::
        burnTickLowerCleanWord ee :: ret :: R)
      (burnPositionKeyMappingMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 82 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21861⟩
      (uniswapV3PoolFullMathMulDivSlowResult
          (uniswapV3PoolFullMathMulDivProd1
            (UInt256.sub (burnTickGetInside1Word σ ee)
              (solcSlotWord σ ee
                (burnPositionBaseSlotWord σ ee + (⟨2⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed
              (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee))))
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub (burnTickGetInside1Word σ ee)
              (solcSlotWord σ ee
                (burnPositionBaseSlotWord σ ee + (⟨2⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed
              (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee))))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
          (burnPositionUpdateSlot0Packed
            (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee)))
          (UInt256.sub (burnTickGetInside1Word σ ee)
            (solcSlotWord σ ee
              (burnPositionBaseSlotWord σ ee + (⟨2⟩ : UInt256)))) ::
        UInt256.div
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub (burnTickGetInside0Word σ ee)
              (solcSlotWord σ ee
                (burnPositionBaseSlotWord σ ee + (⟨1⟩ : UInt256))))
            (burnPositionUpdateSlot0Packed
              (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee))))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ::
        burnPositionUpdateSlot0Packed
          (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee)) ::
        burnPositionKeyNewFreePtrWord ::
        burnTickGetInside1Word σ ee :: burnTickGetInside0Word σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        burnPositionBaseSlotWord σ ee :: ⟨19527⟩ ::
        burnTickGetInside1Word σ ee :: burnTickGetInside0Word σ ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        burnPositionBaseSlotWord σ ee :: slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee ::
        burnTickLowerCleanWord ee :: ret :: R)
      (burnPositionUpdateMem5 σ ee
        (solcSlotWord σ ee (burnPositionBaseSlotWord σ ee))
        (burnPositionBaseSlotWord σ ee))
      (UInt256.ofNat 22) rdata
      (cA, sstoreAccountMap ee.codeOwner
        (sstoreAccountMap ee.codeOwner σ
          (burnPositionBaseSlotWord σ ee + (⟨1⟩ : UInt256))
          (burnTickGetInside0Word σ ee))
        (burnPositionBaseSlotWord σ ee + (⟨2⟩ : UInt256))
        (burnTickGetInside1Word σ ee)) k' C' := by
  let inside1 := burnTickGetInside1Word σ ee
  let inside0 := burnTickGetInside0Word σ ee
  let posBase := burnPositionBaseSlotWord σ ee
  let delta := UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee))
  let postFreeR : List UInt256 :=
    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
    burnAmountCleanWord ee :: burnTickUpperCleanWord ee ::
    burnTickLowerCleanWord ee :: ret :: R
  let tail : List UInt256 :=
    ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
    solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
    posBase :: slot0TickReturnWord σ ee ::
    delta ::
    UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
    UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
    UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ :: postFreeR
  obtain ⟨_, _, hrdReturn⟩ :=
    uniswapV3PoolBurnFeeGrowthInsideEntryReturnConcrete
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (ret := ret) (R := R) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch htickLt h (by omega)
  obtain ⟨_, _, hrdEntry⟩ :=
    uniswapV3PoolBurnFeeGrowthInsideEnterPositionUpdate
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0)
      (z0 := ⟨0⟩) (z1 := ⟨0⟩) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase := posBase) (tick := slot0TickReturnWord σ ee)
      (delta := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR)
      hpatch
      (by simpa [inside1, inside0, posBase, delta] using hrdReturn)
      (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdSlot0⟩ :=
    uniswapV3PoolBurnPositionUpdateLoadSlot0
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdEntry (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdPacked⟩ :=
    uniswapV3PoolBurnPositionUpdateStoreSlot0Packed
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (pos0 := solcSlotWord σ ee posBase)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdSlot0 (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdFee0⟩ :=
    uniswapV3PoolBurnPositionUpdateStoreFeeGrowthInside0Last
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch (by simpa [inside1, inside0, posBase, delta] using hrdPacked)
      (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdFee1⟩ :=
    uniswapV3PoolBurnPositionUpdateStoreFeeGrowthInside1Last
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdFee0 (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdTokens0⟩ :=
    uniswapV3PoolBurnPositionUpdateStoreTokensOwed0
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdFee1 (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdTokens1⟩ :=
    uniswapV3PoolBurnPositionUpdateStoreTokensOwed1
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdTokens0 (by simp [postFreeR] at hov ⊢; omega)
  have hdelta : UInt256.signextend ⟨15⟩ delta = ⟨0⟩ := by
    dsimp [delta]
    rw [hzero]
    native_decide
  obtain ⟨_, _, hrdFallthrough⟩ :=
    uniswapV3PoolBurnPositionUpdateLiquidityDeltaZeroFallthrough
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hdelta hrdTokens1 (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdNonzero⟩ :=
    uniswapV3PoolBurnPositionUpdateLiquidityNonzeroJump
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hliq hrdFallthrough (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrdReload⟩ :=
    uniswapV3PoolBurnPositionUpdateReloadLiquidity
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdNonzero (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrd13017⟩ :=
    uniswapV3PoolBurnPositionUpdateStartMulDiv0
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hrdReload (by simp [postFreeR] at hov ⊢; omega)
  obtain ⟨_, _, hrd21861⟩ :=
    uniswapV3PoolBurnPositionUpdateMulDiv0Prod1ZeroMulDiv1Prod1NonzeroStoreFeeGrowthLast
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (inside1 := inside1) (inside0 := inside0) (delta := delta)
      (posBase := posBase) (retPos := ⟨19527⟩)
      (inside1' := inside1) (inside0' := inside0) (z2 := ⟨0⟩) (z3 := ⟨0⟩)
      (fee1 := solcSlotWord σ ee ⟨2⟩) (fee0 := solcSlotWord σ ee ⟨1⟩)
      (posBase' := posBase) (tick := slot0TickReturnWord σ ee)
      (delta' := delta)
      (upper := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
      (lower := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
      (owner := UInt256.ofNat ee.source.val) (ret := ⟨16428⟩) (free := ⟨256⟩)
      (R := postFreeR) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hperm hrd13017
      (by simpa [inside0, posBase] using hprod0)
      (by simpa [inside1, posBase] using hprod1)
      (by simpa [inside1, posBase] using hden)
      hdelta (by simp [postFreeR] at hov ⊢; omega)
  exact ⟨_, _, by simpa [inside1, inside0, posBase, delta, postFreeR, tail] using hrd21861⟩

theorem burnPositionUpdateTokensOwedState_stateEquiv_of_addedSlot3
    {evmEvm evmSolm : EVM.State} {σ I}
    {feeGrowthInside0X128 feeGrowthInside1X128 tokensOwed0 tokensOwed1 : UInt256}
    (hstate : EVMStateEquiv evmEvm evmSolm)
    (hword :
      burnPositionUpdateSourceTokensOwed1StoreWord
          (burnPositionUpdateSourceAfterTokensOwed0State evmSolm σ I feeGrowthInside0X128)
          σ I feeGrowthInside1X128 =
        burnPositionUpdateTokensOwedAddedSlot3
          (Solm.EVM.storageLoad evmEvm evmEvm.executionEnv.codeOwner
            (burnPositionUpdateSourceTokensOwedSlot I))
          tokensOwed0 tokensOwed1) :
    EVMStateEquiv
      (Solm.EVM.storageStore evmEvm evmEvm.executionEnv.codeOwner
        (burnPositionUpdateSourceTokensOwedSlot I)
        (burnPositionUpdateTokensOwedAddedSlot3
          (Solm.EVM.storageLoad evmEvm evmEvm.executionEnv.codeOwner
            (burnPositionUpdateSourceTokensOwedSlot I))
          tokensOwed0 tokensOwed1))
      (burnPositionUpdateSourceAfterTokensOwedState evmSolm σ I
        feeGrowthInside0X128 feeGrowthInside1X128) := by
  exact burnPositionUpdateTokensOwedState_stateEquiv_of_final_word hstate hword

theorem burnPositionUpdateTokensOwedAccountMapEquiv_of_addedSlot3
    {evmEvm evmSolm : EVM.State} {σ I}
    {feeGrowthInside0X128 feeGrowthInside1X128 tokensOwed0 tokensOwed1 : UInt256}
    (hstate : EVMStateEquiv evmEvm evmSolm)
    (hword :
      burnPositionUpdateSourceTokensOwed1StoreWord
          (burnPositionUpdateSourceAfterTokensOwed0State evmSolm σ I feeGrowthInside0X128)
          σ I feeGrowthInside1X128 =
        burnPositionUpdateTokensOwedAddedSlot3
          (Solm.EVM.storageLoad evmEvm evmEvm.executionEnv.codeOwner
            (burnPositionUpdateSourceTokensOwedSlot I))
          tokensOwed0 tokensOwed1) :
    accountMapEquiv
      (sstoreAccountMap evmEvm.executionEnv.codeOwner evmEvm.accountMap
        (burnPositionUpdateSourceTokensOwedSlot I)
        (burnPositionUpdateTokensOwedAddedSlot3
          (Solm.EVM.storageLoad evmEvm evmEvm.executionEnv.codeOwner
            (burnPositionUpdateSourceTokensOwedSlot I))
          tokensOwed0 tokensOwed1))
      (burnPositionUpdateSourceAfterTokensOwedState evmSolm σ I
        feeGrowthInside0X128 feeGrowthInside1X128).accountMap := by
  have hstate' :=
    burnPositionUpdateTokensOwedState_stateEquiv_of_addedSlot3
      (evmEvm := evmEvm) (evmSolm := evmSolm) (σ := σ) (I := I)
      (feeGrowthInside0X128 := feeGrowthInside0X128)
      (feeGrowthInside1X128 := feeGrowthInside1X128)
      (tokensOwed0 := tokensOwed0) (tokensOwed1 := tokensOwed1) hstate hword
  simpa [storageStore_accountMap] using hstate'.accountMap

theorem uniswapV3PoolBurnPositionUpdateZeroDeltaReturnToCallerByTokensCases
    {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity inside1 inside0 delta posBase inside1' inside0'
      z2 z3 fee1 fee0 posBase' tick delta' upper lower owner free r1 r2 r3 callerRet :
      UInt256}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdest : (D_J code 0).contains callerRet = true)
    (hperm : ee.perm = true)
    (hzero : burnAmountCleanWord ee = ⟨0⟩)
    (hmload224 :
      (if (⟨224⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)))
    (h : RD code ee g s0 ⟨21861⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: ⟨19527⟩ :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ⟨16428⟩ :: free :: r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R)
      mem (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hdelta : UInt256.slt (UInt256.signextend ⟨15⟩ delta') ⟨0⟩ = ⟨0⟩)
    (hov : R.length + 40 ≤ 1024) :
    (∃ k' C', RD code ee g s0 callerRet (r1 :: r2 :: posBase' :: R)
      mem (UInt256.ofNat 22) rdata (cA, σ) k' C' ∧
      UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 = ⟨0⟩ ∧
      UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 = ⟨0⟩) ∨
    (∃ k' C', RD code ee g s0 callerRet (r1 :: r2 :: posBase' :: R)
      mem (UInt256.ofNat 22) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (posBase + (⟨3⟩ : UInt256))
        (burnPositionUpdateTokensOwedAddedSlot3
          (solcSlotWord σ ee (posBase + (⟨3⟩ : UInt256))) tokensOwed0 tokensOwed1))
      k' C' ∧
      (UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 ≠ ⟨0⟩ ∨
        UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 ≠ ⟨0⟩)) := by
  by_cases htokens0 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed0 = ⟨0⟩
  · by_cases htokens1 : UInt256.land burnPositionUpdateSlot0Mask tokensOwed1 = ⟨0⟩
    · obtain ⟨_, _, hrd⟩ :=
        uniswapV3PoolBurnPositionUpdateTokensOwedZeroZeroDeltaReturnToCallerGeneric
          (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
          (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
          (liquidity := liquidity) (inside1 := inside1) (inside0 := inside0)
          (delta := delta) (posBase := posBase) (inside1' := inside1')
          (inside0' := inside0') (z2 := z2) (z3 := z3) (fee1 := fee1)
          (fee0 := fee0) (posBase' := posBase') (tick := tick) (delta' := delta')
          (upper := upper) (lower := lower) (owner := owner) (free := free)
          (r1 := r1) (r2 := r2) (r3 := r3) (callerRet := callerRet)
          (R := R) (mem := mem) (rdata := rdata) (acc := (cA, σ))
          hpatch hdest hzero hmload224 h htokens0 htokens1 hdelta hov
      exact Or.inl ⟨_, _, hrd, htokens0, htokens1⟩
    · obtain ⟨_, _, hrd⟩ :=
        uniswapV3PoolBurnPositionUpdateTokensOwed1NonzeroZeroDeltaReturnToCaller
          (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
          (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
          (liquidity := liquidity) (inside1 := inside1) (inside0 := inside0)
          (delta := delta) (posBase := posBase) (inside1' := inside1')
          (inside0' := inside0') (z2 := z2) (z3 := z3) (fee1 := fee1)
          (fee0 := fee0) (posBase' := posBase') (tick := tick) (delta' := delta')
          (upper := upper) (lower := lower) (owner := owner) (free := free)
          (r1 := r1) (r2 := r2) (r3 := r3) (callerRet := callerRet)
          (R := R) (mem := mem) (rdata := rdata) (cA := cA) (σ := σ)
          hpatch hdest hperm hzero hmload224 h htokens0 htokens1 hdelta hov
      exact Or.inr ⟨_, _, hrd, Or.inr htokens1⟩
  · obtain ⟨_, _, hrd⟩ :=
      uniswapV3PoolBurnPositionUpdateTokensOwed0NonzeroZeroDeltaReturnToCaller
        (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
        (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
        (liquidity := liquidity) (inside1 := inside1) (inside0 := inside0)
        (delta := delta) (posBase := posBase) (inside1' := inside1')
        (inside0' := inside0') (z2 := z2) (z3 := z3) (fee1 := fee1)
        (fee0 := fee0) (posBase' := posBase') (tick := tick) (delta' := delta')
        (upper := upper) (lower := lower) (owner := owner) (free := free)
        (r1 := r1) (r2 := r2) (r3 := r3) (callerRet := callerRet)
        (R := R) (mem := mem) (rdata := rdata) (cA := cA) (σ := σ)
        hpatch hdest hperm hzero hmload224 h htokens0 hdelta hov
    exact Or.inr ⟨_, _, hrd, Or.inl htokens0⟩

theorem uniswapV3PoolBurnPositionUpdateZeroDeltaReturnToCallerByTokens
    {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tokensOwed1 tokensOwed0 liquidity inside1 inside0 delta posBase inside1' inside0'
      z2 z3 fee1 fee0 posBase' tick delta' upper lower owner free r1 r2 r3 callerRet :
      UInt256}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdest : (D_J code 0).contains callerRet = true)
    (hperm : ee.perm = true)
    (hzero : burnAmountCleanWord ee = ⟨0⟩)
    (hmload224 :
      (if (⟨224⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 22 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)))
    (h : RD code ee g s0 ⟨21861⟩
      (tokensOwed1 :: tokensOwed0 :: liquidity :: burnPositionKeyNewFreePtrWord ::
        inside1 :: inside0 :: delta :: posBase :: ⟨19527⟩ :: inside1' :: inside0' ::
        z2 :: z3 :: fee1 :: fee0 :: posBase' :: tick :: delta' :: upper :: lower ::
        owner :: ⟨16428⟩ :: free :: r1 :: r2 :: r3 :: ⟨128⟩ :: callerRet :: R)
      mem (UInt256.ofNat 22) rdata (cA, σ) k C)
    (hdelta : UInt256.slt (UInt256.signextend ⟨15⟩ delta') ⟨0⟩ = ⟨0⟩)
    (hov : R.length + 40 ≤ 1024) :
    ∃ acc' k' C', RD code ee g s0 callerRet (r1 :: r2 :: posBase' :: R)
      mem (UInt256.ofNat 22) rdata acc' k' C' := by
  obtain hcases :=
    uniswapV3PoolBurnPositionUpdateZeroDeltaReturnToCallerByTokensCases
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (tokensOwed1 := tokensOwed1) (tokensOwed0 := tokensOwed0)
      (liquidity := liquidity) (inside1 := inside1) (inside0 := inside0)
      (delta := delta) (posBase := posBase) (inside1' := inside1')
      (inside0' := inside0') (z2 := z2) (z3 := z3) (fee1 := fee1)
      (fee0 := fee0) (posBase' := posBase') (tick := tick) (delta' := delta')
      (upper := upper) (lower := lower) (owner := owner) (free := free)
      (r1 := r1) (r2 := r2) (r3 := r3) (callerRet := callerRet)
      (R := R) (mem := mem) (rdata := rdata) (cA := cA) (σ := σ)
      hpatch hdest hperm hzero hmload224 h hdelta hov
  rcases hcases with hzeroTokens | hsomeTokens
  · rcases hzeroTokens with ⟨k', C', hrd, _, _⟩
    exact ⟨(cA, σ), k', C', hrd⟩
  · rcases hsomeTokens with ⟨k', C', hrd, _⟩
    exact ⟨_, k', C', hrd⟩

end Benchmarks.UniswapV3Pool
