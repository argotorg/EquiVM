import Benchmarks.Morpho.MorphoBlue.ReturnDataMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def safeTransferStatusPC (isFrom : Bool) : UInt256 := UInt256.ofNat (if isFrom then 15174 else 14869)
def safeTransferBoolPC (isFrom : Bool) : UInt256 := UInt256.ofNat (if isFrom then 15235 else 14930)
def safeTransferResultPC (isFrom : Bool) : UInt256 := UInt256.ofNat (if isFrom then 15248 else 14943)
def safeTransferMessagePC (isFrom decoded : Bool) : UInt256 :=
  UInt256.ofNat (if isFrom then (if decoded then 15263 else 15188)
    else (if decoded then 14958 else 14883))
def safeTransferErrorLength (isFrom decoded : Bool) : UInt256 :=
  UInt256.ofNat (if isFrom then (if decoded then 27 else 21) else (if decoded then 23 else 17))
def safeTransferErrorPayload (isFrom decoded : Bool) : UInt256 :=
  UInt256.ofNat (if isFrom then
    (if decoded then 52670383448186445862291048024289571784745826197126020892859664823105636794368
      else 52670383448186445862291048024289571785405123404729757618625217871871874170880)
    else (if decoded then 52670383448186445861359287004714696247472142465354858391252985466156581126144
      else 52670383448186445861359287007546356192474314229912029299057068147248459677696))
def safeTransferMessageMem (isFrom decoded : Bool) (mem : ByteArray) : ByteArray :=
  morphoErrorMem (safeTransferErrorLength isFrom decoded) (safeTransferErrorPayload isFrom decoded) mem

theorem morphoTransferStatusPrepare {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw data next status : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom : Bool) (hstack : R.length + 7 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferStatusPC isFrom)
      (data :: next :: status :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11507)
      (memLoad (UInt256.ofNat 64) mem :: safeTransferMessagePC isFrom false :: status ::
        memLoad (UInt256.ofNat 64) mem :: next :: data :: R) mem aw' out σ k' C' := by
  cases isFrom
  · exact morphoBlocks.morpho_block_14869_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  · exact morphoBlocks.morpho_block_15174_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h

theorem morphoTransferResultPrepare {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw a b status : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom : Bool) (hstack : R.length + 5 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferResultPC isFrom)
      (a :: b :: status :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11507)
      (memLoad (UInt256.ofNat 64) mem :: safeTransferMessagePC isFrom true :: status ::
        memLoad (UInt256.ofNat 64) mem :: R) mem aw' out σ k' C' := by
  cases isFrom
  · exact morphoBlocks.morpho_block_14943_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  · exact morphoBlocks.morpho_block_15248_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h

theorem morphoTransferMessageWrite {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr status : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom decoded : Bool) (hstack : R.length + 5 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferMessagePC isFrom decoded)
      (status :: ptr :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      (status :: ptr :: R)
      (writeWord (writeWord mem ptr.toNat (safeTransferErrorLength isFrom decoded))
        (ptr + UInt256.ofNat 32).toNat (safeTransferErrorPayload isFrom decoded)) aw' out σ k' C' := by
  cases isFrom <;> cases decoded
  · exact morphoBlocks.morpho_block_14883_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  · exact morphoBlocks.morpho_block_14958_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  · exact morphoBlocks.morpho_block_15188_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  · exact morphoBlocks.morpho_block_15263_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h

theorem morphoTransferMessage {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr status : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom decoded : Bool) (hstack : R.length + 7 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hfit : ptr.toNat + 64 < 2 ^ 64)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11507)
      (ptr :: safeTransferMessagePC isFrom decoded :: status :: ptr :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      (status :: ptr :: R) (safeTransferMessageMem isFrom decoded mem) aw' out σ k' C' := by
  have hp := uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)
  have hg : UInt256.lor (UInt256.gt (ptr + UInt256.ofNat 64) (UInt256.ofNat 18446744073709551615))
      (UInt256.lt (ptr + UInt256.ofNat 64) ptr) = UInt256.ofNat 0 := by
    rw [ugt_zero (by rw [hp]; change _ ≤ 18446744073709551615; omega), ult_zero (by rw [hp]; omega)]
    rfl
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAlloc64
    (by change R.length + 2 + 5 ≤ 1024; omega)
    (by cases isFrom <;> cases decoded <;> rw [morphoPatchedValidJumps v] <;> jump_dest) hg h
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoTransferMessageWrite isFrom decoded (by omega) rd1
  refine ⟨aw2, k2, C2, ?_⟩
  dsimp only [safeTransferMessageMem, morphoErrorMem]
  rw [hfree]
  exact rd2

theorem morphoAlloc64Overflow {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (hp : ptr.toNat < 2 ^ 64) (hbad : 2 ^ 64 ≤ ptr.toNat + 64)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11507)
      (ptr :: R) mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have ha := uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)
  have rd1 := morphoBlocks.morpho_block_11507_taken
    (immWords := wordsOf (immStore v)) hstack
    (by rw [ugt_one (by rw [ha]; change 18446744073709551615 < _; omega)]
        exact u256_lor_one_left_ne_zero _)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_6709 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 2 ≤ 1024; omega) rd1

theorem morphoTransferRequireFalse {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom decoded : Bool) (hstack : R.length + 11 ≤ 1024)
    (hm : MorphoHeap mem ptr 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      (UInt256.ofNat 0 :: ptr :: ret :: R) (safeTransferMessageMem isFrom decoded mem)
      aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have he := (morphoErrorMem_properties_general (safeTransferErrorLength isFrom decoded)
    (safeTransferErrorPayload isFrom decoded) ptr mem hm.lower hm.free hm.size
    (by have hg := hm.gap; omega) (by have hb := hm.space; change _ < 2 ^ 256; omega)).2.2
  refine morphoRequireFalseShort hstack rfl ?_ ?_ h
  · change UInt256.lt (UInt256.ofNat 0) (morphoErrorLength
      (morphoErrorMem _ _ mem) ptr) ≠ UInt256.ofNat 0
    rw [he]
    cases isFrom <;> cases decoded <;> decide
  · change UInt256.lt (UInt256.ofNat 32) (morphoErrorLength
      (morphoErrorMem _ _ mem) ptr) = UInt256.ofNat 0
    rw [he]
    cases isFrom <;> cases decoded <;> decide
end Benchmarks.Morpho.MorphoBlue
