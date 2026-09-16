import Examples.UniswapV2Pair.ErrorDynamicMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

-- GENERALIZES Reasoning.Reach.RD.solcErrorStringRevertTail: arbitrary free pointer, memory, and active words.
set_option maxHeartbeats 1000000 in
theorem RD.solcErrorStringRevertTail_dynamic
    {code : ByteArray} {g : Sat256} {s0 : State} {I : ExecutionEnv} {k C : Nat}
    {pc len rawWord shift word ptr aw : UInt256} {op : Operation.POp} {width : Nat}
    {R : List UInt256} {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD code I g s0 pc R mem aw rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0) (hword : UInt256.shiftLeft rawWord shift = word)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat - mem.size < USize.size)
    (hfit : ptr.toNat + 131 < UInt256.size) (haw : aw.toNat * 32 < UInt256.size)
    (hawLo : 96 ≤ aw.toNat * 32) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hov : R.length + 5 ≤ 1024) : RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have h64cover : (⟨64⟩ : UInt256).toNat + 32 ≤ aw.toNat * 32 := hawLo
  have hload : memoryWordLoad mem aw ⟨64⟩ = ptr :=
    mloadWordValue_of_readWithPadding (by change 64 < mem.size; omega)
      (UInt256_mload_haw_of_cover aw ⟨64⟩ haw h64cover) hread
  have hw64 : memoryWordActiveWords aw ⟨64⟩ = aw := UInt256_M_same_of_cover aw ⟨64⟩ haw h64cover
  have rdLoad := evm_run rd with [raw push1 ⟨64⟩ hd0 (by evm_ov), raw dup1 hd2 (by evm_ov)]
  have rdSelector := RD.mloadWord rdLoad hd3 hload (by simp only [List.length_cons]; omega)
  rw [hw64] at rdSelector
  have rdRawSelector := rdSelector.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdStore0 := evm_run rdRawSelector with [raw push1 ⟨229⟩ hd8 (by evm_ov), raw shl hd10 (by evm_ov), raw dup2 hd11 (by evm_ov)]
  have rdHeader := RD.mstoreWord rdStore0 hd12 (by simp only [List.length_cons]; omega)
  have rdStore1 := evm_run rdHeader with [raw push1 ⟨32⟩ hd13 (by evm_ov), raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov), raw add hd18 (by evm_ov)]
  have rdLength := RD.mstoreWord rdStore1 hd19 (by simp only [List.length_cons]; omega)
  have rdStore2 := evm_run rdLength with [raw push1 len hd20 (by evm_ov), raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov), raw add hd25 (by evm_ov)]
  have rdLiteral := RD.mstoreWord rdStore2 hd26 (by simp only [List.length_cons]; omega)
  have rdRaw := rdLiteral.pushConst rawWord (width := width) (op := op) hpush hd27 (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [raw push1 shift hdRawOut (by evm_ov), raw shl hdShl (by evm_ov)]
  rw [hword] at rdWord
  have rdStore3 := evm_run rdWord with [raw push1 ⟨68⟩ hd68 (by evm_ov), raw dup3 hdDup3 (by evm_ov), raw add hdAdd (by evm_ov)]
  have rdSwap := RD.mstoreWord rdStore3 hdMstore3 (by simp only [List.length_cons]; omega)
  have rdLoadFinal := evm_run rdSwap with [raw swap1 hdSwap (by evm_ov)]
  obtain ⟨hm3, hw3⟩ := solcErrorDynamicMem3_mload64 aw ptr len word hin hlo hgap hfit haw hread
  have rdTail := RD.mloadWord rdLoadFinal hdMload hm3 (by simp only [List.length_cons]; omega)
  rw [hw3] at rdTail
  have rdRev := evm_run rdTail with [raw swap1 hdSwap2 (by evm_ov), raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov), raw sub hdSub (by evm_ov), raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov), raw swap1 hdSwap4 (by evm_ov)]
  rw [u256_sub_self, show (⟨100⟩ : UInt256) + ⟨0⟩ = ⟨100⟩ by native_decide] at rdRev
  have hcover := (solcErrorDynamicWords3_bounds aw ptr haw hfit).2
  have hwRev := UInt256_M_same_of_cover_len (solcErrorDynamicWords3 aw ptr) ptr 100 hcover
  exact RD.rev 0 rdRev hdRev (by
    intro s haws hstk
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk, List.getElem!_cons_zero, List.getElem!_cons_succ]
    change Cₘ (UInt256.ofNat (MachineState.M (solcErrorDynamicWords3 aw ptr).toNat ptr.toNat 100)) - Cₘ (solcErrorDynamicWords3 aw ptr) = 0
    rw [hwRev, Nat.sub_self]) (by omega)

end UniswapV2Pair
