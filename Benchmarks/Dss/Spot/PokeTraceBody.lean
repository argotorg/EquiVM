import Benchmarks.Dss.Spot.PokeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Spot

theorem spotPokeBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some pokeTransition)
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨185⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := spotBytecode) (sel := sel) (entry := ⟨185⟩) (ret := ⟨214⟩)
    (decoded := ⟨207⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (spotDecode_poke_none_short hsz4 hshort)

theorem spotPokeX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨185⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨598⟩
        [pokeIlkWord I, ⟨214⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := spotBytecode) (sel := sel) (entry := ⟨185⟩) (ret := ⟨214⟩)
    (decoded := ⟨207⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  have rd208 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd209 := rd208.pop (by native_decide) (by evm_ov)
  have rd210 := rd209.calldataload (by native_decide) (by evm_ov)
  have rd213 := rd210.push2 ⟨598⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [pokeIlkWord, ilksArgWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd213.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.spotPokeToPeekExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (rd : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨598⟩
      [pokeIlkWord I, ⟨214⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨664⟩
      (pokePipTargetWord σ I :: pokePipTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨4⟩ :: ⟨128⟩ :: ⟨64⟩ :: ⟨132⟩ :: ⟨1507864023⟩ ::
        pokePipTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ :: pokeIlkWord I :: ⟨214⟩ ::
        sel :: [])
      (pokePeekCalldataMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k' C' := by
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rd599 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd601 := rd599.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd602 := rd601.dup2 (by native_decide) (by evm_ov)
  have rd603 := rd602.dup2 (by native_decide) (by evm_ov)
  have rd604 := rd603.mstore 0 (wordAt0Mem (pokeIlkWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)
  have rd606 := rd604.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd608 := rd606.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd609 := rd608.mstore 0 (pokePipHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by rfl)
    (by decide) (by evm_ov)
  have rd611 := rd609.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd612 := rd611.dup1 (by native_decide) (by evm_ov)
  have rd613 := rd612.dup3 (by native_decide) (by evm_ov)
  have hslot := twoWordHashMem_solcMappingSlot (⟨1⟩ : UInt256) (pokeIlkWord I)
    solcFreePtrMem_size
  have rd614 := rd613.keccak256 0 (solcMappingSlot ⟨1⟩ (pokeIlkWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd615Raw⟩ := rd614.sload (by native_decide) (by evm_ov)
  have rd615 := by
    simpa [pokePipRawWord, spotSlotWord, pokePipSlotFor_eq (I := I) hsz36,
      solcSlotWord] using rd615Raw
  have rd616 := rd615.dup2 (by native_decide) (by evm_ov)
  have rd617 := rd616.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
    mem_cost (pokePipHashMem_mload64 I) (by decide) (by evm_ov)
  have rd622 := rd617.push4 ⟨1507864023⟩ (by native_decide) (by evm_ov)
  have rd624 := rd622.push1 ⟨224⟩ (by native_decide) (by evm_ov)
  have rd625 := rd624.shl (by native_decide) (by evm_ov)
  have rd626 := rd625.dup2 (by native_decide) (by evm_ov)
  have rd627 := rd626.mstore 6 (pokePeekCalldataMem I) (UInt256.ofNat 5)
    (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)
  have rd664 := evm_run rd627 with [
    dup3,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (pokePeekCalldataMem_mload64 I) (by decide) (by evm_ov),
    dup5,
    swap4,
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap4,
    and,
    swap3,
    push4 ⟨1507864023⟩,
    swap3,
    push1 ⟨4⟩,
    dup1,
    dup3,
    add,
    swap4,
    swap2,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup8,
    dup8,
    dup1]
  exact ⟨_, _, by
    simpa [pokePipTargetWord, pokePipRawWord, spotSlotWord,
      pokePipSlotFor_eq (I := I) hsz36, solcSlotWord, hmask] using rd664⟩

theorem RD.spotPokePeekNoCode
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (rd598 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨598⟩
      [pokeIlkWord I, ⟨214⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (pokePipTargetWord σ I) = ⟨0⟩) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd664⟩ := RD.spotPokeToPeekExtcodesizeGuard hsz36 rd598
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨664⟩) (okPc := ⟨676⟩) rd664
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.spotPokePeekCallReady
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (rd598 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨598⟩
      [pokeIlkWord I, ⟨214⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (pokePipTargetWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨679⟩
      (gasWord :: pokePipTargetWord σ I :: ⟨0⟩ :: pokePeekOutPtr ::
        pokePeekInSize :: pokePeekOutPtr :: pokePeekOutSize :: pokePeekEndPtr ::
        pokePeekSelectorPlainWord :: pokePipTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ ::
        pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      (pokePeekCalldataMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd664⟩ := RD.spotPokeToPeekExtcodesizeGuard hsz36 rd598
  obtain ⟨gasWord, k', C', rd679⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨664⟩) (okPc := ⟨676⟩) rd664
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by
    simpa [pokePeekOutPtr, pokePeekInSize, pokePeekOutSize, pokePeekEndPtr,
      pokePeekSelectorPlainWord] using rd679⟩

theorem RD.spotPokePeekPostCall
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel gasWord : UInt256} {k C : ℕ}
    (rd679 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨679⟩
      (gasWord :: pokePipTargetWord σ I :: ⟨0⟩ :: pokePeekOutPtr ::
        pokePeekInSize :: pokePeekOutPtr :: pokePeekOutSize :: pokePeekEndPtr ::
        pokePeekSelectorPlainWord :: pokePipTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ ::
        pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      (pokePeekCalldataMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          σ σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (pokePipTargetWord σ I))
          (toExecute σ (AccountAddress.ofUInt256 (pokePipTargetWord σ I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((pokePeekCalldataMem I).readWithPadding
            pokePeekOutPtr.toNat pokePeekInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD spotBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨680⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: pokePeekEndPtr ::
            pokePeekSelectorPlainWord :: pokePipTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ ::
            pokeIlkWord I :: ⟨214⟩ :: sel :: [])
          (pokePeekPostCallMem I out) (UInt256.ofNat 6) out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd680raw, hout⟩ :=
    RD.call rd679 (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
          pokePeekOutPtr.toNat pokePeekInSize.toNat)
          pokePeekOutPtr.toNat pokePeekOutSize.toNat) = UInt256.ofNat 6 := by
      unfold pokePeekOutPtr pokePeekInSize pokePeekOutSize
      native_decide
    simpa [pokePeekPostCallMem, pokePeekOutPtr, pokePeekInSize, pokePeekOutSize,
      pokePeekEndPtr, pokePeekSelectorPlainWord, haw] using rd680raw

theorem RD.spotPokePeekCallDepthLimit
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel gasWord : UInt256} {k C : ℕ}
    (rd679 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨679⟩
      (gasWord :: pokePipTargetWord σ I :: ⟨0⟩ :: pokePeekOutPtr ::
        pokePeekInSize :: pokePeekOutPtr :: pokePeekOutSize :: pokePeekEndPtr ::
        pokePeekSelectorPlainWord :: pokePipTargetWord σ I :: ⟨0⟩ :: ⟨0⟩ ::
        pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      (pokePeekCalldataMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨680⟩
      (⟨0⟩ :: pokePeekEndPtr :: pokePeekSelectorPlainWord :: pokePipTargetWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      (pokePeekCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd680raw⟩ :=
    RD.callDepthLimit rd679 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin :
      (min pokePeekOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
        pokePeekOutPtr.toNat pokePeekInSize.toNat)
        pokePeekOutPtr.toNat pokePeekOutSize.toNat) = UInt256.ofNat 6 := by
    unfold pokePeekOutPtr pokePeekInSize pokePeekOutSize
    native_decide
  simpa [pokePeekOutPtr, pokePeekInSize, pokePeekOutSize, pokePeekEndPtr,
    pokePeekSelectorPlainWord, hmin, byteArray_write_len_zero, haw] using rd680raw

theorem RD.spotPokePeekCallFailed
    {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256} {sel : UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (rd680 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨680⟩
      (⟨0⟩ :: pokePeekEndPtr :: pokePeekSelectorPlainWord :: pokePipTargetWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨680⟩) (okPc := ⟨696⟩) rd680
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp)

theorem RD.spotPokePeekCallSucceeded
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (rd680 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨680⟩
      (⟨1⟩ :: pokePeekEndPtr :: pokePeekSelectorPlainWord :: pokePipTargetWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 6) rdata acc k C) :
    ∃ k' C', RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨698⟩
      (pokePeekEndPtr :: pokePeekSelectorPlainWord :: pokePipTargetWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 6) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨680⟩) (okPc := ⟨696⟩) rd680
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.spotPokePeekReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {out : ByteArray} {k C : ℕ}
    (rd698 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨698⟩
      (pokePeekEndPtr :: pokePeekSelectorPlainWord :: pokePipTargetWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      (pokePeekPostCallMem I out) (UInt256.ofNat 6) out acc k C)
    (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rdPop0 := RD.pop rd698 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop1 := RD.pop rdPop0 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop2 := RD.pop rdPop1 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 6) rdPush64
    (by native_decide)
    mem_cost
    (pokePeekPostCallMem_mload64 I out hshort hout)
    (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush64' := RD.push1 rdReturndatasize ⟨64⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDup2 := RD.dup2 rdPush64' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLt := RD.lt rdDup2 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' out.size hout]
    exact hshort
  have rdIszero := RD.iszero rdLt (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨718⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk (by native_decide) hcond
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.spotPokePeekReturnDecodeOk
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {out : ByteArray} {k C : ℕ}
    (rd698 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨698⟩
      (pokePeekEndPtr :: pokePeekSelectorPlainWord :: pokePipTargetWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      (pokePeekPostCallMem I out) (UInt256.ofNat 6) out acc k C)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    ∃ k' C', RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨733⟩
      (pokePeekHasWord out :: pokePeekValWord out :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      (pokePeekPostCallMem I out) (UInt256.ofNat 6) out acc k' C' := by
  have rdPop0 := RD.pop rd698 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop1 := RD.pop rdPop0 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop2 := RD.pop rdPop1 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 6) rdPush64
    (by native_decide)
    mem_cost
    (pokePeekPostCallMem_mload64_long I out hlo hout)
    (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush64' := RD.push1 rdReturndatasize ⟨64⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDup2 := RD.dup2 rdPush64' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLt := RD.lt rdDup2 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' out.size hout]
    exact hlo
  have rdIszero := RD.iszero rdLt (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨718⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rdJumpi := RD.jumpiT rdPushOk (by native_decide) hcond (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPopLen := RD.pop rdJumpdest (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDup1 := RD.dup1 rdPopLen (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload128 := RD.mload 0 (pokePeekValWord out) (UInt256.ofNat 6) rdDup1
    (by native_decide)
    mem_cost
    (pokePeekPostCallMem_mload128_long I out hlo hout)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPush32 := RD.push1 rdMload128 ⟨32⟩ (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap1 := RD.swap1 rdPush32 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap2 := RD.swap2 rdSwap1 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAdd := RD.add rdSwap2 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdMload160 := RD.mload 0 (pokePeekHasWord out) (UInt256.ofNat 6) rdAdd
    (by native_decide)
    mem_cost
    (pokePeekPostCallMem_mload160_long I out hlo hout)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap1' := RD.swap1 rdMload160 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap3 := RD.swap3 rdSwap1' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop0' := RD.pop rdSwap3 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSwap1'' := RD.swap1 rdPop0' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop1' := RD.pop rdSwap1'' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rdPop1'⟩

theorem spotRDInvalidError {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.INVALID, .none)) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
      X (g.toNat + 1) (D_J code 0) s0 = .error .InvalidInstruction := by
  rcases RD.conclude h with hoog | ⟨k', C', s', hX, hcode, hpc, _hstk, _hgas, hk, _hC,
    _hmem, _haw, _hrdata, _hacc⟩
  · exact Or.inl hoog
  · have hdec' : decode s'.executionEnv.code s'.machineState.pc = some (.INVALID, .none) := by
      rw [hcode, hpc]
      exact hdec
    have hstep : Xstep (D_J code 0) s' = .error .InvalidInstruction := by
      have hstep' := Ethereum.EVM.step_invalid s' hdec'
      simpa [hcode] using hstep'
    have hfuel : g.toNat + 1 - k' = (g.toNat + 1 - (k' + 1)) + 1 := by
      omega
    exact Or.inr (by
      rw [hX, hfuel]
      exact Ethereum.EVM.Xstep_X_X_except _ s' _ _ hstep)

theorem RD.spotCheckedMulReturns
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1010)
    (hret : (D_J spotBytecode 0).contains ret = true)
    (hfit : x.toNat * y.toNat < UInt256.size)
    (rd2051 : RD spotBytecode I g s0 ⟨2051⟩ (y :: x :: ret :: R)
      mem aw rdata acc k C) :
    ∃ k' C', RD spotBytecode I g s0 ret (x * y :: R) mem aw rdata acc k' C' := by
  have rd2078prep := evm_run rd2051 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨2078⟩ (by native_decide) (by evm_ov)]
  by_cases hy0 : y = ⟨0⟩
  · have hcond : UInt256.isZero y ≠ ⟨0⟩ := by
      rw [hy0]
      decide
    have rd2078 := rd2078prep.jumpiT (by native_decide) hcond (by jump_dest)
      (by evm_ov)
    have rd2082 := evm_run rd2078 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨2087⟩ (by native_decide) (by evm_ov)]
    have rd2087 := rd2082.jumpiT (by native_decide) hcond (by jump_dest)
      (by evm_ov)
    have rd2092 := evm_run rd2087 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rdret := rd2092.jump (by native_decide) hret (by evm_ov)
    exact ⟨_, _, by simpa [hy0] using rdret⟩
  · have hcond : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hy0
    have rd2061 := rd2078prep.jumpiNT (by native_decide) hcond (by evm_ov)
    have rd2073 := evm_run rd2061 with [
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw dup1 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw mul (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup2 (by native_decide) (by evm_ov),
      raw push2 ⟨2075⟩ (by native_decide) (by evm_ov)]
    have rd2075 := rd2073.jumpiT (by native_decide) hy0 (by jump_dest) (by evm_ov)
    have hyNatNe : y.toNat ≠ 0 := by
      intro hzero
      exact hy0 (uint256_toNat_eq_zero hzero)
    have hdivWord : UInt256.div (x * y) y = x := by
      apply u256_inj
      rw [udiv_toNat]
      have hprod : (x * y).toNat = x.toNat * y.toNat := by
        rw [umul_toNat x y hfit]
      rw [hprod]
      simpa [Nat.mul_comm] using Nat.mul_div_right x.toNat
        (Nat.pos_of_ne_zero hyNatNe)
    have rd2082 := evm_run rd2075 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw eq (by native_decide) (by evm_ov),
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨2087⟩ (by native_decide) (by evm_ov)]
    have heqCond : UInt256.eq (UInt256.div (x * y) y) x ≠ ⟨0⟩ := by
      rw [hdivWord, u256_eq_refl]
      exact one_ne_zero_uint
    have rd2087 := rd2082.jumpiT (by native_decide) heqCond (by jump_dest)
      (by evm_ov)
    have rd2092 := evm_run rd2087 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    have rdret := rd2092.jump (by native_decide) hret (by evm_ov)
    exact ⟨_, _, by simpa using rdret⟩

theorem RD.spotCheckedMulOverflowReverts
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1010)
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (rd2051 : RD spotBytecode I g s0 ⟨2051⟩ (y :: x :: ret :: R)
      mem aw rdata acc k C) :
    RDrev spotBytecode g s0 := by
  have hyNe : y ≠ ⟨0⟩ := by
    intro hzero
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hzero]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hdivNe : UInt256.div (x * y) y ≠ x := by
    intro hbad
    have h := spot_u256_mul_div_overflow_ne x y hover
    exact h (by
      have hcomm : y * x = x * y := by
        simpa using u256_mul_comm y x
      rw [hcomm]
      exact hbad)
  have rd2078prep := evm_run rd2051 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨2078⟩ (by native_decide) (by evm_ov)]
  have hcond : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hyNe
  have rd2061 := rd2078prep.jumpiNT (by native_decide) hcond (by evm_ov)
  have rd2073 := evm_run rd2061 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨2075⟩ (by native_decide) (by evm_ov)]
  have rd2075 := rd2073.jumpiT (by native_decide) hyNe (by jump_dest) (by evm_ov)
  have rd2082 := evm_run rd2075 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2087⟩ (by native_decide) (by evm_ov)]
  have heqCond : UInt256.eq (UInt256.div (x * y) y) x = ⟨0⟩ :=
    u256_eq_of_ne hdivNe
  have rdFallthrough := rd2082.jumpiNT (by native_decide) heqCond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.spotRdivReturns
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x denom ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hret : (D_J spotBytecode 0).contains ret = true)
    (hfit : x.toNat * pokeRay.toNat < UInt256.size)
    (hdenom : denom ≠ ⟨0⟩)
    (rd2093 : RD spotBytecode I g s0 ⟨2093⟩ (denom :: x :: ret :: R)
      mem aw rdata acc k C) :
    ∃ k' C', RD spotBytecode I g s0 ret
      (UInt256.div (x * pokeRay) denom :: R) mem aw rdata acc k' C' := by
  have rd2117 := evm_run rd2093 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨2118⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rd2101 := rd2117.pushConst pokeRay (width := 12) (op := .PUSH12)
    (by decide) (by native_decide) (by evm_ov)
  have rd2051 := rd2101.push2 ⟨2051⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
  have hmulRlen : (denom :: ⟨0⟩ :: denom :: x :: ret :: R).length ≤ 1010 := by
    simp only [List.length_cons]
    omega
  obtain ⟨_, _, rd2118⟩ :=
    RD.spotCheckedMulReturns
      (R := denom :: ⟨0⟩ :: denom :: x :: ret :: R)
      (ret := (⟨2118⟩ : UInt256)) hmulRlen
      (by native_decide) hfit rd2051
  have rd2123 := evm_run rd2118 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨2125⟩ (by native_decide) (by evm_ov)]
  have rd2125 := rd2123.jumpiT (by native_decide) hdenom (by jump_dest)
    (by evm_ov)
  have rd2132 := evm_run rd2125 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rdret := rd2132.jump (by native_decide) hret (by evm_ov)
  exact ⟨_, _, by simpa using rdret⟩

theorem RD.spotRdivMulOverflowReverts
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x denom ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hover : UInt256.size ≤ x.toNat * pokeRay.toNat)
    (rd2093 : RD spotBytecode I g s0 ⟨2093⟩ (denom :: x :: ret :: R)
      mem aw rdata acc k C) :
    RDrev spotBytecode g s0 := by
  have rd2117 := evm_run rd2093 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨2118⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rd2101 := rd2117.pushConst pokeRay (width := 12) (op := .PUSH12)
    (by decide) (by native_decide) (by evm_ov)
  have rd2051 := rd2101.push2 ⟨2051⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
  have hmulRlen : (denom :: ⟨0⟩ :: denom :: x :: ret :: R).length ≤ 1010 := by
    simp only [List.length_cons]
    omega
  exact RD.spotCheckedMulOverflowReverts
    (R := denom :: ⟨0⟩ :: denom :: x :: ret :: R)
    (ret := (⟨2118⟩ : UInt256)) hmulRlen hover rd2051

theorem RD.spotRdivDivZeroInvalid
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x denom ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hRlen : R.length ≤ 1000)
    (hfit : x.toNat * pokeRay.toNat < UInt256.size)
    (hdenom : denom = ⟨0⟩)
    (rd2093 : RD spotBytecode I g s0 ⟨2093⟩ (denom :: x :: ret :: R)
      mem aw rdata acc k C) :
    X (g.toNat + 1) (D_J spotBytecode 0) s0 = .error .OutOfGass ∨
      X (g.toNat + 1) (D_J spotBytecode 0) s0 = .error .InvalidInstruction := by
  have rd2117 := evm_run rd2093 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨2118⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rd2101 := rd2117.pushConst pokeRay (width := 12) (op := .PUSH12)
    (by decide) (by native_decide) (by evm_ov)
  have rd2051 := rd2101.push2 ⟨2051⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
  have hmulRlen : (denom :: ⟨0⟩ :: denom :: x :: ret :: R).length ≤ 1010 := by
    simp only [List.length_cons]
    omega
  obtain ⟨_, _, rd2118⟩ :=
    RD.spotCheckedMulReturns
      (R := denom :: ⟨0⟩ :: denom :: x :: ret :: R)
      (ret := (⟨2118⟩ : UInt256)) hmulRlen
      (by native_decide) hfit rd2051
  have rd2123 := evm_run rd2118 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨2125⟩ (by native_decide) (by evm_ov)]
  have rd2124 := rd2123.jumpiNT (by native_decide) hdenom (by evm_ov)
  exact spotRDInvalidError rd2124 (by native_decide)

theorem RD.spotPokeHasTrueToValScaledMul
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {out : ByteArray} {k C : ℕ}
    (rd733 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨733⟩
      (pokePeekHasWord out :: pokePeekValWord out :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      (pokePeekPostCallMem I out) (UInt256.ofNat 6) out acc k C)
    (hhas : pokePeekHasWord out ≠ ⟨0⟩) :
    ∃ k' C', RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2051⟩
      (pokeBillion :: pokePeekValWord out :: ⟨766⟩ :: ⟨774⟩ :: ⟨798⟩ :: ⟨0⟩ ::
        pokePeekHasWord out :: pokePeekValWord out :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      (pokePeekPostCallMem I out) (UInt256.ofNat 6) out acc k' C' := by
  have hBillion : (⟨1000000000⟩ : UInt256) = pokeBillion := by rfl
  have rd746pre := evm_run rd733 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨746⟩ (by native_decide) (by evm_ov)]
  have rd746 := rd746pre.jumpiT (by native_decide) hhas (by jump_dest) (by evm_ov)
  have rd2051 := evm_run rd746 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨798⟩ (by native_decide) (by evm_ov),
    raw push2 ⟨774⟩ (by native_decide) (by evm_ov),
    raw push2 ⟨766⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw push4 ⟨1000000000⟩ (by native_decide) (by evm_ov),
    raw push2 ⟨2051⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [hBillion] using rd2051⟩

theorem RD.spotPokeValScaledToRdivPar
    {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {valScaled has val sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (rd766 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨766⟩
      (valScaled :: ⟨774⟩ :: ⟨798⟩ :: ⟨0⟩ :: has :: val ::
        pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k C) :
    ∃ k' C', RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2093⟩
      (pokeParWord σ' I :: valScaled :: ⟨774⟩ :: ⟨798⟩ :: ⟨0⟩ :: has :: val ::
        pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k' C' := by
  have rd767 := rd766.jumpdest (by native_decide) (by evm_ov)
  have rd769 := rd767.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  obtain ⟨k770, C770, rd770raw⟩ := rd769.sload (by native_decide) (by evm_ov)
  have rd770 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨770⟩
      (pokeParWord σ' I :: valScaled :: ⟨774⟩ :: ⟨798⟩ :: ⟨0⟩ :: has :: val ::
        pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k770 C770 := by
    simpa [pokeParWord, spotSlotWord, solcSlotWord] using rd770raw
  have rd2093 := evm_run rd770 with [
    raw push2 ⟨2093⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa using rd2093⟩

theorem RD.spotPokeAfterRdivParToRdivMat
    {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {spot1 has val sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hsz36 : 36 ≤ I.calldata.size)
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd774 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨774⟩
      (spot1 :: ⟨798⟩ :: ⟨0⟩ :: has :: val :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k C) :
    ∃ k' C', RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2093⟩
      (pokeMatWord σ' I :: spot1 :: ⟨798⟩ :: ⟨0⟩ :: has :: val ::
        pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      (twoWordHashMem (pokeIlkWord I) ⟨1⟩ mem) (UInt256.ofNat 6) out (cA', σ') k' C' := by
  let mem1 := twoWordHashMem (pokeIlkWord I) ⟨1⟩ mem
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (mem1.readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (pokeIlkWord I) := by
    dsimp [mem1]
    exact poke_twoWordHashMem_solcMappingSlot_of_ge64 (⟨1⟩ : UInt256)
      (pokeIlkWord I) (by rw [hmem]; omega)
  have rd775 := rd774.jumpdest (by native_decide) (by evm_ov)
  have rd779pre := evm_run rd775 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd779 := rd779pre.mstore 0 (wordAt0Mem (pokeIlkWord I) mem)
    (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd786pre := evm_run rd779 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd786 := rd786pre.mstore 0 mem1 (UInt256.ofNat 6)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd792pre := evm_run rd786 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd791 := rd792pre.keccak256 0 (solcMappingSlot ⟨1⟩ (pokeIlkWord I))
    (UInt256.ofNat 6) (by native_decide) mem_cost hslot (by native_decide)
    (by evm_ov)
  have rd792 := rd791.add (by native_decide) (by evm_ov)
  obtain ⟨k794, C794, rd794raw⟩ := rd792.sload (by native_decide) (by evm_ov)
  have rd794 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨794⟩
      (pokeMatWord σ' I :: spot1 :: ⟨798⟩ :: ⟨0⟩ :: has :: val ::
        pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem1 (UInt256.ofNat 6) out (cA', σ') k794 C794 := by
    simpa [pokeMatWord, spotSlotWord, solcSlotWord, pokeMatSlotFor_eq hsz36]
      using rd794raw
  have rd2093 := evm_run rd794 with [
    raw push2 ⟨2093⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [mem1] using rd2093⟩

theorem RD.spotPokeHasFalseToVatFileEntry
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {out : ByteArray} {k C : ℕ}
    (rd733 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨733⟩
      (pokePeekHasWord out :: pokePeekValWord out :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      (pokePeekPostCallMem I out) (UInt256.ofNat 6) out acc k C)
    (hhas : pokePeekHasWord out = ⟨0⟩) :
    ∃ k' C', RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨798⟩
      (⟨0⟩ :: ⟨0⟩ :: pokePeekHasWord out :: pokePeekValWord out ::
        pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      (pokePeekPostCallMem I out) (UInt256.ofNat 6) out acc k' C' := by
  have rd798 := evm_run rd733 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨746⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) hhas (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push2 ⟨798⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa using rd798⟩

theorem RD.spotPokeVatFileCallGuard
    {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256} {spot scratch has val sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd798 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨798⟩
      (spot :: scratch :: has :: val :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k C) :
    ∃ k' C', RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨886⟩
      (pokeVatTargetWord σ' I :: pokeVatTargetWord σ' I :: ⟨0⟩ :: pokeVatFileOutPtr ::
        pokeVatFileInSize :: pokeVatFileOutPtr :: pokeVatFileOutSize :: pokeVatFileEndPtr ::
        pokeVatFileSelectorPlainWord :: pokeVatTargetWord σ' I :: spot :: has :: val ::
        pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      (pokeVatFileCalldataMem I spot mem) (UInt256.ofNat 8) out (cA', σ') k' C' := by
  let vatRaw := spotSlotWord ⟨2⟩ σ' I
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hselector :
      UInt256.shiftLeft (⟨218469439⟩ : UInt256) ⟨225⟩ =
        pokeVatFileSelectorShifted := by
    native_decide
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hvatMask :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        vatRaw = pokeVatTargetWord σ' I := by
    rw [u256_land_comm, hmask]
  have hinsize :
      UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨100⟩ = pokeVatFileInSize := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + ⟨100⟩ = pokeVatFileEndPtr := by
    native_decide
  have rd799 := rd798.jumpdest (by native_decide) (by evm_ov)
  have rd801 := rd799.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  obtain ⟨k802, C802, rd802raw⟩ := rd801.sload (by native_decide) (by evm_ov)
  have rd802 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨802⟩
      (vatRaw :: spot :: scratch :: has :: val :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k802 C802 := by
    simpa [vatRaw, spotSlotWord, solcSlotWord] using rd802raw
  have rd886 := evm_run rd802 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 ⟨218469439⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨225⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (pokeVatFileSelectorMem mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rw [hselector]; rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup9 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (pokeVatFileIlkMem I mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push4 ⟨484187101⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨226⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (pokeVatFileWhatMem I mem) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 (pokeVatFileCalldataMem I spot mem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost (pokeVatFileCalldataMem_mload64 I spot hmem hread64)
      (by decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push4 ⟨436938878⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [pokeVatFileOutPtr, pokeVatFileInSize, pokeVatFileOutSize,
      pokeVatFileEndPtr, pokeVatFileSelectorPlainWord, pokeVatFileSelectorShifted,
      hselector, hvatMask, hinsize, hend] using rd886⟩

theorem RD.spotPokeVatFileCallReady
    {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256} {spot scratch has val sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (pokeVatTargetWord σ' I) ≠ ⟨0⟩)
    (rd798 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨798⟩
      (spot :: scratch :: has :: val :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k C) :
    ∃ gasWord k' C', RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨901⟩
      (gasWord :: pokeVatTargetWord σ' I :: ⟨0⟩ :: pokeVatFileOutPtr ::
        pokeVatFileInSize :: pokeVatFileOutPtr :: pokeVatFileOutSize :: pokeVatFileEndPtr ::
        pokeVatFileSelectorPlainWord :: pokeVatTargetWord σ' I :: spot :: has :: val ::
        pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      (pokeVatFileCalldataMem I spot mem) (UInt256.ofNat 8) out (cA', σ') k' C' := by
  obtain ⟨_, _, rd886⟩ := RD.spotPokeVatFileCallGuard hmem hread64 rd798
  obtain ⟨gasWord, k', C', rd901⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨886⟩) (okPc := ⟨898⟩) rd886
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd901⟩

theorem RD.spotPokeVatFileNoCode
    {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256} {spot scratch has val sel : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (pokeVatTargetWord σ' I) = ⟨0⟩)
    (rd798 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨798⟩
      (spot :: scratch :: has :: val :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 6) out (cA', σ') k C) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd886⟩ := RD.spotPokeVatFileCallGuard hmem hread64 rd798
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨886⟩) (okPc := ⟨898⟩) rd886
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.spotPokeVatFilePostCall
    {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256} {spot has val sel gasWord : UInt256}
    {mem out : ByteArray} {k C : ℕ}
    (rd901 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨901⟩
      (gasWord :: pokeVatTargetWord σ' I :: ⟨0⟩ :: pokeVatFileOutPtr ::
        pokeVatFileInSize :: pokeVatFileOutPtr :: pokeVatFileOutSize :: pokeVatFileEndPtr ::
        pokeVatFileSelectorPlainWord :: pokeVatTargetWord σ' I :: spot :: has :: val ::
        pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 8) out (cA', σ') k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (fileOut : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, fileOut) = Ethereum.EVM.Θ I.blobVersionedHashes cA'
          gh bl σ' σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (pokeVatTargetWord σ' I))
          (toExecute σ' (AccountAddress.ofUInt256 (pokeVatTargetWord σ' I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding pokeVatFileOutPtr.toNat pokeVatFileInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD spotBytecode I g
          (initState cA gh bl σ σ₀ g A I) ⟨902⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: pokeVatFileEndPtr ::
            pokeVatFileSelectorPlainWord :: pokeVatTargetWord σ' I :: spot :: has :: val ::
            pokeIlkWord I :: ⟨214⟩ :: sel :: [])
          mem (UInt256.ofNat 8) fileOut (cA'', σ'') k' C'
      ∧ fileOut.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, fileOut, Ain, callGas, k', C', hΘ, rd902raw, hout⟩ :=
    RD.call rd901 (by native_decide) hdepth (by evm_ov)
  refine ⟨cA'', σ'', z, fileOut, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin :
        (min pokeVatFileOutSize (UInt256.ofNat fileOut.size)).toNat = 0 := by
      change (if pokeVatFileOutSize ≤ UInt256.ofNat fileOut.size then pokeVatFileOutSize
        else UInt256.ofNat fileOut.size).toNat = 0
      by_cases h : pokeVatFileOutSize ≤ UInt256.ofNat fileOut.size
      · simp [h, pokeVatFileOutSize]
      · exact False.elim (h (Fin.zero_le _))
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          pokeVatFileOutPtr.toNat pokeVatFileInSize.toNat)
          pokeVatFileOutPtr.toNat pokeVatFileOutSize.toNat) = UInt256.ofNat 8 := by
      unfold pokeVatFileOutPtr pokeVatFileInSize pokeVatFileOutSize
      native_decide
    simpa [pokeVatFileOutPtr, pokeVatFileInSize, pokeVatFileOutSize,
      pokeVatFileEndPtr, pokeVatFileSelectorPlainWord, hmin, byteArray_write_len_zero,
      haw] using rd902raw

theorem RD.spotPokeVatFileCallFailed
    {cA cA'' gh bl σ σ' σ'' σ₀ A I} {g : Sat256}
    {spot has val sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (rd902 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨902⟩
      (⟨0⟩ :: pokeVatFileEndPtr :: pokeVatFileSelectorPlainWord ::
        pokeVatTargetWord σ' I :: spot :: has :: val :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata (cA'', σ'') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨902⟩) (okPc := ⟨918⟩) rd902
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp)

theorem RD.spotPokeVatFileCallSucceeded
    {cA gh bl σ σ' σ₀ A I} {g : Sat256} {spot has val sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (rd902 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨902⟩
      (⟨1⟩ :: pokeVatFileEndPtr :: pokeVatFileSelectorPlainWord ::
        pokeVatTargetWord σ' I :: spot :: has :: val :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k C) :
    ∃ k' C', RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨920⟩
      (pokeVatFileEndPtr :: pokeVatFileSelectorPlainWord :: pokeVatTargetWord σ' I ::
        spot :: has :: val :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨902⟩) (okPc := ⟨918⟩) rd902
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.spotPokeVatFileLogReturns
    {cA gh bl σ σ' σ₀ A I} {g : Sat256} {spot has val sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hperm : I.perm = true)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd920 : RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨920⟩
      (pokeVatFileEndPtr :: pokeVatFileSelectorPlainWord :: pokeVatTargetWord σ' I ::
        spot :: has :: val :: pokeIlkWord I :: ⟨214⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k C) :
    RDret spotBytecode g (initState cA gh bl σ σ₀ g A I) acc ByteArray.empty := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        (⟨128⟩ : UInt256) := by
    exact mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hmload64Log :
      (if (⟨64⟩ : UInt256).toNat ≥ (pokeEventSpotMem I val spot mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((pokeEventSpotMem I val spot mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        (⟨128⟩ : UInt256) :=
    pokeEventSpotMem_mload64 I val spot hmem hread64
  have rd943 := evm_run rd920 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide) mem_cost hmload64
      (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (pokeEventIlkMem I mem) (UInt256.ofNat 8) (by native_decide) mem_cost
      (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (pokeEventValMem I val mem) (UInt256.ofNat 8) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (pokeEventSpotMem I val spot mem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide) mem_cost
      hmload64Log (by native_decide) (by evm_ov)]
  have rd976 := rd943.pushConst pokeEventTopic (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd992 := evm_run rd976 with [
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨96⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw log1 0 (UInt256.ofNat 8) (by native_decide) hperm mem_cost
      (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd214 := rd992.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd215 := rd214.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd215 (by native_decide) (by evm_ov)
end Benchmarks.Dss.Spot
