import Benchmarks.Dss.Pot.DripSuckBase
import Benchmarks.Dss.Pot.DripSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Pot

/-! ## EVM-side `_mul(Pie, chi_)` + `vat.suck` trace (`@1960` onward) -/

set_option maxHeartbeats 0 in
/-- `@1960 → @2005`: load `vat`/`vow`/`Pie`, mask addresses, `_mul(Pie, chi_) = Pie*chi_`. -/
theorem potDripX_mulReady {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel chi_ tmp : UInt256}
    (hfit : chi_.toNat * (dripPieWord σ'' I).toNat < UInt256.size)
    (h : RD potBytecode I g s0 ⟨1960⟩ (chi_ :: ⟨0⟩ :: tmp :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ'') k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨2005⟩
      (dripPieWord σ'' I * chi_ :: dripThisWord I :: dripVowTargetWord σ'' I ::
        potSuckSelectorWord :: dripVatTargetWord σ'' I :: chi_ :: tmp :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ'') k' C' := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hvatEq : UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
      (solcSlotWord σ'' I ⟨5⟩) = dripVatTargetWord σ'' I := by
    rw [hmask, u256_land_comm]; rfl
  have hvowEq : UInt256.land (solcSlotWord σ'' I ⟨6⟩)
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) = dripVowTargetWord σ'' I := by
    rw [hmask]; rfl
  have rd1962 := h.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1963⟩ := rd1962.sload (by native_decide) (by evm_ov)
  have rd1965 := rd1963.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1966⟩ := rd1965.sload (by native_decide) (by evm_ov)
  have rd1968 := rd1966.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1969⟩ := rd1968.sload (by native_decide) (by evm_ov)
  have rd1993 := evm_run rd1969 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 potSuckSelectorWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1994 := rd1993.address (by native_decide) (by evm_ov)
  have rd2001 := evm_run rd1994 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨2005⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw push2 ⟨2300⟩ (by native_decide) (by evm_ov)]
  have rd2300 := rd2001.jump (by native_decide) (by jump_dest) (by evm_ov)
  rw [hvatEq, hvowEq] at rd2300
  obtain ⟨_, _, rd2005⟩ := RD.potMulReturnsDrip (x := chi_) (y := solcSlotWord σ'' I ⟨2⟩)
    (ret := ⟨2005⟩)
    (R := [dripThisWord I, dripVowTargetWord σ'' I, potSuckSelectorWord,
      dripVatTargetWord σ'' I, chi_, tmp, ⟨341⟩, sel]) rfl
    (by simpa [dripPieWord, potSlotWord] using hfit) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega) rd2300
  exact ⟨_, _, by simpa [dripPieWord, potSlotWord] using rd2005⟩

set_option maxHeartbeats 0 in
/-- `@2005 → @2079`: build the `suck(vow,this,rad)` calldata in memory, reach the CALL
`EXTCODESIZE` guard. -/
theorem potDripX_callGuard {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel chi_ tmp : UInt256}
    (h : RD potBytecode I g s0 ⟨2005⟩
      (dripPieWord σ'' I * chi_ :: dripThisWord I :: dripVowTargetWord σ'' I ::
        potSuckSelectorWord :: dripVatTargetWord σ'' I :: chi_ :: tmp :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ'') k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨2079⟩
      (dripVatTargetWord σ'' I :: dripVatTargetWord σ'' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ :: ⟨128⟩ ::
        ⟨0⟩ :: ⟨228⟩ :: potSuckSelectorWord :: dripVatTargetWord σ'' I :: chi_ :: tmp ::
        ⟨341⟩ :: [sel])
      (potSuckCalldataMem σ'' I (dripPieWord σ'' I * chi_) solcFreePtrMem)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ'') k' C' := by
  set rad := dripPieWord σ'' I * chi_ with hrad
  have hselShift : UInt256.shiftLeft
      (UInt256.land (⟨4294967295⟩ : UInt256) potSuckSelectorWord) ⟨224⟩ =
      potSuckSelectorShifted := by native_decide
  have hmload0 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩
          then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide) solcFreePtrMem_read64
  have rd2006 := h.jumpdest (by native_decide) (by evm_ov)
  have rd2008 := rd2006.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd2009 := rd2008.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
    mem_cost hmload0 (by decide) (by evm_ov)
  have rdSel := evm_run rd2009 with [
    raw dup5 (by native_decide) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2020 := rdSel.mstore 6 (potSuckSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
    (by native_decide) mem_cost (by rw [hselShift]; rfl) (by decide) (by evm_ov)
  have rdVow := evm_run rd2020 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2036 := rdVow.mstore 3 (potSuckVowMem σ'' I solcFreePtrMem) (UInt256.ofNat 6)
    (by native_decide) mem_cost (by rw [dripVowTargetWord_mask_clean]; rfl)
    (by native_decide) (by evm_ov)
  have rdThis := evm_run rd2036 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2051 := rdThis.mstore 3 (potSuckThisMem σ'' I solcFreePtrMem) (UInt256.ofNat 7)
    (by native_decide) mem_cost (by rw [dripThisWord_mask_clean]; rfl)
    (by native_decide) (by evm_ov)
  have rdCd := evm_run rd2051 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2057 := rdCd.mstore 3 (potSuckCalldataMem σ'' I rad solcFreePtrMem) (UInt256.ofNat 8)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hmload1 :
      (if (⟨64⟩ : UInt256).toNat ≥ (potSuckCalldataMem σ'' I rad solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((potSuckCalldataMem σ'' I rad solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
    potSuckCalldataMem_mload64 σ'' I rad solcFreePtrMem_size solcFreePtrMem_read64
  have rdEnd := evm_run rd2057 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov)]
  have rd2070 := rdEnd.mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
    mem_cost hmload1 (by decide) (by evm_ov)
  have rd2079 := evm_run rd2070 with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd2079⟩

/-- `@2079 → @2095`: `extcodesize(vat) ≠ 0` ⇒ fire the `suck` CALL, exposing the opaque `Θ`-link
    and the post-`CALL` cursor. -/
theorem potDripX_postCall {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel chi_ tmp : UInt256}
    (hdepth : I.depth.val < 1024)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ'' (dripVatTargetWord σ'' I) ≠ ⟨0⟩)
    (h : RD potBytecode I g s0 ⟨2079⟩
      (dripVatTargetWord σ'' I :: dripVatTargetWord σ'' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ :: ⟨128⟩ ::
        ⟨0⟩ :: ⟨228⟩ :: potSuckSelectorWord :: dripVatTargetWord σ'' I :: chi_ :: tmp ::
        ⟨341⟩ :: [sel])
      (potSuckCalldataMem σ'' I (dripPieWord σ'' I * chi_) solcFreePtrMem)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ'') k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool) (o : ByteArray)
      (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA s0.genesisBlockHeader
          s0.blocks σ'' s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (dripVatTargetWord σ'' I))
          (toExecute σ'' (AccountAddress.ofUInt256 (dripVatTargetWord σ'' I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((potSuckCalldataMem σ'' I (dripPieWord σ'' I * chi_) solcFreePtrMem).readWithPadding
            128 100)
          (I.depth + 1) I.header I.perm)
      ∧ RD potBytecode I g s0 ⟨2095⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: potSuckSelectorWord :: dripVatTargetWord σ'' I ::
            chi_ :: tmp :: ⟨341⟩ :: [sel])
          (potSuckCalldataMem σ'' I (dripPieWord σ'' I * chi_) solcFreePtrMem)
          (UInt256.ofNat 8) o (cA', σ') k' C'
      ∧ o.size < UInt256.size := by
  obtain ⟨gasWord, k1, C1, rd2094⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2079⟩) (okPc := ⟨2091⟩) h hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd2095raw, hosz⟩ :=
    RD.call (target := dripVatTargetWord σ'' I) rd2094 (by native_decide) hdepth (by evm_ov)
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat o.size := by
      show (0 : Nat) ≤ (UInt256.ofNat o.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  have haw : UInt256.ofNat (MachineState.M
      (MachineState.M (UInt256.ofNat 8).toNat (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
      (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by native_decide
  rw [hmin, byteArray_write_len_zero, haw] at rd2095raw
  exact ⟨cA', σ', z, o, A_in, callGas, _, _, hΘ, rd2095raw, hosz⟩

set_option maxHeartbeats 0 in
/-- Post-`CALL` success tail (`z = true`): pop the frame, `return tmp` (`@341` epilogue). -/
theorem potDripX_successTail {I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel chi_ tmp w1 w2 w3 : UInt256} {o mem : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hsize : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD potBytecode I g s0 ⟨2095⟩
      (⟨1⟩ :: w1 :: w2 :: w3 :: chi_ :: tmp :: ⟨341⟩ :: [sel])
      mem (UInt256.ofNat 8) o acc k C) :
    RDret potBytecode g s0 acc (UInt256.toByteArray tmp) := by
  obtain ⟨k1, C1, rd2113⟩ := RD.solcCallSuccessGuardOk (pc := ⟨2095⟩) (okPc := ⟨2111⟩) h
    (by decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2118 := evm_run rd2113 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd341 := rd2118.jump (by native_decide) (by jump_dest) (by evm_ov)
  set memout := potSuckReturnMem mem tmp with hmemoutdef
  have hmemoutSize : memout.size = 228 := potSuckReturnMem_size tmp hsize
  have hval1 := mloadFreePtrValue (mem := mem) (aw := UInt256.ofNat 8)
    (by rw [hsize]; decide) (by decide) hread64
  have hval2 := mloadFreePtrValue (mem := memout) (aw := UInt256.ofNat 8)
    (by rw [hmemoutSize]; decide) (by decide)
    (potSuckReturnMem_read64 tmp hsize hread64)
  have hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray tmp :=
    potSuckReturnMem_read128 tmp hsize
  exact evm_run rd341 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide) mem_cost hval1 (by decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mstore 0 memout (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide)
      (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide) mem_cost hval2 (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw ret 0 (UInt256.toByteArray tmp) (by native_decide) mem_cost (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        show ((⟨32⟩ : UInt256) + UInt256.sub ⟨128⟩ ⟨128⟩).toNat = 32 from by decide]
      exact hread128) (by evm_ov)]

/-- Post-`CALL` failure tail (`z = false`): the solc success guard bubbles the revert. -/
theorem potDripX_failTail {I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel chi_ tmp w1 w2 w3 : UInt256} {o mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hosz : o.size < UInt256.size)
    (h : RD potBytecode I g s0 ⟨2095⟩
      (⟨0⟩ :: w1 :: w2 :: w3 :: chi_ :: tmp :: ⟨341⟩ :: [sel])
      mem aw o acc k C) :
    RDrev potBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2095⟩) (okPc := ⟨2111⟩) h rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- `@2079`: `extcodesize(vat) = 0` ⇒ the checked external call reverts. -/
theorem potDripX_ecsZero {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel chi_ tmp : UInt256}
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ'' (dripVatTargetWord σ'' I) = ⟨0⟩)
    (h : RD potBytecode I g s0 ⟨2079⟩
      (dripVatTargetWord σ'' I :: dripVatTargetWord σ'' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ :: ⟨128⟩ ::
        ⟨0⟩ :: ⟨228⟩ :: potSuckSelectorWord :: dripVatTargetWord σ'' I :: chi_ :: tmp ::
        ⟨341⟩ :: [sel])
      (potSuckCalldataMem σ'' I (dripPieWord σ'' I * chi_) solcFreePtrMem)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ'') k C) :
    RDrev potBytecode g s0 := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2079⟩) (okPc := ⟨2091⟩) h hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

/-- `@2079`: `depth = 1024` ⇒ the CALL cannot proceed (checked external call reverts). -/
theorem potDripX_depthLimit {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel chi_ tmp : UInt256}
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ'' (dripVatTargetWord σ'' I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (h : RD potBytecode I g s0 ⟨2079⟩
      (dripVatTargetWord σ'' I :: dripVatTargetWord σ'' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ :: ⟨128⟩ ::
        ⟨0⟩ :: ⟨228⟩ :: potSuckSelectorWord :: dripVatTargetWord σ'' I :: chi_ :: tmp ::
        ⟨341⟩ :: [sel])
      (potSuckCalldataMem σ'' I (dripPieWord σ'' I * chi_) solcFreePtrMem)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ'') k C) :
    RDrev potBytecode g s0 := by
  obtain ⟨gasWord, k1, C1, rd2094⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2079⟩) (okPc := ⟨2091⟩) h hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨k', C', rd2095⟩ :=
    RD.callDepthLimit rd2094 (by native_decide) hdepth (by evm_ov)
  exact potDripX_failTail (o := ByteArray.empty) (by decide) (by simpa using rd2095)

set_option maxHeartbeats 0 in
/-- `@1960`: `_mul(Pie, chi_)` overflow (`size ≤ chi_ * Pie`) reverts (empty revert). -/
theorem potDripX_mulReverts {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel chi_ tmp : UInt256}
    (hover : UInt256.size ≤ chi_.toNat * (dripPieWord σ'' I).toNat)
    (h : RD potBytecode I g s0 ⟨1960⟩ (chi_ :: ⟨0⟩ :: tmp :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ'') k C) :
    RDrev potBytecode g s0 := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hvatEq : UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
      (solcSlotWord σ'' I ⟨5⟩) = dripVatTargetWord σ'' I := by
    rw [hmask, u256_land_comm]; rfl
  have hvowEq : UInt256.land (solcSlotWord σ'' I ⟨6⟩)
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) = dripVowTargetWord σ'' I := by
    rw [hmask]; rfl
  have rd1962 := h.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1963⟩ := rd1962.sload (by native_decide) (by evm_ov)
  have rd1965 := rd1963.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1966⟩ := rd1965.sload (by native_decide) (by evm_ov)
  have rd1968 := rd1966.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1969⟩ := rd1968.sload (by native_decide) (by evm_ov)
  have rd1993 := evm_run rd1969 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 potSuckSelectorWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1994 := rd1993.address (by native_decide) (by evm_ov)
  have rd2001 := evm_run rd1994 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨2005⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw push2 ⟨2300⟩ (by native_decide) (by evm_ov)]
  have rd2300 := rd2001.jump (by native_decide) (by jump_dest) (by evm_ov)
  rw [hvatEq, hvowEq] at rd2300
  exact RD.potMulRevertsDrip (x := chi_) (y := solcSlotWord σ'' I ⟨2⟩) (ret := ⟨2005⟩)
    (R := [dripThisWord I, dripVowTargetWord σ'' I, potSuckSelectorWord,
      dripVatTargetWord σ'' I, chi_, tmp, ⟨341⟩, sel]) rfl
    (by simpa [dripPieWord, potSlotWord] using hover)
    (by simp only [List.length_cons, List.length_nil]; omega) rd2300

/-! ## `vat.suck(vow, this, rad)` ABI encode lemma -/

/-- The 100-byte `suck` calldata window reads back as `selector ++ vow ++ this ++ rad`. -/
theorem potSuckCalldataMem_read128_100 (σ : AccountMap) (I : ExecutionEnv) (rad : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (potSuckCalldataMem σ I rad mem).readWithPadding 128 100 =
      vatSuckSelector ++ (dripVowTargetWord σ I).toByteArray ++ (dripThisWord I).toByteArray ++
        rad.toByteArray := by
  set final := potSuckCalldataMem σ I rad mem with hfinaldef
  have hfinalSize : final.size = 228 := potSuckCalldataMem_size σ I rad hmem
  have hselectorRead : final.readWithPadding 128 4 = vatSuckSelector := by
    rw [hfinaldef]; unfold potSuckCalldataMem
    rw [toByteArray_write_read_below_len_of_gap rad (potSuckThisMem σ I mem) 196 128 4
      (by rw [potSuckThisMem_size σ I hmem]; omega) (by omega) (by omega) (by norm_num)
      (by rw [potSuckThisMem_size σ I hmem]; native_decide)]
    unfold potSuckThisMem
    rw [toByteArray_write_read_below_len_of_gap (dripThisWord I) (potSuckVowMem σ I mem) 164 128 4
      (by rw [potSuckVowMem_size σ I hmem]; omega) (by omega) (by omega) (by norm_num)
      (by rw [potSuckVowMem_size σ I hmem]; native_decide)]
    unfold potSuckVowMem
    rw [toByteArray_write_read_below_len_of_gap (dripVowTargetWord σ I) (potSuckSelectorMem mem)
      132 128 4 (by rw [potSuckSelectorMem_size hmem]; omega) (by omega) (by omega) (by norm_num)
      (by rw [potSuckSelectorMem_size hmem]; native_decide)]
    unfold potSuckSelectorMem
    have hw := toByteArray_write_read_window_of_gap potSuckSelectorShifted mem 128 0 4
      (by omega) (by omega) (by norm_num) (by rw [hmem]; native_decide)
    simp only [Nat.add_zero] at hw
    rw [hw]; native_decide
  have hvowRead : final.readWithPadding 132 32 = (dripVowTargetWord σ I).toByteArray := by
    rw [hfinaldef]; unfold potSuckCalldataMem
    rw [toByteArray_write_read_below_len_of_gap rad (potSuckThisMem σ I mem) 196 132 32
      (by rw [potSuckThisMem_size σ I hmem]; omega) (by omega) (by omega) (by norm_num)
      (by rw [potSuckThisMem_size σ I hmem]; native_decide)]
    unfold potSuckThisMem
    rw [toByteArray_write_read_below_len_of_gap (dripThisWord I) (potSuckVowMem σ I mem) 164 132 32
      (by rw [potSuckVowMem_size σ I hmem]) (by omega) (by omega) (by norm_num)
      (by rw [potSuckVowMem_size σ I hmem]; native_decide)]
    unfold potSuckVowMem
    rw [toByteArray_write_read_back_of_gap (dripVowTargetWord σ I) (potSuckSelectorMem mem) 132
      (by rw [potSuckSelectorMem_size hmem]; native_decide)]
  have hthisRead : final.readWithPadding 164 32 = (dripThisWord I).toByteArray := by
    rw [hfinaldef]; unfold potSuckCalldataMem
    rw [toByteArray_write_read_below_len_of_gap rad (potSuckThisMem σ I mem) 196 164 32
      (by rw [potSuckThisMem_size σ I hmem]) (by omega) (by omega) (by norm_num)
      (by rw [potSuckThisMem_size σ I hmem]; native_decide)]
    unfold potSuckThisMem
    rw [toByteArray_write_read_back_of_gap (dripThisWord I) (potSuckVowMem σ I mem) 164
      (by rw [potSuckVowMem_size σ I hmem]; native_decide)]
  have hradRead : final.readWithPadding 196 32 = rad.toByteArray := by
    rw [hfinaldef]; unfold potSuckCalldataMem
    rw [toByteArray_write_read_back_of_gap rad (potSuckThisMem σ I mem) 196
      (by rw [potSuckThisMem_size σ I hmem]; native_decide)]
  rw [readWithPadding_eq_extract' final 128 100 (by norm_num) (by norm_num) (by rw [hfinalSize])]
  have hselectorExt : final.extract 128 132 = vatSuckSelector := by
    rw [← readWithPadding_eq_extract' final 128 4 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hselectorRead
  have hvowExt : final.extract 132 164 = (dripVowTargetWord σ I).toByteArray := by
    rw [← readWithPadding_eq_extract' final 132 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hvowRead
  have hthisExt : final.extract 164 196 = (dripThisWord I).toByteArray := by
    rw [← readWithPadding_eq_extract' final 164 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hthisRead
  have hradExt : final.extract 196 228 = rad.toByteArray := by
    rw [← readWithPadding_eq_extract' final 196 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize])]
    exact hradRead
  have hsplit : final.extract 128 228 =
      final.extract 128 132 ++ final.extract 132 164 ++ final.extract 164 196 ++
        final.extract 196 228 := by
    rw [show final.extract 128 228 = final.extract 128 132 ++ final.extract 132 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 132 228 = final.extract 132 164 ++ final.extract 164 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 164 228 = final.extract 164 196 ++ final.extract 196 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    simp
  rw [hsplit, hselectorExt, hvowExt, hthisExt, hradExt]

/-- `config.externalABI.encode? "suck" [vow, this, rad]` is the 100-byte calldata window. -/
theorem potSuckEncode_eq (σ : AccountMap) (I : ExecutionEnv) (rad : UInt256)
    (vowA thisA : AccountAddress) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hvowWord : EVM.word ↑vowA = dripVowTargetWord σ I)
    (hthisWord : EVM.word ↑thisA = dripThisWord I) :
    config.externalABI.encode? "suck"
        [.address vowA, .address thisA, .int (Int.ofNat rad.toNat)] =
      some ((potSuckCalldataMem σ I rad mem).readWithPadding 128 100) := by
  rw [potSuckCalldataMem_read128_100 σ I rad hmem]
  have hradWord : EVM.word rad.toNat = rad := by
    show UInt256.ofNat rad.toNat = rad
    exact u256_ofNat_toNat rad
  have hradLt : rad.toNat < EVM.twoPow 256 := by
    change rad.val.val < EVM.twoPow 256
    exact rad.val.isLt
  simp [config, potExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, uint256, uint256Int,
    vatSuckSelector, selectorBytes, hvowWord, hthisWord, hradWord, hradLt,
    word_toBytesBE_toByteArray_eq_toByteArray]
  simp [ByteArray.append_assoc]

/-! ## Solm-side `_rpow(0, n, base)` (the coupling only covers `x ≠ 0`) -/

/-- `_rpow(0, n, base)` returns `base` if `n = 0`, else `0`. -/
theorem execRpowFunctionXZeroReturns (evm : EVM.State) (n : UInt256) :
    ExecFuncBody config { contract := contract, locals := uintTernaryLocals ⟨0⟩ n potRay } evm
      rpowFunction.body
      (.returned { contract := contract, locals := uintTernaryLocals ⟨0⟩ n potRay } evm
        (some [.int (Int.ofNat (if n = ⟨0⟩ then potRay else ⟨0⟩).toNat)])) := by
  let locals := uintTernaryLocals ⟨0⟩ n potRay
  have hx : evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
      .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := (⟨0⟩ : UInt256))
      (uintTernaryLocals_get_x ⟨0⟩ n potRay)
  have hn : evalExpr? config { contract := contract, locals := locals } evm (.var "n") =
      .ok (.int (Int.ofNat n.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "n") (value := n)
      (uintTernaryLocals_get_n ⟨0⟩ n potRay)
  have hbase : evalExpr? config { contract := contract, locals := locals } evm (.var "base") =
      .ok (.int (Int.ofNat potRay.toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "base") (value := potRay)
      (uintTernaryLocals_get_b ⟨0⟩ n potRay)
  have hzeroLit : evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
      .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by simp [evalExpr?, pure]
  have hxZero : evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "x") (.intLit 0)) = .ok (.bool true) :=
    evalExpr_eq_int_true hx hzeroLit rfl
  by_cases hnz : n = ⟨0⟩
  · have hnZero : evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "n") (.intLit 0)) = .ok (.bool true) := by
      apply evalExpr_eq_int_true hn hzeroLit; rw [hnz]
    have hblock : ExecBlock config { contract := contract, locals := locals } evm rpowFunction.body
        (.returned { contract := contract, locals := locals } evm
          (some [.int (Int.ofNat potRay.toNat)])) := by
      simpa [rpowFunction] using ExecBlock.consReturn (ExecStmt.iteTrue hxZero
        (ExecBlock.consReturn (ExecStmt.iteTrue hnZero
          (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hbase))))))
    simpa [locals, hnz] using ExecFuncBody.execBlockRet hblock
  · have hnZero : evalExpr? config { contract := contract, locals := locals } evm
        (.binary .eq (.var "n") (.intLit 0)) = .ok (.bool false) := by
      apply evalExpr_eq_int_false hn hzeroLit
      intro hbad; exact hnz (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    have hzeroRet : evalExpr? config { contract := contract, locals := locals } evm (.intLit 0) =
        .ok (.int 0) := by simp [evalExpr?, pure]
    have hblock : ExecBlock config { contract := contract, locals := locals } evm rpowFunction.body
        (.returned { contract := contract, locals := locals } evm (some [.int 0])) := by
      simpa [rpowFunction] using ExecBlock.consReturn (ExecStmt.iteTrue hxZero
        (ExecBlock.consReturn (ExecStmt.iteFalse hnZero
          (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzeroRet))))))
    simpa [locals, hnz] using ExecFuncBody.execBlockRet hblock

/-! ## Solm-side `drip()` body building blocks

`evm0 = initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I`.  `s0..s2` (nonpayable, `now ≥ rho`,
`_rpow`) are shared by every non-`now<rho` leaf; the `hrpow` hypothesis supplies the `_rpow` result. -/

/-- The shared `now ≥ rho` guard eval on `evm0`. -/
theorem potDripSolm_timeGuard {cA gh bl σ σ₀ A I} {g : UInt256}
    (hle : (dripRhoWord σ I).toNat ≤ (dripNowWord I).toNat) :
    evalExpr? config { contract := contract, locals := (∅ : Store) }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .ge (.env .timestamp) (.storage rhoRef)) = .ok (.bool true) := by
  refine evalExpr_dripNowGeRho_true _ ?_
  rw [dripEvm0_load (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) ⟨7⟩]
  simpa [initState, dripRhoWord, dripNowWord, potSlotWord] using hle

/-- The shared `_rpow` argument evaluation on `evm0` (empty locals). -/
theorem potDripSolm_rpowArgs {cA gh bl σ σ₀ A I} {g : UInt256}
    (hle : (dripRhoWord σ I).toNat ≤ (dripNowWord I).toNat) :
    evalExprs? config { contract := contract, locals := (∅ : Store) }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        [.storage dsrRef, sub256 (.env .timestamp) (.storage rhoRef), .intLit one] =
      .ok [.int (Int.ofNat (dripDsrWord σ I).toNat),
        .int (Int.ofNat (dripSubNowRho σ I).toNat), .int (Int.ofNat potRay.toNat)] := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  have hdsr : evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
      (.storage dsrRef) = .ok (.int (Int.ofNat (dripDsrWord σ I).toNat)) := by
    rw [evalExpr_potDsrOfLocals (by simp), dripEvm0_load (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) ⟨3⟩]
  have htime : evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
      (.env .timestamp) = .ok (.int (Int.ofNat (dripNowWord I).toNat)) := by
    simp [evalExpr?, envValue, pure, hevm0, initState, dripNowWord]
  have hrho : evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
      (.storage rhoRef) = .ok (.int (Int.ofNat (dripRhoWord σ I).toNat)) := by
    rw [evalExpr_dripStorageRho, dripEvm0_load (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) ⟨7⟩]
  have hsub : evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
      (sub256 (.env .timestamp) (.storage rhoRef)) =
        .ok (.int (Int.ofNat (dripSubNowRho σ I).toNat)) :=
    evalExpr_sub256_ok htime hrho rfl hle
  have hone : evalExpr? config { contract := contract, locals := (∅ : Store) } evm0
      (.intLit one) = .ok (.int (Int.ofNat potRay.toNat)) := by
    simp [evalExpr?, pure, one_eq_potRay_toNat]
  simp [evalExprs?, EvalResult.bind, bind, pure, hdsr, hsub, hone]

/-- `s2` returns `pow`: the `_rpow` internal call, given the coupled/`x=0` `_rpow` body. -/
theorem potDripSolm_rpowReturn {cA gh bl σ σ₀ A I} {g pow : UInt256} {rpowLocals : Store}
    (hle : (dripRhoWord σ I).toNat ≤ (dripNowWord I).toNat)
    (hrpow : ExecFuncBody config
      { contract := contract,
        locals := uintTernaryLocals (dripDsrWord σ I) (dripSubNowRho σ I) potRay }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) rpowFunction.body
      (.returned { contract := contract, locals := rpowLocals }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (some [.int (Int.ofNat pow.toNat)]))) :
    ExecStmt config { contract := contract, locals := (∅ : Store) }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (.internalCall "_rpow"
        [.storage dsrRef, sub256 (.env .timestamp) (.storage rhoRef), .intLit one] "pow")
      (.ok { contract := contract, locals := dripPowFrameLocals pow }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)) := by
  have h := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := (∅ : Store) })
    (evm := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (name := "_rpow") (retVar := "pow")
    (args := [.storage dsrRef, sub256 (.env .timestamp) (.storage rhoRef), .intLit one])
    (argVals := [.int (Int.ofNat (dripDsrWord σ I).toNat),
      .int (Int.ofNat (dripSubNowRho σ I).toNat), .int (Int.ofNat potRay.toNat)])
    (callee := rpowFunction)
    (locals := uintTernaryLocals (dripDsrWord σ I) (dripSubNowRho σ I) potRay)
    (calleeSolm := { contract := contract, locals := rpowLocals })
    (potDripSolm_rpowArgs hle) rfl
    (by simp [rpowFunction, uintTernaryLocals, bindParams?]) hrpow
  simpa [resumeAfterInternalCall, dripPowFrameLocals, collapseReturns] using h

/-- `s3` returns `tmp = _rmul(pow, chi)` when `pow * chi` fits. -/
theorem potDripSolm_rmulReturn {cA gh bl σ σ₀ A I} {g pow : UInt256}
    (hfit : pow.toNat * (dripChiWord σ I).toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := dripPowFrameLocals pow }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (.internalCall "_rmul" [.var "pow", .storage chiRef] "tmp")
      (.ok { contract := contract, locals := dripTmpFrameLocals σ I pow }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)) := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  have hpow : evalExpr? config { contract := contract, locals := dripPowFrameLocals pow } evm0
      (.var "pow") = .ok (.int (Int.ofNat pow.toNat)) :=
    evalExpr_varUInt256 (store_get_self _ _ _)
  have hchi : evalExpr? config { contract := contract, locals := dripPowFrameLocals pow } evm0
      (.storage chiRef) = .ok (.int (Int.ofNat (dripChiWord σ I).toNat)) := by
    rw [evalExpr_potChiOfLocals (by simp [dripPowFrameLocals]),
      dripEvm0_load (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) ⟨4⟩]
  have hargs : evalExprs? config { contract := contract, locals := dripPowFrameLocals pow } evm0
      [.var "pow", .storage chiRef] =
        .ok [.int (Int.ofNat pow.toNat), .int (Int.ofNat (dripChiWord σ I).toNat)] := by
    simp [evalExprs?, EvalResult.bind, bind, pure, hpow, hchi]
  have h := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := dripPowFrameLocals pow })
    (evm := evm0) (name := "_rmul") (retVar := "tmp") (args := [.var "pow", .storage chiRef])
    (argVals := [.int (Int.ofNat pow.toNat), .int (Int.ofNat (dripChiWord σ I).toNat)])
    (callee := rmulFunction) (locals := uintBinaryLocals pow (dripChiWord σ I))
    hargs rfl (by simp [rmulFunction, uintBinaryLocals, bindParams?])
    (execRmulFunctionReturn evm0 (x := pow) (y := dripChiWord σ I)
      (prod := pow * dripChiWord σ I) (q := dripTmpVal σ I pow) rfl hfit rfl)
  simpa [resumeAfterInternalCall, dripTmpFrameLocals, collapseReturns] using h

/-- `s3` reverts: `_rmul(pow, chi)` overflows in the inner `_mul`. -/
theorem potDripSolm_rmulRevert {cA gh bl σ σ₀ A I} {g pow : UInt256}
    (hover : UInt256.size ≤ pow.toNat * (dripChiWord σ I).toNat) :
    ExecStmt config { contract := contract, locals := dripPowFrameLocals pow }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (.internalCall "_rmul" [.var "pow", .storage chiRef] "tmp") .reverted := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  have hpow : evalExpr? config { contract := contract, locals := dripPowFrameLocals pow } evm0
      (.var "pow") = .ok (.int (Int.ofNat pow.toNat)) :=
    evalExpr_varUInt256 (store_get_self _ _ _)
  have hchi : evalExpr? config { contract := contract, locals := dripPowFrameLocals pow } evm0
      (.storage chiRef) = .ok (.int (Int.ofNat (dripChiWord σ I).toNat)) := by
    rw [evalExpr_potChiOfLocals (by simp [dripPowFrameLocals]),
      dripEvm0_load (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) ⟨4⟩]
  exact internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := dripPowFrameLocals pow })
    (evm := evm0) (name := "_rmul") (retVar := "tmp") (args := [.var "pow", .storage chiRef])
    (argVals := [.int (Int.ofNat pow.toNat), .int (Int.ofNat (dripChiWord σ I).toNat)])
    (callee := rmulFunction) (locals := uintBinaryLocals pow (dripChiWord σ I))
    (by simp [evalExprs?, EvalResult.bind, bind, pure, hpow, hchi]) rfl
    (by simp [rmulFunction, uintBinaryLocals, bindParams?])
    (execRmulFunctionRevert evm0 hover)

/-- `s4` returns `chi_ = _sub(tmp, chi)` when `chi ≤ tmp`. -/
theorem potDripSolm_subReturn {cA gh bl σ σ₀ A I} {g pow : UInt256}
    (hle : (dripChiWord σ I).toNat ≤ (dripTmpVal σ I pow).toNat) :
    ExecStmt config { contract := contract, locals := dripTmpFrameLocals σ I pow }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (.internalCall "_sub" [.var "tmp", .storage chiRef] "chi_")
      (.ok { contract := contract, locals := dripChiDeltaFrameLocals σ I pow }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)) := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  have htmp : evalExpr? config { contract := contract, locals := dripTmpFrameLocals σ I pow } evm0
      (.var "tmp") = .ok (.int (Int.ofNat (dripTmpVal σ I pow).toNat)) :=
    evalExpr_varUInt256 (store_get_self _ _ _)
  have hchi : evalExpr? config { contract := contract, locals := dripTmpFrameLocals σ I pow } evm0
      (.storage chiRef) = .ok (.int (Int.ofNat (dripChiWord σ I).toNat)) := by
    rw [evalExpr_potChiOfLocals (by simp [dripTmpFrameLocals, dripPowFrameLocals]),
      dripEvm0_load (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) ⟨4⟩]
  have h := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := dripTmpFrameLocals σ I pow })
    (evm := evm0) (name := "_sub") (retVar := "chi_") (args := [.var "tmp", .storage chiRef])
    (argVals := [.int (Int.ofNat (dripTmpVal σ I pow).toNat),
      .int (Int.ofNat (dripChiWord σ I).toNat)])
    (callee := subFunction) (locals := uintBinaryLocals (dripTmpVal σ I pow) (dripChiWord σ I))
    (by simp [evalExprs?, EvalResult.bind, bind, pure, htmp, hchi]) rfl
    (by simp [subFunction, uintBinaryLocals, bindParams?])
    (execSubFunctionReturn evm0 (x := dripTmpVal σ I pow) (y := dripChiWord σ I)
      (diff := dripChiDeltaVal σ I pow) rfl hle)
  simpa [resumeAfterInternalCall, dripChiDeltaFrameLocals, collapseReturns] using h

/-- `s4` reverts: `_sub(tmp, chi)` underflows (`tmp < chi`). -/
theorem potDripSolm_subRevert {cA gh bl σ σ₀ A I} {g pow : UInt256}
    (hlt : (dripTmpVal σ I pow).toNat < (dripChiWord σ I).toNat) :
    ExecStmt config { contract := contract, locals := dripTmpFrameLocals σ I pow }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (.internalCall "_sub" [.var "tmp", .storage chiRef] "chi_") .reverted := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  have htmp : evalExpr? config { contract := contract, locals := dripTmpFrameLocals σ I pow } evm0
      (.var "tmp") = .ok (.int (Int.ofNat (dripTmpVal σ I pow).toNat)) :=
    evalExpr_varUInt256 (store_get_self _ _ _)
  have hchi : evalExpr? config { contract := contract, locals := dripTmpFrameLocals σ I pow } evm0
      (.storage chiRef) = .ok (.int (Int.ofNat (dripChiWord σ I).toNat)) := by
    rw [evalExpr_potChiOfLocals (by simp [dripTmpFrameLocals, dripPowFrameLocals]),
      dripEvm0_load (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) ⟨4⟩]
  exact internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := dripTmpFrameLocals σ I pow })
    (evm := evm0) (name := "_sub") (retVar := "chi_") (args := [.var "tmp", .storage chiRef])
    (argVals := [.int (Int.ofNat (dripTmpVal σ I pow).toNat),
      .int (Int.ofNat (dripChiWord σ I).toNat)])
    (callee := subFunction) (locals := uintBinaryLocals (dripTmpVal σ I pow) (dripChiWord σ I))
    (by simp [evalExprs?, EvalResult.bind, bind, pure, htmp, hchi]) rfl
    (by simp [subFunction, uintBinaryLocals, bindParams?])
    (execSubFunctionRevert evm0 hlt)

/-- `s5`: `chi := tmp` mutates slot 4 (`evm0 → dripEvmChi`). -/
theorem potDripSolm_assignChi {cA gh bl σ σ₀ A I} {g pow : UInt256} :
    ExecStmt config { contract := contract, locals := dripChiDeltaFrameLocals σ I pow }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (.assign .storage chiRef (.var "tmp"))
      (.ok { contract := contract, locals := dripChiDeltaFrameLocals σ I pow }
        (dripEvmChi (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          (dripTmpVal σ I pow))) := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  have hval : evalExpr? config { contract := contract, locals := dripChiDeltaFrameLocals σ I pow }
      evm0 (.var "tmp") = .ok (.int (Int.ofNat (dripTmpVal σ I pow).toNat)) :=
    evalExpr_varUInt256
      (by rw [dripChiDeltaFrameLocals, store_get_ne _ _ (by decide)]; exact store_get_self _ _ _)
  exact ExecStmt.assign hval
    (dripAssignChi evm0 (dripTmpVal σ I pow)
      (by simp [dripChiDeltaFrameLocals, dripTmpFrameLocals, dripPowFrameLocals]))

/-- `s6`: `rho := now` mutates slot 7 (`dripEvmChi → dripEvmRho`). -/
theorem potDripSolm_assignRho {cA gh bl σ σ₀ A I} {g pow : UInt256} :
    ExecStmt config { contract := contract, locals := dripChiDeltaFrameLocals σ I pow }
      (dripEvmChi (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (dripTmpVal σ I pow))
      (.assign .storage rhoRef (.env .timestamp))
      (.ok { contract := contract, locals := dripChiDeltaFrameLocals σ I pow }
        (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          (dripTmpVal σ I pow) (dripNowWord I))) := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  have hval : evalExpr? config { contract := contract, locals := dripChiDeltaFrameLocals σ I pow }
      (dripEvmChi evm0 (dripTmpVal σ I pow)) (.env .timestamp) =
        .ok (.int (Int.ofNat (dripNowWord I).toNat)) := by
    simp [evalExpr?, envValue, pure, dripEvmChi, storageStore_executionEnv, hevm0, initState,
      dripNowWord]
  exact ExecStmt.assign hval
    (dripAssignRho (dripEvmChi evm0 (dripTmpVal σ I pow)) (dripNowWord I)
      (by simp [dripChiDeltaFrameLocals, dripTmpFrameLocals, dripPowFrameLocals]))

/-- `s7` returns `rad = _mul(Pie, chi_)` on `dripEvmRho` when `Pie * chi_` fits. -/
theorem potDripSolm_mulReturn {cA gh bl σ σ₀ A I} {g pow : UInt256}
    (hfit : (dripPieWord σ I).toNat * (dripChiDeltaVal σ I pow).toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := dripChiDeltaFrameLocals σ I pow }
      (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (dripTmpVal σ I pow) (dripNowWord I))
      (.internalCall "_mul" [.storage PieRef, .var "chi_"] "rad")
      (.ok { contract := contract, locals := dripRadFrameLocals σ I pow }
        (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          (dripTmpVal σ I pow) (dripNowWord I))) := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  set evmR := dripEvmRho evm0 (dripTmpVal σ I pow) (dripNowWord I) with hevmR
  have hPie : evalExpr? config { contract := contract, locals := dripChiDeltaFrameLocals σ I pow }
      evmR (.storage PieRef) = .ok (.int (Int.ofNat (dripPieWord σ I).toNat)) := by
    rw [evalExpr_potPieOfLocals
      (by simp [dripChiDeltaFrameLocals, dripTmpFrameLocals, dripPowFrameLocals])]
    rw [hevmR, dripEvmRho_load (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (tmp := dripTmpVal σ I pow) (now := dripNowWord I) ⟨2⟩ (by decide) (by decide)]
  have hchi_ : evalExpr? config { contract := contract, locals := dripChiDeltaFrameLocals σ I pow }
      evmR (.var "chi_") = .ok (.int (Int.ofNat (dripChiDeltaVal σ I pow).toNat)) :=
    evalExpr_varUInt256 (store_get_self _ _ _)
  have h := internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := dripChiDeltaFrameLocals σ I pow })
    (evm := evmR) (name := "_mul") (retVar := "rad") (args := [.storage PieRef, .var "chi_"])
    (argVals := [.int (Int.ofNat (dripPieWord σ I).toNat),
      .int (Int.ofNat (dripChiDeltaVal σ I pow).toNat)])
    (callee := mulFunction)
    (locals := uintBinaryLocals (dripPieWord σ I) (dripChiDeltaVal σ I pow))
    (by simp [evalExprs?, EvalResult.bind, bind, pure, hPie, hchi_]) rfl
    (by simp [mulFunction, uintBinaryLocals, bindParams?])
    (execMulFunctionReturn evmR (x := dripPieWord σ I) (y := dripChiDeltaVal σ I pow)
      (prod := dripRadVal σ I pow) rfl hfit)
  simpa [resumeAfterInternalCall, dripRadFrameLocals, collapseReturns] using h

/-- `s7` reverts: `_mul(Pie, chi_)` overflows. -/
theorem potDripSolm_mulRevert {cA gh bl σ σ₀ A I} {g pow : UInt256}
    (hover : UInt256.size ≤ (dripPieWord σ I).toNat * (dripChiDeltaVal σ I pow).toNat) :
    ExecStmt config { contract := contract, locals := dripChiDeltaFrameLocals σ I pow }
      (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (dripTmpVal σ I pow) (dripNowWord I))
      (.internalCall "_mul" [.storage PieRef, .var "chi_"] "rad") .reverted := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  set evmR := dripEvmRho evm0 (dripTmpVal σ I pow) (dripNowWord I) with hevmR
  have hPie : evalExpr? config { contract := contract, locals := dripChiDeltaFrameLocals σ I pow }
      evmR (.storage PieRef) = .ok (.int (Int.ofNat (dripPieWord σ I).toNat)) := by
    rw [evalExpr_potPieOfLocals
      (by simp [dripChiDeltaFrameLocals, dripTmpFrameLocals, dripPowFrameLocals])]
    rw [hevmR, dripEvmRho_load (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (tmp := dripTmpVal σ I pow) (now := dripNowWord I) ⟨2⟩ (by decide) (by decide)]
  have hchi_ : evalExpr? config { contract := contract, locals := dripChiDeltaFrameLocals σ I pow }
      evmR (.var "chi_") = .ok (.int (Int.ofNat (dripChiDeltaVal σ I pow).toNat)) :=
    evalExpr_varUInt256 (store_get_self _ _ _)
  exact internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := dripChiDeltaFrameLocals σ I pow })
    (evm := evmR) (name := "_mul") (retVar := "rad") (args := [.storage PieRef, .var "chi_"])
    (argVals := [.int (Int.ofNat (dripPieWord σ I).toNat),
      .int (Int.ofNat (dripChiDeltaVal σ I pow).toNat)])
    (callee := mulFunction)
    (locals := uintBinaryLocals (dripPieWord σ I) (dripChiDeltaVal σ I pow))
    (by simp [evalExprs?, EvalResult.bind, bind, pure, hPie, hchi_]) rfl
    (by simp [mulFunction, uintBinaryLocals, bindParams?])
    (execMulFunctionRevert evmR hover)

/-! ## Post-store `σ''` word reductions (slots `≠ 4, 7` unchanged by the two SSTOREs) -/

/-- A code-owner slot `≠ 4, 7` reads the same on the twice-stored map as on `σ`. -/
theorem potSlotWord_twiceStore_eq (σ : AccountMap) (I : ExecutionEnv) (slot v4 v7 : UInt256)
    (h4 : slot ≠ (⟨4⟩ : UInt256)) (h7 : slot ≠ (⟨7⟩ : UInt256)) :
    potSlotWord slot
      (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨4⟩ v4) ⟨7⟩ v7) I =
      potSlotWord slot σ I := by
  show ((sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨4⟩ v4) ⟨7⟩ v7).find?
        I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD slot (default : UInt256)) =
    ((σ.find? I.codeOwner).option (default : UInt256)
      (fun acc => acc.storage.findD slot (default : UInt256)))
  rw [sstoreAccountMap_storage_findD_ne (sstoreAccountMap I.codeOwner σ ⟨4⟩ v4) I.codeOwner
    slot ⟨7⟩ v7 h7]
  rw [sstoreAccountMap_storage_findD_ne σ I.codeOwner slot ⟨4⟩ v4 h4]

/-! ## `s8` `require extcodesize(vat) > 0` on `dripEvmRho` -/

/-- On `dripEvmRho`, `.storage vatRef` evaluates to the (original-`σ`) `vat` address. -/
theorem potDripSolm_evalVat {cA gh bl σ σ₀ A I} {g pow : UInt256} :
    evalExpr? config { contract := contract, locals := dripRadFrameLocals σ I pow }
      (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (dripTmpVal σ I pow) (dripNowWord I)) (.storage vatRef) =
      .ok (.address (dripVatAddress σ I)) := by
  rw [evalExpr_potVatOfLocals
    (by simp [dripRadFrameLocals, dripChiDeltaFrameLocals, dripTmpFrameLocals, dripPowFrameLocals])]
  rw [dripEvmRho_load (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (tmp := dripTmpVal σ I pow) (now := dripNowWord I) ⟨5⟩ (by decide) (by decide)]

/-- The `extcodesize(vat) > 0` guard is `true` when `vat` has nonempty code. -/
theorem potDripSolm_vatGuardTrue {cA gh bl σ σ₀ A I} {g pow : UInt256}
    (hcode : 0 < (UInt256.ofNat
      (((dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (dripTmpVal σ I pow) (dripNowWord I)).lookupAccount (dripVatAddress σ I)).option 0
        (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := dripRadFrameLocals σ I pow }
      (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (dripTmpVal σ I pow) (dripNowWord I))
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, potDripSolm_evalVat, evalBinaryOp?, EVM.Word.ofNat,
    hcode]

/-- The `extcodesize(vat) > 0` guard is `false` when `vat` has empty code. -/
theorem potDripSolm_vatGuardFalse {cA gh bl σ σ₀ A I} {g pow : UInt256}
    (hnocode : (UInt256.ofNat
      (((dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (dripTmpVal σ I pow) (dripNowWord I)).lookupAccount (dripVatAddress σ I)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := dripRadFrameLocals σ I pow }
      (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (dripTmpVal σ I pow) (dripNowWord I))
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, potDripSolm_evalVat, evalBinaryOp?, EVM.Word.ofNat,
    hnocode]

/-- On `dripEvmRho σ_solm`, the `vat` code lookup matches the twice-stored map. -/
theorem potDripSolm_vatLookup {cA gh bl σ σ₀ A I} {g v4 v7 : UInt256} :
    (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) v4 v7).lookupAccount
        (dripVatAddress σ I) =
      (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨4⟩ v4) ⟨7⟩ v7).find?
        (dripVatAddress σ I) := by
  simp only [dripEvmRho, dripEvmChi, storageStore_accountMap, storageStore_executionEnv,
    State.lookupAccount, initState]

/-- Bridge the EVM `extcodesize(vat) ≠ 0` fact to Solm-side `vat` code positivity on `dripEvmRho`. -/
theorem potDripSolm_vatCodePos {cA gh bl σ_evm σ_solm σ₀ A I} {g v4 v7 : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord
      (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ_evm ⟨4⟩ v4) ⟨7⟩ v7)
      (dripVatTargetWord
        (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ_evm ⟨4⟩ v4) ⟨7⟩ v7) I) ≠
        ⟨0⟩) :
    0 < (UInt256.ofNat
      (((dripEvmRho (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) v4 v7).lookupAccount
        (dripVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat := by
  set σ''s := sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ_solm ⟨4⟩ v4) ⟨7⟩ v7
    with hσs
  have htarget : dripVatTargetWord
      (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ_evm ⟨4⟩ v4) ⟨7⟩ v7) I =
      dripVatTargetWord σ_solm I := by
    have h1 := potSlotWord_twiceStore_eq σ_evm I ⟨5⟩ v4 v7 (by decide) (by decide)
    have h2 : potSlotWord ⟨5⟩ σ_evm I = potSlotWord ⟨5⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
    simp only [dripVatTargetWord, potAddressReturnWord, h1, h2]
  have haccEquiv : accountMapEquiv
      (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ_evm ⟨4⟩ v4) ⟨7⟩ v7) σ''s :=
    accountMapEquiv_sstoreAccountMap_two I.codeOwner I.codeOwner ⟨4⟩ v4 ⟨7⟩ v7 hAccounts
  have hne : Reasoning.Theory.extCodeSizeWord σ''s (dripVatTargetWord σ_solm I) ≠ ⟨0⟩ := by
    rw [← htarget, ← Reasoning.Theory.extCodeSizeWord_accountMapEquiv haccEquiv]
    exact hcodeSize
  rw [potDripSolm_vatLookup, ← hσs]
  have haddr : dripVatAddress σ_solm I = AccountAddress.ofUInt256 (dripVatTargetWord σ_solm I) := by
    rw [dripVatAddress]; exact (accountAddress_ofUInt256_eq_ofNat_toNat _).symm
  rw [haddr]
  unfold Reasoning.Theory.extCodeSizeWord at hne
  cases hf : σ''s.find? (AccountAddress.ofUInt256 (dripVatTargetWord σ_solm I)) with
  | none => simp only [hf, Option.option] at hne; exact absurd rfl hne
  | some acc =>
      simp only [hf, Option.option, Function.comp] at hne ⊢
      exact Nat.pos_of_ne_zero (fun h => hne (uint256_toNat_eq_zero h))

/-- Bridge the EVM `extcodesize(vat) = 0` fact to Solm-side `vat` empty code on `dripEvmRho`. -/
theorem potDripSolm_vatCodeZero {cA gh bl σ_evm σ_solm σ₀ A I} {g v4 v7 : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord
      (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ_evm ⟨4⟩ v4) ⟨7⟩ v7)
      (dripVatTargetWord
        (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ_evm ⟨4⟩ v4) ⟨7⟩ v7) I) =
        ⟨0⟩) :
    (UInt256.ofNat
      (((dripEvmRho (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) v4 v7).lookupAccount
        (dripVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  set σ''s := sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ_solm ⟨4⟩ v4) ⟨7⟩ v7
    with hσs
  have htarget : dripVatTargetWord
      (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ_evm ⟨4⟩ v4) ⟨7⟩ v7) I =
      dripVatTargetWord σ_solm I := by
    have h1 := potSlotWord_twiceStore_eq σ_evm I ⟨5⟩ v4 v7 (by decide) (by decide)
    have h2 : potSlotWord ⟨5⟩ σ_evm I = potSlotWord ⟨5⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
    simp only [dripVatTargetWord, potAddressReturnWord, h1, h2]
  have haccEquiv : accountMapEquiv
      (sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ_evm ⟨4⟩ v4) ⟨7⟩ v7) σ''s :=
    accountMapEquiv_sstoreAccountMap_two I.codeOwner I.codeOwner ⟨4⟩ v4 ⟨7⟩ v7 hAccounts
  have hz : Reasoning.Theory.extCodeSizeWord σ''s (dripVatTargetWord σ_solm I) = ⟨0⟩ := by
    rw [← htarget, ← Reasoning.Theory.extCodeSizeWord_accountMapEquiv haccEquiv]
    exact hcodeSize
  rw [potDripSolm_vatLookup, ← hσs]
  have haddr : dripVatAddress σ_solm I = AccountAddress.ofUInt256 (dripVatTargetWord σ_solm I) := by
    rw [dripVatAddress]; exact (accountAddress_ofUInt256_eq_ofNat_toNat _).symm
  rw [haddr]
  unfold Reasoning.Theory.extCodeSizeWord at hz
  cases hf : σ''s.find? (AccountAddress.ofUInt256 (dripVatTargetWord σ_solm I)) with
  | none => simp only [Option.option]; native_decide
  | some acc =>
      simp only [hf, Option.option, Function.comp] at hz ⊢
      exact congrArg UInt256.toNat hz

/-! ## Solm-side full-body leaves (one per control-flow outcome) -/

/-- The shared `require callvalue == 0` opener on `evm0`. -/
theorem potDripSolm_cv {cA gh bl σ σ₀ A I} {g : UInt256} (hwv : I.weiValue = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := (∅ : Store) }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
  evalCallvalueEq_true (by simp only [initState]; exact hwv)

/-- `L3`: `_rmul` overflow reverts the whole body. -/
theorem potDripSolmBody_rmulReverts {cA gh bl σ σ₀ A I} {g pow : UInt256} {rpowLocals : Store}
    (hwv : I.weiValue = ⟨0⟩)
    (hle : (dripRhoWord σ I).toNat ≤ (dripNowWord I).toNat)
    (hrpow : ExecFuncBody config
      { contract := contract,
        locals := uintTernaryLocals (dripDsrWord σ I) (dripSubNowRho σ I) potRay }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) rpowFunction.body
      (.returned { contract := contract, locals := rpowLocals }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (some [.int (Int.ofNat pow.toNat)])))
    (hover : UInt256.size ≤ pow.toNat * (dripChiWord σ I).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      dripTransition.body .reverted := by
  have hblock : ExecBlock config { contract := contract, locals := (∅ : Store) }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) dripTransition.body .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_cv hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_timeGuard hle)) ?_
    refine ExecBlock.consNormal (potDripSolm_rpowReturn hle hrpow) ?_
    exact ExecBlock.consRevert (potDripSolm_rmulRevert hover)
  exact ExecFuncBody.execBlockRevert hblock

/-- `L4`: `_sub` underflow reverts the whole body. -/
theorem potDripSolmBody_subReverts {cA gh bl σ σ₀ A I} {g pow : UInt256} {rpowLocals : Store}
    (hwv : I.weiValue = ⟨0⟩)
    (hle : (dripRhoWord σ I).toNat ≤ (dripNowWord I).toNat)
    (hrpow : ExecFuncBody config
      { contract := contract,
        locals := uintTernaryLocals (dripDsrWord σ I) (dripSubNowRho σ I) potRay }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) rpowFunction.body
      (.returned { contract := contract, locals := rpowLocals }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (some [.int (Int.ofNat pow.toNat)])))
    (hfitRmul : pow.toNat * (dripChiWord σ I).toNat < UInt256.size)
    (hlt : (dripTmpVal σ I pow).toNat < (dripChiWord σ I).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      dripTransition.body .reverted := by
  have hblock : ExecBlock config { contract := contract, locals := (∅ : Store) }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) dripTransition.body .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_cv hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_timeGuard hle)) ?_
    refine ExecBlock.consNormal (potDripSolm_rpowReturn hle hrpow) ?_
    refine ExecBlock.consNormal (potDripSolm_rmulReturn hfitRmul) ?_
    exact ExecBlock.consRevert (potDripSolm_subRevert hlt)
  exact ExecFuncBody.execBlockRevert hblock

/-- `L5`: `_mul(Pie, chi_)` overflow reverts (after the two SSTOREs). -/
theorem potDripSolmBody_mulReverts {cA gh bl σ σ₀ A I} {g pow : UInt256} {rpowLocals : Store}
    (hwv : I.weiValue = ⟨0⟩)
    (hle : (dripRhoWord σ I).toNat ≤ (dripNowWord I).toNat)
    (hrpow : ExecFuncBody config
      { contract := contract,
        locals := uintTernaryLocals (dripDsrWord σ I) (dripSubNowRho σ I) potRay }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) rpowFunction.body
      (.returned { contract := contract, locals := rpowLocals }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (some [.int (Int.ofNat pow.toNat)])))
    (hfitRmul : pow.toNat * (dripChiWord σ I).toNat < UInt256.size)
    (hleSub : (dripChiWord σ I).toNat ≤ (dripTmpVal σ I pow).toNat)
    (hover : UInt256.size ≤ (dripPieWord σ I).toNat * (dripChiDeltaVal σ I pow).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      dripTransition.body .reverted := by
  have hblock : ExecBlock config { contract := contract, locals := (∅ : Store) }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) dripTransition.body .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_cv hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_timeGuard hle)) ?_
    refine ExecBlock.consNormal (potDripSolm_rpowReturn hle hrpow) ?_
    refine ExecBlock.consNormal (potDripSolm_rmulReturn hfitRmul) ?_
    refine ExecBlock.consNormal (potDripSolm_subReturn hleSub) ?_
    refine ExecBlock.consNormal potDripSolm_assignChi ?_
    refine ExecBlock.consNormal potDripSolm_assignRho ?_
    exact ExecBlock.consRevert (potDripSolm_mulRevert hover)
  exact ExecFuncBody.execBlockRevert hblock

/-- `L6`: `extcodesize(vat) = 0` reverts (checked external call). -/
theorem potDripSolmBody_ecsZero {cA gh bl σ σ₀ A I} {g pow : UInt256} {rpowLocals : Store}
    (hwv : I.weiValue = ⟨0⟩)
    (hle : (dripRhoWord σ I).toNat ≤ (dripNowWord I).toNat)
    (hrpow : ExecFuncBody config
      { contract := contract,
        locals := uintTernaryLocals (dripDsrWord σ I) (dripSubNowRho σ I) potRay }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) rpowFunction.body
      (.returned { contract := contract, locals := rpowLocals }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (some [.int (Int.ofNat pow.toNat)])))
    (hfitRmul : pow.toNat * (dripChiWord σ I).toNat < UInt256.size)
    (hleSub : (dripChiWord σ I).toNat ≤ (dripTmpVal σ I pow).toNat)
    (hfitMul : (dripPieWord σ I).toNat * (dripChiDeltaVal σ I pow).toNat < UInt256.size)
    (hnocode : (UInt256.ofNat
      (((dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (dripTmpVal σ I pow) (dripNowWord I)).lookupAccount (dripVatAddress σ I)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      dripTransition.body .reverted := by
  have hblock : ExecBlock config { contract := contract, locals := (∅ : Store) }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) dripTransition.body .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_cv hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_timeGuard hle)) ?_
    refine ExecBlock.consNormal (potDripSolm_rpowReturn hle hrpow) ?_
    refine ExecBlock.consNormal (potDripSolm_rmulReturn hfitRmul) ?_
    refine ExecBlock.consNormal (potDripSolm_subReturn hleSub) ?_
    refine ExecBlock.consNormal potDripSolm_assignChi ?_
    refine ExecBlock.consNormal potDripSolm_assignRho ?_
    refine ExecBlock.consNormal (potDripSolm_mulReturn hfitMul) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse (potDripSolm_vatGuardFalse hnocode))
  exact ExecFuncBody.execBlockRevert hblock

/-- `s9` argument evaluation `[vow, this, rad]` on `dripEvmRho`. -/
theorem potDripSolm_suckArgs {cA gh bl σ σ₀ A I} {g pow : UInt256} :
    evalExprs? config { contract := contract, locals := dripRadFrameLocals σ I pow }
      (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (dripTmpVal σ I pow) (dripNowWord I))
      [.storage vowRef, .env .this, .var "rad"] =
      .ok [.address (AccountAddress.ofNat (dripVowTargetWord σ I).toNat),
        .address I.codeOwner, .int (Int.ofNat (dripRadVal σ I pow).toNat)] := by
  set evmR := dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
    (dripTmpVal σ I pow) (dripNowWord I) with hevmR
  have hvow : evalExpr? config { contract := contract, locals := dripRadFrameLocals σ I pow }
      evmR (.storage vowRef) =
        .ok (.address (AccountAddress.ofNat (dripVowTargetWord σ I).toNat)) := by
    rw [evalExpr_potVowOfLocals
      (by simp [dripRadFrameLocals, dripChiDeltaFrameLocals, dripTmpFrameLocals, dripPowFrameLocals])]
    rw [hevmR, dripEvmRho_load (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (tmp := dripTmpVal σ I pow) (now := dripNowWord I) ⟨6⟩ (by decide) (by decide)]
  have hthis : evalExpr? config { contract := contract, locals := dripRadFrameLocals σ I pow }
      evmR (.env .this) = .ok (.address I.codeOwner) := by
    simp [evalExpr?, envValue, pure, hevmR, dripEvmRho, dripEvmChi, storageStore_executionEnv,
      initState]
  have hrad : evalExpr? config { contract := contract, locals := dripRadFrameLocals σ I pow }
      evmR (.var "rad") = .ok (.int (Int.ofNat (dripRadVal σ I pow).toNat)) :=
    evalExpr_varUInt256 (store_get_self _ _ _)
  simp [evalExprs?, EvalResult.bind, bind, pure, hvow, hthis, hrad]

/-- `L7`: the `vat.suck` call fails (`z = false`), reverting the whole body. -/
theorem potDripSolmBody_callFail {cA gh bl σ σ₀ A I} {g pow : UInt256} {rpowLocals : Store}
    {evm' : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hle : (dripRhoWord σ I).toNat ≤ (dripNowWord I).toNat)
    (hrpow : ExecFuncBody config
      { contract := contract,
        locals := uintTernaryLocals (dripDsrWord σ I) (dripSubNowRho σ I) potRay }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) rpowFunction.body
      (.returned { contract := contract, locals := rpowLocals }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (some [.int (Int.ofNat pow.toNat)])))
    (hfitRmul : pow.toNat * (dripChiWord σ I).toNat < UInt256.size)
    (hleSub : (dripChiWord σ I).toNat ≤ (dripTmpVal σ I pow).toNat)
    (hfitMul : (dripPieWord σ I).toNat * (dripChiDeltaVal σ I pow).toNat < UInt256.size)
    (hcodePos : 0 < (UInt256.ofNat
      (((dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (dripTmpVal σ I pow) (dripNowWord I)).lookupAccount (dripVatAddress σ I)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config
      (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (dripTmpVal σ I pow) (dripNowWord I))
      (EVM.address (dripVatAddress σ I)) "suck" 0
      [.address (AccountAddress.ofNat (dripVowTargetWord σ I).toNat), .address I.codeOwner,
        .int (Int.ofNat (dripRadVal σ I pow).toNat)] (false, evm', out) true) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      dripTransition.body .reverted := by
  have hblock : ExecBlock config { contract := contract, locals := (∅ : Store) }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) dripTransition.body .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_cv hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_timeGuard hle)) ?_
    refine ExecBlock.consNormal (potDripSolm_rpowReturn hle hrpow) ?_
    refine ExecBlock.consNormal (potDripSolm_rmulReturn hfitRmul) ?_
    refine ExecBlock.consNormal (potDripSolm_subReturn hleSub) ?_
    refine ExecBlock.consNormal potDripSolm_assignChi ?_
    refine ExecBlock.consNormal potDripSolm_assignRho ?_
    refine ExecBlock.consNormal (potDripSolm_mulReturn hfitMul) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_vatGuardTrue hcodePos)) ?_
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure potDripSolm_evalVat
      (by simp [evalExpr?, pure]) potDripSolm_suckArgs hcall)
  exact ExecFuncBody.execBlockRevert hblock

/-- `L8`: the `vat.suck` call succeeds (`z = true`), the body returns `tmp`. -/
theorem potDripSolmBody_callSucc {cA gh bl σ σ₀ A I} {g pow : UInt256} {rpowLocals : Store}
    {evm' : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hle : (dripRhoWord σ I).toNat ≤ (dripNowWord I).toNat)
    (hrpow : ExecFuncBody config
      { contract := contract,
        locals := uintTernaryLocals (dripDsrWord σ I) (dripSubNowRho σ I) potRay }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) rpowFunction.body
      (.returned { contract := contract, locals := rpowLocals }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (some [.int (Int.ofNat pow.toNat)])))
    (hfitRmul : pow.toNat * (dripChiWord σ I).toNat < UInt256.size)
    (hleSub : (dripChiWord σ I).toNat ≤ (dripTmpVal σ I pow).toNat)
    (hfitMul : (dripPieWord σ I).toNat * (dripChiDeltaVal σ I pow).toNat < UInt256.size)
    (hcodePos : 0 < (UInt256.ofNat
      (((dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (dripTmpVal σ I pow) (dripNowWord I)).lookupAccount (dripVatAddress σ I)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config
      (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (dripTmpVal σ I pow) (dripNowWord I))
      (EVM.address (dripVatAddress σ I)) "suck" 0
      [.address (AccountAddress.ofNat (dripVowTargetWord σ I).toNat), .address I.codeOwner,
        .int (Int.ofNat (dripRadVal σ I pow).toNat)] (true, evm', out) true)
    (hdec : config.externalABI.decode? "suck" out = some []) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      dripTransition.body
      (.returned { contract := contract, locals := dripSuckFrameLocals σ I pow } evm'
        (some [.int (Int.ofNat (dripTmpVal σ I pow).toNat)])) := by
  have hblock : ExecBlock config { contract := contract, locals := (∅ : Store) }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) dripTransition.body
      (.returned { contract := contract, locals := dripSuckFrameLocals σ I pow } evm'
        (some [.int (Int.ofNat (dripTmpVal σ I pow).toNat)])) := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_cv hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_timeGuard hle)) ?_
    refine ExecBlock.consNormal (potDripSolm_rpowReturn hle hrpow) ?_
    refine ExecBlock.consNormal (potDripSolm_rmulReturn hfitRmul) ?_
    refine ExecBlock.consNormal (potDripSolm_subReturn hleSub) ?_
    refine ExecBlock.consNormal potDripSolm_assignChi ?_
    refine ExecBlock.consNormal potDripSolm_assignRho ?_
    refine ExecBlock.consNormal (potDripSolm_mulReturn hfitMul) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_vatGuardTrue hcodePos)) ?_
    refine ExecBlock.consNormal (ExecStmt.externalCallSuccess potDripSolm_evalVat
      (by simp [evalExpr?, pure]) potDripSolm_suckArgs hcall hdec) ?_
    exact ExecBlock.consReturn (ExecStmt.return
      (evalExprs?_singleton (evalExpr_varUInt256 (dripSuckFrameLocals_get_tmp σ I pow))))
  exact ExecFuncBody.execBlockRet hblock

/-! ## `dripEvmRho` field-preservation (for the external-call bridge) -/

theorem storageStore_genesisBlockHeader (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (EVM.storageStore evm a slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  simp only [EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount]

theorem storageStore_blocks_drip (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (EVM.storageStore evm a slot val).blocks = evm.blocks := by
  simp only [EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount]

theorem storageStore_σ₀_drip (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (EVM.storageStore evm a slot val).σ₀ = evm.σ₀ := by
  simp only [EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount]

theorem storageStore_substate_drip (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (EVM.storageStore evm a slot val).substate = evm.substate := by
  simp only [EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount]

theorem dripEvmRho_executionEnv {cA gh bl σ σ₀ A I} {g tmp now : UInt256} :
    (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) tmp now).executionEnv = I := by
  simp only [dripEvmRho, dripEvmChi, storageStore_executionEnv, initState]

theorem dripEvmRho_createdAccounts {cA gh bl σ σ₀ A I} {g tmp now : UInt256} :
    (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) tmp now).createdAccounts = cA := by
  simp only [dripEvmRho, dripEvmChi, storageStore_createdAccounts, initState]

theorem dripEvmRho_genesisBlockHeader {cA gh bl σ σ₀ A I} {g tmp now : UInt256} :
    (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) tmp now).genesisBlockHeader =
      gh := by
  simp only [dripEvmRho, dripEvmChi, storageStore_genesisBlockHeader, initState]

theorem dripEvmRho_blocks {cA gh bl σ σ₀ A I} {g tmp now : UInt256} :
    (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) tmp now).blocks = bl := by
  simp only [dripEvmRho, dripEvmChi, storageStore_blocks_drip, initState]

theorem dripEvmRho_σ₀ {cA gh bl σ σ₀ A I} {g tmp now : UInt256} :
    (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) tmp now).σ₀ = σ₀ := by
  simp only [dripEvmRho, dripEvmChi, storageStore_σ₀_drip, initState]

theorem dripEvmRho_substate {cA gh bl σ σ₀ A I} {g tmp now : UInt256} :
    (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) tmp now).substate = A := by
  simp only [dripEvmRho, dripEvmChi, storageStore_substate_drip, initState]

theorem dripEvmRho_accountMap {cA gh bl σ σ₀ A I} {g tmp now : UInt256} :
    (dripEvmRho (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) tmp now).accountMap =
      sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨4⟩ tmp) ⟨7⟩ now := by
  simp only [dripEvmRho, dripEvmChi, storageStore_accountMap, storageStore_executionEnv, initState]

theorem potEvmAddress_accountAddress (a : AccountAddress) : EVM.address a.val = a := by
  apply Fin.ext
  show a.val % EVM.addressModulus = a.val
  rw [show EVM.addressModulus = AccountAddress.size from by decide]
  exact Nat.mod_eq_of_lt a.isLt

/-- The `now ≥ rho` guard is `false` on `evm0` when `now < rho`. -/
theorem potDripSolm_timeGuardFalse {cA gh bl σ σ₀ A I} {g : UInt256}
    (hlt : (dripNowWord I).toNat < (dripRhoWord σ I).toNat) :
    evalExpr? config { contract := contract, locals := (∅ : Store) }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .ge (.env .timestamp) (.storage rhoRef)) = .ok (.bool false) := by
  refine evalExpr_dripNowGeRho_false _ ?_
  rw [dripEvm0_load (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) ⟨7⟩]
  simpa [initState, dripRhoWord, dripNowWord, potSlotWord] using hlt

/-- `L1`: `now < rho` reverts at the `require now ≥ rho` guard. -/
theorem potDripSolmBody_invalidNow {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlt : (dripNowWord I).toNat < (dripRhoWord σ I).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      dripTransition.body .reverted := by
  have hblock : ExecBlock config { contract := contract, locals := (∅ : Store) }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) dripTransition.body .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_cv hwv)) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse (potDripSolm_timeGuardFalse hlt))
  exact ExecFuncBody.execBlockRevert hblock

/-- `s2` reverts: the `_rpow` internal call reverts (from the coupled loop). -/
theorem potDripSolm_rpowRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    (hle : (dripRhoWord σ I).toNat ≤ (dripNowWord I).toNat)
    (hrpow : ExecFuncBody config
      { contract := contract,
        locals := uintTernaryLocals (dripDsrWord σ I) (dripSubNowRho σ I) potRay }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) rpowFunction.body .reverted) :
    ExecStmt config { contract := contract, locals := (∅ : Store) }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (.internalCall "_rpow"
        [.storage dsrRef, sub256 (.env .timestamp) (.storage rhoRef), .intLit one] "pow")
      .reverted :=
  internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := (∅ : Store) })
    (evm := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (name := "_rpow") (retVar := "pow")
    (args := [.storage dsrRef, sub256 (.env .timestamp) (.storage rhoRef), .intLit one])
    (argVals := [.int (Int.ofNat (dripDsrWord σ I).toNat),
      .int (Int.ofNat (dripSubNowRho σ I).toNat), .int (Int.ofNat potRay.toNat)])
    (callee := rpowFunction)
    (locals := uintTernaryLocals (dripDsrWord σ I) (dripSubNowRho σ I) potRay)
    (potDripSolm_rpowArgs hle) rfl
    (by simp [rpowFunction, uintTernaryLocals, bindParams?]) hrpow

/-- `L2`: the `_rpow` call reverts the whole body. -/
theorem potDripSolmBody_rpowReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hle : (dripRhoWord σ I).toNat ≤ (dripNowWord I).toNat)
    (hrpow : ExecFuncBody config
      { contract := contract,
        locals := uintTernaryLocals (dripDsrWord σ I) (dripSubNowRho σ I) potRay }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) rpowFunction.body .reverted) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∅
      dripTransition.body .reverted := by
  have hblock : ExecBlock config { contract := contract, locals := (∅ : Store) }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) dripTransition.body .reverted := by
    simp only [dripTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_cv hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (potDripSolm_timeGuard hle)) ?_
    exact ExecBlock.consRevert (potDripSolm_rpowRevert hle hrpow)
  exact ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 0 in
/-- Downstream of `_rpow` (shared by `dsr = 0` and the coupled `dsr ≠ 0` return branch): the
    `_rmul`/`_sub`/store/`_mul`/`vat.suck` cascade and its EVM↔Solm glue. -/
theorem potDripBodyAfterRpow {cA gh bl σ_evm σ_solm σ₀ A I} {g pow : UInt256} {rpowLocals : Store}
    {sel : UInt256} {k C : ℕ}
    (hcode : I.code = potBytecode) (_hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some dripTransition)
    (hdecode : decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
      (transitionSignature dripTransition).paramTypes I.calldata = some ∅)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hle : (dripRhoWord σ_evm I).toNat ≤ (dripNowWord I).toNat)
    (hrpow : ExecFuncBody config
      { contract := contract,
        locals := uintTernaryLocals (dripDsrWord σ_solm I) (dripSubNowRho σ_solm I) potRay }
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) rpowFunction.body
      (.returned { contract := contract, locals := rpowLocals }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (some [.int (Int.ofNat pow.toNat)])))
    (rd1926 : RD potBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1926⟩
      (pow :: ⟨1934⟩ :: ⟨0⟩ :: ⟨341⟩ :: [sel]) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hchi : dripChiWord σ_evm I = dripChiWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
  have hPie : dripPieWord σ_evm I = dripPieWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hVat : potSlotWord ⟨5⟩ σ_evm I = potSlotWord ⟨5⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hVow : potSlotWord ⟨6⟩ σ_evm I = potSlotWord ⟨6⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have hrho : dripRhoWord σ_evm I = dripRhoWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨7⟩ ⟨0⟩
  have hleSolm : (dripRhoWord σ_solm I).toNat ≤ (dripNowWord I).toNat := hrho ▸ hle
  by_cases hfitRmul : pow.toNat * (dripChiWord σ_solm I).toNat < UInt256.size
  · obtain ⟨_, _, rd1934⟩ := potDripX_rmulReturns (by rw [hchi]; exact hfitRmul) rd1926
    rw [hchi] at rd1934
    by_cases hleSub : (dripChiWord σ_solm I).toNat ≤ (dripTmpVal σ_solm I pow).toNat
    · obtain ⟨_, _, rd1950⟩ := potDripX_subReturns (by rw [hchi]; exact hleSub) rd1934
      rw [hchi] at rd1950
      obtain ⟨_, _, rd1960⟩ := potDripX_stores hperm rd1950
      set σ2 := sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ_evm ⟨4⟩
        (dripTmpVal σ_solm I pow)) ⟨7⟩ (UInt256.ofNat I.header.timestamp) with hσ2
      have hPie'' : dripPieWord σ2 I = dripPieWord σ_solm I := by
        show potSlotWord ⟨2⟩ σ2 I = dripPieWord σ_solm I
        rw [hσ2, potSlotWord_twiceStore_eq σ_evm I ⟨2⟩ _ _ (by decide) (by decide)]; exact hPie
      by_cases hfitMul :
          (dripPieWord σ_solm I).toNat * (dripChiDeltaVal σ_solm I pow).toNat < UInt256.size
      · obtain ⟨_, _, rd2005⟩ := potDripX_mulReady (by rw [hPie'', Nat.mul_comm]; exact hfitMul)
          rd1960
        obtain ⟨_, _, rd2079⟩ := potDripX_callGuard rd2005
        by_cases hecs :
            Reasoning.Theory.extCodeSizeWord σ2 (dripVatTargetWord σ2 I) = ⟨0⟩
        · exact RDrev.reEquivExecutionRevert hcode (potDripX_ecsZero hecs rd2079) hdispatch hdecode
            (potDripSolmBody_ecsZero hwv hleSolm hrpow hfitRmul hleSub hfitMul
              (potDripSolm_vatCodeZero (v4 := dripTmpVal σ_solm I pow)
                (v7 := UInt256.ofNat I.header.timestamp) hAccounts hecs))
        · have hVat'' : dripVatTargetWord σ2 I = dripVatTargetWord σ_solm I := by
            simp only [dripVatTargetWord, potAddressReturnWord, hσ2,
              potSlotWord_twiceStore_eq σ_evm I ⟨5⟩ _ _ (by decide) (by decide), hVat]
          have hVow'' : dripVowTargetWord σ2 I = dripVowTargetWord σ_solm I := by
            simp only [dripVowTargetWord, potAddressReturnWord, hσ2,
              potSlotWord_twiceStore_eq σ_evm I ⟨6⟩ _ _ (by decide) (by decide), hVow]
          have hradEq2 :
              dripPieWord σ2 I * dripChiDeltaVal σ_solm I pow = dripRadVal σ_solm I pow := by
            rw [hPie'']
          have hcodePos : 0 < (UInt256.ofNat
              (((dripEvmRho (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I)).lookupAccount
                  (dripVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat :=
            potDripSolm_vatCodePos (v4 := dripTmpVal σ_solm I pow)
              (v7 := UInt256.ofNat I.header.timestamp) hAccounts hecs
          have hvowWord :
              EVM.word ↑(AccountAddress.ofNat (dripVowTargetWord σ_solm I).toNat) =
                dripVowTargetWord σ2 I := by
            rw [hVow'']
            show UInt256.ofNat (AccountAddress.ofNat (dripVowTargetWord σ_solm I).toNat).val =
              dripVowTargetWord σ_solm I
            rw [show (AccountAddress.ofNat (dripVowTargetWord σ_solm I).toNat).val =
                (dripVowTargetWord σ_solm I).toNat from
              Nat.mod_eq_of_lt (lt_of_lt_of_le (dripVowTargetWord_canonical σ_solm I)
                (le_of_eq (by decide)))]
            exact u256_ofNat_toNat _
          have hthisWord : EVM.word ↑I.codeOwner = dripThisWord I := by
            show UInt256.ofNat I.codeOwner.val = UInt256.ofNat I.codeOwner.val; rfl
          have hcd : config.externalABI.encode? "suck"
              [.address (AccountAddress.ofNat (dripVowTargetWord σ_solm I).toNat),
                .address I.codeOwner, .int (Int.ofNat (dripRadVal σ_solm I pow).toNat)] =
              some ((potSuckCalldataMem σ2 I (dripPieWord σ2 I * dripChiDeltaVal σ_solm I pow)
                solcFreePtrMem).readWithPadding 128 100) := by
            rw [hradEq2]
            exact potSuckEncode_eq σ2 I (dripRadVal σ_solm I pow)
              (AccountAddress.ofNat (dripVowTargetWord σ_solm I).toNat) I.codeOwner
              solcFreePtrMem_size hvowWord hthisWord
          have htgt : EVM.address (dripVatAddress σ_solm I) =
              AccountAddress.ofUInt256 (dripVatTargetWord σ2 I) := by
            rw [show dripVatAddress σ_solm I =
                AccountAddress.ofUInt256 (dripVatTargetWord σ_solm I) from
              (accountAddress_ofUInt256_eq_ofNat_toNat _).symm, hVat'']
            exact potEvmAddress_accountAddress _
          by_cases hdepth : I.depth.val < 1024
          case neg =>
            have hdepthEq : I.depth = 1024 := by
              apply Fin.ext
              have hlt := Nat.le_of_lt_succ I.depth.isLt
              have h1024 : (1024 : Fin 1025).val = 1024 := by decide
              omega
            have hcallSolm := callNotMade_depthLimit (cfg := config)
              (evm := dripEvmRho (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I))
              (tgt := EVM.address (dripVatAddress σ_solm I)) (name := "suck")
              (args := [.address (AccountAddress.ofNat (dripVowTargetWord σ_solm I).toNat),
                .address I.codeOwner, .int (Int.ofNat (dripRadVal σ_solm I pow).toNat)])
              (callPerm := true) hcd (by rw [dripEvmRho_executionEnv]; exact hdepthEq)
            exact RDrev.reEquivExecutionRevert hcode (potDripX_depthLimit hecs hdepthEq rd2079)
              hdispatch hdecode (potDripSolmBody_callFail hwv hleSolm hrpow hfitRmul hleSub hfitMul
                hcodePos hcallSolm)
          have hdepthNe : (dripEvmRho (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (dripTmpVal σ_solm I pow) (dripNowWord I)).executionEnv.depth ≠ 1024 := by
            rw [dripEvmRho_executionEnv]; exact potDepth_ne_1024_of_lt hdepth
          obtain ⟨cA', σ', z, o, A_in, callGas, _, _, hΘ, rd2095, hosz⟩ :=
            potDripX_postCall hdepth hecs rd2079
          rcases hΘ with ⟨g'', A', hΘ⟩
          have hΘE : (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ
              (dripEvmRho (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I)).executionEnv.blobVersionedHashes
              (dripEvmRho (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I)).createdAccounts
              (dripEvmRho (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I)).genesisBlockHeader
              (dripEvmRho (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I)).blocks
              (dripEvmRho (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I)).accountMap
              (dripEvmRho (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I)).σ₀ A_in
              (AccountAddress.ofUInt256 (UInt256.ofNat
                (dripEvmRho (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  (dripTmpVal σ_solm I pow) (dripNowWord I)).executionEnv.codeOwner))
              (dripEvmRho (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I)).executionEnv.sender
              (AccountAddress.ofUInt256 (dripVatTargetWord σ2 I))
              (toExecute (dripEvmRho (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I)).accountMap
                (AccountAddress.ofUInt256 (dripVatTargetWord σ2 I)))
              callGas (UInt256.ofNat (dripEvmRho (initState cA gh bl σ_evm σ₀
                (Sat256.ofUInt256 g) A I) (dripTmpVal σ_solm I pow)
                (dripNowWord I)).executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
              ((potSuckCalldataMem σ2 I (dripPieWord σ2 I * dripChiDeltaVal σ_solm I pow)
                solcFreePtrMem).readWithPadding (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
              ((dripEvmRho (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I)).executionEnv.depth + 1)
              (dripEvmRho (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I)).executionEnv.header true := by
            simpa only [dripEvmRho_executionEnv, dripEvmRho_createdAccounts,
              dripEvmRho_genesisBlockHeader, dripEvmRho_blocks, dripEvmRho_σ₀,
              dripEvmRho_accountMap, hperm] using hΘ
          obtain ⟨σ'_solm, A'_solm, hcallSolm, hAccounts'⟩ :=
            typedCallViaEVM_callMade_accountMapEquiv (cfg := config)
              (evm_evm := dripEvmRho (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I))
              (evm_solm := dripEvmRho (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I))
              (tgt := EVM.address (dripVatAddress σ_solm I))
              (targetWord := dripVatTargetWord σ2 I) (name := "suck")
              (args := [.address (AccountAddress.ofNat (dripVowTargetWord σ_solm I).toNat),
                .address I.codeOwner, .int (Int.ofNat (dripRadVal σ_solm I pow).toNat)])
              (cA' := cA') (σ' := σ') (A' := A') (A_in := A_in) (z := z) (out := o)
              (g'' := g'') (callGas := callGas)
              (mem := potSuckCalldataMem σ2 I (dripPieWord σ2 I * dripChiDeltaVal σ_solm I pow)
                solcFreePtrMem)
              (inOff := ⟨128⟩) (inSize := ⟨100⟩) (callPerm := true)
              hdepthNe htgt (by rw [hradEq2] at hcd ⊢; exact hcd) hΘE
              (by simp only [dripEvmRho_accountMap]
                  exact accountMapEquiv_sstoreAccountMap_two I.codeOwner I.codeOwner ⟨4⟩ _ ⟨7⟩ _
                    hAccounts)
              (by simp only [dripEvmRho_σ₀])
              (by simp only [dripEvmRho_createdAccounts])
              (by simp only [dripEvmRho_genesisBlockHeader])
              (by simp only [dripEvmRho_blocks])
              (by simp only [dripEvmRho_substate])
              (by simp only [dripEvmRho_executionEnv])
          have hcallSolm' : typedCallViaEVM config
              (dripEvmRho (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I))
              (EVM.address (dripVatAddress σ_solm I)) "suck" 0
              [.address (AccountAddress.ofNat (dripVowTargetWord σ_solm I).toNat),
                .address I.codeOwner, .int (Int.ofNat (dripRadVal σ_solm I pow).toNat)]
              (z, { dripEvmRho (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (dripTmpVal σ_solm I pow) (dripNowWord I) with
                accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }, o) true :=
            hcallSolm
          cases z
          · exact RDrev.reEquivExecutionRevert hcode (potDripX_failTail hosz rd2095) hdispatch
              hdecode (potDripSolmBody_callFail hwv hleSolm hrpow hfitRmul hleSub hfitMul hcodePos
                hcallSolm')
          · have hread64 : (potSuckCalldataMem σ2 I (dripPieWord σ2 I * dripChiDeltaVal σ_solm I pow)
                solcFreePtrMem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
              potSuckCalldataMem_read64 σ2 I _ solcFreePtrMem_size solcFreePtrMem_read64
            have hmemSize : (potSuckCalldataMem σ2 I
                (dripPieWord σ2 I * dripChiDeltaVal σ_solm I pow) solcFreePtrMem).size = 228 :=
              potSuckCalldataMem_size σ2 I _ solcFreePtrMem_size
            have rdRet := potDripX_successTail hmemSize hread64 rd2095
            refine (potDripX_successTail hmemSize hread64 rd2095).reEquivExecutionGenAccountMapEquiv
              hcode hdispatch hdecode
              (potDripSolmBody_callSucc hwv hleSolm hrpow hfitRmul hleSub hfitMul hcodePos
                hcallSolm' (by rfl)) ?_ ?_ ?_
            · rfl
            · exact hAccounts'
            · exact returnEquiv_of_encode
                (by simpa [uint256] using uint256ReturnEncoding (dripTmpVal σ_solm I pow))
      · exact RDrev.reEquivExecutionRevert hcode
          (potDripX_mulReverts (by rw [hPie'', Nat.mul_comm]; exact not_lt.mp hfitMul) rd1960)
          hdispatch hdecode
          (potDripSolmBody_mulReverts hwv hleSolm hrpow hfitRmul hleSub (not_lt.mp hfitMul))
    · exact RDrev.reEquivExecutionRevert hcode
        (potDripX_subReverts (by rw [hchi]; exact not_le.mp hleSub) rd1934) hdispatch hdecode
        (potDripSolmBody_subReverts hwv hleSolm hrpow hfitRmul (not_le.mp hleSub))
  · exact RDrev.reEquivExecutionRevert hcode (potDripX_rmulReverts (by rw [hchi]; omega) rd1926)
      hdispatch hdecode (potDripSolmBody_rmulReverts hwv hleSolm hrpow (by omega))

/-- `drip()` external: rate accumulation, `_rpow`/`_rmul`/`_sub`/`_mul` + external `vat.suck`. -/
theorem potDripBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (potSelBytes 4))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (potSelBytes 4) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dripTransition := potDispatchDrip hsel
  have hdecode : decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
      (transitionSignature dripTransition).paramTypes I.calldata = some ∅ := potDecode_drip hsz4
  have hrho : dripRhoWord σ_evm I = dripRhoWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨7⟩ ⟨0⟩
  have hdsr : dripDsrWord σ_evm I = dripDsrWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  have hsubEq : dripSubNowRho σ_evm I = dripSubNowRho σ_solm I := by
    simp only [dripSubNowRho, hrho]
  obtain ⟨k, C, h1819⟩ := potReachDripBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  by_cases hnow : (dripNowWord I).toNat < (dripRhoWord σ_evm I).toNat
  · exact RDrev.reEquivExecutionRevert hcode (potDripX_invalidNow hnow h1819) hdispatch hdecode
      (potDripSolmBody_invalidNow hwv (hrho ▸ hnow))
  · have hle : (dripRhoWord σ_evm I).toNat ≤ (dripNowWord I).toNat := by omega
    have hleSolm : (dripRhoWord σ_solm I).toNat ≤ (dripNowWord I).toNat := hrho ▸ hle
    obtain ⟨_, _, h1894⟩ := potDripX_nowOk hle h1819
    obtain ⟨_, _, h2352⟩ := potDripX_rpowSetup h1894
    by_cases hdsr0 : dripDsrWord σ_evm I = ⟨0⟩
    · have hdsr0S : dripDsrWord σ_solm I = ⟨0⟩ := hdsr ▸ hdsr0
      rw [hdsr0] at h2352
      obtain ⟨_, _, rd1926⟩ := potDripRpowXZeroReturns
        (R := [⟨1934⟩, ⟨0⟩, ⟨341⟩, potSelWord I])
        (by simp only [List.length_cons, List.length_nil]; omega) h2352
      rw [hrho] at rd1926
      have hrpow : ExecFuncBody config
          { contract := contract,
            locals := uintTernaryLocals (dripDsrWord σ_solm I) (dripSubNowRho σ_solm I) potRay }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) rpowFunction.body
          (.returned
            { contract := contract,
              locals := uintTernaryLocals ⟨0⟩ (dripSubNowRho σ_solm I) potRay }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [.int (Int.ofNat
              (if dripSubNowRho σ_solm I = ⟨0⟩ then potRay else ⟨0⟩).toNat)])) := by
        rw [hdsr0S]
        exact execRpowFunctionXZeroReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (dripSubNowRho σ_solm I)
      exact potDripBodyAfterRpow hcode hsize _hperm hwv hdispatch hdecode hAccounts hle hrpow
        rd1926
    · cases rpowFunctionCoupled
        (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (x := dripDsrWord σ_evm I) (n := dripSubNowRho σ_evm I) (b := potRay)
        (R := [⟨1934⟩, ⟨0⟩, ⟨341⟩, potSelWord I])
        (by simp only [List.length_cons, List.length_nil]; omega) hdsr0 potRay_ne_zero h2352 with
      | inl h =>
        obtain ⟨xFinal, zFinal, localsFinal, k', C', hstore, hbody, rd1926⟩ := h
        have hrpow : ExecFuncBody config
            { contract := contract,
              locals := uintTernaryLocals (dripDsrWord σ_solm I) (dripSubNowRho σ_solm I) potRay }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) rpowFunction.body
            (.returned { contract := contract, locals := localsFinal }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (some [.int (Int.ofNat zFinal.toNat)])) := by
          rw [← hdsr, ← hsubEq]; exact hbody
        exact potDripBodyAfterRpow hcode hsize _hperm hwv hdispatch hdecode hAccounts hle hrpow
          rd1926
      | inr h =>
        obtain ⟨hbody, rdRev⟩ := h
        have hrpow : ExecFuncBody config
            { contract := contract,
              locals := uintTernaryLocals (dripDsrWord σ_solm I) (dripSubNowRho σ_solm I) potRay }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) rpowFunction.body
            .reverted := by
          rw [← hdsr, ← hsubEq]; exact hbody
        exact RDrev.reEquivExecutionRevert hcode rdRev hdispatch hdecode
          (potDripSolmBody_rpowReverts hwv hleSolm hrpow)

end Benchmarks.Dss.Pot
