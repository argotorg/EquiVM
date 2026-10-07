import Benchmarks.Dss.Cure.DropSource
import Benchmarks.Dss.Cure.Srcs

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cure

abbrev cureSrcNotDefinedRawWord : UInt256 :=
  ⟨0x437572652f6e6f6e2d6578697374696e672d736f75726365⟩

theorem RD.cureDropPosZeroRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata σ k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hpos : solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) = ⟨0⟩)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 8 ≤ 1024) :
    RDrev cureBytecode g s0 := by
  have hmask : UInt256.land solcAddrMask key = key :=
    solcAddrMask_clean_left hcanonKey
  have hmaskLiteral :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) key =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hmaskLiteral' :
      UInt256.land key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        key := by
    rw [u256_land_comm key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)]
    exact hmaskLiteral
  have rdMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmaskLiteral'] at rdMasked
  have rdMstoreKeyPrefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdAfterKey := rdMstoreKeyPrefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨5⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨5⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨5⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoad⟩ := rdSlot.sload (by native_decide) (by evm_ov)
  have hposRaw :
      (σ.get? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.getD (solcMappingSlot ⟨5⟩ key) ⟨0⟩)) = ⟨0⟩ := by
    simpa [solcSlotWord] using hpos
  rw [hposRaw] at rdLoad
  have rdDup := rdLoad.dup1 (by native_decide) (by evm_ov)
  have rdPush := rdDup.push2 ⟨3064⟩ (by native_decide) (by evm_ov)
  have rdTail := rdPush.jumpiNT (by native_decide) (by rfl) (by evm_ov)
  have htailMem : (twoWordHashMem key ⟨5⟩ mem).size = 96 :=
    twoWordHashMem_size_96 key ⟨5⟩ hmem
  have htailRead64 :
      (twoWordHashMem key ⟨5⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 key ⟨5⟩ hmem hread64
  exact RD.solcErrorStringRevertTail
    (len := ⟨24⟩)
    (rawWord := cureSrcNotDefinedRawWord)
    (shift := ⟨64⟩)
    (word := UInt256.shiftLeft cureSrcNotDefinedRawWord ⟨64⟩)
    (op := .PUSH24)
    (width := 24)
    rdTail
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    rfl
    htailMem htailRead64
    (by simp only [List.length_cons]; omega)

theorem RD.cureDropLoadedPosLenPrefix {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata σ k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hpos : solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩)
    (hmem : mem.size = 96)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3068⟩
      (solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) ::
        key :: ret :: R)
      (twoWordHashMem key ⟨5⟩ mem) (UInt256.ofNat 3) rdata σ k' C' := by
  have hmask : UInt256.land solcAddrMask key = key :=
    solcAddrMask_clean_left hcanonKey
  have hmaskLiteral :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) key =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hmaskLiteral' :
      UInt256.land key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        key := by
    rw [u256_land_comm key (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)]
    exact hmaskLiteral
  have rdMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmaskLiteral'] at rdMasked
  have rdMstoreKeyPrefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdAfterKey := rdMstoreKeyPrefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨5⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot ⟨5⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨5⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoad'⟩ := rdSlot.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdLoad⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨2988⟩
      (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) :: key :: ret :: R)
      (twoWordHashMem key ⟨5⟩ mem) (UInt256.ofNat 3) rdata σ k' C' := by
    exact ⟨_, _, by simpa [solcSlotWord] using rdLoad'⟩
  have rdDup := rdLoad.dup1 (by native_decide) (by evm_ov)
  have rdPush := rdDup.push2 ⟨3064⟩ (by native_decide) (by evm_ov)
  have rdPosOk := rdPush.jumpiT (by native_decide) hpos (by jump_dest) (by evm_ov)
  have rdLenPrefix := evm_run rdPosOk with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdLenLoad'⟩ := rdLenPrefix.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdLenLoad⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨3068⟩
      (solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) ::
        key :: ret :: R)
      (twoWordHashMem key ⟨5⟩ mem) (UInt256.ofNat 3) rdata σ k' C' := by
    exact ⟨_, _, by simpa [solcSlotWord] using rdLenLoad'⟩
  exact ⟨_, _, rdLenLoad⟩

theorem RD.cureDropNoSwapPrefix {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata σ k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hpos : solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩)
    (hnoswap :
      (solcSlotWord σ ee ⟨2⟩).toNat ≤
        (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key)).toNat)
    (hmem : mem.size = 96)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3197⟩
      (solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) ::
        key :: ret :: R)
      (twoWordHashMem key ⟨5⟩ mem) (UInt256.ofNat 3) rdata σ k' C' := by
  obtain ⟨_, _, rdLenLoad⟩ := RD.cureDropLoadedPosLenPrefix
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ret) (R := R)
    h hcanonKey hpos hmem hov
  have rdCmp := evm_run rdLenLoad with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨3197⟩ (by native_decide) (by evm_ov)]
  have hcond :
      UInt256.isZero
          (UInt256.lt (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key))
            (solcSlotWord σ ee ⟨2⟩)) ≠ ⟨0⟩ := by
    have hnotlt :
        ¬ (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key)).toNat <
          (solcSlotWord σ ee ⟨2⟩).toNat := by
      omega
    rw [show UInt256.lt (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key))
        (solcSlotWord σ ee ⟨2⟩) = ⟨0⟩ by
      show UInt256.fromBool
          (decide ((solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key)).toNat <
            (solcSlotWord σ ee ⟨2⟩).toNat)) = ⟨0⟩
      simp [hnotlt]
      rfl]
    native_decide
  exact ⟨_, _, rdCmp.jumpiT (by native_decide) hcond (by jump_dest) (by evm_ov)⟩

theorem RD.cureDropSwapBranchEntered {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret len pos : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3068⟩ (len :: pos :: key :: ret :: R) mem
        (UInt256.ofNat 3) rdata σ k C)
    (hswap : pos.toNat < len.toNat)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3076⟩ (len :: pos :: key :: ret :: R)
      mem (UInt256.ofNat 3) rdata σ k' C' := by
  have rdCmp := evm_run h with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨3197⟩ (by native_decide) (by evm_ov)]
  have hcond :
      UInt256.isZero (UInt256.lt pos len) = ⟨0⟩ := by
    rw [show UInt256.lt pos len = ⟨1⟩ by
      show UInt256.fromBool (decide (pos.toNat < len.toNat)) = ⟨1⟩
      simp [hswap]
      rfl]
    native_decide
  exact ⟨_, _, rdCmp.jumpiNT (by native_decide) hcond (by evm_ov)⟩

theorem RD.cureDropSwapLoadMovePrefix {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret len pos : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3076⟩ (len :: pos :: key :: ret :: R) mem
        (UInt256.ofNat 3) rdata σ k C)
    (hlen : solcSlotWord σ ee ⟨2⟩ = len)
    (hlenPos : 0 < len.toNat)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3106⟩
      (solcSlotWord σ ee (dropSrcsSlotForIndex (dropLastIndex len)) ::
        ⟨0⟩ :: len :: pos :: key :: ret :: R)
      (wordAt0Mem ⟨2⟩ mem) (UInt256.ofNat 3) rdata σ k' C' := by
  have hlastIndex : UInt256.sub len ⟨1⟩ = dropLastIndex len := by
    simpa [dropLastIndex] using u256_sub_one_eq_pred_of_pos len hlenPos
  have hlastLt :
      UInt256.lt (dropLastIndex len) len ≠ ⟨0⟩ := by
    show UInt256.fromBool (decide ((dropLastIndex len).toNat < len.toNat)) ≠ ⟨0⟩
    have hto :
        (dropLastIndex len).toNat = len.toNat - 1 := by
      unfold dropLastIndex
      rw [ulit_toNat' (len.toNat - 1) (by
        have hlt : len.toNat < UInt256.size := len.val.isLt
        omega)]
    rw [hto]
    have : len.toNat - 1 < len.toNat := by omega
    simp [this]
    native_decide
  have hsrcsSlot :
      UInt256.ofNat
          (fromByteArrayBigEndian (KEC ((wordAt0Mem (⟨2⟩ : UInt256) mem).readWithPadding 0 32))) =
        srcsDataSlot := by
    simpa [srcsDataSlot, uInt256OfByteArray_eq] using
      wordAt0Mem_keccak_word (⟨2⟩ : UInt256) mem
  have hslot :
      srcsDataSlot + dropLastIndex len = dropSrcsSlotForIndex (dropLastIndex len) := by
    exact (dropSrcsSlotForIndex_eq_add (dropLastIndex len)).symm
  have rdIndexRaw := evm_run h with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov)]
  rw [hlastIndex] at rdIndexRaw
  have rdLenSlot := rdIndexRaw.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLenLoaded'⟩ := rdLenSlot.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdLenLoaded⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨3086⟩
      (len :: dropLastIndex len :: ⟨2⟩ :: ⟨0⟩ :: len :: pos :: key :: ret :: R)
      mem (UInt256.ofNat 3) rdata σ k' C' := by
    exact ⟨_, _, by simpa [-Std.ExtTreeMap.get?_eq_getElem?, solcSlotWord, hlen] using rdLenLoaded'⟩
  have rdCheck := evm_run rdLenLoaded with [
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw push2 ⟨3093⟩ (by native_decide) (by evm_ov)]
  have rdOk := rdCheck.jumpiT (by native_decide) hlastLt (by jump_dest) (by evm_ov)
  have rdMstorePrefix := evm_run rdOk with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rdBaseMem := rdMstorePrefix.mstore 0 (wordAt0Mem ⟨2⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdBasePrefix := evm_run rdBaseMem with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rdBase := rdBasePrefix.keccak256 0 srcsDataSlot (UInt256.ofNat 3)
    (by native_decide) mem_cost hsrcsSlot (by native_decide) (by evm_ov)
  have rdSlotRaw := rdBase.add (by native_decide) (by evm_ov)
  rw [hslot] at rdSlotRaw
  obtain ⟨_, _, rdMoveLoaded'⟩ := rdSlotRaw.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [solcSlotWord] using rdMoveLoaded'⟩

theorem RD.cureDropSwapMaskMovePrefix {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret len pos : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3106⟩
        (solcSlotWord σ ee (dropSrcsSlotForIndex (dropLastIndex len)) ::
          ⟨0⟩ :: len :: pos :: key :: ret :: R)
        mem (UInt256.ofNat 3) rdata σ k C)
    (hlen : solcSlotWord σ ee ⟨2⟩ = len)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3123⟩
      (⟨2⟩ :: len :: dropMoveWordFor σ ee len :: len :: pos :: key :: ret :: R)
      mem (UInt256.ofNat 3) rdata σ k' C' := by
  have hmaskLiteral :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hmove :
      UInt256.land
          (solcSlotWord σ ee (dropSrcsSlotForIndex (dropLastIndex len)))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        dropMoveWordFor σ ee len := by
    rw [hmaskLiteral]
  have rdRaw := evm_run h with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdLenLoaded'⟩ := rdRaw.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdLenLoaded⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨3110⟩
      (len :: ⟨2⟩ :: solcSlotWord σ ee (dropSrcsSlotForIndex (dropLastIndex len)) ::
        ⟨0⟩ :: len :: pos :: key :: ret :: R)
      mem (UInt256.ofNat 3) rdata σ k' C' := by
    exact ⟨_, _, by simpa [-Std.ExtTreeMap.get?_eq_getElem?, solcSlotWord, hlen] using rdLenLoaded'⟩
  have rdMaskedRaw := evm_run rdLenLoaded with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmove] at rdMaskedRaw
  exact ⟨_, _, evm_run rdMaskedRaw with [
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]⟩

theorem RD.cureDropSwapStoreMoveElemPrefixSplit {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret len pos : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3123⟩
        (⟨2⟩ :: len :: dropMoveWordFor σ ee len :: len :: pos :: key :: ret :: R)
        mem (UInt256.ofNat 3) rdata σ k C)
    (hswap : pos.toNat < len.toNat)
    (hposNat : 0 < pos.toNat)
    (hov : R.length + 20 ≤ 1024) :
    (ee.perm = true ∧
      ∃ k' C', RD cureBytecode ee g s0 ⟨3179⟩
        (⟨32⟩ :: ⟨0⟩ :: solcAddrMask :: dropMoveWordFor σ ee len ::
          len :: pos :: key :: ret :: R)
        (wordAt0Mem ⟨2⟩ mem) (UInt256.ofNat 3) rdata
        (dropMoveElemAccountMapFor σ ee pos len) k' C') ∨
      (ee.perm = false ∧ RDstatic cureBytecode g s0) := by
  have hdstIndex : pos + UInt256.lnot ⟨0⟩ = dropDstIndex pos := by
    simpa [dropDstIndex] using u256_add_lnot_zero_eq_pred_of_pos pos hposNat
  have hdstLt :
      UInt256.lt (dropDstIndex pos) len ≠ ⟨0⟩ := by
    show UInt256.fromBool (decide ((dropDstIndex pos).toNat < len.toNat)) ≠ ⟨0⟩
    have hto :
        (dropDstIndex pos).toNat = pos.toNat - 1 := by
      unfold dropDstIndex
      rw [ulit_toNat' (pos.toNat - 1) (by
        have hlt : pos.toNat < UInt256.size := pos.val.isLt
        omega)]
    rw [hto]
    have : pos.toNat - 1 < len.toNat := by omega
    simp [this]
    native_decide
  have hsrcsSlot :
      UInt256.ofNat
          (fromByteArrayBigEndian (KEC ((wordAt0Mem (⟨2⟩ : UInt256) mem).readWithPadding 0 32))) =
        srcsDataSlot := by
    simpa [srcsDataSlot, uInt256OfByteArray_eq] using
      wordAt0Mem_keccak_word (⟨2⟩ : UInt256) mem
  have hslot :
      srcsDataSlot + dropDstIndex pos = dropSrcsSlotForIndex (dropDstIndex pos) := by
    exact (dropSrcsSlotForIndex_eq_add (dropDstIndex pos)).symm
  have hnotMaskLiteral :
      UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        UInt256.lnot solcAddrMask := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
  have hclear :
      UInt256.land
          (UInt256.lnot
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
          (solcSlotWord σ ee (dropSrcsSlotForIndex (dropDstIndex pos))) =
        UInt256.land
          (UInt256.lnot solcAddrMask)
          (solcSlotWord σ ee (dropSrcsSlotForIndex (dropDstIndex pos))) := by
    rw [hnotMaskLiteral]
  have hmoveCanon : (dropMoveWordFor σ ee len).toNat < EVM.addressModulus := by
    unfold dropMoveWordFor
    exact solcAddrMask_result_canonical
      (solcSlotWord σ ee (dropSrcsSlotForIndex (dropLastIndex len)))
  have hmoveMask :
      UInt256.land solcAddrMask (dropMoveWordFor σ ee len) = dropMoveWordFor σ ee len :=
    solcAddrMask_clean_left hmoveCanon
  have hmoveMaskRight :
      UInt256.land (dropMoveWordFor σ ee len) solcAddrMask = dropMoveWordFor σ ee len :=
    solcAddrMask_clean hmoveCanon
  have hstored :
      UInt256.lor
          (UInt256.land solcAddrMask (dropMoveWordFor σ ee len))
          (UInt256.land (UInt256.lnot solcAddrMask)
            (solcSlotWord σ ee (dropSrcsSlotForIndex (dropDstIndex pos)))) =
        setAddressOffset0Word
          (solcSlotWord σ ee (dropSrcsSlotForIndex (dropDstIndex pos)))
          (dropMoveWordFor σ ee len) := by
    unfold setAddressOffset0Word
    rw [hmoveMask]
    rw [u256_lor_comm (dropMoveWordFor σ ee len)]
    rw [u256_land_comm (UInt256.lnot solcAddrMask)
      (solcSlotWord σ ee (dropSrcsSlotForIndex (dropDstIndex pos)))]
    rw [hmoveMaskRight]
  have rdDstRaw := evm_run h with [
    raw dup3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [hdstIndex] at rdDstRaw
  have rdCheck := evm_run rdDstRaw with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw push2 ⟨3138⟩ (by native_decide) (by evm_ov)]
  have rdOk := rdCheck.jumpiT (by native_decide) hdstLt (by jump_dest) (by evm_ov)
  have rdMstorePrefix := evm_run rdOk with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rdBaseMem := rdMstorePrefix.mstore 0 (wordAt0Mem ⟨2⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdBase := evm_run rdBaseMem with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdHash := rdBase.keccak256 0 srcsDataSlot (UInt256.ofNat 3)
    (by native_decide) mem_cost hsrcsSlot (by native_decide) (by evm_ov)
  have rdSlotRaw := evm_run rdHash with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  rw [hslot] at rdSlotRaw
  obtain ⟨_, _, rdOldLoaded'⟩ := rdSlotRaw.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdOldLoaded⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨3155⟩
      (solcSlotWord σ ee (dropSrcsSlotForIndex (dropDstIndex pos)) ::
        dropSrcsSlotForIndex (dropDstIndex pos) :: ⟨32⟩ :: ⟨0⟩ ::
        dropMoveWordFor σ ee len :: dropMoveWordFor σ ee len :: len :: pos :: key :: ret :: R)
      (wordAt0Mem ⟨2⟩ mem) (UInt256.ofNat 3) rdata σ k' C' := by
    exact ⟨_, _, by simpa [solcSlotWord] using rdOldLoaded'⟩
  have rdClearRaw := evm_run rdOldLoaded with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hclear] at rdClearRaw
  have rdSetRaw := evm_run rdClearRaw with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw or (by native_decide) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rdSetRaw
  rw [hstored] at rdSetRaw
  have rdStoreReady := rdSetRaw.swap1 (by native_decide) (by evm_ov)
  have hstoreDec : decode cureBytecode ⟨3178⟩ = some (.SSTORE, none) := by
    native_decide
  by_cases hperm : ee.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      rdStoreReady.sstoreStatic (by simpa using hperm) hstoreDec (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨_, _, rdStored'⟩ := rdStoreReady.sstore hperm hstoreDec
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [dropMoveElemAccountMapFor] using rdStored'⟩

theorem RD.cureDropSwapStoreMoveElemPrefix {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret len pos : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3123⟩
        (⟨2⟩ :: len :: dropMoveWordFor σ ee len :: len :: pos :: key :: ret :: R)
        mem (UInt256.ofNat 3) rdata σ k C)
    (hperm : ee.perm = true)
    (hswap : pos.toNat < len.toNat)
    (hposNat : 0 < pos.toNat)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3179⟩
      (⟨32⟩ :: ⟨0⟩ :: solcAddrMask :: dropMoveWordFor σ ee len ::
        len :: pos :: key :: ret :: R)
      (wordAt0Mem ⟨2⟩ mem) (UInt256.ofNat 3) rdata
      (dropMoveElemAccountMapFor σ ee pos len) k' C' :=
  permSplit_true hperm (RD.cureDropSwapStoreMoveElemPrefixSplit h hswap hposNat hov)

theorem RD.cureDropSwapStoreMovePosPrefix {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret len pos : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3179⟩
        (⟨32⟩ :: ⟨0⟩ :: solcAddrMask :: dropMoveWordFor σ ee len ::
          len :: pos :: key :: ret :: R)
        mem (UInt256.ofNat 3) rdata
        (dropMoveElemAccountMapFor σ ee pos len) k C)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3197⟩
      (len :: pos :: key :: ret :: R)
      (twoWordHashMem (dropMoveWordFor σ ee len) ⟨5⟩ mem)
      (UInt256.ofNat 3) rdata
      (dropMovePosAccountMapFor σ ee pos len) k' C' := by
  have hmoveCanon : (dropMoveWordFor σ ee len).toNat < EVM.addressModulus := by
    unfold dropMoveWordFor
    exact solcAddrMask_result_canonical
      (solcSlotWord σ ee (dropSrcsSlotForIndex (dropLastIndex len)))
  have hmoveMask :
      UInt256.land solcAddrMask (dropMoveWordFor σ ee len) = dropMoveWordFor σ ee len :=
    solcAddrMask_clean_left hmoveCanon
  have hslot :
      UInt256.ofNat
          (fromByteArrayBigEndian
            (KEC
              ((twoWordHashMem (dropMoveWordFor σ ee len) ⟨5⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨5⟩ (dropMoveWordFor σ ee len) := by
    simpa [solcMappingSlot, uInt256OfByteArray_eq] using
      twoWordHashMem_solcMappingSlot ⟨5⟩ (dropMoveWordFor σ ee len) hmem
  have rdMoveRaw := evm_run h with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmoveMask] at rdMoveRaw
  have rdMoveMemPrefix := rdMoveRaw.dup2 (by native_decide) (by evm_ov)
  have rdMoveMem := rdMoveMemPrefix.mstore 0 (wordAt0Mem (dropMoveWordFor σ ee len) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdSlotMemPrefix := evm_run rdMoveMem with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rdSlotMem := rdSlotMemPrefix.mstore 0
    (twoWordHashMem (dropMoveWordFor σ ee len) ⟨5⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdHashPrefix := evm_run rdSlotMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdHash := rdHashPrefix.keccak256 0 (solcMappingSlot ⟨5⟩ (dropMoveWordFor σ ee len))
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rdStoreReady := evm_run rdHash with [
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdStored'⟩ := rdStoreReady.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [dropMovePosAccountMapFor] using rdStored'⟩

theorem RD.cureDropNoSwapPopTailSplit {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret oldLen popLen pos : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3197⟩ (oldLen :: pos :: key :: ret :: R) mem
        (UInt256.ofNat 3) rdata σ k C)
    (hlen : solcSlotWord σ ee ⟨2⟩ = popLen)
    (hlenPos : 0 < popLen.toNat)
    (hov : R.length + 20 ≤ 1024) :
    (ee.perm = true ∧
      ∃ k' C', RD cureBytecode ee g s0 ⟨3247⟩
        (⟨32⟩ :: ⟨0⟩ :: oldLen :: pos :: key :: ret :: R)
        (wordAt0Mem ⟨2⟩ mem) (UInt256.ofNat 3) rdata
        (dropPopAccountMap σ ee popLen) k' C') ∨
      (ee.perm = false ∧ RDstatic cureBytecode g s0) := by
  have hsrcsSlot :
      UInt256.ofNat
          (fromByteArrayBigEndian (KEC ((wordAt0Mem (⟨2⟩ : UInt256) mem).readWithPadding 0 32))) =
        srcsDataSlot := by
    simpa [srcsDataSlot, uInt256OfByteArray_eq] using
      wordAt0Mem_keccak_word (⟨2⟩ : UInt256) mem
  have hlastSlot :
      srcsDataSlot + UInt256.ofNat (popLen.toNat - 1) = dropSrcsLastSlot popLen := by
    exact (dropSrcsLastSlot_eq popLen hlenPos).symm
  have hpred : popLen + UInt256.lnot ⟨0⟩ = UInt256.ofNat (popLen.toNat - 1) :=
    u256_add_lnot_zero_eq_pred_of_pos popLen hlenPos
  have hlastSlotRaw :
      UInt256.lnot ⟨0⟩ + (popLen + srcsDataSlot) = dropSrcsLastSlot popLen := by
    rw [u256_add_comm (UInt256.lnot ⟨0⟩) (popLen + srcsDataSlot)]
    rw [u256_add_assoc popLen srcsDataSlot (UInt256.lnot ⟨0⟩)]
    rw [u256_add_comm srcsDataSlot (UInt256.lnot ⟨0⟩)]
    rw [← u256_add_assoc popLen (UInt256.lnot ⟨0⟩) srcsDataSlot]
    rw [hpred]
    rw [u256_add_comm (UInt256.ofNat (popLen.toNat - 1)) srcsDataSlot]
    exact hlastSlot
  have rdLoadLenPrefix := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdLenLoaded'⟩ := rdLoadLenPrefix.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdLenLoaded⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨3202⟩
      (popLen :: ⟨2⟩ :: oldLen :: pos :: key :: ret :: R) mem (UInt256.ofNat 3)
      rdata σ k' C' := by
    exact ⟨_, _, by simpa [-Std.ExtTreeMap.get?_eq_getElem?, solcSlotWord, hlen] using rdLenLoaded'⟩
  have rdCheckPrefix := evm_run rdLenLoaded with [
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨3208⟩ (by native_decide) (by evm_ov)]
  have hlenNe : popLen ≠ ⟨0⟩ := by
    intro hz
    rw [hz] at hlenPos
    simp at hlenPos
  have rdLenOk := rdCheckPrefix.jumpiT (by native_decide) hlenNe (by jump_dest)
    (by evm_ov)
  have rdMstorePrefix := evm_run rdLenOk with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdBaseMem := rdMstorePrefix.mstore 0 (wordAt0Mem ⟨2⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdBasePrefix := evm_run rdBaseMem with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rdBase := rdBasePrefix.keccak256 0 srcsDataSlot (UInt256.ofNat 3)
    (by native_decide) mem_cost hsrcsSlot (by native_decide) (by evm_ov)
  have rdLastSlotRaw := evm_run rdBase with [
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  rw [hlastSlotRaw] at rdLastSlotRaw
  obtain ⟨_, _, rdLastLoaded'⟩ := rdLastSlotRaw.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdLastLoaded⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨3229⟩
      (solcSlotWord σ ee (dropSrcsLastSlot popLen) :: dropSrcsLastSlot popLen ::
        UInt256.lnot ⟨0⟩ :: ⟨32⟩ :: ⟨0⟩ :: popLen :: ⟨2⟩ :: oldLen :: pos ::
        key :: ret :: R)
      (wordAt0Mem ⟨2⟩ mem) (UInt256.ofNat 3) rdata σ k' C' := by
    exact ⟨_, _, by simpa [solcSlotWord] using rdLastLoaded'⟩
  have rdClearRaw := evm_run rdLastLoaded with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hclear :
      UInt256.land (UInt256.lnot
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
          (solcSlotWord σ ee (dropSrcsLastSlot popLen)) =
        setAddressOffset0Word (solcSlotWord σ ee (dropSrcsLastSlot popLen)) ⟨0⟩ := by
    unfold setAddressOffset0Word
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    rw [u256_land_comm (UInt256.lnot solcAddrMask)
      (solcSlotWord σ ee (dropSrcsLastSlot popLen))]
    rw [show UInt256.land (⟨0⟩ : UInt256) solcAddrMask = ⟨0⟩ by native_decide]
    rw [u256_lor_zero]
  rw [hclear] at rdClearRaw
  have hstoreDec : decode cureBytecode ⟨3240⟩ = some (.SSTORE, none) := by
    native_decide
  by_cases hperm : ee.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      rdClearRaw.sstoreStatic (by simpa using hperm) hstoreDec (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨_, _, rdCleared'⟩ := rdClearRaw.sstore hperm hstoreDec
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdCleared⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨3241⟩
      (UInt256.lnot ⟨0⟩ :: ⟨32⟩ :: ⟨0⟩ :: popLen :: ⟨2⟩ :: oldLen :: pos ::
        key :: ret :: R)
      (wordAt0Mem ⟨2⟩ mem) (UInt256.ofNat 3) rdata
      (dropPopClearAccountMap σ ee popLen) k' C' := by
    exact ⟨_, _, by simpa [dropPopClearAccountMap] using rdCleared'⟩
  have rdLenStoreReady := evm_run rdCleared with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  rw [hpred] at rdLenStoreReady
  obtain ⟨_, _, rdLenStored'⟩ := rdLenStoreReady.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [dropPopAccountMap] using rdLenStored'⟩

theorem RD.cureDropNoSwapPopTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret oldLen popLen pos : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3197⟩ (oldLen :: pos :: key :: ret :: R) mem
        (UInt256.ofNat 3) rdata σ k C)
    (hperm : ee.perm = true)
    (hlen : solcSlotWord σ ee ⟨2⟩ = popLen)
    (hlenPos : 0 < popLen.toNat)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3247⟩
      (⟨32⟩ :: ⟨0⟩ :: oldLen :: pos :: key :: ret :: R)
      (wordAt0Mem ⟨2⟩ mem) (UInt256.ofNat 3) rdata
      (dropPopAccountMap σ ee popLen) k' C' :=
  permSplit_true hperm (RD.cureDropNoSwapPopTailSplit h hlen hlenPos hov)

theorem RD.cureDropPopEmptyInvalid {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret oldLen pos : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3197⟩ (oldLen :: pos :: key :: ret :: R) mem
        (UInt256.ofNat 3) rdata σ k C)
    (hlen : solcSlotWord σ ee ⟨2⟩ = ⟨0⟩)
    (hov : R.length + 20 ≤ 1024) :
    RDinvalid cureBytecode g s0 := by
  have rdLoadLenPrefix := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdLenLoaded'⟩ := rdLoadLenPrefix.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdLenLoaded⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨3202⟩
      (⟨0⟩ :: ⟨2⟩ :: oldLen :: pos :: key :: ret :: R) mem (UInt256.ofNat 3)
      rdata σ k' C' := by
    exact ⟨_, _, by simpa [-Std.ExtTreeMap.get?_eq_getElem?, solcSlotWord, hlen] using rdLenLoaded'⟩
  have rdCheckPrefix := evm_run rdLenLoaded with [
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨3208⟩ (by native_decide) (by evm_ov)]
  have rdInvalidPc := rdCheckPrefix.jumpiNT (by native_decide) rfl
    (by simp only [List.length_cons]; omega)
  exact rdInvalidHalt rdInvalidPc (by native_decide)

theorem RD.cureDropNoSwapDeleteLogTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret len pos : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3247⟩
        (⟨32⟩ :: ⟨0⟩ :: len :: pos :: key :: ret :: R) mem
        (UInt256.ofNat 3) rdata σ k C)
    (hret : (D_J cureBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ret R
      (wordAt32Mem ⟨6⟩ (twoWordHashMem key ⟨5⟩ mem)) (UInt256.ofNat 3) rdata
      (dropDeleteAmtAccountMapFor (dropDeletePosAccountMapFor σ ee key) ee key) k' C' := by
  have hmask : UInt256.land key solcAddrMask = key :=
    solcAddrMask_clean hcanonKey
  have hmaskLiteral :
      UInt256.land key
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        key := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have rdMaskKeyRaw := evm_run h with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmaskLiteral] at rdMaskKeyRaw
  have rdKeyMemPrefix := evm_run rdMaskKeyRaw with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdKeyMem := rdKeyMemPrefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdPosMemPrefix := evm_run rdKeyMem with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rdPosMem := rdPosMemPrefix.mstore 0 (twoWordHashMem key ⟨5⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdPosHashPrefix := evm_run rdPosMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have hposSlot := twoWordHashMem_solcMappingSlot ⟨5⟩ key hmem
  have rdPosHash := rdPosHashPrefix.keccak256 0 (solcMappingSlot ⟨5⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost hposSlot (by native_decide) (by evm_ov)
  have rdPosStoreReady := evm_run rdPosHash with [
    raw dup5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdPosStored'⟩ := rdPosStoreReady.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdPosStored⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨3272⟩
      (⟨64⟩ :: key :: ⟨32⟩ :: ⟨0⟩ :: len :: pos :: key :: ret :: R)
      (twoWordHashMem key ⟨5⟩ mem) (UInt256.ofNat 3) rdata
      (dropDeletePosAccountMapFor σ ee key) k' C' := by
    exact ⟨_, _, by simpa [dropDeletePosAccountMapFor] using rdPosStored'⟩
  have rdAmtMemPrefix := evm_run rdPosStored with [
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  have rdAmtMem := rdAmtMemPrefix.mstore 0
    (wordAt32Mem ⟨6⟩ (twoWordHashMem key ⟨5⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdAmtHashPrefix := evm_run rdAmtMem with [
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have hamtSlot := wordAt32TwoWordHashMem_solcMappingSlot ⟨6⟩ key ⟨5⟩ hmem
  have rdAmtHash := rdAmtHashPrefix.keccak256 0 (solcMappingSlot ⟨6⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost hamtSlot (by native_decide) (by evm_ov)
  have rdAmtStoreReady := evm_run rdAmtHash with [
    raw dup4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdAmtStored'⟩ := rdAmtStoreReady.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdAmtStored⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨3283⟩
      (key :: ⟨64⟩ :: ⟨0⟩ :: len :: pos :: key :: ret :: R)
      (wordAt32Mem ⟨6⟩ (twoWordHashMem key ⟨5⟩ mem)) (UInt256.ofNat 3) rdata
      (dropDeleteAmtAccountMapFor (dropDeletePosAccountMapFor σ ee key) ee key) k' C' := by
    exact ⟨_, _, by simpa [dropDeleteAmtAccountMapFor] using rdAmtStored'⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (wordAt32Mem ⟨6⟩ (twoWordHashMem key ⟨5⟩ mem)).size
        then ⟨0⟩ else UInt256.ofNat (fromByteArrayBigEndian
          ((wordAt32Mem ⟨6⟩ (twoWordHashMem key ⟨5⟩ mem)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
    rw [if_neg (by
      rw [wordAt32Mem_size_96 ⟨6⟩ (twoWordHashMem_size_96 key ⟨5⟩ hmem)]
      native_decide)]
    rw [show (⟨64⟩ : UInt256).toNat = 64 from rfl,
      wordAt32TwoWordHashMem_read64 key ⟨5⟩ ⟨6⟩ hmem hread64]
    native_decide
  have rdMloadPrefix := rdAmtStored.swap1 (by native_decide) (by evm_ov)
  have rdMload := rdMloadPrefix.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
    mem_cost hmload64 (by native_decide) (by evm_ov)
  have rdTopic := rdMload.swap1 (by native_decide) (by evm_ov)
  have rdTopicReady := rdTopic.swap2 (by native_decide) (by evm_ov)
  have rdEventTopic := rdTopicReady.pushConst
    ⟨99406632185228453606804164848468116191150314180684667023680336451755226916254⟩
    (op := .PUSH32) (width := 32) (by decide) (by native_decide) (by evm_ov)
  have rdLogPrefix := evm_run rdEventTopic with [
    raw swap2 (by native_decide) (by evm_ov)]
  have rdLogged := RD.log2 0 (UInt256.ofNat 3) rdLogPrefix
    (by native_decide) hperm mem_cost (by native_decide) (by evm_ov)
  have rdTail := evm_run rdLogged with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, RD.jump rdTail (by native_decide) hret (by evm_ov)⟩

theorem RD.cureDropNoSwapStoreAndLogReturnSplit {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ⟨484⟩ :: R) mem
        (UInt256.ofNat 3) rdata σ k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hpos : solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩)
    (hnoswap :
      (solcSlotWord σ ee ⟨2⟩).toNat ≤
        (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key)).toNat)
    (hlenPos : 0 < (solcSlotWord σ ee ⟨2⟩).toNat)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 20 ≤ 1024) :
    (ee.perm = true ∧
      RDret cureBytecode g s0
        (dropNoSwapFinalAccountMapFor σ ee key (solcSlotWord σ ee ⟨2⟩))
        ByteArray.empty) ∨
      (ee.perm = false ∧ RDstatic cureBytecode g s0) := by
  obtain ⟨_, _, rd3197⟩ := RD.cureDropNoSwapPrefix
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    h hcanonKey hpos hnoswap hmem (by omega)
  have hfirstWrite := RD.cureDropNoSwapPopTailSplit
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3197 rfl hlenPos hov
  refine permSplit_bind hfirstWrite ?_
  intro hperm hreach
  obtain ⟨_, _, rd3247⟩ := hreach
  have hprefixMem :
      (twoWordHashMem key ⟨5⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 key ⟨5⟩ hmem hread64
  have hpopMemSize :
      (wordAt0Mem ⟨2⟩ (twoWordHashMem key ⟨5⟩ mem)).size = 96 :=
    wordAt0Mem_size_96 ⟨2⟩ (twoWordHashMem_size_96 key ⟨5⟩ hmem)
  have hpopRead64 :
      (wordAt0Mem ⟨2⟩ (twoWordHashMem key ⟨5⟩ mem)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    wordAt0Mem_read64_of_size96 ⟨2⟩
      (twoWordHashMem_size_96 key ⟨5⟩ hmem) hprefixMem
  obtain ⟨_, _, rdRetPc⟩ := RD.cureDropNoSwapDeleteLogTail
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3247 (by jump_dest) hperm hcanonKey hpopMemSize hpopRead64 hov
  have rdRetJd := rdRetPc.jumpdest (by native_decide) (by evm_ov)
  simpa [dropNoSwapFinalAccountMapFor] using
    RD.stop rdRetJd (by native_decide) (by evm_ov)

theorem RD.cureDropNoSwapStoreAndLogReturn {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ⟨484⟩ :: R) mem
        (UInt256.ofNat 3) rdata σ k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hpos : solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩)
    (hnoswap :
      (solcSlotWord σ ee ⟨2⟩).toNat ≤
        (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key)).toNat)
    (hperm : ee.perm = true)
    (hlenPos : 0 < (solcSlotWord σ ee ⟨2⟩).toNat)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 20 ≤ 1024) :
    RDret cureBytecode g s0
      (dropNoSwapFinalAccountMapFor σ ee key (solcSlotWord σ ee ⟨2⟩))
      ByteArray.empty :=
  permSplit_true hperm (RD.cureDropNoSwapStoreAndLogReturnSplit
    h hcanonKey hpos hnoswap hlenPos hmem hread64 hov)

theorem RD.cureDropNoSwapPopEmptyInvalid {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ⟨484⟩ :: R) mem
        (UInt256.ofNat 3) rdata σ k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hpos : solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩)
    (hnoswap :
      (solcSlotWord σ ee ⟨2⟩).toNat ≤
        (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key)).toNat)
    (hlenZero : solcSlotWord σ ee ⟨2⟩ = ⟨0⟩)
    (hmem : mem.size = 96)
    (hov : R.length + 20 ≤ 1024) :
    RDinvalid cureBytecode g s0 := by
  obtain ⟨_, _, rd3197⟩ := RD.cureDropNoSwapPrefix
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    h hcanonKey hpos hnoswap hmem (by omega)
  exact RD.cureDropPopEmptyInvalid
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3197 hlenZero (by omega)

theorem RD.cureDropSwapStoreAndLogReturn {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ⟨484⟩ :: R) mem
        (UInt256.ofNat 3) rdata σ k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hpos : solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩)
    (hswap :
      (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key)).toNat <
        (solcSlotWord σ ee ⟨2⟩).toNat)
    (hperm : ee.perm = true)
    (hlenPos : 0 < (solcSlotWord σ ee ⟨2⟩).toNat)
    (hposNat : 0 < (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key)).toNat)
    (hpopLenPos :
      0 <
        (dropSwapPopLenAccountMapFor σ ee
          (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key))
          (solcSlotWord σ ee ⟨2⟩)).toNat)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 24 ≤ 1024) :
    RDret cureBytecode g s0
      (dropSwapFinalAccountMapFor σ ee key
        (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key)) (solcSlotWord σ ee ⟨2⟩))
      ByteArray.empty := by
  let len := solcSlotWord σ ee ⟨2⟩
  let pos := solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key)
  let popLen := dropSwapPopLenAccountMapFor σ ee pos len
  obtain ⟨_, _, rd3068⟩ := RD.cureDropLoadedPosLenPrefix
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    h hcanonKey hpos hmem (by omega)
  obtain ⟨_, _, rd3076⟩ := RD.cureDropSwapBranchEntered
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3068 hswap (by omega)
  obtain ⟨_, _, rd3106⟩ := RD.cureDropSwapLoadMovePrefix
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3076 rfl hlenPos (by omega)
  obtain ⟨_, _, rd3123⟩ := RD.cureDropSwapMaskMovePrefix
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3106 rfl (by omega)
  obtain ⟨_, _, rd3179⟩ := RD.cureDropSwapStoreMoveElemPrefix
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3123 hperm hswap hposNat (by omega)
  have hprefixMemSize :
      (twoWordHashMem key ⟨5⟩ mem).size = 96 :=
    twoWordHashMem_size_96 key ⟨5⟩ hmem
  have hmoveLoadMemSize :
      (wordAt0Mem ⟨2⟩ (twoWordHashMem key ⟨5⟩ mem)).size = 96 :=
    wordAt0Mem_size_96 ⟨2⟩ hprefixMemSize
  have hmoveElemMemSize :
      (wordAt0Mem ⟨2⟩ (wordAt0Mem ⟨2⟩ (twoWordHashMem key ⟨5⟩ mem))).size = 96 :=
    wordAt0Mem_size_96 ⟨2⟩ hmoveLoadMemSize
  obtain ⟨_, _, rd3197⟩ := RD.cureDropSwapStoreMovePosPrefix
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3179 hperm hmoveElemMemSize (by omega)
  have hlenAfterMove :
      solcSlotWord (dropMovePosAccountMapFor σ ee pos len) ee ⟨2⟩ = popLen := by
    rfl
  have hpopLenPos' : 0 < popLen.toNat := by
    simpa [popLen, pos, len] using hpopLenPos
  obtain ⟨_, _, rd3247⟩ := RD.cureDropNoSwapPopTail
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3197 hperm hlenAfterMove hpopLenPos' (by omega)
  have hprefixRead64 :
      (twoWordHashMem key ⟨5⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 key ⟨5⟩ hmem hread64
  have hmoveLoadRead64 :
      (wordAt0Mem ⟨2⟩ (twoWordHashMem key ⟨5⟩ mem)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    wordAt0Mem_read64_of_size96 ⟨2⟩ hprefixMemSize hprefixRead64
  have hmoveElemRead64 :
      (wordAt0Mem ⟨2⟩ (wordAt0Mem ⟨2⟩ (twoWordHashMem key ⟨5⟩ mem))).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    wordAt0Mem_read64_of_size96 ⟨2⟩ hmoveLoadMemSize hmoveLoadRead64
  have hswapMemSize :
      (twoWordHashMem (dropMoveWordFor σ ee len) ⟨5⟩
        (wordAt0Mem ⟨2⟩ (wordAt0Mem ⟨2⟩ (twoWordHashMem key ⟨5⟩ mem)))).size = 96 :=
    twoWordHashMem_size_96 (dropMoveWordFor σ ee len) ⟨5⟩ hmoveElemMemSize
  have hswapRead64 :
      (twoWordHashMem (dropMoveWordFor σ ee len) ⟨5⟩
        (wordAt0Mem ⟨2⟩ (wordAt0Mem ⟨2⟩ (twoWordHashMem key ⟨5⟩ mem)))).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (dropMoveWordFor σ ee len) ⟨5⟩ hmoveElemMemSize hmoveElemRead64
  have hpopMemSize :
      (wordAt0Mem ⟨2⟩
        (twoWordHashMem (dropMoveWordFor σ ee len) ⟨5⟩
          (wordAt0Mem ⟨2⟩ (wordAt0Mem ⟨2⟩ (twoWordHashMem key ⟨5⟩ mem))))).size = 96 :=
    wordAt0Mem_size_96 ⟨2⟩ hswapMemSize
  have hpopRead64 :
      (wordAt0Mem ⟨2⟩
        (twoWordHashMem (dropMoveWordFor σ ee len) ⟨5⟩
          (wordAt0Mem ⟨2⟩ (wordAt0Mem ⟨2⟩ (twoWordHashMem key ⟨5⟩ mem))))).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    wordAt0Mem_read64_of_size96 ⟨2⟩ hswapMemSize hswapRead64
  obtain ⟨_, _, rdRetPc⟩ := RD.cureDropNoSwapDeleteLogTail
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3247 (by jump_dest) hperm hcanonKey hpopMemSize hpopRead64 (by omega)
  have rdRetJd := rdRetPc.jumpdest (by native_decide) (by evm_ov)
  simpa [dropSwapFinalAccountMapFor, len, pos, popLen] using
    RD.stop rdRetJd (by native_decide) (by evm_ov)

theorem RD.cureDropSwapPopEmptyInvalidSplit {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ⟨484⟩ :: R) mem
        (UInt256.ofNat 3) rdata σ k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hpos : solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩)
    (hswap :
      (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key)).toNat <
        (solcSlotWord σ ee ⟨2⟩).toNat)
    (hmem : mem.size = 96)
    (hov : R.length + 24 ≤ 1024) :
    (ee.perm = true ∧
      (dropSwapPopLenAccountMapFor σ ee
          (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key))
          (solcSlotWord σ ee ⟨2⟩) = ⟨0⟩ →
      RDinvalid cureBytecode g s0)) ∨
      (ee.perm = false ∧ RDstatic cureBytecode g s0) := by
  let len := solcSlotWord σ ee ⟨2⟩
  let pos := solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key)
  let popLen := dropSwapPopLenAccountMapFor σ ee pos len
  obtain ⟨_, _, rd3068⟩ := RD.cureDropLoadedPosLenPrefix
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    h hcanonKey hpos hmem (by omega)
  have hposNat : 0 < pos.toNat := by
    by_contra hnot
    have hz : pos.toNat = 0 := by omega
    have hposZero : pos = ⟨0⟩ := by
      rw [← u256_ofNat_toNat pos, hz]
      rfl
    apply hpos
    simpa [pos] using hposZero
  have hlastNat : 0 < len.toNat := by
    have hlt : pos.toNat < len.toNat := by simpa [pos, len] using hswap
    omega
  obtain ⟨_, _, rd3076⟩ := RD.cureDropSwapBranchEntered
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3068 hswap (by omega)
  obtain ⟨_, _, rd3106⟩ := RD.cureDropSwapLoadMovePrefix
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3076 rfl hlastNat (by omega)
  obtain ⟨_, _, rd3123⟩ := RD.cureDropSwapMaskMovePrefix
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3106 rfl (by omega)
  have hfirstWrite := RD.cureDropSwapStoreMoveElemPrefixSplit
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3123 hswap hposNat (by omega)
  refine permSplit_bind hfirstWrite ?_
  intro hperm hreach hpopLenZero
  obtain ⟨_, _, rd3179⟩ := hreach
  have hprefixMemSize :
      (twoWordHashMem key ⟨5⟩ mem).size = 96 :=
    twoWordHashMem_size_96 key ⟨5⟩ hmem
  have hmoveLoadMemSize :
      (wordAt0Mem ⟨2⟩ (twoWordHashMem key ⟨5⟩ mem)).size = 96 :=
    wordAt0Mem_size_96 ⟨2⟩ hprefixMemSize
  have hmoveElemMemSize :
      (wordAt0Mem ⟨2⟩ (wordAt0Mem ⟨2⟩ (twoWordHashMem key ⟨5⟩ mem))).size = 96 :=
    wordAt0Mem_size_96 ⟨2⟩ hmoveLoadMemSize
  obtain ⟨_, _, rd3197⟩ := RD.cureDropSwapStoreMovePosPrefix
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3179 hperm hmoveElemMemSize (by omega)
  have hlenAfterMove :
      solcSlotWord (dropMovePosAccountMapFor σ ee pos len) ee ⟨2⟩ = ⟨0⟩ := by
    simpa [popLen, pos, len] using hpopLenZero
  exact RD.cureDropPopEmptyInvalid
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3197 hlenAfterMove (by omega)

theorem RD.cureDropSwapPopEmptyInvalid {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ⟨484⟩ :: R) mem
        (UInt256.ofNat 3) rdata σ k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hpos : solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩)
    (hswap :
      (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key)).toNat <
        (solcSlotWord σ ee ⟨2⟩).toNat)
    (hperm : ee.perm = true)
    (hpopLenZero :
      dropSwapPopLenAccountMapFor σ ee
        (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key))
        (solcSlotWord σ ee ⟨2⟩) = ⟨0⟩)
    (hmem : mem.size = 96)
    (hov : R.length + 24 ≤ 1024) :
    RDinvalid cureBytecode g s0 :=
  permSplit_true hperm (RD.cureDropSwapPopEmptyInvalidSplit
    h hcanonKey hpos hswap hmem hov) hpopLenZero

theorem cureDispatchDrop {I : ExecutionEnv}
    (hsel : selIs I (cureSelBytes 3)) :
    dispatchMsg contract I.calldata = some dropTransition := by
  have hcd : I.calldata.extract 0 4 = cureSelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some dropTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, cureSelBytes,
    cureAmtSelectorBytes, cureCageSelectorBytes, cureDenySelectorBytes,
    cureDropSelectorBytes]
  native_decide

theorem cureDecode_drop_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (dropTransition.params.map Param.name)
      (transitionSignature dropTransition).paramTypes I.calldata =
        some (dropLocals I) := by
  simpa [config, dropTransition, dropLocals, dropSrc] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "src") hsz36)

theorem cureDecode_drop_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (dropTransition.params.map Param.name)
      (transitionSignature dropTransition).paramTypes I.calldata = none := by
  simpa [config, dropTransition] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "src") hsz4 hshort)

set_option maxHeartbeats 5000000 in
theorem cureDropSwapFinalAccountMapEq
    {σ : AccountMap} {I : ExecutionEnv} {key : UInt256}
    (hposSlotEq : dropPosSlotFor I = solcMappingSlot ⟨5⟩ key)
    (hamtSlotEq : dropAmtSlotFor I = solcMappingSlot ⟨6⟩ key)
    :
    let posEvm := solcSlotWordAt (dropPosSlotFor I) σ I
    let posSolm := solcSlotWordAt (dropPosSlotFor I) σ I
    let lenEvm := solcSlotWordAt ⟨2⟩ σ I
    let lenSolm := solcSlotWordAt ⟨2⟩ σ I
    dropSwapFinalAccountMapFor σ I key posEvm lenEvm =
      (dropSwapFinalAccountMap σ I posSolm lenSolm) := by
  intro posEvm posSolm lenEvm lenSolm
  simp only [posEvm, posSolm, lenEvm, lenSolm,
    dropSwapFinalAccountMapFor, dropSwapFinalAccountMap,
    dropDeleteAmtAccountMapFor, dropDeletePosAccountMapFor,
    dropDeleteAmtAccountMap, dropDeletePosAccountMap]
  rw [hposSlotEq, hamtSlotEq]

theorem cureDropSwapPopLenAccountMapEq
    {σ : AccountMap} {I : ExecutionEnv} :
    let posEvm := solcSlotWordAt (dropPosSlotFor I) σ I
    let posSolm := solcSlotWordAt (dropPosSlotFor I) σ I
    let lenEvm := solcSlotWordAt ⟨2⟩ σ I
    let lenSolm := solcSlotWordAt ⟨2⟩ σ I
    dropSwapPopLenAccountMapFor σ I posEvm lenEvm =
      dropSwapPopLenAccountMapFor σ I posSolm lenSolm := by
  intro posEvm posSolm lenEvm lenSolm
  simp only [posEvm, posSolm, lenEvm, lenSolm]

theorem cureDropSwapSourceBodyForRefinement
    {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : solcSlotWordAt (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : solcSlotWordAt ⟨1⟩ σ I = ⟨1⟩)
    (hposNe : solcSlotWordAt (dropPosSlotFor I) σ I ≠ ⟨0⟩)
    (hlenPos : 0 < (solcSlotWordAt ⟨2⟩ σ I).toNat)
    (hswap :
      (solcSlotWordAt (dropPosSlotFor I) σ I).toNat <
        (solcSlotWordAt ⟨2⟩ σ I).toNat)
    (hpopLenPos :
      0 <
        (dropSwapPopLenState
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (solcSlotWordAt (dropPosSlotFor I) σ I)
          (solcSlotWordAt ⟨2⟩ σ I)).toNat) :
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let posWord := solcSlotWordAt (dropPosSlotFor I) σ I
    let lenWord := solcSlotWordAt ⟨2⟩ σ I
    let lastIndex := dropLastIndex lenWord
    let dstIndex := dropDstIndex posWord
    let localsPos : Store := (dropLocals I).insert "pos_" (.int (Int.ofNat posWord.toNat))
    let localsLast : Store := localsPos.insert "last" (.int (Int.ofNat lenWord.toNat))
    let localsLastIndex : Store :=
      localsLast.insert "lastIndex" (.int (Int.ofNat lastIndex.toNat))
    let localsMove : Store :=
      localsLastIndex.insert "move" (.address (dropMoveAddr evm0 lenWord))
    let localsDst : Store :=
      localsMove.insert "dstIndex" (.int (Int.ofNat dstIndex.toNat))
    let evmMoveElem := dropAfterMoveElemState evm0 posWord lenWord
    let evmMovePos := dropAfterMovePosState evm0 evmMoveElem posWord lenWord
    let popLen := dropSwapPopLenState evm0 posWord lenWord
    let evmPop := dropAfterPopState evmMovePos popLen
    let evmPos := dropAfterDeletePosState evmPop I
    let evmAmt := dropAfterDeleteAmtState evmPos I
    ExecTransitionBody config contract evm0 (dropLocals I) dropTransition.body
      (.returned { contract := contract, locals := localsDst } evmAmt none) := by
  intro evm0 posWord lenWord lastIndex dstIndex localsPos localsLast localsLastIndex
    localsMove localsDst evmMoveElem evmMovePos popLen evmPop evmPos evmAmt
  simpa [evm0, posWord, lenWord, lastIndex, dstIndex, localsPos, localsLast,
    localsLastIndex, localsMove, localsDst, evmMoveElem, evmMovePos, popLen, evmPop, evmPos,
    evmAmt] using
    (cureDropSourceBodyOkSwap (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hauth hlive hposNe hlenPos hswap hpopLenPos)

theorem cureDropSwapFinalAccountMapMatchesSolmState
    {σ σ₀ A I} {g key : UInt256}
    (hposSlotEq : dropPosSlotFor I = solcMappingSlot ⟨5⟩ key)
    (hamtSlotEq : dropAmtSlotFor I = solcMappingSlot ⟨6⟩ key)
    :
    let posEvm := solcSlotWordAt (dropPosSlotFor I) σ I
    let lenEvm := solcSlotWordAt ⟨2⟩ σ I
    let posSolm := solcSlotWordAt (dropPosSlotFor I) σ I
    let lenSolm := solcSlotWordAt ⟨2⟩ σ I
    let evm0Solm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evmMoveElem := dropAfterMoveElemState evm0Solm posSolm lenSolm
    let evmMovePos := dropAfterMovePosState evm0Solm evmMoveElem posSolm lenSolm
    let popLenSolm := dropSwapPopLenState evm0Solm posSolm lenSolm
    let evmPop := dropAfterPopState evmMovePos popLenSolm
    let evmPos := dropAfterDeletePosState evmPop I
    let evmAmt := dropAfterDeleteAmtState evmPos I
    dropSwapFinalAccountMapFor σ I key posEvm lenEvm =
      evmAmt.accountMap := by
  intro posEvm lenEvm posSolm lenSolm evm0Solm evmMoveElem evmMovePos popLenSolm evmPop
    evmPos evmAmt
  have hmap : dropSwapFinalAccountMapFor σ I key posEvm lenEvm =
      dropSwapFinalAccountMap σ I posSolm lenSolm := by
    simpa [posEvm, posSolm, lenEvm, lenSolm] using
      (cureDropSwapFinalAccountMapEq (σ := σ) (I := I) (key := key)
        hposSlotEq hamtSlotEq)
  simpa [evmAmt, evmPos, evmPop, popLenSolm, evmMovePos, evmMoveElem, evm0Solm,
    dropAfterDeleteAmtState, dropAfterDeletePosState, dropAfterPopState,
    dropAfterPopClearState, dropAfterMovePosState, dropAfterMoveElemState,
    dropSwapFinalAccountMap, dropMovePosAccountMapFor, dropMoveElemAccountMapFor,
    dropPopAccountMap, dropPopClearAccountMap, dropDeletePosAccountMap,
    dropDeleteAmtAccountMap, initState, storageStore_accountMap, storageStore_executionEnv,
    Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    solcSlotWordAt, solcSlotWord, posSolm, lenSolm]
    using hmap

theorem cureDropReturnRuntimeEquiv
    {σ σ₀ A I} {g : UInt256}
    {acc : AccountMap}
    {fr : Frame} {evm' : EVM.State}
    (hcode : I.code = cureBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some dropTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dropTransition.params.map Param.name)
        (transitionSignature dropTransition).paramTypes I.calldata = some (dropLocals I))
    (hret :
      RDret cureBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) acc ByteArray.empty)
    (hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) (dropLocals I)
        dropTransition.body (.returned fr evm' none))
    (haccounts : acc = evm'.accountMap) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have henc : returnEquiv ByteArray.empty none dropTransition.returnType := by
    rw [show dropTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
    haccounts henc

set_option maxHeartbeats 2000000 in
theorem cureDropSwapBranchRefinement {σ σ₀ A I} {g sel key : UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (hcode : I.code = cureBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some dropTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dropTransition.params.map Param.name)
        (transitionSignature dropTransition).paramTypes I.calldata = some (dropLocals I))
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hposSlotEq : dropPosSlotFor I = solcMappingSlot ⟨5⟩ key)
    (hamtSlotEq : dropAmtSlotFor I = solcMappingSlot ⟨6⟩ key)
    (hauthSolm : solcSlotWordAt (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hliveSolm : solcSlotWordAt ⟨1⟩ σ I = ⟨1⟩)
    (hposSolm : solcSlotWordAt (dropPosSlotFor I) σ I ≠ ⟨0⟩)
    (hafterLive :
      RD cureBytecode I (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        ⟨2962⟩ (key :: ⟨484⟩ :: [sel]) mem (UInt256.ofNat 3) rdata
        σ k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlenPos : 0 < (solcSlotWordAt ⟨2⟩ σ I).toNat)
    (hswap :
      (solcSlotWordAt (dropPosSlotFor I) σ I).toNat <
        (solcSlotWordAt ⟨2⟩ σ I).toNat)
    (hpopLenPosEvm :
      0 <
        (dropSwapPopLenAccountMapFor σ I
          (solcSlotWordAt (dropPosSlotFor I) σ I)
          (solcSlotWordAt ⟨2⟩ σ I)).toNat)
    (hpopLenPosSolm :
      0 <
        (dropSwapPopLenState
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (solcSlotWordAt (dropPosSlotFor I) σ I)
          (solcSlotWordAt ⟨2⟩ σ I)).toNat) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hposEvm : solcSlotWordAt (dropPosSlotFor I) σ I ≠ ⟨0⟩ := by
    intro hz
    apply hposSolm
    exact hz
  have hposNat : 0 < (solcSlotWordAt (dropPosSlotFor I) σ I).toNat := by
    by_contra hnot
    have hzeroNat : (solcSlotWordAt (dropPosSlotFor I) σ I).toNat = 0 := by
      omega
    apply hposEvm
    rw [← u256_ofNat_toNat (solcSlotWordAt (dropPosSlotFor I) σ I), hzeroNat]
    rfl
  have hlenPosSolm : 0 < (solcSlotWordAt ⟨2⟩ σ I).toNat := by
    exact hlenPos
  have hswapSolm :
      (solcSlotWordAt (dropPosSlotFor I) σ I).toNat <
        (solcSlotWordAt ⟨2⟩ σ I).toNat := by
    exact hswap
  have hbody := cureDropSwapSourceBodyForRefinement
    (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    hwv hauthSolm hliveSolm hposSolm hlenPosSolm hswapSolm hpopLenPosSolm
  have hposSolc : solcSlotWord σ I (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩ := by
    rw [← hposSlotEq]
    simpa [solcSlotWordAt] using hposEvm
  have hswapSolc :
      (solcSlotWord σ I (solcMappingSlot ⟨5⟩ key)).toNat <
        (solcSlotWord σ I ⟨2⟩).toNat := by
    simpa [solcSlotWordAt, hposSlotEq] using hswap
  have hposNatSolc :
      0 < (solcSlotWord σ I (solcMappingSlot ⟨5⟩ key)).toNat := by
    simpa [solcSlotWordAt, hposSlotEq] using hposNat
  have hret := RD.cureDropSwapStoreAndLogReturn
    (g := Sat256.ofUInt256 g)
    (s0 := initState σ σ₀ (Sat256.ofUInt256 g) A I)
    (ee := I) (key := key) (R := [sel])
    hafterLive hcanonKey hposSolc hswapSolc hperm hlenPos hposNatSolc
    (by simpa [solcSlotWordAt, hposSlotEq] using hpopLenPosEvm) hmem hread64
    (by simp)
  refine cureDropReturnRuntimeEquiv hcode hdispatch hdecode hret hbody ?_
  · simpa [solcSlotWordAt, hposSlotEq] using
      (cureDropSwapFinalAccountMapMatchesSolmState
        (σ := σ)  (σ₀ := σ₀) (A := A) (I := I)
        (g := g) (key := key) hposSlotEq hamtSlotEq)

set_option maxHeartbeats 5000000 in
theorem cureDropBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 3))
    (_hStorageWF : cureStorageWF σ I) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let sel := cureSelWord I
  let key := dropKey I
  let callerSlot := cureCallerWardsSlot I
  let locals := dropLocals I
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dropTransition :=
    cureDispatchDrop hsel
  have hreach := cureReachDropBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode :
        decodeCalldataWithMode config.abiDecodeMode (dropTransition.params.map Param.name)
          (transitionSignature dropTransition).paramTypes I.calldata = some (dropLocals I) :=
      cureDecode_drop_ok hsz36
    have hposSlotEq : dropPosSlotFor I = solcMappingSlot ⟨5⟩ key := by
      simpa [key] using dropPosSlotFor_eq I
    have hamtSlotEq : dropAmtSlotFor I = solcMappingSlot ⟨6⟩ key := by
      simpa [key] using dropAmtSlotFor_eq I
    obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
      (code := cureBytecode) (sel := sel) (entry := ⟨640⟩) (ret := ⟨484⟩)
      (decoded := ⟨662⟩) hreach
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by jump_dest) hsz36 hsize
    obtain ⟨_, _, hroutine⟩ := RD.solcOneAddressExternalMaskAndJumpMasked
      (code := cureBytecode) (decoded := ⟨662⟩) (ret := ⟨484⟩) (routine := ⟨2801⟩)
      (R := [sel]) hdecoded
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by jump_dest) (by simp)
    by_cases hauthEvm : solcSlotWordAt callerSlot σ I = ⟨1⟩
    · have hauthSolm : solcSlotWordAt callerSlot σ I = ⟨1⟩ := by
        exact hauthEvm
      have hauthSolc :
          solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
        simpa [callerSlot, cureCallerWardsSlot, solcSlotWordAt] using hauthEvm
      obtain ⟨_, _, hafterAuth⟩ := RD.cureAuthCheckOk
        (code := cureBytecode) (pc := ⟨2801⟩) (okPc := ⟨2891⟩)
        (key := key) (ret := ⟨484⟩) (R := [sel])
        (by simpa [key, dropKey] using hroutine)
        (by
          unfold cureAuthCheckWf
          repeat' first | apply And.intro | native_decide)
        hauthSolc (by jump_dest) (by simp)
      by_cases hliveEvm : solcSlotWordAt ⟨1⟩ σ I = ⟨1⟩
      · have hliveSolm : solcSlotWordAt ⟨1⟩ σ I = ⟨1⟩ := by
          exact hliveEvm
        have hliveSolc : solcSlotWord σ I ⟨1⟩ = ⟨1⟩ := by
          simpa [solcSlotWordAt] using hliveEvm
        obtain ⟨_, _, hafterLive⟩ := RD.cureLiveGuardOk
          (code := cureBytecode) (pc := ⟨2891⟩) (okPc := ⟨2962⟩)
          (key := key) (ret := ⟨484⟩) (R := [sel]) hafterAuth
          (by
            unfold cureLiveGuardWf
            repeat' first | apply And.intro | native_decide)
          hliveSolc (by jump_dest) (by simp)
        by_cases hposEvm : solcSlotWordAt (dropPosSlotFor I) σ I = ⟨0⟩
        · have hposSolm : solcSlotWordAt (dropPosSlotFor I) σ I = ⟨0⟩ := by
            exact hposEvm
          let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
          have hbody : ExecTransitionBody config contract evm0 locals dropTransition.body .reverted := by
            simpa [evm0, locals] using
              (cureDropSourceBodyPosZeroRevert
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hauthSolm hliveSolm hposSolm)
          have hposSolc : solcSlotWord σ I (solcMappingSlot ⟨5⟩ key) = ⟨0⟩ := by
            rw [← hposSlotEq]
            simpa [solcSlotWordAt] using hposEvm
          have hmemAuth :
              (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
            twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
          have hread64 :
              (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
            twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
              solcFreePtrMem_read64
          have hcanonKey : key.toNat < EVM.addressModulus := by
            dsimp [key, dropKey]
            rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
            exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
          have hrev := RD.cureDropPosZeroRevert
            (g := Sat256.ofUInt256 g)
            (s0 := initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (ee := I) (key := key) (ret := ⟨484⟩) (R := [sel])
            hafterLive hcanonKey hposSolc hmemAuth hread64 (by simp)
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hposSolm : solcSlotWordAt (dropPosSlotFor I) σ I ≠ ⟨0⟩ := by
            intro hsolm
            exact hposEvm hsolm
          have hposNat : 0 < (solcSlotWordAt (dropPosSlotFor I) σ I).toNat := by
            by_contra hnot
            have hzero : (solcSlotWordAt (dropPosSlotFor I) σ I).toNat = 0 := by omega
            apply hposEvm
            rw [← u256_ofNat_toNat (solcSlotWordAt (dropPosSlotFor I) σ I), hzero]
            rfl
          have hcanonKey : key.toNat < EVM.addressModulus := by
            dsimp [key, dropKey]
            rw [u256_land_comm solcAddrMask (calldataWord I.calldata 4)]
            exact solcAddrMask_result_canonical (calldataWord I.calldata 4)
          have hmemAuth :
              (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
            twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
          have hread64 :
              (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
                UInt256.toByteArray ⟨128⟩ :=
            twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
              solcFreePtrMem_read64
          by_cases hswap :
              (solcSlotWordAt (dropPosSlotFor I) σ I).toNat <
                (solcSlotWordAt ⟨2⟩ σ I).toNat
          · let popLenEvm :=
                dropSwapPopLenAccountMapFor σ I
                  (solcSlotWordAt (dropPosSlotFor I) σ I)
                  (solcSlotWordAt ⟨2⟩ σ I)
            let popLenSolm :=
                dropSwapPopLenAccountMapFor σ I
                  (solcSlotWordAt (dropPosSlotFor I) σ I)
                  (solcSlotWordAt ⟨2⟩ σ I)
            have hlenPos : 0 < (solcSlotWordAt ⟨2⟩ σ I).toNat := by
              omega
            have hpopLenEq : popLenEvm = popLenSolm := by
              simpa [popLenEvm, popLenSolm] using
                (cureDropSwapPopLenAccountMapEq (σ := σ) (I := I))
            have hlenPosSolm : 0 < (solcSlotWordAt ⟨2⟩ σ I).toNat := by
              exact hlenPos
            have hswapSolm :
                (solcSlotWordAt (dropPosSlotFor I) σ I).toNat <
                  (solcSlotWordAt ⟨2⟩ σ I).toNat := by
              exact hswap
            by_cases _hperm : I.perm = true
            swap
            · have hperm : I.perm = false := by simpa using _hperm
              have hposSolc : solcSlotWord σ I (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩ := by
                simpa [solcSlotWordAt, hposSlotEq] using hposEvm
              have hswapSolc :
                  (solcSlotWord σ I (solcMappingSlot ⟨5⟩ key)).toNat <
                    (solcSlotWord σ I ⟨2⟩).toNat := by
                simpa [solcSlotWordAt, hposSlotEq] using hswap
              have hstatic := permSplit_false hperm (RD.cureDropSwapPopEmptyInvalidSplit
                hafterLive hcanonKey hposSolc hswapSolc hmemAuth (by simp))
              exact hstatic.reEquivStaticHalt hcode hdispatch hdecode
                ((cureDropSourceBodySwapPopZeroRevertSplit
                  hwv hauthSolm hliveSolm hposSolm hlenPosSolm hswapSolm).2 hperm)
            by_cases hpopLenZero : popLenEvm = ⟨0⟩
            · have hpopLenZeroSolmState :
                  dropSwapPopLenState
                    (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (solcSlotWordAt (dropPosSlotFor I) σ I)
                    (solcSlotWordAt ⟨2⟩ σ I) = ⟨0⟩ := by
                rw [dropSwapPopLenState_initState_eq]
                change popLenSolm = ⟨0⟩
                rw [← hpopLenEq]
                exact hpopLenZero
              let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
              have hbody :
                  ExecTransitionBody config contract evm0 (dropLocals I)
                    dropTransition.body .reverted := by
                simpa [evm0] using
                  (cureDropSourceBodySwapPopZeroRevert
                    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hwv hauthSolm hliveSolm hposSolm hlenPosSolm hswapSolm
                    hpopLenZeroSolmState)
              have hposSolc :
                  solcSlotWord σ I (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩ := by
                rw [← hposSlotEq]
                simpa [solcSlotWordAt] using hposEvm
              have hswapSolc :
                  (solcSlotWord σ I (solcMappingSlot ⟨5⟩ key)).toNat <
                    (solcSlotWord σ I ⟨2⟩).toNat := by
                simpa [solcSlotWordAt, hposSlotEq] using hswap
              have hinv := RD.cureDropSwapPopEmptyInvalid
                (g := Sat256.ofUInt256 g)
                (s0 := initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (ee := I) (key := key) (R := [sel])
                hafterLive hcanonKey hposSolc hswapSolc _hperm
                (by simpa [popLenEvm, solcSlotWordAt, hposSlotEq] using hpopLenZero)
                hmemAuth (by simp)
              exact RDinvalid.reEquivExecutionInvalid hcode hinv hdispatch hdecode hbody
            · have hpopLenPosRaw : 0 < popLenEvm.toNat := by
                by_contra hnot
                have hzeroNat : popLenEvm.toNat = 0 := by omega
                apply hpopLenZero
                rw [← u256_ofNat_toNat popLenEvm, hzeroNat]
                rfl
              have hpopLenPosEvm :
                  0 <
                    (dropSwapPopLenAccountMapFor σ I
                      (solcSlotWordAt (dropPosSlotFor I) σ I)
                      (solcSlotWordAt ⟨2⟩ σ I)).toNat := by
                simpa [popLenEvm] using hpopLenPosRaw
              have hpopLenPosSolm :
                  0 <
                    (dropSwapPopLenState
                      (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                      (solcSlotWordAt (dropPosSlotFor I) σ I)
                      (solcSlotWordAt ⟨2⟩ σ I)).toNat := by
                rw [dropSwapPopLenState_initState_eq]
                change 0 < popLenSolm.toNat
                rw [← hpopLenEq]
                exact hpopLenPosRaw
              exact cureDropSwapBranchRefinement hcode hdispatch hdecode _hperm hwv
                hposSlotEq hamtSlotEq hauthSolm hliveSolm hposSolm
                hafterLive hcanonKey hmemAuth hread64 hlenPos hswap
                hpopLenPosEvm hpopLenPosSolm
          · have hnoswapEvm :
                (solcSlotWordAt ⟨2⟩ σ I).toNat ≤
                  (solcSlotWordAt (dropPosSlotFor I) σ I).toNat := by
              omega
            have hnoswapSolm :
                (solcSlotWordAt ⟨2⟩ σ I).toNat ≤
                  (solcSlotWordAt (dropPosSlotFor I) σ I).toNat := by
              exact hnoswapEvm
            have hposSolc :
                solcSlotWord σ I (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩ := by
              rw [← hposSlotEq]
              simpa [solcSlotWordAt] using hposEvm
            have hnoswapSolc :
                (solcSlotWord σ I ⟨2⟩).toNat ≤
                  (solcSlotWord σ I (solcMappingSlot ⟨5⟩ key)).toNat := by
              simpa [solcSlotWordAt, hposSlotEq] using hnoswapEvm
            by_cases hlenZeroEvm : solcSlotWordAt ⟨2⟩ σ I = ⟨0⟩
            · have hlenZeroSolm : solcSlotWordAt ⟨2⟩ σ I = ⟨0⟩ := by
                exact hlenZeroEvm
              let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
              have hbody :
                  ExecTransitionBody config contract evm0 (dropLocals I)
                    dropTransition.body .reverted := by
                simpa [evm0] using
                  (cureDropSourceBodyNoSwapPopZeroRevert
                    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hwv hauthSolm hliveSolm hposSolm hlenZeroSolm hnoswapSolm)
              have hinv := RD.cureDropNoSwapPopEmptyInvalid
                (g := Sat256.ofUInt256 g)
                (s0 := initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (ee := I) (key := key) (R := [sel])
                hafterLive hcanonKey hposSolc hnoswapSolc
                (by simpa [solcSlotWordAt] using hlenZeroEvm)
                hmemAuth (by simp)
              exact RDinvalid.reEquivExecutionInvalid hcode hinv hdispatch hdecode hbody
            · have hlenPos : 0 < (solcSlotWordAt ⟨2⟩ σ I).toNat := by
                by_contra hnot
                have hzeroNat : (solcSlotWordAt ⟨2⟩ σ I).toNat = 0 := by omega
                apply hlenZeroEvm
                rw [← u256_ofNat_toNat (solcSlotWordAt ⟨2⟩ σ I), hzeroNat]
                rfl
              have hlenPosSolm : 0 < (solcSlotWordAt ⟨2⟩ σ I).toNat := by
                exact hlenPos
              let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
              let lenSolm := solcSlotWordAt ⟨2⟩ σ I
              let evmPop := dropAfterPopState evm0 lenSolm
              let evmPos := dropAfterDeletePosState evmPop I
              let evmAmt := dropAfterDeleteAmtState evmPos I
              have hbodySplit := cureDropSourceBodyOkNoSwapSplit
                (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hauthSolm hliveSolm hposSolm hlenPosSolm hnoswapSolm
              have hfirstWrite := RD.cureDropNoSwapStoreAndLogReturnSplit
                (g := Sat256.ofUInt256 g)
                (s0 := initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (ee := I) (key := key) (R := [sel])
                hafterLive hcanonKey hposSolc hnoswapSolc hlenPos hmemAuth hread64 (by simp)
              rcases hfirstWrite with ⟨_, hret⟩ | ⟨hperm, hstatic⟩
              swap
              · exact hstatic.reEquivStaticHalt hcode hdispatch hdecode (hbodySplit.2 hperm)
              have hbody := hbodySplit.1
              have haccounts :
                  dropNoSwapFinalAccountMapFor σ I key
                    (solcSlotWordAt ⟨2⟩ σ I) = evmAmt.accountMap := by
                simp [evmAmt, evmPos, evmPop, evm0, lenSolm,
                  dropAfterDeleteAmtState, dropAfterDeletePosState, dropAfterPopState,
                  dropAfterPopClearState, dropNoSwapFinalAccountMapFor,
                  dropNoSwapFinalAccountMap, dropPopAccountMap, dropPopClearAccountMap,
                  dropDeletePosAccountMapFor, dropDeleteAmtAccountMapFor,
                  dropDeletePosAccountMap, dropDeleteAmtAccountMap, initState,
                  storageStore_accountMap, storageStore_executionEnv,
                  Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
                  solcSlotWordAt, solcSlotWord,
                  hposSlotEq, hamtSlotEq]
              have henc : returnEquiv ByteArray.empty none dropTransition.returnType := by
                rw [show dropTransition.returnType = [] by rfl]
                exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
              exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
                haccounts henc
      · have hliveSolm : solcSlotWordAt ⟨1⟩ σ I ≠ ⟨1⟩ := by
          intro hsolm
          exact hliveEvm hsolm
        let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
        have hbody : ExecTransitionBody config contract evm0 locals dropTransition.body .reverted := by
          have hguardAuth := cureAuthGuardEval_true
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := locals)
            (by simp [locals, dropLocals]) hauthSolm
          have hguardLive := cureLiveGuardEval_false
            (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := locals)
            (by simp [locals, dropLocals]) hliveSolm
          have hblock :
              ExecBlock config { contract := contract, locals := locals } evm0
              [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
                .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
                .require (.binary .eq (.storage liveRef) (.intLit 1)),
                .letDecl "pos_" (some uint256) (.storage (posRef (.var "src"))),
                .require (.binary .gt (.var "pos_") (.intLit 0)),
                .letDecl "last" (some uint256) (.arrayLength .storage srcsRef),
                .ite
                (.binary .lt (.var "pos_") (.var "last"))
                [ .letDecl "lastIndex" (some uint256) (sub256 (.var "last") (.intLit 1)),
                  .letDecl "move" (some addr) (.storage (srcElemRef (.var "lastIndex"))),
                  .letDecl "dstIndex" (some uint256) (sub256 (.var "pos_") (.intLit 1)),
                  .assign .storage (srcElemRef (.var "dstIndex")) (.var "move"),
                  .assign .storage (posRef (.var "move")) (.var "pos_") ]
                [],
                .pop srcsRef,
                .delete (posRef (.var "src")),
                .delete (amtRef (.var "src")) ]
              .reverted := by
            refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
            · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
            refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
            exact ExecBlock.consRevert (ExecStmt.requireFalse hguardLive)
          simpa [ExecTransitionBody, dropTransition, nonpayable, auth, live, evm0, locals]
            using ExecFuncBody.execBlockRevert hblock
        have hliveSolc : solcSlotWord σ I ⟨1⟩ ≠ ⟨1⟩ := by
          simpa [solcSlotWordAt] using hliveEvm
        have hmemAuth :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
          twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
        have hread64 :
            (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
            solcFreePtrMem_read64
        have hrev := RD.cureLiveGuardRevert
          (code := cureBytecode) (pc := ⟨2891⟩) (okPc := ⟨2962⟩)
          (key := key) (ret := ⟨484⟩) (R := [sel]) hafterAuth
          (by
            unfold cureLiveGuardWf
            repeat' first | apply And.intro | native_decide)
          (by
            unfold solcErrorStringRevertTailWf cureLiveGuardTailPc cureNotLiveRawWord
            repeat' first | apply And.intro | native_decide)
          hliveSolc hmemAuth hread64 (by simp)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : solcSlotWordAt callerSlot σ I ≠ ⟨1⟩ := by
        intro hsolm
        exact hauthEvm hsolm
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      have hbody : ExecTransitionBody config contract evm0 locals dropTransition.body .reverted := by
        have hguard := cureAuthGuardEval_false
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) (locals := locals)
          (by simp [locals, dropLocals]) hauthSolm
        have hblock := nonpayableSecondRequireReverts
          (cfg := config) (solm := { contract := contract, locals := locals })
          (evm := evm0)
          (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
          (rest := [
            .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .letDecl "pos_" (some uint256) (.storage (posRef (.var "src"))),
            .require (.binary .gt (.var "pos_") (.intLit 0)),
            .letDecl "last" (some uint256) (.arrayLength .storage srcsRef),
            .ite
              (.binary .lt (.var "pos_") (.var "last"))
              [ .letDecl "lastIndex" (some uint256) (sub256 (.var "last") (.intLit 1)),
              .letDecl "move" (some addr) (.storage (srcElemRef (.var "lastIndex"))),
              .letDecl "dstIndex" (some uint256) (sub256 (.var "pos_") (.intLit 1)),
              .assign .storage (srcElemRef (.var "dstIndex")) (.var "move"),
              .assign .storage (posRef (.var "move")) (.var "pos_") ]
              [],
            .pop srcsRef,
            .delete (posRef (.var "src")),
            .delete (amtRef (.var "src"))])
          (by simp [evm0, initState]; exact hwv)
          hguard
        simpa [ExecTransitionBody, dropTransition, nonpayable, auth, evm0, locals] using
          ExecFuncBody.execBlockRevert hblock
      have hauthSolc :
          solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
        simpa [callerSlot, cureCallerWardsSlot, solcSlotWordAt] using hauthEvm
      have hrev := RD.cureAuthCheckRevert
        (code := cureBytecode) (pc := ⟨2801⟩) (okPc := ⟨2891⟩)
        (key := key) (ret := ⟨484⟩) (R := [sel])
        (by simpa [key, dropKey] using hroutine)
        (by
          unfold cureAuthCheckWf
          repeat' first | apply And.intro | native_decide)
        (by
          unfold solcErrorStringRevertTailWf cureAuthTailPc cureNotAuthorizedRawWord
          repeat' first | apply And.intro | native_decide)
        hauthSolc (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hlt :
        UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
      apply ult_one
      rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
      change I.calldata.size - 4 < 32
      omega
    have hrev := RD.solcExternalStaticArgsShortReverts
      (code := cureBytecode) (sel := sel) (entry := ⟨640⟩) (ret := ⟨484⟩)
      (decoded := ⟨662⟩) (need := ⟨32⟩) hreach
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) hlt
    exact hrev.reEquivDecodingFailed hcode hdispatch
      (cureDecode_drop_none_short hsz4 (by omega))

end Benchmarks.Dss.Cure
