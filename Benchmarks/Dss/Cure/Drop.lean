import Benchmarks.Dss.Cure.DropSource
import Benchmarks.Dss.Cure.Srcs

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cure

abbrev cureSrcNotDefinedRawWord : UInt256 :=
  ⟨0x437572652f6e6f6e2d6578697374696e672d736f75726365⟩

theorem RD.cureDropPosZeroRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata (cA, σ) k C)
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
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD (solcMappingSlot ⟨5⟩ key) ⟨0⟩)) = ⟨0⟩ := by
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
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata (cA, σ) k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hpos : solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩)
    (hmem : mem.size = 96)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3068⟩
      (solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) ::
        key :: ret :: R)
      (twoWordHashMem key ⟨5⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
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
      (twoWordHashMem key ⟨5⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
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
      (twoWordHashMem key ⟨5⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [solcSlotWord] using rdLenLoad'⟩
  exact ⟨_, _, rdLenLoad⟩

theorem RD.cureDropNoSwapPrefix {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata (cA, σ) k C)
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
      (twoWordHashMem key ⟨5⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
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
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3068⟩ (len :: pos :: key :: ret :: R) mem
        (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hswap : pos.toNat < len.toNat)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3076⟩ (len :: pos :: key :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
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
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3076⟩ (len :: pos :: key :: ret :: R) mem
        (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨2⟩ = len)
    (hlenPos : 0 < len.toNat)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3106⟩
      (solcSlotWord σ ee (dropSrcsSlotForIndex (dropLastIndex len)) ::
        ⟨0⟩ :: len :: pos :: key :: ret :: R)
      (wordAt0Mem ⟨2⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hlastIndex : UInt256.sub len ⟨1⟩ = dropLastIndex len := by
    simpa [dropLastIndex] using dropSubOne_eq_pred len hlenPos
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
          (fromByteArrayBigEndian (ffi.KEC ((wordAt0Mem (⟨2⟩ : UInt256) mem).readWithPadding 0 32))) =
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
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [solcSlotWord, hlen] using rdLenLoaded'⟩
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
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3106⟩
        (solcSlotWord σ ee (dropSrcsSlotForIndex (dropLastIndex len)) ::
          ⟨0⟩ :: len :: pos :: key :: ret :: R)
        mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hlen : solcSlotWord σ ee ⟨2⟩ = len)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3123⟩
      (⟨2⟩ :: len :: dropMoveWordFor σ ee len :: len :: pos :: key :: ret :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
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
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [solcSlotWord, hlen] using rdLenLoaded'⟩
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

theorem RD.cureDropSwapStoreMoveElemPrefix {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret len pos : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3123⟩
        (⟨2⟩ :: len :: dropMoveWordFor σ ee len :: len :: pos :: key :: ret :: R)
        mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hswap : pos.toNat < len.toNat)
    (hposNat : 0 < pos.toNat)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3179⟩
      (⟨32⟩ :: ⟨0⟩ :: solcAddrMask :: dropMoveWordFor σ ee len ::
        len :: pos :: key :: ret :: R)
      (wordAt0Mem ⟨2⟩ mem) (UInt256.ofNat 3) rdata
      (cA, dropMoveElemAccountMapFor σ ee pos len) k' C' := by
  have hdstIndex : pos + UInt256.lnot ⟨0⟩ = dropDstIndex pos := by
    simpa [dropDstIndex] using dropLenAddLnotZero_eq_pred pos hposNat
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
          (fromByteArrayBigEndian (ffi.KEC ((wordAt0Mem (⟨2⟩ : UInt256) mem).readWithPadding 0 32))) =
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
      (wordAt0Mem ⟨2⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
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
    raw lor (by native_decide) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rdSetRaw
  rw [hstored] at rdSetRaw
  have rdStoreReady := rdSetRaw.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdStored'⟩ := rdStoreReady.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [dropMoveElemAccountMapFor] using rdStored'⟩

theorem RD.cureDropSwapStoreMovePosPrefix {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret len pos : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3179⟩
        (⟨32⟩ :: ⟨0⟩ :: solcAddrMask :: dropMoveWordFor σ ee len ::
          len :: pos :: key :: ret :: R)
        mem (UInt256.ofNat 3) rdata
        (cA, dropMoveElemAccountMapFor σ ee pos len) k C)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3197⟩
      (len :: pos :: key :: ret :: R)
      (twoWordHashMem (dropMoveWordFor σ ee len) ⟨5⟩ mem)
      (UInt256.ofNat 3) rdata
      (cA, dropMovePosAccountMapFor σ ee pos len) k' C' := by
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
            (ffi.KEC
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

theorem RD.cureDropNoSwapPopTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret oldLen popLen pos : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3197⟩ (oldLen :: pos :: key :: ret :: R) mem
        (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hlen : solcSlotWord σ ee ⟨2⟩ = popLen)
    (hlenPos : 0 < popLen.toNat)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3247⟩
      (⟨32⟩ :: ⟨0⟩ :: oldLen :: pos :: key :: ret :: R)
      (wordAt0Mem ⟨2⟩ mem) (UInt256.ofNat 3) rdata
      (cA, dropPopAccountMap σ ee popLen) k' C' := by
  have hsrcsSlot :
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC ((wordAt0Mem (⟨2⟩ : UInt256) mem).readWithPadding 0 32))) =
        srcsDataSlot := by
    simpa [srcsDataSlot, uInt256OfByteArray_eq] using
      wordAt0Mem_keccak_word (⟨2⟩ : UInt256) mem
  have hlastSlot :
      srcsDataSlot + UInt256.ofNat (popLen.toNat - 1) = dropSrcsLastSlot popLen := by
    exact (dropSrcsLastSlot_eq popLen hlenPos).symm
  have hpred : popLen + UInt256.lnot ⟨0⟩ = UInt256.ofNat (popLen.toNat - 1) :=
    dropLenAddLnotZero_eq_pred popLen hlenPos
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
      rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [solcSlotWord, hlen] using rdLenLoaded'⟩
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
      (wordAt0Mem ⟨2⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
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
  obtain ⟨_, _, rdCleared'⟩ := rdClearRaw.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdCleared⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨3241⟩
      (UInt256.lnot ⟨0⟩ :: ⟨32⟩ :: ⟨0⟩ :: popLen :: ⟨2⟩ :: oldLen :: pos ::
        key :: ret :: R)
      (wordAt0Mem ⟨2⟩ mem) (UInt256.ofNat 3) rdata
      (cA, dropPopClearAccountMap σ ee popLen) k' C' := by
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

theorem RD.cureDropPopEmptyInvalid {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret oldLen pos : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3197⟩ (oldLen :: pos :: key :: ret :: R) mem
        (UInt256.ofNat 3) rdata (cA, σ) k C)
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
      rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [solcSlotWord, hlen] using rdLenLoaded'⟩
  have rdCheckPrefix := evm_run rdLenLoaded with [
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨3208⟩ (by native_decide) (by evm_ov)]
  have rdInvalidPc := rdCheckPrefix.jumpiNT (by native_decide) rfl
    (by simp only [List.length_cons]; omega)
  exact rdInvalidHalt rdInvalidPc (by native_decide)

theorem RD.cureDropNoSwapDeleteLogTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret len pos : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3247⟩
        (⟨32⟩ :: ⟨0⟩ :: len :: pos :: key :: ret :: R) mem
        (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hret : (D_J cureBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ret R
      (wordAt32Mem ⟨6⟩ (twoWordHashMem key ⟨5⟩ mem)) (UInt256.ofNat 3) rdata
      (cA, dropDeleteAmtAccountMapFor (dropDeletePosAccountMapFor σ ee key) ee key) k' C' := by
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
      (cA, dropDeletePosAccountMapFor σ ee key) k' C' := by
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
  have hamtSlot := dropWordAt32TwoWordHashMem_solcMappingSlot ⟨6⟩ key ⟨5⟩ hmem
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
      (cA, dropDeleteAmtAccountMapFor (dropDeletePosAccountMapFor σ ee key) ee key) k' C' := by
    exact ⟨_, _, by simpa [dropDeleteAmtAccountMapFor] using rdAmtStored'⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (wordAt32Mem ⟨6⟩ (twoWordHashMem key ⟨5⟩ mem)).size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩
        then ⟨0⟩ else UInt256.ofNat (fromByteArrayBigEndian
          ((wordAt32Mem ⟨6⟩ (twoWordHashMem key ⟨5⟩ mem)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
    rw [if_neg (by
      rw [wordAt32Mem_size_96 ⟨6⟩ (twoWordHashMem_size_96 key ⟨5⟩ hmem)]
      native_decide)]
    rw [show (⟨64⟩ : UInt256).toNat = 64 from rfl,
      dropWordAt32TwoWordHashMem_read64 key ⟨5⟩ ⟨6⟩ hmem hread64]
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
  have rdLogged := RD.cureLog2 0 (UInt256.ofNat 3) rdLogPrefix
    (by native_decide) hperm mem_cost (by native_decide) (by evm_ov)
  have rdTail := evm_run rdLogged with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, RD.jump rdTail (by native_decide) hret (by evm_ov)⟩

theorem RD.cureDropNoSwapStoreAndLogReturn {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ⟨484⟩ :: R) mem
        (UInt256.ofNat 3) rdata (cA, σ) k C)
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
      (cA, dropNoSwapFinalAccountMapFor σ ee key (solcSlotWord σ ee ⟨2⟩))
      ByteArray.empty := by
  obtain ⟨_, _, rd3197⟩ := RD.cureDropNoSwapPrefix
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    h hcanonKey hpos hnoswap hmem (by omega)
  obtain ⟨_, _, rd3247⟩ := RD.cureDropNoSwapPopTail
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3197 hperm rfl hlenPos hov
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
    dropWordAt0Mem_read64_of_size96 ⟨2⟩
      (twoWordHashMem_size_96 key ⟨5⟩ hmem) hprefixMem
  obtain ⟨_, _, rdRetPc⟩ := RD.cureDropNoSwapDeleteLogTail
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3247 (by jump_dest) hperm hcanonKey hpopMemSize hpopRead64 hov
  have rdRetJd := rdRetPc.jumpdest (by native_decide) (by evm_ov)
  simpa [dropNoSwapFinalAccountMapFor] using
    RD.stop rdRetJd (by native_decide) (by evm_ov)

theorem RD.cureDropNoSwapPopEmptyInvalid {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ⟨484⟩ :: R) mem
        (UInt256.ofNat 3) rdata (cA, σ) k C)
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
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ⟨484⟩ :: R) mem
        (UInt256.ofNat 3) rdata (cA, σ) k C)
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
      (cA, dropSwapFinalAccountMapFor σ ee key
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
    dropWordAt0Mem_read64_of_size96 ⟨2⟩ hprefixMemSize hprefixRead64
  have hmoveElemRead64 :
      (wordAt0Mem ⟨2⟩ (wordAt0Mem ⟨2⟩ (twoWordHashMem key ⟨5⟩ mem))).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    dropWordAt0Mem_read64_of_size96 ⟨2⟩ hmoveLoadMemSize hmoveLoadRead64
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
    dropWordAt0Mem_read64_of_size96 ⟨2⟩ hswapMemSize hswapRead64
  obtain ⟨_, _, rdRetPc⟩ := RD.cureDropNoSwapDeleteLogTail
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3247 (by jump_dest) hperm hcanonKey hpopMemSize hpopRead64 (by omega)
  have rdRetJd := rdRetPc.jumpdest (by native_decide) (by evm_ov)
  simpa [dropSwapFinalAccountMapFor, len, pos, popLen] using
    RD.stop rdRetJd (by native_decide) (by evm_ov)

theorem RD.cureDropSwapPopEmptyInvalid {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨2962⟩ (key :: ⟨484⟩ :: R) mem
        (UInt256.ofNat 3) rdata (cA, σ) k C)
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
    RDinvalid cureBytecode g s0 := by
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
      solcSlotWord (dropMovePosAccountMapFor σ ee pos len) ee ⟨2⟩ = ⟨0⟩ := by
    simpa [popLen, pos, len] using hpopLenZero
  exact RD.cureDropPopEmptyInvalid
    (g := g) (s0 := s0) (ee := ee) (key := key) (ret := ⟨484⟩) (R := R)
    rd3197 hlenAfterMove (by omega)

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
theorem cureDropSwapFinalAccountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv} {key : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hposSlotEq : dropPosSlotFor I = solcMappingSlot ⟨5⟩ key)
    (hamtSlotEq : dropAmtSlotFor I = solcMappingSlot ⟨6⟩ key)
    (hposWord :
      cureSlotWord (dropPosSlotFor I) σ_evm I =
        cureSlotWord (dropPosSlotFor I) σ_solm I)
    (hlenWord : cureSlotWord ⟨2⟩ σ_evm I = cureSlotWord ⟨2⟩ σ_solm I) :
    let posEvm := cureSlotWord (dropPosSlotFor I) σ_evm I
    let posSolm := cureSlotWord (dropPosSlotFor I) σ_solm I
    let lenEvm := cureSlotWord ⟨2⟩ σ_evm I
    let lenSolm := cureSlotWord ⟨2⟩ σ_solm I
    accountMapEquiv (dropSwapFinalAccountMapFor σ_evm I key posEvm lenEvm)
      (dropSwapFinalAccountMap σ_solm I posSolm lenSolm) := by
  intro posEvm posSolm lenEvm lenSolm
  have hposEq : posEvm = posSolm := by
    simpa [posEvm, posSolm] using hposWord
  have hlenEq : lenEvm = lenSolm := by
    simpa [lenEvm, lenSolm] using hlenWord
  have hlastSrcSlot :
      dropSrcsSlotForIndex (dropLastIndex lenEvm) =
        dropSrcsSlotForIndex (dropLastIndex lenSolm) := by
    rw [hlenEq]
  have hlastSrcWord :
      solcSlotWord σ_evm I (dropSrcsSlotForIndex (dropLastIndex lenEvm)) =
        solcSlotWord σ_solm I (dropSrcsSlotForIndex (dropLastIndex lenSolm)) := by
    rw [hlastSrcSlot]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner
      (dropSrcsSlotForIndex (dropLastIndex lenSolm)) ⟨0⟩
  have hlastSrcWord' :
      solcSlotWord σ_evm I (dropSrcsSlotForIndex (dropLastIndex lenSolm)) =
        solcSlotWord σ_solm I (dropSrcsSlotForIndex (dropLastIndex lenSolm)) := by
    simpa [hlastSrcSlot] using hlastSrcWord
  have hmoveWord :
      dropMoveWordFor σ_evm I lenEvm =
        dropMoveWordFor σ_solm I lenSolm := by
    simpa [dropMoveWordFor, hlenEq] using
      congrArg (fun word => UInt256.land word solcAddrMask) hlastSrcWord'
  have hdstIndex :
      dropDstIndex posEvm = dropDstIndex posSolm := by
    rw [hposEq]
  have hdstSlot :
      dropSrcsSlotForIndex (dropDstIndex posEvm) =
        dropSrcsSlotForIndex (dropDstIndex posSolm) := by
    rw [hdstIndex]
  have hdstWord :
      solcSlotWord σ_evm I (dropSrcsSlotForIndex (dropDstIndex posEvm)) =
        solcSlotWord σ_solm I (dropSrcsSlotForIndex (dropDstIndex posSolm)) := by
    rw [hdstSlot]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner
      (dropSrcsSlotForIndex (dropDstIndex posSolm)) ⟨0⟩
  have hmoveElemVal :
      setAddressOffset0Word
          (solcSlotWord σ_evm I (dropSrcsSlotForIndex (dropDstIndex posEvm)))
          (dropMoveWordFor σ_evm I lenEvm) =
        setAddressOffset0Word
          (solcSlotWord σ_solm I (dropSrcsSlotForIndex (dropDstIndex posSolm)))
          (dropMoveWordFor σ_solm I lenSolm) := by
    rw [hdstWord, hmoveWord]
  have hmoveElemVal' :
      setAddressOffset0Word
          (solcSlotWord σ_evm I (dropSrcsSlotForIndex (dropDstIndex posSolm)))
          (dropMoveWordFor σ_evm I lenEvm) =
        setAddressOffset0Word
          (solcSlotWord σ_solm I (dropSrcsSlotForIndex (dropDstIndex posSolm)))
          (dropMoveWordFor σ_solm I lenSolm) := by
    simpa [hdstSlot] using hmoveElemVal
  have haccountsMoveElem :
      accountMapEquiv
        (dropMoveElemAccountMapFor σ_evm I posEvm lenEvm)
        (dropMoveElemAccountMapFor σ_solm I posSolm lenSolm) := by
    simpa [dropMoveElemAccountMapFor, hdstSlot, hmoveElemVal'] using
      accountMapEquiv_sstoreAccountMap I.codeOwner
        (dropSrcsSlotForIndex (dropDstIndex posSolm))
        (setAddressOffset0Word
          (solcSlotWord σ_solm I (dropSrcsSlotForIndex (dropDstIndex posSolm)))
          (dropMoveWordFor σ_solm I lenSolm))
        hAccounts
  have haccountsMovePos :
      accountMapEquiv
        (dropMovePosAccountMapFor σ_evm I posEvm lenEvm)
        (dropMovePosAccountMapFor σ_solm I posSolm lenSolm) := by
    simpa [dropMovePosAccountMapFor, hmoveWord, hposEq] using
      accountMapEquiv_sstoreAccountMap I.codeOwner
        (solcMappingSlot ⟨5⟩ (dropMoveWordFor σ_solm I lenSolm)) posSolm
        haccountsMoveElem
  let popLenEvm := dropSwapPopLenAccountMapFor σ_evm I posEvm lenEvm
  let popLenSolm := dropSwapPopLenAccountMapFor σ_solm I posSolm lenSolm
  have hpopLenEq : popLenEvm = popLenSolm := by
    simpa [popLenEvm, popLenSolm, dropSwapPopLenAccountMapFor] using
      accountMapEquiv_storage_findD haccountsMovePos I.codeOwner ⟨2⟩ ⟨0⟩
  have hlastPopSlot :
      dropSrcsLastSlot popLenEvm = dropSrcsLastSlot popLenSolm := by
    rw [hpopLenEq]
  have hlastPopWord :
      solcSlotWord (dropMovePosAccountMapFor σ_evm I posEvm lenEvm) I
          (dropSrcsLastSlot popLenEvm) =
        solcSlotWord (dropMovePosAccountMapFor σ_solm I posSolm lenSolm) I
          (dropSrcsLastSlot popLenSolm) := by
    rw [hlastPopSlot]
    exact accountMapEquiv_storage_findD haccountsMovePos I.codeOwner
      (dropSrcsLastSlot popLenSolm) ⟨0⟩
  have hclearWord :
      setAddressOffset0Word
          (solcSlotWord (dropMovePosAccountMapFor σ_evm I posEvm lenEvm) I
            (dropSrcsLastSlot popLenEvm)) ⟨0⟩ =
        setAddressOffset0Word
          (solcSlotWord (dropMovePosAccountMapFor σ_solm I posSolm lenSolm) I
            (dropSrcsLastSlot popLenSolm)) ⟨0⟩ := by
    rw [hlastPopWord]
  have hclearWord' :
      setAddressOffset0Word
          (solcSlotWord (dropMovePosAccountMapFor σ_evm I posEvm lenEvm) I
            (dropSrcsLastSlot popLenSolm)) ⟨0⟩ =
        setAddressOffset0Word
          (solcSlotWord (dropMovePosAccountMapFor σ_solm I posSolm lenSolm) I
            (dropSrcsLastSlot popLenSolm)) ⟨0⟩ := by
    simpa [hlastPopSlot] using hclearWord
  have haccountsClear :
      accountMapEquiv
        (dropPopClearAccountMap
          (dropMovePosAccountMapFor σ_evm I posEvm lenEvm) I popLenEvm)
        (dropPopClearAccountMap
          (dropMovePosAccountMapFor σ_solm I posSolm lenSolm) I popLenSolm) := by
    simpa [dropPopClearAccountMap, hlastPopSlot, hclearWord'] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (dropSrcsLastSlot popLenSolm)
        (setAddressOffset0Word
          (solcSlotWord (dropMovePosAccountMapFor σ_solm I posSolm lenSolm) I
            (dropSrcsLastSlot popLenSolm)) ⟨0⟩)
        haccountsMovePos
  have hpredWord :
      UInt256.ofNat (popLenEvm.toNat - 1) = UInt256.ofNat (popLenSolm.toNat - 1) := by
    rw [hpopLenEq]
  have haccountsPop :
      accountMapEquiv
        (dropPopAccountMap (dropMovePosAccountMapFor σ_evm I posEvm lenEvm) I popLenEvm)
        (dropPopAccountMap (dropMovePosAccountMapFor σ_solm I posSolm lenSolm) I popLenSolm) := by
    simpa [dropPopAccountMap, hpredWord] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩
        (UInt256.ofNat (popLenSolm.toNat - 1)) haccountsClear
  have haccountsPos :
      accountMapEquiv
        (dropDeletePosAccountMapFor
          (dropPopAccountMap (dropMovePosAccountMapFor σ_evm I posEvm lenEvm) I popLenEvm)
          I key)
        (dropDeletePosAccountMap
          (dropPopAccountMap (dropMovePosAccountMapFor σ_solm I posSolm lenSolm) I popLenSolm)
          I) := by
    simpa [dropDeletePosAccountMapFor, dropDeletePosAccountMap, hposSlotEq] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (dropPosSlotFor I) ⟨0⟩ haccountsPop
  have haccountsAmt :
      accountMapEquiv
        (dropDeleteAmtAccountMapFor
          (dropDeletePosAccountMapFor
            (dropPopAccountMap (dropMovePosAccountMapFor σ_evm I posEvm lenEvm) I popLenEvm)
            I key) I key)
        (dropDeleteAmtAccountMap
          (dropDeletePosAccountMap
          (dropPopAccountMap
              (dropMovePosAccountMapFor σ_solm I posSolm lenSolm) I popLenSolm)
            I) I) := by
    simpa [dropDeleteAmtAccountMapFor, dropDeleteAmtAccountMap, hamtSlotEq] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (dropAmtSlotFor I) ⟨0⟩ haccountsPos
  simpa [dropSwapFinalAccountMapFor, dropSwapFinalAccountMap] using haccountsAmt

theorem cureDropSwapPopLenAccountMapEq
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hposWord :
      cureSlotWord (dropPosSlotFor I) σ_evm I =
        cureSlotWord (dropPosSlotFor I) σ_solm I)
    (hlenWord : cureSlotWord ⟨2⟩ σ_evm I = cureSlotWord ⟨2⟩ σ_solm I) :
    let posEvm := cureSlotWord (dropPosSlotFor I) σ_evm I
    let posSolm := cureSlotWord (dropPosSlotFor I) σ_solm I
    let lenEvm := cureSlotWord ⟨2⟩ σ_evm I
    let lenSolm := cureSlotWord ⟨2⟩ σ_solm I
    dropSwapPopLenAccountMapFor σ_evm I posEvm lenEvm =
      dropSwapPopLenAccountMapFor σ_solm I posSolm lenSolm := by
  intro posEvm posSolm lenEvm lenSolm
  have hposEq : posEvm = posSolm := by
    simpa [posEvm, posSolm] using hposWord
  have hlenEq : lenEvm = lenSolm := by
    simpa [lenEvm, lenSolm] using hlenWord
  have hlastSrcSlot :
      dropSrcsSlotForIndex (dropLastIndex lenEvm) =
        dropSrcsSlotForIndex (dropLastIndex lenSolm) := by
    rw [hlenEq]
  have hlastSrcWord :
      solcSlotWord σ_evm I (dropSrcsSlotForIndex (dropLastIndex lenEvm)) =
        solcSlotWord σ_solm I (dropSrcsSlotForIndex (dropLastIndex lenSolm)) := by
    rw [hlastSrcSlot]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner
      (dropSrcsSlotForIndex (dropLastIndex lenSolm)) ⟨0⟩
  have hlastSrcWord' :
      solcSlotWord σ_evm I (dropSrcsSlotForIndex (dropLastIndex lenSolm)) =
        solcSlotWord σ_solm I (dropSrcsSlotForIndex (dropLastIndex lenSolm)) := by
    simpa [hlastSrcSlot] using hlastSrcWord
  have hmoveWord :
      dropMoveWordFor σ_evm I lenEvm =
        dropMoveWordFor σ_solm I lenSolm := by
    simpa [dropMoveWordFor, hlenEq] using
      congrArg (fun word => UInt256.land word solcAddrMask) hlastSrcWord'
  have hdstIndex :
      dropDstIndex posEvm = dropDstIndex posSolm := by
    rw [hposEq]
  have hdstSlot :
      dropSrcsSlotForIndex (dropDstIndex posEvm) =
        dropSrcsSlotForIndex (dropDstIndex posSolm) := by
    rw [hdstIndex]
  have hdstWord :
      solcSlotWord σ_evm I (dropSrcsSlotForIndex (dropDstIndex posEvm)) =
        solcSlotWord σ_solm I (dropSrcsSlotForIndex (dropDstIndex posSolm)) := by
    rw [hdstSlot]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner
      (dropSrcsSlotForIndex (dropDstIndex posSolm)) ⟨0⟩
  have hmoveElemVal :
      setAddressOffset0Word
          (solcSlotWord σ_evm I (dropSrcsSlotForIndex (dropDstIndex posEvm)))
          (dropMoveWordFor σ_evm I lenEvm) =
        setAddressOffset0Word
          (solcSlotWord σ_solm I (dropSrcsSlotForIndex (dropDstIndex posSolm)))
          (dropMoveWordFor σ_solm I lenSolm) := by
    rw [hdstWord, hmoveWord]
  have hmoveElemVal' :
      setAddressOffset0Word
          (solcSlotWord σ_evm I (dropSrcsSlotForIndex (dropDstIndex posSolm)))
          (dropMoveWordFor σ_evm I lenEvm) =
        setAddressOffset0Word
          (solcSlotWord σ_solm I (dropSrcsSlotForIndex (dropDstIndex posSolm)))
          (dropMoveWordFor σ_solm I lenSolm) := by
    simpa [hdstSlot] using hmoveElemVal
  have haccountsMoveElem :
      accountMapEquiv
        (dropMoveElemAccountMapFor σ_evm I posEvm lenEvm)
        (dropMoveElemAccountMapFor σ_solm I posSolm lenSolm) := by
    simpa [dropMoveElemAccountMapFor, hdstSlot, hmoveElemVal'] using
      accountMapEquiv_sstoreAccountMap I.codeOwner
        (dropSrcsSlotForIndex (dropDstIndex posSolm))
        (setAddressOffset0Word
          (solcSlotWord σ_solm I (dropSrcsSlotForIndex (dropDstIndex posSolm)))
          (dropMoveWordFor σ_solm I lenSolm))
        hAccounts
  have haccountsMovePos :
      accountMapEquiv
        (dropMovePosAccountMapFor σ_evm I posEvm lenEvm)
        (dropMovePosAccountMapFor σ_solm I posSolm lenSolm) := by
    simpa [dropMovePosAccountMapFor, hmoveWord, hposEq] using
      accountMapEquiv_sstoreAccountMap I.codeOwner
        (solcMappingSlot ⟨5⟩ (dropMoveWordFor σ_solm I lenSolm)) posSolm
        haccountsMoveElem
  simpa [dropSwapPopLenAccountMapFor] using
    accountMapEquiv_storage_findD haccountsMovePos I.codeOwner ⟨2⟩ ⟨0⟩

theorem cureDropSwapSourceBodyForRefinement
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩)
    (hposNe : cureSlotWord (dropPosSlotFor I) σ I ≠ ⟨0⟩)
    (hlenPos : 0 < (cureSlotWord ⟨2⟩ σ I).toNat)
    (hswap :
      (cureSlotWord (dropPosSlotFor I) σ I).toNat <
        (cureSlotWord ⟨2⟩ σ I).toNat)
    (hpopLenPos :
      0 <
        (dropSwapPopLenState
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          (cureSlotWord (dropPosSlotFor I) σ I)
          (cureSlotWord ⟨2⟩ σ I)).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let posWord := cureSlotWord (dropPosSlotFor I) σ I
    let lenWord := cureSlotWord ⟨2⟩ σ I
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
    (cureDropSourceBodyOkSwap (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hauth hlive hposNe hlenPos hswap hpopLenPos)

theorem cureDropSwapFinalCreated
    {cA gh bl σ σ₀ A I} {g pos len : UInt256} :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmMoveElem := dropAfterMoveElemState evm0 pos len
    let evmMovePos := dropAfterMovePosState evm0 evmMoveElem pos len
    let popLen := dropSwapPopLenState evm0 pos len
    let evmPop := dropAfterPopState evmMovePos popLen
    let evmPos := dropAfterDeletePosState evmPop I
    let evmAmt := dropAfterDeleteAmtState evmPos I
    cA = evmAmt.createdAccounts := by
  intro evm0 evmMoveElem evmMovePos popLen evmPop evmPos evmAmt
  simp [evmAmt, evmPos, evmPop, popLen, evmMovePos, evmMoveElem, evm0,
    dropAfterDeleteAmtState, dropAfterDeletePosState, dropAfterPopState,
    dropAfterPopClearState, dropAfterMovePosState, dropAfterMoveElemState,
    initState, storageStore_createdAccounts]

theorem cureDropSwapFinalAccountMapMatchesSolmState
    {cA gh bl σ_evm σ_solm σ₀ A I} {g key : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hposSlotEq : dropPosSlotFor I = solcMappingSlot ⟨5⟩ key)
    (hamtSlotEq : dropAmtSlotFor I = solcMappingSlot ⟨6⟩ key)
    (hposWord :
      cureSlotWord (dropPosSlotFor I) σ_evm I =
        cureSlotWord (dropPosSlotFor I) σ_solm I)
    (hlenWord : cureSlotWord ⟨2⟩ σ_evm I = cureSlotWord ⟨2⟩ σ_solm I) :
    let posEvm := cureSlotWord (dropPosSlotFor I) σ_evm I
    let lenEvm := cureSlotWord ⟨2⟩ σ_evm I
    let posSolm := cureSlotWord (dropPosSlotFor I) σ_solm I
    let lenSolm := cureSlotWord ⟨2⟩ σ_solm I
    let evm0Solm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmMoveElem := dropAfterMoveElemState evm0Solm posSolm lenSolm
    let evmMovePos := dropAfterMovePosState evm0Solm evmMoveElem posSolm lenSolm
    let popLenSolm := dropSwapPopLenState evm0Solm posSolm lenSolm
    let evmPop := dropAfterPopState evmMovePos popLenSolm
    let evmPos := dropAfterDeletePosState evmPop I
    let evmAmt := dropAfterDeleteAmtState evmPos I
    accountMapEquiv (dropSwapFinalAccountMapFor σ_evm I key posEvm lenEvm)
      evmAmt.accountMap := by
  intro posEvm lenEvm posSolm lenSolm evm0Solm evmMoveElem evmMovePos popLenSolm evmPop
    evmPos evmAmt
  have haccountsFinal :
      accountMapEquiv (dropSwapFinalAccountMapFor σ_evm I key posEvm lenEvm)
        (dropSwapFinalAccountMap σ_solm I posSolm lenSolm) := by
    simpa [posEvm, posSolm, lenEvm, lenSolm] using
      (cureDropSwapFinalAccountMapEquiv (σ_evm := σ_evm) (σ_solm := σ_solm)
        (I := I) (key := key) hAccounts hposSlotEq hamtSlotEq hposWord hlenWord)
  simpa [evmAmt, evmPos, evmPop, popLenSolm, evmMovePos, evmMoveElem, evm0Solm,
    dropAfterDeleteAmtState, dropAfterDeletePosState, dropAfterPopState,
    dropAfterPopClearState, dropAfterMovePosState, dropAfterMoveElemState,
    dropSwapFinalAccountMap, dropMovePosAccountMapFor, dropMoveElemAccountMapFor,
    dropPopAccountMap, dropPopClearAccountMap, dropDeletePosAccountMap,
    dropDeleteAmtAccountMap, initState, storageStore_accountMap, storageStore_executionEnv,
    Solm.EVM.storageLoad, State.lookupAccount, cureSlotWord, solcSlotWord, posSolm, lenSolm]
    using haccountsFinal

theorem cureDropReturnRuntimeEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {fr : Frame} {evm' : EVM.State}
    (hcode : I.code = cureBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some dropTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dropTransition.params.map Param.name)
        (transitionSignature dropTransition).paramTypes I.calldata = some (dropLocals I))
    (hret :
      RDret cureBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc ByteArray.empty)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (dropLocals I)
        dropTransition.body (.returned fr evm' none))
    (hcreated : acc.1 = evm'.createdAccounts)
    (haccounts : accountMapEquiv acc.2 evm'.accountMap) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have henc : returnEquiv ByteArray.empty none dropTransition.returnType := by
    rw [show dropTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    hcreated haccounts henc

set_option maxHeartbeats 2000000 in
theorem cureDropSwapBranchRefinement {cA gh bl σ_evm σ_solm σ₀ A I} {g sel key : UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (hcode : I.code = cureBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some dropTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (dropTransition.params.map Param.name)
        (transitionSignature dropTransition).paramTypes I.calldata = some (dropLocals I))
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hposSlotEq : dropPosSlotFor I = solcMappingSlot ⟨5⟩ key)
    (hamtSlotEq : dropAmtSlotFor I = solcMappingSlot ⟨6⟩ key)
    (hposWord :
      cureSlotWord (dropPosSlotFor I) σ_evm I =
        cureSlotWord (dropPosSlotFor I) σ_solm I)
    (hlenWord : cureSlotWord ⟨2⟩ σ_evm I = cureSlotWord ⟨2⟩ σ_solm I)
    (hauthSolm : cureSlotWord (cureCallerWardsSlot I) σ_solm I = ⟨1⟩)
    (hliveSolm : cureSlotWord ⟨1⟩ σ_solm I = ⟨1⟩)
    (hposSolm : cureSlotWord (dropPosSlotFor I) σ_solm I ≠ ⟨0⟩)
    (hafterLive :
      RD cureBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨2962⟩ (key :: ⟨484⟩ :: [sel]) mem (UInt256.ofNat 3) rdata
        (cA, σ_evm) k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlenPos : 0 < (cureSlotWord ⟨2⟩ σ_evm I).toNat)
    (hswap :
      (cureSlotWord (dropPosSlotFor I) σ_evm I).toNat <
        (cureSlotWord ⟨2⟩ σ_evm I).toNat)
    (hpopLenPosEvm :
      0 <
        (dropSwapPopLenAccountMapFor σ_evm I
          (cureSlotWord (dropPosSlotFor I) σ_evm I)
          (cureSlotWord ⟨2⟩ σ_evm I)).toNat)
    (hpopLenPosSolm :
      0 <
        (dropSwapPopLenState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (cureSlotWord (dropPosSlotFor I) σ_solm I)
          (cureSlotWord ⟨2⟩ σ_solm I)).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hposEvm : cureSlotWord (dropPosSlotFor I) σ_evm I ≠ ⟨0⟩ := by
    intro hz
    apply hposSolm
    rw [← hposWord]
    exact hz
  have hposNat : 0 < (cureSlotWord (dropPosSlotFor I) σ_evm I).toNat := by
    by_contra hnot
    have hzeroNat : (cureSlotWord (dropPosSlotFor I) σ_evm I).toNat = 0 := by
      omega
    apply hposEvm
    rw [← u256_ofNat_toNat (cureSlotWord (dropPosSlotFor I) σ_evm I), hzeroNat]
    rfl
  have hlenPosSolm : 0 < (cureSlotWord ⟨2⟩ σ_solm I).toNat := by
    rw [← hlenWord]
    exact hlenPos
  have hswapSolm :
      (cureSlotWord (dropPosSlotFor I) σ_solm I).toNat <
        (cureSlotWord ⟨2⟩ σ_solm I).toNat := by
    rw [← hposWord, ← hlenWord]
    exact hswap
  have hbody := cureDropSwapSourceBodyForRefinement
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    hwv hauthSolm hliveSolm hposSolm hlenPosSolm hswapSolm hpopLenPosSolm
  have hposSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩ := by
    rw [← hposSlotEq]
    simpa [cureSlotWord] using hposEvm
  have hswapSolc :
      (solcSlotWord σ_evm I (solcMappingSlot ⟨5⟩ key)).toNat <
        (solcSlotWord σ_evm I ⟨2⟩).toNat := by
    simpa [cureSlotWord, hposSlotEq] using hswap
  have hposNatSolc :
      0 < (solcSlotWord σ_evm I (solcMappingSlot ⟨5⟩ key)).toNat := by
    simpa [cureSlotWord, hposSlotEq] using hposNat
  have hret := RD.cureDropSwapStoreAndLogReturn
    (g := Sat256.ofUInt256 g)
    (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
    (ee := I) (key := key) (R := [sel])
    hafterLive hcanonKey hposSolc hswapSolc hperm hlenPos hposNatSolc
    (by simpa [cureSlotWord, hposSlotEq] using hpopLenPosEvm) hmem hread64
    (by simp)
  refine cureDropReturnRuntimeEquiv hcode hdispatch hdecode hret hbody ?_ ?_
  · simpa using
      (cureDropSwapFinalCreated (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (pos := cureSlotWord (dropPosSlotFor I) σ_solm I)
        (len := cureSlotWord ⟨2⟩ σ_solm I))
  · simpa [cureSlotWord, hposSlotEq] using
      (cureDropSwapFinalAccountMapMatchesSolmState (cA := cA) (gh := gh) (bl := bl)
        (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := g) (key := key) hAccounts hposSlotEq hamtSlotEq hposWord hlenWord)

set_option maxHeartbeats 5000000 in
theorem cureDropBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cureSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (_hStorageWF : cureStorageWF σ_evm I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let sel := cureSelWord I
  let key := dropKey I
  let callerSlot := cureCallerWardsSlot I
  let locals := dropLocals I
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (cureSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some dropTransition :=
    cureDispatchDrop hsel
  have hreach := cureReachDropBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode :
        decodeCalldataWithMode config.abiDecodeMode (dropTransition.params.map Param.name)
          (transitionSignature dropTransition).paramTypes I.calldata = some (dropLocals I) :=
      cureDecode_drop_ok hsz36
    have hcallerWord :
        cureSlotWord callerSlot σ_evm I = cureSlotWord callerSlot σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
    have hliveWord :
        cureSlotWord ⟨1⟩ σ_evm I = cureSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    have hposWord :
        cureSlotWord (dropPosSlotFor I) σ_evm I =
          cureSlotWord (dropPosSlotFor I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (dropPosSlotFor I) ⟨0⟩
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
    by_cases hauthEvm : cureSlotWord callerSlot σ_evm I = ⟨1⟩
    · have hauthSolm : cureSlotWord callerSlot σ_solm I = ⟨1⟩ := by
        rw [← hcallerWord]
        exact hauthEvm
      have hauthSolc :
          solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
        simpa [callerSlot, cureCallerWardsSlot, cureSlotWord] using hauthEvm
      obtain ⟨_, _, hafterAuth⟩ := RD.cureAuthCheckOk
        (code := cureBytecode) (pc := ⟨2801⟩) (okPc := ⟨2891⟩)
        (key := key) (ret := ⟨484⟩) (R := [sel])
        (by simpa [key, dropKey] using hroutine)
        (by
          unfold cureAuthCheckWf
          repeat' first | apply And.intro | native_decide)
        hauthSolc (by jump_dest) (by simp)
      by_cases hliveEvm : cureSlotWord ⟨1⟩ σ_evm I = ⟨1⟩
      · have hliveSolm : cureSlotWord ⟨1⟩ σ_solm I = ⟨1⟩ := by
          rw [← hliveWord]
          exact hliveEvm
        have hliveSolc : solcSlotWord σ_evm I ⟨1⟩ = ⟨1⟩ := by
          simpa [cureSlotWord] using hliveEvm
        obtain ⟨_, _, hafterLive⟩ := RD.cureLiveGuardOk
          (code := cureBytecode) (pc := ⟨2891⟩) (okPc := ⟨2962⟩)
          (key := key) (ret := ⟨484⟩) (R := [sel]) hafterAuth
          (by
            unfold cureLiveGuardWf
            repeat' first | apply And.intro | native_decide)
          hliveSolc (by jump_dest) (by simp)
        by_cases hposEvm : cureSlotWord (dropPosSlotFor I) σ_evm I = ⟨0⟩
        · have hposSolm : cureSlotWord (dropPosSlotFor I) σ_solm I = ⟨0⟩ := by
            rw [← hposWord]
            exact hposEvm
          let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          have hbody : ExecTransitionBody config contract evm0 locals dropTransition.body .reverted := by
            simpa [evm0, locals] using
              (cureDropSourceBodyPosZeroRevert (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hauthSolm hliveSolm hposSolm)
          have hposSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨5⟩ key) = ⟨0⟩ := by
            rw [← hposSlotEq]
            simpa [cureSlotWord] using hposEvm
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
            (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (ee := I) (key := key) (ret := ⟨484⟩) (R := [sel])
            hafterLive hcanonKey hposSolc hmemAuth hread64 (by simp)
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hposSolm : cureSlotWord (dropPosSlotFor I) σ_solm I ≠ ⟨0⟩ := by
            intro hsolm
            exact hposEvm (by rw [hposWord, hsolm])
          have hposNat : 0 < (cureSlotWord (dropPosSlotFor I) σ_evm I).toNat := by
            by_contra hnot
            have hzero : (cureSlotWord (dropPosSlotFor I) σ_evm I).toNat = 0 := by omega
            apply hposEvm
            rw [← u256_ofNat_toNat (cureSlotWord (dropPosSlotFor I) σ_evm I), hzero]
            rfl
          have hlenWord :
              cureSlotWord ⟨2⟩ σ_evm I = cureSlotWord ⟨2⟩ σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
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
              (cureSlotWord (dropPosSlotFor I) σ_evm I).toNat <
                (cureSlotWord ⟨2⟩ σ_evm I).toNat
          · let popLenEvm :=
                dropSwapPopLenAccountMapFor σ_evm I
                  (cureSlotWord (dropPosSlotFor I) σ_evm I)
                  (cureSlotWord ⟨2⟩ σ_evm I)
            let popLenSolm :=
                dropSwapPopLenAccountMapFor σ_solm I
                  (cureSlotWord (dropPosSlotFor I) σ_solm I)
                  (cureSlotWord ⟨2⟩ σ_solm I)
            have hlenPos : 0 < (cureSlotWord ⟨2⟩ σ_evm I).toNat := by
              omega
            have hpopLenEq : popLenEvm = popLenSolm := by
              simpa [popLenEvm, popLenSolm] using
                (cureDropSwapPopLenAccountMapEq (σ_evm := σ_evm) (σ_solm := σ_solm)
                  (I := I) hAccounts hposWord hlenWord)
            have hlenPosSolm : 0 < (cureSlotWord ⟨2⟩ σ_solm I).toNat := by
              rw [← hlenWord]
              exact hlenPos
            have hswapSolm :
                (cureSlotWord (dropPosSlotFor I) σ_solm I).toNat <
                  (cureSlotWord ⟨2⟩ σ_solm I).toNat := by
              rw [← hposWord, ← hlenWord]
              exact hswap
            by_cases hpopLenZero : popLenEvm = ⟨0⟩
            · have hpopLenZeroSolmState :
                  dropSwapPopLenState
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (cureSlotWord (dropPosSlotFor I) σ_solm I)
                    (cureSlotWord ⟨2⟩ σ_solm I) = ⟨0⟩ := by
                rw [dropSwapPopLenState_initState_eq]
                change popLenSolm = ⟨0⟩
                rw [← hpopLenEq]
                exact hpopLenZero
              let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
              have hbody :
                  ExecTransitionBody config contract evm0 (dropLocals I)
                    dropTransition.body .reverted := by
                simpa [evm0] using
                  (cureDropSourceBodySwapPopZeroRevert (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hwv hauthSolm hliveSolm hposSolm hlenPosSolm hswapSolm
                    hpopLenZeroSolmState)
              have hposSolc :
                  solcSlotWord σ_evm I (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩ := by
                rw [← hposSlotEq]
                simpa [cureSlotWord] using hposEvm
              have hswapSolc :
                  (solcSlotWord σ_evm I (solcMappingSlot ⟨5⟩ key)).toNat <
                    (solcSlotWord σ_evm I ⟨2⟩).toNat := by
                simpa [cureSlotWord, hposSlotEq] using hswap
              have hinv := RD.cureDropSwapPopEmptyInvalid
                (g := Sat256.ofUInt256 g)
                (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (ee := I) (key := key) (R := [sel])
                hafterLive hcanonKey hposSolc hswapSolc _hperm
                (by simpa [popLenEvm, cureSlotWord, hposSlotEq] using hpopLenZero)
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
                    (dropSwapPopLenAccountMapFor σ_evm I
                      (cureSlotWord (dropPosSlotFor I) σ_evm I)
                      (cureSlotWord ⟨2⟩ σ_evm I)).toNat := by
                simpa [popLenEvm] using hpopLenPosRaw
              have hpopLenPosSolm :
                  0 <
                    (dropSwapPopLenState
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      (cureSlotWord (dropPosSlotFor I) σ_solm I)
                      (cureSlotWord ⟨2⟩ σ_solm I)).toNat := by
                rw [dropSwapPopLenState_initState_eq]
                change 0 < popLenSolm.toNat
                rw [← hpopLenEq]
                exact hpopLenPosRaw
              exact cureDropSwapBranchRefinement hcode hdispatch hdecode _hperm hwv
                hAccounts hposSlotEq hamtSlotEq hposWord hlenWord hauthSolm hliveSolm hposSolm
                hafterLive hcanonKey hmemAuth hread64 hlenPos hswap
                hpopLenPosEvm hpopLenPosSolm
          · have hnoswapEvm :
                (cureSlotWord ⟨2⟩ σ_evm I).toNat ≤
                  (cureSlotWord (dropPosSlotFor I) σ_evm I).toNat := by
              omega
            have hnoswapSolm :
                (cureSlotWord ⟨2⟩ σ_solm I).toNat ≤
                  (cureSlotWord (dropPosSlotFor I) σ_solm I).toNat := by
              rw [← hlenWord, ← hposWord]
              exact hnoswapEvm
            have hposSolc :
                solcSlotWord σ_evm I (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩ := by
              rw [← hposSlotEq]
              simpa [cureSlotWord] using hposEvm
            have hnoswapSolc :
                (solcSlotWord σ_evm I ⟨2⟩).toNat ≤
                  (solcSlotWord σ_evm I (solcMappingSlot ⟨5⟩ key)).toNat := by
              simpa [cureSlotWord, hposSlotEq] using hnoswapEvm
            by_cases hlenZeroEvm : cureSlotWord ⟨2⟩ σ_evm I = ⟨0⟩
            · have hlenZeroSolm : cureSlotWord ⟨2⟩ σ_solm I = ⟨0⟩ := by
                rw [← hlenWord]
                exact hlenZeroEvm
              let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
              have hbody :
                  ExecTransitionBody config contract evm0 (dropLocals I)
                    dropTransition.body .reverted := by
                simpa [evm0] using
                  (cureDropSourceBodyNoSwapPopZeroRevert (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hwv hauthSolm hliveSolm hposSolm hlenZeroSolm hnoswapSolm)
              have hinv := RD.cureDropNoSwapPopEmptyInvalid
                (g := Sat256.ofUInt256 g)
                (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (ee := I) (key := key) (R := [sel])
                hafterLive hcanonKey hposSolc hnoswapSolc
                (by simpa [cureSlotWord] using hlenZeroEvm)
                hmemAuth (by simp)
              exact RDinvalid.reEquivExecutionInvalid hcode hinv hdispatch hdecode hbody
            · have hlenPos : 0 < (cureSlotWord ⟨2⟩ σ_evm I).toNat := by
                by_contra hnot
                have hzeroNat : (cureSlotWord ⟨2⟩ σ_evm I).toNat = 0 := by omega
                apply hlenZeroEvm
                rw [← u256_ofNat_toNat (cureSlotWord ⟨2⟩ σ_evm I), hzeroNat]
                rfl
              have hlenPosSolm : 0 < (cureSlotWord ⟨2⟩ σ_solm I).toNat := by
                rw [← hlenWord]
                exact hlenPos
              let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
              let lenSolm := cureSlotWord ⟨2⟩ σ_solm I
              let evmPop := dropAfterPopState evm0 lenSolm
              let evmPos := dropAfterDeletePosState evmPop I
              let evmAmt := dropAfterDeleteAmtState evmPos I
              have hbody := cureDropSourceBodyOkNoSwap (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hauthSolm hliveSolm hposSolm hlenPosSolm hnoswapSolm
              have hret := RD.cureDropNoSwapStoreAndLogReturn
                (g := Sat256.ofUInt256 g)
                (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                (ee := I) (key := key) (R := [sel])
                hafterLive hcanonKey hposSolc hnoswapSolc _hperm hlenPos hmemAuth hread64 (by simp)
              have hcreated :
                  (cA, dropNoSwapFinalAccountMapFor σ_evm I key
                    (cureSlotWord ⟨2⟩ σ_evm I)).1 = evmAmt.createdAccounts := by
                simp [evmAmt, evmPos, evmPop, evm0, dropAfterDeleteAmtState,
                  dropAfterDeletePosState, dropAfterPopState, dropAfterPopClearState,
                  initState, storageStore_createdAccounts]
              have hlastSlot :
                  dropSrcsLastSlot (cureSlotWord ⟨2⟩ σ_evm I) =
                    dropSrcsLastSlot (cureSlotWord ⟨2⟩ σ_solm I) := by
                rw [hlenWord]
              have hlastWord :
                  solcSlotWord σ_evm I (dropSrcsLastSlot (cureSlotWord ⟨2⟩ σ_evm I)) =
                    solcSlotWord σ_solm I (dropSrcsLastSlot (cureSlotWord ⟨2⟩ σ_solm I)) := by
                rw [hlastSlot]
                exact accountMapEquiv_storage_findD hAccounts I.codeOwner
                  (dropSrcsLastSlot (cureSlotWord ⟨2⟩ σ_solm I)) ⟨0⟩
              have hclearWord :
                  setAddressOffset0Word
                      (solcSlotWord σ_evm I
                        (dropSrcsLastSlot (cureSlotWord ⟨2⟩ σ_evm I))) ⟨0⟩ =
                    setAddressOffset0Word
                      (solcSlotWord σ_solm I
                        (dropSrcsLastSlot (cureSlotWord ⟨2⟩ σ_solm I))) ⟨0⟩ := by
                rw [hlastWord]
              have hclearWord' :
                  setAddressOffset0Word
                      (solcSlotWord σ_evm I
                        (dropSrcsLastSlot (cureSlotWord ⟨2⟩ σ_solm I))) ⟨0⟩ =
                    setAddressOffset0Word
                      (solcSlotWord σ_solm I
                        (dropSrcsLastSlot (cureSlotWord ⟨2⟩ σ_solm I))) ⟨0⟩ := by
                simpa [hlastSlot] using hclearWord
              have haccountsClear :
                  accountMapEquiv
                    (dropPopClearAccountMap σ_evm I (cureSlotWord ⟨2⟩ σ_evm I))
                    (dropPopClearAccountMap σ_solm I (cureSlotWord ⟨2⟩ σ_solm I)) := by
                simpa [dropPopClearAccountMap, hlastSlot, hclearWord'] using
                  accountMapEquiv_sstoreAccountMap I.codeOwner
                    (dropSrcsLastSlot (cureSlotWord ⟨2⟩ σ_solm I))
                    (setAddressOffset0Word
                      (solcSlotWord σ_solm I
                        (dropSrcsLastSlot (cureSlotWord ⟨2⟩ σ_solm I))) ⟨0⟩)
                    hAccounts
              have hpredWord :
                  UInt256.ofNat ((cureSlotWord ⟨2⟩ σ_evm I).toNat - 1) =
                    UInt256.ofNat ((cureSlotWord ⟨2⟩ σ_solm I).toNat - 1) := by
                rw [hlenWord]
              have haccountsPop :
                  accountMapEquiv
                    (dropPopAccountMap σ_evm I (cureSlotWord ⟨2⟩ σ_evm I))
                    (dropPopAccountMap σ_solm I (cureSlotWord ⟨2⟩ σ_solm I)) := by
                simpa [dropPopAccountMap, hpredWord] using
                  accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩
                    (UInt256.ofNat ((cureSlotWord ⟨2⟩ σ_solm I).toNat - 1))
                    haccountsClear
              have haccountsPos :
                  accountMapEquiv
                    (dropDeletePosAccountMapFor
                      (dropPopAccountMap σ_evm I (cureSlotWord ⟨2⟩ σ_evm I)) I key)
                    (dropDeletePosAccountMap
                      (dropPopAccountMap σ_solm I (cureSlotWord ⟨2⟩ σ_solm I)) I) := by
                simpa [dropDeletePosAccountMapFor, dropDeletePosAccountMap, hposSlotEq] using
                  accountMapEquiv_sstoreAccountMap I.codeOwner (dropPosSlotFor I) ⟨0⟩
                    haccountsPop
              have haccountsAmt :
                  accountMapEquiv
                    (dropDeleteAmtAccountMapFor
                      (dropDeletePosAccountMapFor
                        (dropPopAccountMap σ_evm I (cureSlotWord ⟨2⟩ σ_evm I)) I key) I key)
                    (dropDeleteAmtAccountMap
                      (dropDeletePosAccountMap
                        (dropPopAccountMap σ_solm I (cureSlotWord ⟨2⟩ σ_solm I)) I) I) := by
                have hamtSlotEq : dropAmtSlotFor I = solcMappingSlot ⟨6⟩ key := by
                  simpa [key] using dropAmtSlotFor_eq I
                simpa [dropDeleteAmtAccountMapFor, dropDeleteAmtAccountMap, hamtSlotEq] using
                  accountMapEquiv_sstoreAccountMap I.codeOwner (dropAmtSlotFor I) ⟨0⟩
                    haccountsPos
              have haccountsFinal :
                  accountMapEquiv
                    (dropNoSwapFinalAccountMapFor σ_evm I key
                      (cureSlotWord ⟨2⟩ σ_evm I))
                    (dropNoSwapFinalAccountMap σ_solm I (cureSlotWord ⟨2⟩ σ_solm I)) := by
                simpa [dropNoSwapFinalAccountMapFor, dropNoSwapFinalAccountMap] using haccountsAmt
              have haccounts :
                  accountMapEquiv
                    (cA, dropNoSwapFinalAccountMapFor σ_evm I key
                      (cureSlotWord ⟨2⟩ σ_evm I)).2 evmAmt.accountMap := by
                simpa [evmAmt, evmPos, evmPop, evm0, lenSolm,
                  dropAfterDeleteAmtState, dropAfterDeletePosState, dropAfterPopState,
                  dropAfterPopClearState, dropNoSwapFinalAccountMap,
                  dropPopAccountMap, dropPopClearAccountMap, dropDeletePosAccountMap,
                  dropDeleteAmtAccountMap, initState, storageStore_accountMap,
                  storageStore_executionEnv, Solm.EVM.storageLoad, State.lookupAccount,
                  cureSlotWord, solcSlotWord] using haccountsFinal
              have henc : returnEquiv ByteArray.empty none dropTransition.returnType := by
                rw [show dropTransition.returnType = [] by rfl]
                exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
              exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                hcreated haccounts henc
      · have hliveSolm : cureSlotWord ⟨1⟩ σ_solm I ≠ ⟨1⟩ := by
          intro hsolm
          exact hliveEvm (by rw [hliveWord, hsolm])
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hbody : ExecTransitionBody config contract evm0 locals dropTransition.body .reverted := by
          have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := locals)
            (by simp [locals, dropLocals]) hauthSolm
          have hguardLive := cureLiveGuardEval_false (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
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
        have hliveSolc : solcSlotWord σ_evm I ⟨1⟩ ≠ ⟨1⟩ := by
          simpa [cureSlotWord] using hliveEvm
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
    · have hauthSolm : cureSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hauthEvm (by rw [hcallerWord, hsolm])
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody : ExecTransitionBody config contract evm0 locals dropTransition.body .reverted := by
        have hguard := cureAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
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
          solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
        simpa [callerSlot, cureCallerWardsSlot, cureSlotWord] using hauthEvm
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
