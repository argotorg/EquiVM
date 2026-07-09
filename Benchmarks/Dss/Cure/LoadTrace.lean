import Benchmarks.Dss.Cure.LoadSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cure

abbrev cureStillLiveRawWord : UInt256 :=
  ⟨0x437572652f7374696c6c2d6c697665⟩

theorem RD.cureLoadStillLiveRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1348⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata (cA, σ) k C)
    (hlive : solcSlotWord σ ee ⟨1⟩ ≠ ⟨0⟩)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev cureBytecode g s0 := by
  have rdLoadPrefix := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdLoad⟩ := rdLoadPrefix.sload (by native_decide) (by evm_ov)
  have hliveRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) ≠ ⟨0⟩ := by
    simpa [solcSlotWord] using hlive
  have rdIsZero := rdLoad.iszero (by native_decide) (by evm_ov)
  have hiszero :
      UInt256.isZero
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hliveRaw
  rw [hiszero] at rdIsZero
  have rdPush := rdIsZero.push2 ⟨1419⟩ (by native_decide) (by evm_ov)
  have rdTail := rdPush.jumpiNT (by native_decide) (by rfl) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (len := ⟨15⟩)
    (rawWord := cureStillLiveRawWord)
    (shift := ⟨136⟩)
    (word := UInt256.shiftLeft cureStillLiveRawWord ⟨136⟩)
    (op := .PUSH15)
    (width := 15)
    rdTail
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    rfl
    hmem hread64
    (by simp only [List.length_cons]; omega)

theorem RD.cureLoadLiveZeroOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1348⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata (cA, σ) k C)
    (hlive : solcSlotWord σ ee ⟨1⟩ = ⟨0⟩)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨1419⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
      rdata (cA, σ) k' C' := by
  have rdLoadPrefix := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdLoad⟩ := rdLoadPrefix.sload (by native_decide) (by evm_ov)
  have hliveRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)) = ⟨0⟩ := by
    simpa [solcSlotWord] using hlive
  rw [hliveRaw] at rdLoad
  have rdIsZero := rdLoad.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdIsZero
  have rdPush := rdIsZero.push2 ⟨1419⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rdPush.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

theorem RD.cureLoadPosZeroRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1419⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
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
  have rdPush := rdLoad.push2 ⟨1520⟩ (by native_decide) (by evm_ov)
  have rdTail := rdPush.jumpiNT (by native_decide) (by rfl) (by evm_ov)
  have htailMem : (twoWordHashMem key ⟨5⟩ mem).size = 96 :=
    twoWordHashMem_size_96 key ⟨5⟩ hmem
  have htailRead64 :
      (twoWordHashMem key ⟨5⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 key ⟨5⟩ hmem hread64
  exact RD.solcErrorStringRevertTail
    (len := ⟨24⟩)
    (rawWord := ⟨0x437572652f6e6f6e2d6578697374696e672d736f75726365⟩)
    (shift := ⟨64⟩)
    (word := UInt256.shiftLeft
      (⟨0x437572652f6e6f6e2d6578697374696e672d736f75726365⟩ : UInt256) ⟨64⟩)
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

theorem RD.cureLoadPosNonzeroOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1419⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata (cA, σ) k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hpos : solcSlotWord σ ee (solcMappingSlot ⟨5⟩ key) ≠ ⟨0⟩)
    (hmem : mem.size = 96)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨1520⟩ (key :: ret :: R) (twoWordHashMem key ⟨5⟩ mem)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
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
        (fun acc => acc.storage.findD (solcMappingSlot ⟨5⟩ key) ⟨0⟩)) ≠ ⟨0⟩ := by
    simpa [solcSlotWord] using hpos
  have rdPush := rdLoad.push2 ⟨1520⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rdPush.jumpiT (by native_decide) hposRaw (by jump_dest) (by evm_ov)⟩

theorem RD.cureLoadToCureExtcodesizeGuard {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1520⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata (cA, σ) k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 16 ≤ 1024) :
    ∃ R' k' C',
      R' =
        (⟨128⟩ :: ((⟨128⟩ : UInt256).sub ⟨128⟩ + ⟨4⟩) :: ⟨128⟩ :: ⟨32⟩ ::
          ((⟨128⟩ : UInt256) + ⟨4⟩) :: ⟨2215084781⟩ :: key :: ⟨0⟩ ::
          solcSlotWord σ ee (solcMappingSlot ⟨6⟩ key) :: key :: ret :: R) ∧
      R'.length = R.length + 11 ∧
      RD cureBytecode ee g s0 ⟨1586⟩ (key :: key :: R')
      (loadCureSelectorMem (twoWordHashMem key ⟨6⟩ mem))
      (UInt256.ofNat 5) rdata (cA, σ) k' C' := by
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
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdAfterKey := rdMstoreKeyPrefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdAmtMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨6⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hAmtMem : (twoWordHashMem key ⟨6⟩ mem).size = 96 :=
    twoWordHashMem_size_96 key ⟨6⟩ hmem
  have hAmtRead64 :
      (twoWordHashMem key ⟨6⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 key ⟨6⟩ hmem hread64
  have hAmtSlot := twoWordHashMem_solcMappingSlot ⟨6⟩ key hmem
  have rdKeccakPrefix := evm_run rdAmtMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdAmtSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨6⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost hAmtSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdAmtLoadRaw⟩ := rdAmtSlot.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdAmtLoad⟩ : ∃ k' C', RD cureBytecode ee g s0 ⟨1549⟩
      (solcSlotWord σ ee (solcMappingSlot ⟨6⟩ key) :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ ::
        key :: key :: ret :: R)
      (twoWordHashMem key ⟨6⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [solcSlotWord] using rdAmtLoadRaw⟩
  have hmload64Amt :
      (if (⟨64⟩ : UInt256).toNat ≥ (twoWordHashMem key ⟨6⟩ mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((twoWordHashMem key ⟨6⟩ mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hAmtMem]; decide) (by decide) hAmtRead64
  have rdSelectorPrefix := evm_run rdAmtLoad with [
    raw dup2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64Amt (by native_decide) (by evm_ov),
    raw push4 ⟨2215084781⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have hselectorShift :
      UInt256.shiftLeft (⟨2215084781⟩ : UInt256) ⟨224⟩ = sourceCureSelectorShifted := by
    rfl
  rw [hselectorShift] at rdSelectorPrefix
  have rdSelectorMem := rdSelectorPrefix.mstore 6
    (loadCureSelectorMem (twoWordHashMem key ⟨6⟩ mem))
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hSelMem : (loadCureSelectorMem (twoWordHashMem key ⟨6⟩ mem)).size = 160 :=
    loadCureSelectorMem_size_of_size96 hAmtMem
  have hSelRead64 :
      (loadCureSelectorMem (twoWordHashMem key ⟨6⟩ mem)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    loadCureSelectorMem_read64_of_size96 hAmtMem hAmtRead64
  have hmload64Sel :
      (if (⟨64⟩ : UInt256).toNat ≥
            (loadCureSelectorMem (twoWordHashMem key ⟨6⟩ mem)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((loadCureSelectorMem (twoWordHashMem key ⟨6⟩ mem)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hSelMem]; decide) (by decide) hSelRead64
  have rd1586 := evm_run rdSelectorMem with [
    raw swap2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64Sel (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 ⟨2215084781⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  let Rext : List UInt256 :=
    ⟨128⟩ :: ((⟨128⟩ : UInt256).sub ⟨128⟩ + ⟨4⟩) :: ⟨128⟩ :: ⟨32⟩ ::
      ((⟨128⟩ : UInt256) + ⟨4⟩) :: ⟨2215084781⟩ :: key :: ⟨0⟩ ::
      solcSlotWord σ ee (solcMappingSlot ⟨6⟩ key) :: key :: ret :: R
  exact ⟨Rext, _, _, rfl, by simp [Rext], by simpa [Rext] using rd1586⟩

theorem RD.cureLoadNoCodeRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1520⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata (cA, σ) k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hnoCode : uniswapExtCodeSizeWord σ key = ⟨0⟩)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 16 ≤ 1024) :
    RDrev cureBytecode g s0 := by
  obtain ⟨Rext, _, _, _hRext, hRextLen, rd1586⟩ :=
    RD.cureLoadToCureExtcodesizeGuard h hcanonKey hmem hread64 hov
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨1586⟩) (okPc := ⟨1598⟩) rd1586
    hnoCode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by rw [hRextLen]; omega)

theorem RD.cureLoadStaticcallSetup {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1520⟩ (key :: ret :: R) mem (UInt256.ofNat 3)
        rdata (cA, σ) k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hcodeSize : uniswapExtCodeSizeWord σ key ≠ ⟨0⟩)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 16 ≤ 1024) :
    ∃ gasWord k' C', RD cureBytecode ee g s0 ⟨1601⟩
      (gasWord :: key :: ⟨128⟩ :: ((⟨128⟩ : UInt256).sub ⟨128⟩ + ⟨4⟩) ::
        ⟨128⟩ :: ⟨32⟩ :: ((⟨128⟩ : UInt256) + ⟨4⟩) :: ⟨2215084781⟩ ::
        key :: ⟨0⟩ :: solcSlotWord σ ee (solcMappingSlot ⟨6⟩ key) ::
        key :: ret :: R)
      (loadCureSelectorMem (twoWordHashMem key ⟨6⟩ mem))
      (UInt256.ofNat 5) rdata (cA, σ) k' C' := by
  obtain ⟨Rext, _, _, hRext, hRextLen, rd1586⟩ :=
    RD.cureLoadToCureExtcodesizeGuard h hcanonKey hmem hread64 hov
  obtain ⟨gasWord, k1601, C1601, rd1601⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨1586⟩) (okPc := ⟨1598⟩) rd1586
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by rw [hRextLen]; omega)
  exact ⟨gasWord, k1601, C1601, by simpa [hRext] using rd1601⟩

theorem RD.cureLoadStaticcall
    {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {cA_call : Batteries.RBSet AccountAddress compare}
    {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (h : RD cureBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1520⟩
        (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA_call, σCall) k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hcodeSize : uniswapExtCodeSizeWord σCall key ≠ ⟨0⟩)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 16 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD cureBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1602⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ((⟨128⟩ : UInt256) + ⟨4⟩) ::
          ⟨2215084781⟩ :: key :: ⟨0⟩ ::
          solcSlotWord σCall I (solcMappingSlot ⟨6⟩ key) :: key :: ret :: R)
        (out.write 0 (loadCureSelectorMem (twoWordHashMem key ⟨6⟩ mem)) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 5) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σCall
          createdAccounts := cA_call }
        (EVM.address (AccountAddress.ofUInt256 key)) "cure" 0 []
        (z,
          { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ'
            substate := A'
            createdAccounts := cA' },
          out) false
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1601⟩ :=
    RD.cureLoadStaticcallSetup h hcanonKey hcodeSize hmem hread64 hov
  obtain ⟨cA', σ', z, out, A_in, callGas, k1602, C1602, hΘpack,
      rd1602raw, houtsz⟩ :=
    RD.uniswapStaticcall rd1601 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  let evmIn := { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
    accountMap := σCall
    createdAccounts := cA_call }
  refine ⟨cA', σ', z, out, A', k1602, C1602, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
          (⟨128⟩ : UInt256).toNat
          (((⟨128⟩ : UInt256).sub ⟨128⟩ + ⟨4⟩).toNat))
          (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 5 := by
      native_decide
    exact haw ▸ rd1602raw
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := key)
      (mem := loadCureSelectorMem (twoWordHashMem key ⟨6⟩ mem))
      (inOff := ⟨128⟩) (inSize := ((⟨128⟩ : UInt256).sub ⟨128⟩ + ⟨4⟩))
      (by
        intro hEq
        have hDepth : I.depth = (1024 : Fin 1025) := by
          simpa [evmIn, initState] using hEq
        exact absurd hdepth (by rw [hDepth]; decide))
      (by
        apply Fin.ext
        change (AccountAddress.ofUInt256 key).val % EVM.twoPow 160 =
          (AccountAddress.ofUInt256 key).val
        exact Nat.mod_eq_of_lt (AccountAddress.ofUInt256 key).isLt)
      (by
        have hAmtMem : (twoWordHashMem key ⟨6⟩ mem).size = 96 :=
          twoWordHashMem_size_96 key ⟨6⟩ hmem
        simpa using loadCureEncode_eq hAmtMem)
      ?_
    simpa [evmIn, initState] using hΘ

theorem RD.cureLoadStaticcallDepthLimit
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {key ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {k C : ℕ}
    (h : RD cureBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1520⟩
        (key :: ret :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hcodeSize : uniswapExtCodeSizeWord σ key ≠ ⟨0⟩)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hdepth : I.depth = 1024)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD cureBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1602⟩
      (⟨0⟩ :: ((⟨128⟩ : UInt256) + ⟨4⟩) ::
        ⟨2215084781⟩ :: key :: ⟨0⟩ ::
        solcSlotWord σ I (solcMappingSlot ⟨6⟩ key) :: key :: ret :: R)
      (ByteArray.empty.write 0 (loadCureSelectorMem (twoWordHashMem key ⟨6⟩ mem)) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 5) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, _, rd1601⟩ :=
    RD.cureLoadStaticcallSetup h hcanonKey hcodeSize hmem hread64 hov
  obtain ⟨k1602, C1602, rd1602raw⟩ :=
    RD.uniswapStaticcallDepthLimit rd1601 (by native_decide) hdepth (by evm_ov)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
        (⟨128⟩ : UInt256).toNat
        (((⟨128⟩ : UInt256).sub ⟨128⟩ + ⟨4⟩).toNat))
        (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 5 := by
    native_decide
  exact ⟨k1602, C1602, haw ▸ rd1602raw⟩

theorem RD.cureLoadCallFailure {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD cureBytecode ee g s0 ⟨1602⟩ (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev cureBytecode g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨1602⟩) (okPc := ⟨1618⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hosz hov

theorem RD.cureLoadCallSuccessToReturnDecode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 d3 d4 d5 d6 : UInt256} {R : List UInt256}
    (rd : RD cureBytecode ee g s0 ⟨1602⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: R) mem aw o acc k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨1623⟩
      (d3 :: d4 :: d5 :: d6 :: R) mem aw o acc k' C' := by
  obtain ⟨_, _, rd1620⟩ :=
    RD.uniswapCallSuccessGuardOk (pc := ⟨1602⟩) (okPc := ⟨1618⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)
  have rd1623 := evm_run rd1620 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd1623⟩

theorem RD.cureLoadReturnDecodeShortReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {R : List UInt256}
    (rd : RD cureBytecode ee g s0 ⟨1623⟩ R mem (UInt256.ofNat 5) o acc k C)
    (hshort : o.size < 32)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hov : R.length + 4 ≤ 1024) :
    RDrev cureBytecode g s0 := by
  have rdPush64 := RD.push1 rd ⟨64⟩ (by native_decide) (by omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 5) rdPush64 (by native_decide)
    mem_cost hMload64Value (by decide) (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' o.size hhi]
    exact hshort
  have rdIszero := RD.iszero rdLt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨1640⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk (by native_decide) hcond
    (by simp only [List.length_cons]; omega)
  exact RD.uniswapPush1Dup1Revert0 rdFallthrough
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)

theorem RD.cureLoadReturnDecodeOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {retWord : UInt256} {R : List UInt256}
    (rd : RD cureBytecode ee g s0 ⟨1623⟩ R mem (UInt256.ofNat 5) o acc k C)
    (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨1643⟩
      (retWord :: R) mem (UInt256.ofNat 5) o acc k' C' := by
  have rdPush64 := RD.push1 rd ⟨64⟩ (by native_decide) (by omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 5) rdPush64 (by native_decide)
    mem_cost hMload64Value (by decide) (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' o.size hhi]
    exact hlo
  have rdIszero := RD.iszero rdLt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨1640⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rdJumpi := RD.jumpiT rdPushOk (by native_decide) hcond (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPopLen := RD.pop rdJumpdest (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdMload128 := RD.mload 0 retWord (UInt256.ofNat 5) rdPopLen (by native_decide)
    mem_cost hMload128Value (by decide) (by omega)
  exact ⟨_, _, rdMload128⟩

theorem RD.cureLoadStoreAmt {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret newAmt oldAmt : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1643⟩
      (newAmt :: ⟨0⟩ :: oldAmt :: key :: ret :: R) mem (UInt256.ofNat 5)
      rdata (cA, σ) k C)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hmem : mem.size = 160)
    (hperm : ee.perm = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨1670⟩
      (newAmt :: ⟨0⟩ :: oldAmt :: key :: ret :: R)
      (twoWordHashMem key ⟨6⟩ mem) (UInt256.ofNat 5) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨6⟩ key) newAmt) k' C' := by
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
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmaskLiteral'] at rdMasked
  have rdMstoreKeyPrefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdAfterKey := rdMstoreKeyPrefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨6⟩ mem)
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot_160 ⟨6⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨6⟩ key)
    (UInt256.ofNat 5) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rdStorePrefix := evm_run rdSlot with [
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdStore⟩ := rdStorePrefix.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa using rdStore⟩

theorem RD.cureLoadToSubRoutine {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret newAmt oldAmt : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1670⟩
      (newAmt :: ⟨0⟩ :: oldAmt :: key :: ret :: R) mem (UInt256.ofNat 5)
      rdata (cA, σ) k C)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ⟨3666⟩
      (oldAmt :: solcSlotWord σ ee ⟨9⟩ :: ⟨1689⟩ :: ⟨1695⟩ ::
        newAmt :: oldAmt :: key :: ret :: R)
      mem (UInt256.ofNat 5) rdata (cA, σ) k' C' := by
  have rdPush := evm_run h with [
    raw push1 ⟨9⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdLoad₀⟩ := rdPush.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hsayRaw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨9⟩ ⟨0⟩)) = solcSlotWord σ ee ⟨9⟩ := by
    rfl
  have rdLoad := rdLoad₀
  rw [hsayRaw] at rdLoad
  have rdSetup := evm_run rdLoad with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push2 ⟨1695⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨1689⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push2 ⟨3666⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rdSetup.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.cureLoadSubUnderflowRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret newAmt oldAmt sayAfter : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cureBytecode ee g s0 ⟨3666⟩
      (oldAmt :: sayAfter :: ⟨1689⟩ :: ⟨1695⟩ :: newAmt :: oldAmt :: key :: ret :: R)
      mem (UInt256.ofNat 5) rdata acc k C)
    (hlt : sayAfter.toNat < oldAmt.toNat)
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 15 ≤ 1024) :
    RDrev cureBytecode g s0 := by
  have hsubNat : (UInt256.sub sayAfter oldAmt).toNat =
      UInt256.size + sayAfter.toNat - oldAmt.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub sayAfter oldAmt) sayAfter = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub sayAfter oldAmt > sayAfter)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub sayAfter oldAmt).toNat > sayAfter.toNat
      rw [hsubNat]
      have hb : oldAmt.toNat < UInt256.size := oldAmt.val.isLt
      omega
  have rd6 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw gt (by native_decide) (by evm_ov)]
  have rd7 := rd7₀
  rw [hgt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero (by native_decide) (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 ⟨3743⟩ (by native_decide) (by evm_ov)]
  have rdTail := rdPush.jumpiNT (by native_decide) (by decide)
    (by simp only [List.length_cons]; omega)
  have rdMload := evm_run rdTail with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨18⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨18⟩ mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst
    (⟨5876488251733609336472438655059826653818743⟩ : UInt256)
    (width := 18) (op := .PUSH18) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 ⟨112⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov)]
  rw [show UInt256.shiftLeft
      (⟨5876488251733609336472438655059826653818743⟩ : UInt256) ⟨112⟩ =
        UInt256.shiftLeft
          (⟨5876488251733609336472438655059826653818743⟩ : UInt256) ⟨112⟩ from rfl] at rdWord
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨18⟩
      (UInt256.shiftLeft
        (⟨5876488251733609336472438655059826653818743⟩ : UInt256) ⟨112⟩) mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64_of_size160 ⟨18⟩
        (UInt256.shiftLeft
          (⟨5876488251733609336472438655059826653818743⟩ : UInt256) ⟨112⟩)
        hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem RD.cureLoadAddOverflowRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret newAmt oldAmt withoutOld : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1689⟩
      (withoutOld :: ⟨1695⟩ :: newAmt :: oldAmt :: key :: ret :: R)
      mem (UInt256.ofNat 5) rdata acc k C)
    (hover : UInt256.size ≤ withoutOld.toNat + newAmt.toNat)
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 13 ≤ 1024) :
    RDrev cureBytecode g s0 := by
  have hsum_lt2 : withoutOld.toNat + newAmt.toNat < 2 * UInt256.size := by
    have ha : withoutOld.toNat < UInt256.size := withoutOld.val.isLt
    have hb : newAmt.toNat < UInt256.size := newAmt.val.isLt
    omega
  have hmod : (withoutOld.toNat + newAmt.toNat) % UInt256.size =
      withoutOld.toNat + newAmt.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (withoutOld + newAmt).toNat =
      withoutOld.toNat + newAmt.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (withoutOld + newAmt) withoutOld = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hb : newAmt.toNat < UInt256.size := newAmt.val.isLt
    omega
  have rdToAdd := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨3749⟩ (by native_decide) (by evm_ov)]
  have rdAdd := rdToAdd.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd6 := evm_run rdAdd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw lt (by native_decide) (by evm_ov)]
  have rd7 := rd7₀
  rw [hlt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero (by native_decide) (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 ⟨3743⟩ (by native_decide) (by evm_ov)]
  have rdTail := rdPush.jumpiNT (by native_decide) (by decide)
    (by simp only [List.length_cons]; omega)
  have rdMload := evm_run rdTail with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨17⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨17⟩ mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst
    (⟨22955032233328820198124048709524453617527⟩ : UInt256)
    (width := 17) (op := .PUSH17) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 ⟨120⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov)]
  rw [show UInt256.shiftLeft
      (⟨22955032233328820198124048709524453617527⟩ : UInt256) ⟨120⟩ =
        UInt256.shiftLeft
          (⟨22955032233328820198124048709524453617527⟩ : UInt256) ⟨120⟩ from rfl] at rdWord
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨17⟩
      (UInt256.shiftLeft
        (⟨22955032233328820198124048709524453617527⟩ : UInt256) ⟨120⟩) mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64_of_size160 ⟨17⟩
        (UInt256.shiftLeft
          (⟨22955032233328820198124048709524453617527⟩ : UInt256) ⟨120⟩)
        hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

abbrev cureLoadEventTopic : UInt256 :=
  ⟨105413615632296640974445119365252681616567580897637397457672069491752444217536⟩

theorem RD.cureLoadEventReturn {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret newAmt oldAmt : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1767⟩ (newAmt :: oldAmt :: key :: ret :: R)
      mem (UInt256.ofNat 5) rdata acc k C)
    (hret : (D_J cureBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ret R mem (UInt256.ofNat 5) rdata acc k' C' := by
  have hmask :
      UInt256.land key
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        key := by
    rw [u256_land_comm key
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hcanonKey
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have rdMload := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmask] at rdMload
  have rdTopic := evm_run rdMload with [
    raw swap1 (by native_decide) (by evm_ov)]
  have rdTopicConst := rdTopic.pushConst cureLoadEventTopic
    (op := .PUSH32) (width := 32) (by decide) (by native_decide) (by evm_ov)
  have rdLogPrefix := evm_run rdTopicConst with [
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdLogged := RD.cureLog2 0 (UInt256.ofNat 5) rdLogPrefix
    (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop := evm_run rdLogged with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, rdPop.jump (by native_decide) hret (by evm_ov)⟩

theorem RD.cureLoadSuccessLoadedNonzero {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret newAmt oldAmt sayNew : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1695⟩
      (sayNew :: newAmt :: oldAmt :: key :: ret :: R)
      mem (UInt256.ofNat 5) rdata (cA, σ) k C)
    (hret : (D_J cureBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hloaded :
      solcSlotWord (sstoreAccountMap ee.codeOwner σ ⟨9⟩ sayNew) ee
        (solcMappingSlot ⟨7⟩ key) ≠ ⟨0⟩)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD cureBytecode ee g s0 ret R (twoWordHashMem key ⟨7⟩ mem)
      (UInt256.ofNat 5) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨9⟩ sayNew) k' C' := by
  let σSay := sstoreAccountMap ee.codeOwner σ ⟨9⟩ sayNew
  have hmask :
      UInt256.land key
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        key := by
    rw [u256_land_comm key
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hcanonKey
  have rdStorePrefix := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨9⟩ (by native_decide) (by evm_ov)]
  obtain ⟨kSay, CSay, rdAfterSayRaw⟩ := rdStorePrefix.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdAfterSay : RD cureBytecode ee g s0 ⟨1699⟩
      (newAmt :: oldAmt :: key :: ret :: R) mem (UInt256.ofNat 5) rdata
      (cA, σSay) kSay CSay := by
    simpa [σSay] using rdAfterSayRaw
  have rdMasked := evm_run rdAfterSay with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmask] at rdMasked
  have rdMstoreKeyPrefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdAfterKey := rdMstoreKeyPrefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨7⟩ mem)
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot_160 ⟨7⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨7⟩ key)
    (UInt256.ofNat 5) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨kLoad, CLoad, rdLoadRaw⟩ := rdSlot.sload (by native_decide) (by evm_ov)
  have rdLoad : RD cureBytecode ee g s0 ⟨1724⟩
      (solcSlotWord σSay ee (solcMappingSlot ⟨7⟩ key) :: newAmt :: oldAmt :: key :: ret :: R)
      (twoWordHashMem key ⟨7⟩ mem) (UInt256.ofNat 5) rdata (cA, σSay) kLoad CLoad := by
    simpa [solcSlotWord] using rdLoadRaw
  have rdPush := rdLoad.push2 ⟨1767⟩ (by native_decide) (by evm_ov)
  have rd1767 := rdPush.jumpiT (by native_decide)
    (by simpa [σSay] using hloaded) (by jump_dest) (by evm_ov)
  have hmemHash : (twoWordHashMem key ⟨7⟩ mem).size = 160 :=
    twoWordHashMem_size_160 key ⟨7⟩ hmem
  have hreadHash :
      (twoWordHashMem key ⟨7⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64_160 key ⟨7⟩ hmem hread64
  exact RD.cureLoadEventReturn rd1767 hret hperm hmemHash hreadHash hcanonKey
    (by omega)

theorem RD.cureLoadSuccessLoadedZero {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret newAmt oldAmt sayNew : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD cureBytecode ee g s0 ⟨1695⟩
      (sayNew :: newAmt :: oldAmt :: key :: ret :: R)
      mem (UInt256.ofNat 5) rdata (cA, σ) k C)
    (hret : (D_J cureBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcanonKey : key.toNat < EVM.addressModulus)
    (hloaded :
      solcSlotWord (sstoreAccountMap ee.codeOwner σ ⟨9⟩ sayNew) ee
        (solcMappingSlot ⟨7⟩ key) = ⟨0⟩)
    (hov : R.length + 13 ≤ 1024) :
    let σSay := sstoreAccountMap ee.codeOwner σ ⟨9⟩ sayNew
    let loadedSlot := solcMappingSlot ⟨7⟩ key
    let σLoaded := sstoreAccountMap ee.codeOwner σSay loadedSlot ⟨1⟩
    let σCount := sstoreAccountMap ee.codeOwner σLoaded ⟨8⟩ (solcSlotWord σLoaded ee ⟨8⟩ + ⟨1⟩)
    ∃ k' C', RD cureBytecode ee g s0 ret R
      (twoWordHashMem key ⟨7⟩ (twoWordHashMem key ⟨7⟩ mem))
      (UInt256.ofNat 5) rdata (cA, σCount) k' C' := by
  intro σSay loadedSlot σLoaded σCount
  have hmask :
      UInt256.land key
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        key := by
    rw [u256_land_comm key
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)]
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hcanonKey
  have rdStorePrefix := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨9⟩ (by native_decide) (by evm_ov)]
  obtain ⟨kSay, CSay, rdAfterSayRaw⟩ := rdStorePrefix.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdAfterSay : RD cureBytecode ee g s0 ⟨1699⟩
      (newAmt :: oldAmt :: key :: ret :: R) mem (UInt256.ofNat 5) rdata
      (cA, σSay) kSay CSay := by
    simpa [σSay] using rdAfterSayRaw
  have rdMasked := evm_run rdAfterSay with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmask] at rdMasked
  have rdMstoreKeyPrefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdAfterKey := rdMstoreKeyPrefix.mstore 0 (wordAt0Mem key mem)
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem key ⟨7⟩ mem)
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hslot := twoWordHashMem_solcMappingSlot_160 ⟨7⟩ key hmem
  have rdSlot := rdKeccakPrefix.keccak256 0 loadedSlot
    (UInt256.ofNat 5) (by native_decide) mem_cost (by simpa [loadedSlot] using hslot)
    (by native_decide) (by evm_ov)
  obtain ⟨kLoad, CLoad, rdLoadRaw⟩ := rdSlot.sload (by native_decide) (by evm_ov)
  have rdLoad : RD cureBytecode ee g s0 ⟨1724⟩
      (solcSlotWord σSay ee loadedSlot :: newAmt :: oldAmt :: key :: ret :: R)
      (twoWordHashMem key ⟨7⟩ mem) (UInt256.ofNat 5) rdata (cA, σSay) kLoad CLoad := by
    simpa [loadedSlot, solcSlotWord] using rdLoadRaw
  have rdPush := rdLoad.push2 ⟨1767⟩ (by native_decide) (by evm_ov)
  have rd1728 := rdPush.jumpiNT (by native_decide)
    (by simpa [σSay, loadedSlot] using hloaded)
    (by simp only [List.length_cons]; omega)
  have rdMasked2 := evm_run rd1728 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmask] at rdMasked2
  have rdMstoreKeyPrefix2 := evm_run rdMasked2 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdAfterKey2 := rdMstoreKeyPrefix2.mstore 0 (wordAt0Mem key (twoWordHashMem key ⟨7⟩ mem))
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix2 := evm_run rdAfterKey2 with [
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdHashMem2 := rdMstoreSlotPrefix2.mstore 0
    (twoWordHashMem key ⟨7⟩ (twoWordHashMem key ⟨7⟩ mem))
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix2 := evm_run rdHashMem2 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hmemHash : (twoWordHashMem key ⟨7⟩ mem).size = 160 :=
    twoWordHashMem_size_160 key ⟨7⟩ hmem
  have hslot2 := twoWordHashMem_solcMappingSlot_160 ⟨7⟩ key hmemHash
  have rdSlot2 := rdKeccakPrefix2.keccak256 0 loadedSlot
    (UInt256.ofNat 5) (by native_decide) mem_cost (by simpa [loadedSlot] using hslot2)
    (by native_decide) (by evm_ov)
  have rdStoreLoadedReady := evm_run rdSlot2 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨kLoaded, CLoaded, rdAfterLoadedRaw⟩ :=
    rdStoreLoadedReady.sstore hperm (by native_decide) (by simp only [List.length_cons]; omega)
  have rdAfterLoaded : RD cureBytecode ee g s0 ⟨1758⟩
      (⟨1⟩ :: newAmt :: oldAmt :: key :: ret :: R)
      (twoWordHashMem key ⟨7⟩ (twoWordHashMem key ⟨7⟩ mem)) (UInt256.ofNat 5) rdata
      (cA, σLoaded) kLoaded CLoaded := by
    simpa [σLoaded, loadedSlot] using rdAfterLoadedRaw
  have rdLCountPrefix := evm_run rdAfterLoaded with [
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨kLCount, CLCount, rdLCountRaw⟩ := rdLCountPrefix.sload
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rdLCount : RD cureBytecode ee g s0 ⟨1762⟩
      (solcSlotWord σLoaded ee ⟨8⟩ :: ⟨8⟩ :: ⟨1⟩ :: newAmt :: oldAmt :: key :: ret :: R)
      (twoWordHashMem key ⟨7⟩ (twoWordHashMem key ⟨7⟩ mem)) (UInt256.ofNat 5) rdata
      (cA, σLoaded) kLCount CLCount := by
    simpa [solcSlotWord] using rdLCountRaw
  have rdCountStoreReady := evm_run rdLCount with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨kCount, CCount, rdAfterCountRaw⟩ :=
    rdCountStoreReady.sstore hperm (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1767 : RD cureBytecode ee g s0 ⟨1767⟩
      (newAmt :: oldAmt :: key :: ret :: R)
      (twoWordHashMem key ⟨7⟩ (twoWordHashMem key ⟨7⟩ mem)) (UInt256.ofNat 5) rdata
      (cA, σCount) kCount CCount := by
    simpa [σCount, u256_add_comm] using rdAfterCountRaw
  have hmemHash2 :
      (twoWordHashMem key ⟨7⟩ (twoWordHashMem key ⟨7⟩ mem)).size = 160 :=
    twoWordHashMem_size_160 key ⟨7⟩ hmemHash
  have hreadHash :
      (twoWordHashMem key ⟨7⟩ (twoWordHashMem key ⟨7⟩ mem)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64_160 key ⟨7⟩ hmemHash
      (twoWordHashMem_read64_160 key ⟨7⟩ hmem hread64)
  exact RD.cureLoadEventReturn rd1767 hret hperm hmemHash2 hreadHash hcanonKey
    (by omega)


end Benchmarks.Dss.Cure
