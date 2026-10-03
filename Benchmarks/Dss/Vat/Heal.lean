import Benchmarks.Dss.Vat.HealBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vat

attribute [local irreducible] Ethereum.KEC

theorem RD.vatHealSinSubUnderflow
    {σ σ₀ A I} {g sel rad : UInt256} {k C : ℕ}
    (rd : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6423⟩
      [rad, ⟨524⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      σ k C)
    (hlt : (vatSlotWord (healSinSlot I) σ I).toNat < rad.toNat) :
    RDrev vatBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hslotEq :
      solcSlotWord σ I (solcMappingSlot ⟨6⟩ (healSourceWord I)) =
        vatSlotWord (healSinSlot I) σ I := by
    simp [vatSlotWord, healSinSlot_eq_mapSlot I]
  have rd6429pre := evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6430 := rd6429pre.mstore 0 (wordAt0Mem (healSourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6434pre := evm_run rd6430 with [
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd6435 := rd6434pre.mstore 0 (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6438pre := evm_run rd6435 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem).readWithPadding 0 64))) =
        solcMappingSlot ⟨6⟩ (healSourceWord I) :=
    twoWordHashMem_solcMappingSlot ⟨6⟩ (healSourceWord I) solcFreePtrMem_size
  have rd6439 := rd6438pre.keccak256 0 (solcMappingSlot ⟨6⟩ (healSourceWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨k6440, C6440, rd6440raw⟩ := rd6439.sload (by native_decide) (by evm_ov)
  have rd6440 : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6440⟩
      (vatSlotWord (healSinSlot I) σ I :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty σ k6440 C6440 := by
    simpa [hslotEq, solcSlotWord, healSourceWord] using rd6440raw
  have rd6621pre := evm_run rd6440 with [
    raw push2 ⟨6449⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨6621⟩ (by native_decide) (by evm_ov)]
  have rd6621 := rd6621pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubEmptyRevertAnyWords
    (code := vatBytecode) (pc := ⟨6621⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord (healSinSlot I) σ I) (b := rad) (ret := ⟨6449⟩)
    (R := [healSourceWord I, rad, ⟨524⟩, sel])
    (by simpa using rd6621)
    (by
      unfold solcCheckedSubEmptyRevertWf solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    hlt
    (by simp)

theorem RD.vatHealSinSubSuccess
    {σ σ₀ A I} {g sel rad : UInt256} {k C : ℕ}
    (rd : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6423⟩
      [rad, ⟨524⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      σ k C)
    (hle : rad.toNat ≤ (vatSlotWord (healSinSlot I) σ I).toNat) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6449⟩
      (UInt256.sub (vatSlotWord (healSinSlot I) σ I) rad ::
        healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty σ k' C' := by
  have hslotEq :
      solcSlotWord σ I (solcMappingSlot ⟨6⟩ (healSourceWord I)) =
        vatSlotWord (healSinSlot I) σ I := by
    simp [vatSlotWord, healSinSlot_eq_mapSlot I]
  have rd6429pre := evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6430 := rd6429pre.mstore 0 (wordAt0Mem (healSourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6434pre := evm_run rd6430 with [
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd6435 := rd6434pre.mstore 0 (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6438pre := evm_run rd6435 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem).readWithPadding 0 64))) =
        solcMappingSlot ⟨6⟩ (healSourceWord I) :=
    twoWordHashMem_solcMappingSlot ⟨6⟩ (healSourceWord I) solcFreePtrMem_size
  have rd6439 := rd6438pre.keccak256 0 (solcMappingSlot ⟨6⟩ (healSourceWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨k6440, C6440, rd6440raw⟩ := rd6439.sload (by native_decide) (by evm_ov)
  have rd6440 : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6440⟩
      (vatSlotWord (healSinSlot I) σ I :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty σ k6440 C6440 := by
    simpa [hslotEq, solcSlotWord, healSourceWord] using rd6440raw
  have rd6621pre := evm_run rd6440 with [
    raw push2 ⟨6449⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨6621⟩ (by native_decide) (by evm_ov)]
  have rd6621 := rd6621pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubSuccess
    (code := vatBytecode) (pc := ⟨6621⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord (healSinSlot I) σ I) (b := rad) (ret := ⟨6449⟩)
    (R := [healSourceWord I, rad, ⟨524⟩, sel])
    (by simpa using rd6621)
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    hle (by jump_dest) (by jump_dest) (by simp)

theorem RD.vatHealDaiLoaded
    {σ σ₀ A I} {g sel rad sinNew : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (rd : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6449⟩
      (sinNew :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty σ k C) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6487⟩
      (vatSlotWord (healDaiSlot I)
          (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) I ::
        healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (wordAt32Mem ⟨5⟩
        (twoWordHashMem (healSourceWord I) ⟨6⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) k' C' := by
  have hcanonSource : (healSourceWord I).toNat < EVM.addressModulus := by
    rw [healSourceWord_toNat]
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using I.source.isLt
  have hmask :
      UInt256.land (healSourceWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        healSourceWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean hcanonSource
  have hsinSlot :
      solcMappingSlot ⟨6⟩ (healSourceWord I) = healSinSlot I := by
    rw [healSinSlot_eq_mapSlot]
  let σSin := sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew
  have hdaiSlotEq :
      solcSlotWord σSin I (solcMappingSlot ⟨5⟩ (healSourceWord I)) =
        vatSlotWord (healDaiSlot I) σSin I := by
    simp [vatSlotWord, healDaiSlot_eq_mapSlot I]
  have rd6459pre := evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd6460₀ := evm_run rd6459pre with [raw and (by native_decide) (by evm_ov)]
  have rd6460 := rd6460₀
  rw [hmask] at rd6460
  have rd6464pre := evm_run rd6460 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6465 := rd6464pre.mstore 0
    (wordAt0Mem (healSourceWord I)
      (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6471pre := evm_run rd6465 with [
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6472 := rd6471pre.mstore 0
    (twoWordHashMem (healSourceWord I) ⟨6⟩
      (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hsinHash :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC (((twoWordHashMem (healSourceWord I) ⟨6⟩
            (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))).readWithPadding 0 64))) =
        solcMappingSlot ⟨6⟩ (healSourceWord I) := by
    exact twoWordHashMem_solcMappingSlot ⟨6⟩ (healSourceWord I)
      (twoWordHashMem_size_96 (healSourceWord I) ⟨6⟩ solcFreePtrMem_size)
  have rd6476pre := evm_run rd6472 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rd6477 := rd6476pre.keccak256 0 (solcMappingSlot ⟨6⟩ (healSourceWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost hsinHash (by native_decide) (by evm_ov)
  have rd6480pre := evm_run rd6477 with [
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov)]
  obtain ⟨k6481, C6481, rd6481raw⟩ := rd6480pre.sstore hperm (by native_decide) (by evm_ov)
  have rd6481 : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6481⟩
      (⟨32⟩ :: ⟨0⟩ :: ⟨64⟩ :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨6⟩
        (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty σSin k6481 C6481 := by
    simpa [σSin, hsinSlot] using rd6481raw
  have rd6484pre := evm_run rd6481 with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  let daiMem := wordAt32Mem ⟨5⟩
    (twoWordHashMem (healSourceWord I) ⟨6⟩
      (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))
  have rd6485 := rd6484pre.mstore 0 daiMem
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hdaiMemSize :
      (twoWordHashMem (healSourceWord I) ⟨6⟩
        (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem)).size = 96 :=
    twoWordHashMem_size_96 (healSourceWord I) ⟨6⟩
      (twoWordHashMem_size_96 (healSourceWord I) ⟨6⟩ solcFreePtrMem_size)
  have hdaiRead0 :
      (twoWordHashMem (healSourceWord I) ⟨6⟩
        (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem)).readWithPadding 0 32 =
        UInt256.toByteArray (healSourceWord I) :=
    twoWordHashMem_read0 (healSourceWord I) ⟨6⟩
      (twoWordHashMem_size_96 (healSourceWord I) ⟨6⟩ solcFreePtrMem_size)
  have hdaiHash :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC (daiMem.readWithPadding 0 64))) =
        solcMappingSlot ⟨5⟩ (healSourceWord I) := by
    exact wordAt32Mem_solcMappingSlot_of_read0 (healSourceWord I) ⟨5⟩ hdaiMemSize hdaiRead0
  have rd6486 := rd6485.keccak256 0 (solcMappingSlot ⟨5⟩ (healSourceWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost hdaiHash (by native_decide) (by evm_ov)
  obtain ⟨k6487, C6487, rd6487raw⟩ := rd6486.sload (by native_decide) (by evm_ov)
  have rd6487 : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6487⟩
      (vatSlotWord (healDaiSlot I) σSin I :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      daiMem (UInt256.ofNat 3) ByteArray.empty σSin k6487 C6487 := by
    simpa [hdaiSlotEq, solcSlotWord, daiMem] using rd6487raw
  exact ⟨_, _, by simpa [σSin, daiMem] using rd6487⟩

theorem RD.vatHealDaiSubUnderflow
    {σ σ₀ A I} {g sel rad sinNew : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (rd : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6449⟩
      (sinNew :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty σ k C)
    (hlt : (vatSlotWord (healDaiSlot I)
        (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) I).toNat < rad.toNat) :
    RDrev vatBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd6487⟩ := RD.vatHealDaiLoaded hperm rd
  have rd6621pre := evm_run rd6487 with [
    raw push2 ⟨6496⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨6621⟩ (by native_decide) (by evm_ov)]
  have rd6621 := rd6621pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubEmptyRevertAnyWords
    (code := vatBytecode) (pc := ⟨6621⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord (healDaiSlot I)
        (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) I)
    (b := rad) (ret := ⟨6496⟩)
    (R := [healSourceWord I, rad, ⟨524⟩, sel])
    (by simpa using rd6621)
    (by
      unfold solcCheckedSubEmptyRevertWf solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    hlt
    (by simp)

theorem RD.vatHealDaiSubSuccess
    {σ σ₀ A I} {g sel rad sinNew : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (rd : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6449⟩
      (sinNew :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty σ k C)
    (hle : rad.toNat ≤
      (vatSlotWord (healDaiSlot I)
        (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) I).toNat) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6496⟩
      (UInt256.sub
          (vatSlotWord (healDaiSlot I)
            (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) I) rad ::
        healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (wordAt32Mem ⟨5⟩
        (twoWordHashMem (healSourceWord I) ⟨6⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) k' C' := by
  obtain ⟨_, _, rd6487⟩ := RD.vatHealDaiLoaded hperm rd
  have rd6621pre := evm_run rd6487 with [
    raw push2 ⟨6496⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨6621⟩ (by native_decide) (by evm_ov)]
  have rd6621 := rd6621pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubSuccess
    (code := vatBytecode) (pc := ⟨6621⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord (healDaiSlot I)
        (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) I)
    (b := rad) (ret := ⟨6496⟩)
    (R := [healSourceWord I, rad, ⟨524⟩, sel])
    (by simpa using rd6621)
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    hle (by jump_dest) (by jump_dest) (by simp)

theorem RD.vatHealViceLoaded
    {σ σ₀ A I} {g sel rad sinNew daiNew : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (rd : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6496⟩
      (daiNew :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (wordAt32Mem ⟨5⟩
        (twoWordHashMem (healSourceWord I) ⟨6⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) k C) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6525⟩
      (vatSlotWord healViceSlot
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
            (healDaiSlot I) daiNew) I ::
        healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨5⟩
        (wordAt32Mem ⟨5⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩
            (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))))
      (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
        (healDaiSlot I) daiNew) k' C' := by
  have hcanonSource : (healSourceWord I).toNat < EVM.addressModulus := by
    rw [healSourceWord_toNat]
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using I.source.isLt
  have hmask :
      UInt256.land (healSourceWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        healSourceWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean hcanonSource
  have hdaiSlot :
      solcMappingSlot ⟨5⟩ (healSourceWord I) = healDaiSlot I := by
    rw [healDaiSlot_eq_mapSlot]
  let σSin := sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew
  let σDai := sstoreAccountMap I.codeOwner σSin (healDaiSlot I) daiNew
  let daiMem := wordAt32Mem ⟨5⟩
    (twoWordHashMem (healSourceWord I) ⟨6⟩
      (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))
  let daiHashMem := twoWordHashMem (healSourceWord I) ⟨5⟩ daiMem
  have rd6505pre := evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rd6506₀ := evm_run rd6505pre with [raw and (by native_decide) (by evm_ov)]
  have rd6506 := rd6506₀
  rw [hmask] at rd6506
  have rd6510pre := evm_run rd6506 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6511 := rd6510pre.mstore 0 (wordAt0Mem (healSourceWord I) daiMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd6516pre := evm_run rd6511 with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd6517 := rd6516pre.mstore 0 daiHashMem
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hdaiMemSize : daiMem.size = 96 := by
    dsimp [daiMem]
    exact wordAt32Mem_size_96 ⟨5⟩
      (twoWordHashMem_size_96 (healSourceWord I) ⟨6⟩
        (twoWordHashMem_size_96 (healSourceWord I) ⟨6⟩ solcFreePtrMem_size))
  have hdaiHash :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC (daiHashMem.readWithPadding 0 64))) =
        solcMappingSlot ⟨5⟩ (healSourceWord I) := by
    dsimp [daiHashMem]
    exact twoWordHashMem_solcMappingSlot ⟨5⟩ (healSourceWord I) hdaiMemSize
  have rd6520pre := evm_run rd6517 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd6521 := rd6520pre.keccak256 0 (solcMappingSlot ⟨5⟩ (healSourceWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost hdaiHash (by native_decide) (by evm_ov)
  obtain ⟨k6522, C6522, rd6522raw⟩ := rd6521.sstore hperm (by native_decide) (by evm_ov)
  have rd6522 : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6522⟩
      (healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      daiHashMem (UInt256.ofNat 3) ByteArray.empty σDai k6522 C6522 := by
    simpa [σSin, σDai, hdaiSlot, daiHashMem] using rd6522raw
  have rd6524 := rd6522.push1 ⟨8⟩ (by native_decide) (by evm_ov)
  obtain ⟨k6525, C6525, rd6525raw⟩ := rd6524.sload (by native_decide) (by evm_ov)
  have rd6525 : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6525⟩
      (vatSlotWord healViceSlot σDai I :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      daiHashMem (UInt256.ofNat 3) ByteArray.empty σDai k6525 C6525 := by
    simpa [vatSlotWord, solcSlotWord, healViceSlot] using rd6525raw
  exact ⟨_, _, by simpa [σSin, σDai, daiMem, daiHashMem] using rd6525⟩

theorem RD.vatHealViceSubUnderflow
    {σ σ₀ A I} {g sel rad sinNew daiNew : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (rd : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6496⟩
      (daiNew :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (wordAt32Mem ⟨5⟩
        (twoWordHashMem (healSourceWord I) ⟨6⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) k C)
    (hlt : (vatSlotWord healViceSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
          (healDaiSlot I) daiNew) I).toNat < rad.toNat) :
    RDrev vatBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd6525⟩ := RD.vatHealViceLoaded hperm rd
  have rd6621pre := evm_run rd6525 with [
    raw push2 ⟨6534⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨6621⟩ (by native_decide) (by evm_ov)]
  have rd6621 := rd6621pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubEmptyRevertAnyWords
    (code := vatBytecode) (pc := ⟨6621⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord healViceSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
          (healDaiSlot I) daiNew) I)
    (b := rad) (ret := ⟨6534⟩)
    (R := [healSourceWord I, rad, ⟨524⟩, sel])
    (by simpa using rd6621)
    (by
      unfold solcCheckedSubEmptyRevertWf solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    hlt
    (by simp)

theorem RD.vatHealViceSubSuccess
    {σ σ₀ A I} {g sel rad sinNew daiNew : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (rd : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6496⟩
      (daiNew :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (wordAt32Mem ⟨5⟩
        (twoWordHashMem (healSourceWord I) ⟨6⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem)))
      (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) k C)
    (hle : rad.toNat ≤ (vatSlotWord healViceSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
          (healDaiSlot I) daiNew) I).toNat) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6534⟩
      (UInt256.sub
          (vatSlotWord healViceSlot
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
              (healDaiSlot I) daiNew) I) rad ::
        healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨5⟩
        (wordAt32Mem ⟨5⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩
            (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))))
      (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
        (healDaiSlot I) daiNew) k' C' := by
  obtain ⟨_, _, rd6525⟩ := RD.vatHealViceLoaded hperm rd
  have rd6621pre := evm_run rd6525 with [
    raw push2 ⟨6534⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨6621⟩ (by native_decide) (by evm_ov)]
  have rd6621 := rd6621pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubSuccess
    (code := vatBytecode) (pc := ⟨6621⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord healViceSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
          (healDaiSlot I) daiNew) I)
    (b := rad) (ret := ⟨6534⟩)
    (R := [healSourceWord I, rad, ⟨524⟩, sel])
    (by simpa using rd6621)
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    hle (by jump_dest) (by jump_dest) (by simp)

theorem RD.vatHealDebtLoaded
    {σ σ₀ A I} {g sel rad sinNew daiNew viceNew : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (rd : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6534⟩
      (viceNew :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨5⟩
        (wordAt32Mem ⟨5⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩
            (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))))
      (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
        (healDaiSlot I) daiNew) k C) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6541⟩
      (vatSlotWord healDebtSlot
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
              (healDaiSlot I) daiNew)
            healViceSlot viceNew) I ::
        healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨5⟩
        (wordAt32Mem ⟨5⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩
            (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))))
      (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
          (healDaiSlot I) daiNew)
        healViceSlot viceNew) k' C' := by
  let σDai := sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) (healDaiSlot I) daiNew
  let σVice := sstoreAccountMap I.codeOwner σDai healViceSlot viceNew
  let mem := twoWordHashMem (healSourceWord I) ⟨5⟩
    (wordAt32Mem ⟨5⟩
      (twoWordHashMem (healSourceWord I) ⟨6⟩
        (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem)))
  have rd6535 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd6537 := rd6535.push1 ⟨8⟩ (by native_decide) (by evm_ov)
  obtain ⟨k6538, C6538, rd6538raw⟩ := rd6537.sstore hperm (by native_decide) (by evm_ov)
  have rd6538 : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6538⟩
      (healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty σVice k6538 C6538 := by
    simpa [σDai, σVice, healViceSlot, mem] using rd6538raw
  have rd6540 := rd6538.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  obtain ⟨k6541, C6541, rd6541raw⟩ := rd6540.sload (by native_decide) (by evm_ov)
  have rd6541 : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6541⟩
      (vatSlotWord healDebtSlot σVice I :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      mem (UInt256.ofNat 3) ByteArray.empty σVice k6541 C6541 := by
    simpa [vatSlotWord, solcSlotWord, healDebtSlot] using rd6541raw
  exact ⟨_, _, by simpa [σDai, σVice, mem] using rd6541⟩

theorem RD.vatHealDebtSubUnderflow
    {σ σ₀ A I} {g sel rad sinNew daiNew viceNew : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (rd : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6534⟩
      (viceNew :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨5⟩
        (wordAt32Mem ⟨5⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩
            (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))))
      (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
        (healDaiSlot I) daiNew) k C)
    (hlt : (vatSlotWord healDebtSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
            (healDaiSlot I) daiNew)
          healViceSlot viceNew) I).toNat < rad.toNat) :
    RDrev vatBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd6541⟩ := RD.vatHealDebtLoaded hperm rd
  have rd6621pre := evm_run rd6541 with [
    raw push2 ⟨6550⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨6621⟩ (by native_decide) (by evm_ov)]
  have rd6621 := rd6621pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubEmptyRevertAnyWords
    (code := vatBytecode) (pc := ⟨6621⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord healDebtSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
            (healDaiSlot I) daiNew)
          healViceSlot viceNew) I)
    (b := rad) (ret := ⟨6550⟩)
    (R := [healSourceWord I, rad, ⟨524⟩, sel])
    (by simpa using rd6621)
    (by
      unfold solcCheckedSubEmptyRevertWf solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    hlt
    (by simp)

theorem RD.vatHealDebtSubSuccess
    {σ σ₀ A I} {g sel rad sinNew daiNew viceNew : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (rd : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6534⟩
      (viceNew :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨5⟩
        (wordAt32Mem ⟨5⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩
            (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))))
      (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
        (healDaiSlot I) daiNew) k C)
    (hle : rad.toNat ≤ (vatSlotWord healDebtSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
            (healDaiSlot I) daiNew)
          healViceSlot viceNew) I).toNat) :
    ∃ k' C', RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6550⟩
      (UInt256.sub
          (vatSlotWord healDebtSlot
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
                (healDaiSlot I) daiNew)
              healViceSlot viceNew) I) rad ::
        healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨5⟩
        (wordAt32Mem ⟨5⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩
            (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))))
      (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
          (healDaiSlot I) daiNew)
        healViceSlot viceNew) k' C' := by
  obtain ⟨_, _, rd6541⟩ := RD.vatHealDebtLoaded hperm rd
  have rd6621pre := evm_run rd6541 with [
    raw push2 ⟨6550⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨6621⟩ (by native_decide) (by evm_ov)]
  have rd6621 := rd6621pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubSuccess
    (code := vatBytecode) (pc := ⟨6621⟩) (okPc := ⟨6615⟩)
    (a := vatSlotWord healDebtSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
            (healDaiSlot I) daiNew)
          healViceSlot viceNew) I)
    (b := rad) (ret := ⟨6550⟩)
    (R := [healSourceWord I, rad, ⟨524⟩, sel])
    (by simpa using rd6621)
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    hle (by jump_dest) (by jump_dest) (by simp)

theorem RD.vatHealStoreDebtReturn
    {σ σ₀ A I} {g sel rad sinNew daiNew viceNew debtNew : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (rd : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6550⟩
      (debtNew :: healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨5⟩
        (wordAt32Mem ⟨5⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩
            (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))))
      (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
          (healDaiSlot I) daiNew)
        healViceSlot viceNew) k C) :
    RDret vatBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
            (healDaiSlot I) daiNew)
          healViceSlot viceNew)
        healDebtSlot debtNew)
      ByteArray.empty := by
  let σVice := sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
      (healDaiSlot I) daiNew) healViceSlot viceNew
  let σDebt := sstoreAccountMap I.codeOwner σVice healDebtSlot debtNew
  have rd6551 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd6553 := rd6551.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  obtain ⟨k6554, C6554, rd6554raw⟩ := rd6553.sstore hperm (by native_decide) (by evm_ov)
  have rd6554 : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6554⟩
      (healSourceWord I :: rad :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨5⟩
        (wordAt32Mem ⟨5⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩
            (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))))
      (UInt256.ofNat 3) ByteArray.empty σDebt k6554 C6554 := by
    simpa [σVice, σDebt, healDebtSlot] using rd6554raw
  have rd6555 := rd6554.pop (by native_decide) (by evm_ov)
  have rd6556 := rd6555.pop (by native_decide) (by evm_ov)
  have rd524 := rd6556.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd525 := rd524.jumpdest (by native_decide) (by evm_ov)
  simpa [σVice, σDebt] using RD.stop rd525 (by native_decide) (by evm_ov)

theorem vatHealFinishSuccess
    {σ σ₀ A I} {g sel sinNew daiNew viceNew debtNew : UInt256}
    {k C : ℕ}
    (hcode : I.code = vatBytecode)
    (hperm : I.perm = true)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (healLocals I) healTransition.body
        (.returned { contract := contract, locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew }
          (healPostState (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            I sinNew daiNew viceNew debtNew) none))
    (hdebtOk : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6550⟩
      (debtNew :: healSourceWord I :: healRad I :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨5⟩
        (wordAt32Mem ⟨5⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩
            (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))))
      (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
          (healDaiSlot I) daiNew)
        healViceSlot viceNew) k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hret := RD.vatHealStoreDebtReturn
    (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (sel := sel) (rad := healRad I) (sinNew := sinNew)
    (daiNew := daiNew) (viceNew := viceNew) (debtNew := debtNew) hperm hdebtOk
  have haccountsFinal :
      Eq
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
              (healDaiSlot I) daiNew)
            healViceSlot viceNew)
          healDebtSlot debtNew)
        (healPostState (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          I sinNew daiNew viceNew debtNew).accountMap := by
    simp [healPostState, initState, storageStore_accountMap, storageStore_executionEnv]
  have henc : returnEquiv ByteArray.empty none healTransition.returnType := by
    rw [show healTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
    haccountsFinal henc

theorem vatHealAllSuccess
    {σ σ₀ A I} {g sel sinNew daiNew viceNew debtNew : UInt256}
    {k C : ℕ}
    (hcode : I.code = vatBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (hsinNewEvm :
      UInt256.sub (vatSlotWord (healSinSlot I) σ I) (healRad I) = sinNew)
    (hsinEnoughEvm :
      (healRad I).toNat ≤ (vatSlotWord (healSinSlot I) σ I).toNat)
    (hdaiNewEvm :
      UInt256.sub
        (vatSlotWord (healDaiSlot I)
          (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) I)
        (healRad I) = daiNew)
    (hdaiEnoughEvm :
      (healRad I).toNat ≤
        (vatSlotWord (healDaiSlot I)
          (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) I).toNat)
    (hviceNewEvm :
      UInt256.sub
        (vatSlotWord healViceSlot
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
            (healDaiSlot I) daiNew) I)
        (healRad I) = viceNew)
    (hviceEnoughEvm :
      (healRad I).toNat ≤
        (vatSlotWord healViceSlot
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
            (healDaiSlot I) daiNew) I).toNat)
    (hdebtNewEvm :
      UInt256.sub
        (vatSlotWord healDebtSlot
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
              (healDaiSlot I) daiNew)
            healViceSlot viceNew) I)
        (healRad I) = debtNew)
    (hdebtEnoughEvm :
      (healRad I).toNat ≤
        (vatSlotWord healDebtSlot
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
              (healDaiSlot I) daiNew)
            healViceSlot viceNew) I).toNat)
    (hdebtOk : RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6550⟩
      (debtNew :: healSourceWord I :: healRad I :: ⟨524⟩ :: sel :: [])
      (twoWordHashMem (healSourceWord I) ⟨5⟩
        (wordAt32Mem ⟨5⟩
          (twoWordHashMem (healSourceWord I) ⟨6⟩
            (twoWordHashMem (healSourceWord I) ⟨6⟩ solcFreePtrMem))))
      (UInt256.ofNat 3) ByteArray.empty
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
          (healDaiSlot I) daiNew)
        healViceSlot viceNew) k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evm0Solm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmSinSolm := Solm.EVM.storageStore evm0Solm evm0Solm.executionEnv.codeOwner
    (healSinSlot I) sinNew
  let evmDaiSolm := Solm.EVM.storageStore evmSinSolm evmSinSolm.executionEnv.codeOwner
    (healDaiSlot I) daiNew
  let evmViceSolm := Solm.EVM.storageStore evmDaiSolm evmDaiSolm.executionEnv.codeOwner
    healViceSlot viceNew
  have hmapSinSolm :
      Eq evmSinSolm.accountMap
        (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) := by
    dsimp [evmSinSolm, evm0Solm]
    rw [storageStore_accountMap]
    simpa [initState] using
      rfl
  have hdaiEnoughSolmLoad :
      (healRad I).toNat ≤
        (Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner
          (healDaiSlot I)).toNat := by
    have htmp := hdaiEnoughEvm
    simp [vatSlotWord, solcSlotWord] at htmp
    rw [← hmapSinSolm] at htmp
    simpa [evmSinSolm, Solm.EVM.storageLoad, storageStore_executionEnv] using htmp
  have hdaiNewSolmLoad :
      UInt256.sub
          (Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner
            (healDaiSlot I)) (healRad I) = daiNew := by
    have htmp := hdaiNewEvm
    simp [vatSlotWord, solcSlotWord] at htmp
    rw [← hmapSinSolm] at htmp
    simpa [evmSinSolm, Solm.EVM.storageLoad, storageStore_executionEnv] using htmp
  have hmapDaiSolm :
      Eq evmDaiSolm.accountMap
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
          (healDaiSlot I) daiNew) := by
    dsimp [evmDaiSolm]
    rw [storageStore_accountMap]
    simpa [evmSinSolm, evm0Solm, storageStore_executionEnv, initState] using
      congrArg (fun accounts =>
        sstoreAccountMap I.codeOwner accounts (healDaiSlot I) daiNew) hmapSinSolm
  have hviceEnoughSolmLoad :
      (healRad I).toNat ≤
        (Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner
          healViceSlot).toNat := by
    have howner : evmSinSolm.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSinSolm, evm0Solm, storageStore_executionEnv, initState]
    have htmp := hviceEnoughEvm
    simp [vatSlotWord, solcSlotWord] at htmp
    rw [← hmapDaiSolm] at htmp
    simpa [howner, evmDaiSolm, Solm.EVM.storageLoad, storageStore_executionEnv,
      State.lookupAccount, Account.lookupStorage] using htmp
  have hviceNewSolmLoad :
      UInt256.sub
          (Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner
            healViceSlot) (healRad I) = viceNew := by
    have howner : evmSinSolm.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSinSolm, evm0Solm, storageStore_executionEnv, initState]
    have htmp := hviceNewEvm
    simp [vatSlotWord, solcSlotWord] at htmp
    rw [← hmapDaiSolm] at htmp
    simpa [howner, evmDaiSolm, Solm.EVM.storageLoad, storageStore_executionEnv,
      State.lookupAccount, Account.lookupStorage] using htmp
  have hmapViceSolm :
      Eq evmViceSolm.accountMap
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
            (healDaiSlot I) daiNew)
          healViceSlot viceNew) := by
    dsimp [evmViceSolm]
    rw [storageStore_accountMap]
    simpa [evmDaiSolm, evmSinSolm, evm0Solm, storageStore_executionEnv, initState] using
      congrArg (fun accounts =>
        sstoreAccountMap I.codeOwner accounts healViceSlot viceNew) hmapDaiSolm
  have hdebtEnoughSolmLoad :
      (healRad I).toNat ≤
        (Solm.EVM.storageLoad evmViceSolm evmViceSolm.executionEnv.codeOwner
          healDebtSlot).toNat := by
    have howner : evmDaiSolm.executionEnv.codeOwner = I.codeOwner := by
      simp [evmDaiSolm, evmSinSolm, evm0Solm, storageStore_executionEnv, initState]
    have htmp := hdebtEnoughEvm
    simp [vatSlotWord, solcSlotWord] at htmp
    rw [← hmapViceSolm] at htmp
    simpa [howner, evmViceSolm, Solm.EVM.storageLoad, storageStore_executionEnv,
      State.lookupAccount, Account.lookupStorage] using htmp
  have hdebtNewSolmLoad :
      UInt256.sub
          (Solm.EVM.storageLoad evmViceSolm evmViceSolm.executionEnv.codeOwner
            healDebtSlot) (healRad I) = debtNew := by
    have howner : evmDaiSolm.executionEnv.codeOwner = I.codeOwner := by
      simp [evmDaiSolm, evmSinSolm, evm0Solm, storageStore_executionEnv, initState]
    have htmp := hdebtNewEvm
    simp [vatSlotWord, solcSlotWord] at htmp
    rw [← hmapViceSolm] at htmp
    simpa [howner, evmViceSolm, Solm.EVM.storageLoad, storageStore_executionEnv,
      State.lookupAccount, Account.lookupStorage] using htmp
  have hsinNewSolmLoad :
      UInt256.sub
          (Solm.EVM.storageLoad evm0Solm evm0Solm.executionEnv.codeOwner
            (healSinSlot I)) (healRad I) = sinNew := by
    simpa [evm0Solm, initState, Solm.EVM.storageLoad, vatSlotWord] using hsinNewEvm
  have hsinEnoughSolmLoad :
      (healRad I).toNat ≤
        (Solm.EVM.storageLoad evm0Solm evm0Solm.executionEnv.codeOwner
          (healSinSlot I)).toNat := by
    simpa [evm0Solm, initState, Solm.EVM.storageLoad, vatSlotWord] using hsinEnoughEvm
  have hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (healLocals I) healTransition.body
        (.returned { contract := contract, locals := healLocalsDebtNew I sinNew daiNew viceNew debtNew }
          (healPostState (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            I sinNew daiNew viceNew debtNew) none) := by
    simpa [evm0Solm] using
      vatHealSourceSuccessNamed
        (evm := evm0Solm) (I := I)
        (by simpa [evm0Solm, initState] using hwv)
        (by simp [evm0Solm, initState])
        hsinNewSolmLoad
        hsinEnoughSolmLoad
        hdaiNewSolmLoad
        hdaiEnoughSolmLoad
        hviceNewSolmLoad
        hviceEnoughSolmLoad
        hdebtNewSolmLoad
        hdebtEnoughSolmLoad
  exact vatHealFinishSuccess hcode hperm hdispatch hdecode hbody hdebtOk

theorem vatHeal_decodeCalldata_legacyUInt256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

theorem vatHeal_decodeCalldata_legacyUInt256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
    (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem vatDecode_heal_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
      (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I) := by
  simpa [config, healTransition, healLocals, healRad, uint256] using
    (vatHeal_decodeCalldata_legacyUInt256_ok (cd := I.calldata) (x := "rad") hsz36)

theorem vatDecode_heal_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
      (transitionSignature healTransition).paramTypes I.calldata = none := by
  simpa [config, healTransition, uint256] using
    (vatHeal_decodeCalldata_legacyUInt256_none_short (cd := I.calldata) (x := "rad")
      hsz4 hshort)

theorem vatDispatchHeal {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 14)) :
    dispatchMsg contract I.calldata = some healTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 14 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some healTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes, fluxSelectorBytes, foldSelectorBytes,
    forkSelectorBytes, frobSelectorBytes, gemSelectorBytes, grabSelectorBytes,
    healSelectorBytes]
  native_decide

theorem vatReachHealBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 14)) :
    ∃ k C, RD vatBytecode I g (initState σ σ₀ g A I)
        ⟨1597⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : vatSelWord I = ⟨0xf37ac61c⟩ :=
    vatSelWord_eq_of_beq I hsz 0xf3 0x7a 0xc6 0x1c ⟨0xf37ac61c⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vatBytecode vatHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhighhigh :
      UInt256.gt (armSelNat vatBytecode vatHighHighSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms65FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms65FirstPc 3))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms65Body 3 (by omega) ⟨1597⟩ hcode hwv hsz hsize
    hroot hhigh hhighhigh heq0 htake (by jump_dest) (by native_decide)

theorem RD.vatHealDecodeToRoutine
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1597⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6423⟩
      [healRad I, ⟨524⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      σ k C := by
  let rad := healRad I
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨1597⟩) (ret := ⟨524⟩)
    (decoded := ⟨1619⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  have rd1620 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd1621 := rd1620.pop (by native_decide) (by evm_ov)
  have rd1622 := rd1621.calldataload (by native_decide) (by evm_ov)
  have rd1625 := rd1622.push2 ⟨6423⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [rad, healRad, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd1625.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem vatHealShort {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsel : selIs I (vatSelBytes 14)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hreach :=
    vatReachHealBody (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := vatSelWord I) (entry := ⟨1597⟩) (ret := ⟨524⟩)
    (decoded := ⟨1619⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (vatDispatchHeal hsel)
    (vatDecode_heal_none_short hsz4 hshort)

theorem vatHealBodyCoreOk
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1597⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  obtain ⟨_, _, hroutine⟩ := RD.vatHealDecodeToRoutine hreach hsz36 hsize
  by_cases hsinEvm : (vatSlotWord (healSinSlot I) σ I).toNat < (healRad I).toNat
  · have hsinSolm :
        (Solm.EVM.storageLoad
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
            (healSinSlot I)).toNat < (healRad I).toNat := by
      simpa [initState, vatSlotWord, Solm.EVM.storageLoad] using hsinEvm
    have hbody :
        ExecTransitionBody config contract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (healLocals I) healTransition.body .reverted := by
      exact vatHealSourceSinUnderflow
        (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (I := I)
        (by simpa [initState] using hwv)
        (by simp [initState])
        hsinSolm
    have hrev := RD.vatHealSinSubUnderflow
      (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (rad := healRad I) hroutine hsinEvm
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hsinEnoughEvm :
        (healRad I).toNat ≤ (vatSlotWord (healSinSlot I) σ I).toNat :=
      le_of_not_gt hsinEvm
    let sinNew := UInt256.sub (vatSlotWord (healSinSlot I) σ I) (healRad I)
    obtain ⟨_, _, hsinOk⟩ := RD.vatHealSinSubSuccess
      (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (rad := healRad I) hroutine hsinEnoughEvm
    by_cases hdaiEvm :
        (vatSlotWord (healDaiSlot I)
          (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) I).toNat <
          (healRad I).toNat
    · have hsinNewSolm :
          UInt256.sub (vatSlotWord (healSinSlot I) σ I) (healRad I) = sinNew := rfl
      let evm0Solm := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evmSinSolm := Solm.EVM.storageStore evm0Solm evm0Solm.executionEnv.codeOwner
        (healSinSlot I)
        (UInt256.sub (Solm.EVM.storageLoad evm0Solm evm0Solm.executionEnv.codeOwner
          (healSinSlot I)) (healRad I))
      have hmapSinSolm :
          Eq evmSinSolm.accountMap
            (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) := by
        have hsinNewSolmRaw :
            UInt256.sub
                (Option.option ⟨0⟩ (fun acc : Account => acc.storage.findD (healSinSlot I) ⟨0⟩)
                  (σ.find? I.codeOwner))
                (healRad I) = sinNew := by
          simpa [vatSlotWord, solcSlotWord, Account.lookupStorage] using hsinNewSolm
        dsimp [evmSinSolm, evm0Solm]
        rw [storageStore_accountMap]
        simp [initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
        rw [hsinNewSolmRaw]
      have hdaiSolm :
          (Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner
              (healDaiSlot I)).toNat < (healRad I).toNat := by
        have htmp := hdaiEvm
        simp [vatSlotWord, solcSlotWord] at htmp
        rw [← hmapSinSolm] at htmp
        simpa [evmSinSolm, Solm.EVM.storageLoad, storageStore_executionEnv] using htmp
      have hbody :
          ExecTransitionBody config contract
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (healLocals I) healTransition.body .reverted := by
        exact vatHealSourceDaiUnderflow
          (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (I := I)
          (by simpa [initState] using hwv)
          (by simp [initState])
          (by simpa [initState, Solm.EVM.storageLoad, vatSlotWord] using hsinEnoughEvm)
          hdaiSolm
      have hrev := RD.vatHealDaiSubUnderflow
        (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (rad := healRad I) (sinNew := sinNew)
        hperm hsinOk hdaiEvm
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hdaiEnoughEvm :
          (healRad I).toNat ≤
            (vatSlotWord (healDaiSlot I)
              (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) I).toNat :=
        le_of_not_gt hdaiEvm
      obtain ⟨_, _, hdaiOk⟩ := RD.vatHealDaiSubSuccess
        (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (rad := healRad I) (sinNew := sinNew)
        hperm hsinOk hdaiEnoughEvm
      let daiNew := UInt256.sub
        (vatSlotWord (healDaiSlot I)
          (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) I) (healRad I)
      by_cases hviceEvm :
          (vatSlotWord healViceSlot
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
              (healDaiSlot I) daiNew) I).toNat < (healRad I).toNat
      · have hsinNewSolm :
            UInt256.sub (vatSlotWord (healSinSlot I) σ I) (healRad I) = sinNew := rfl
        have hdaiNewSolm :
            UInt256.sub
                (vatSlotWord (healDaiSlot I)
                  (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) I)
                (healRad I) = daiNew := rfl
        let evm0Solm := initState σ σ₀ (Sat256.ofUInt256 g) A I
        let evmSinSolm := Solm.EVM.storageStore evm0Solm evm0Solm.executionEnv.codeOwner
          (healSinSlot I)
          (UInt256.sub (Solm.EVM.storageLoad evm0Solm evm0Solm.executionEnv.codeOwner
            (healSinSlot I)) (healRad I))
        let evmDaiSolm := Solm.EVM.storageStore evmSinSolm
          evmSinSolm.executionEnv.codeOwner (healDaiSlot I)
          (UInt256.sub (Solm.EVM.storageLoad evmSinSolm
            evmSinSolm.executionEnv.codeOwner (healDaiSlot I)) (healRad I))
        have hmapSinSolm :
            Eq evmSinSolm.accountMap
              (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) := by
          have hsinNewSolmRaw :
              UInt256.sub
                  (Option.option ⟨0⟩ (fun acc : Account => acc.storage.findD (healSinSlot I) ⟨0⟩)
                    (σ.find? I.codeOwner))
                  (healRad I) = sinNew := by
            simpa [vatSlotWord, solcSlotWord, Account.lookupStorage] using hsinNewSolm
          dsimp [evmSinSolm, evm0Solm]
          rw [storageStore_accountMap]
          simp [initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
          rw [hsinNewSolmRaw]
        have hdaiEnoughSolmLoad :
            (healRad I).toNat ≤
              (Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner
                (healDaiSlot I)).toNat := by
          have htmp := hdaiEnoughEvm
          simp [vatSlotWord, solcSlotWord] at htmp
          rw [← hmapSinSolm] at htmp
          simpa [evmSinSolm, Solm.EVM.storageLoad, storageStore_executionEnv] using htmp
        have hdaiNewSolmLoad :
            UInt256.sub
                (Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner
                  (healDaiSlot I)) (healRad I) = daiNew := by
          have htmp := hdaiNewSolm
          simp [vatSlotWord, solcSlotWord] at htmp
          rw [← hmapSinSolm] at htmp
          simpa [evmSinSolm, Solm.EVM.storageLoad, storageStore_executionEnv] using htmp
        have hmapDaiSolm :
            Eq evmDaiSolm.accountMap
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
                (healDaiSlot I) daiNew) := by
          dsimp [evmDaiSolm]
          rw [storageStore_accountMap]
          rw [hdaiNewSolmLoad]
          simpa [evmSinSolm, evm0Solm, storageStore_executionEnv, initState] using
            congrArg (fun accounts =>
              sstoreAccountMap I.codeOwner accounts (healDaiSlot I) daiNew) hmapSinSolm
        have hviceSolm :
            (Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner
                healViceSlot).toNat < (healRad I).toNat := by
          have howner : evmSinSolm.executionEnv.codeOwner = I.codeOwner := by
            simp [evmSinSolm, evm0Solm, storageStore_executionEnv, initState]
          have htmp := hviceEvm
          simp [vatSlotWord, solcSlotWord] at htmp
          rw [← hmapDaiSolm] at htmp
          simpa [howner, evmDaiSolm, Solm.EVM.storageLoad, storageStore_executionEnv,
            State.lookupAccount, Account.lookupStorage] using htmp
        have hbody :
            ExecTransitionBody config contract
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (healLocals I) healTransition.body .reverted := by
          exact vatHealSourceViceUnderflow
            (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (I := I)
            (by simpa [initState] using hwv)
            (by simp [initState])
            (by simpa [initState, Solm.EVM.storageLoad, vatSlotWord] using hsinEnoughEvm)
            hdaiEnoughSolmLoad
            hviceSolm
        have hrev := RD.vatHealViceSubUnderflow
          (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) (sel := sel) (rad := healRad I) (sinNew := sinNew)
          (daiNew := daiNew) hperm hdaiOk hviceEvm
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hviceEnoughEvm :
            (healRad I).toNat ≤
              (vatSlotWord healViceSlot
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
                  (healDaiSlot I) daiNew) I).toNat :=
          le_of_not_gt hviceEvm
        obtain ⟨_, _, hviceOk⟩ := RD.vatHealViceSubSuccess
          (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) (sel := sel) (rad := healRad I) (sinNew := sinNew)
          (daiNew := daiNew) hperm hdaiOk hviceEnoughEvm
        let viceNew := UInt256.sub
          (vatSlotWord healViceSlot
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
              (healDaiSlot I) daiNew) I) (healRad I)
        by_cases hdebtEvm :
            (vatSlotWord healDebtSlot
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
                  (healDaiSlot I) daiNew)
                healViceSlot viceNew) I).toNat < (healRad I).toNat
        · have hsinNewSolm :
              UInt256.sub (vatSlotWord (healSinSlot I) σ I) (healRad I) = sinNew := rfl
          have hdaiNewSolm :
              UInt256.sub
                  (vatSlotWord (healDaiSlot I)
                    (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) I)
                  (healRad I) = daiNew := rfl
          have hviceNewSolm :
              UInt256.sub
                  (vatSlotWord healViceSlot
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
                      (healDaiSlot I) daiNew) I)
                  (healRad I) = viceNew := rfl
          let evm0Solm := initState σ σ₀ (Sat256.ofUInt256 g) A I
          let evmSinSolm := Solm.EVM.storageStore evm0Solm evm0Solm.executionEnv.codeOwner
            (healSinSlot I)
            (UInt256.sub (Solm.EVM.storageLoad evm0Solm evm0Solm.executionEnv.codeOwner
              (healSinSlot I)) (healRad I))
          let evmDaiSolm := Solm.EVM.storageStore evmSinSolm
            evmSinSolm.executionEnv.codeOwner (healDaiSlot I)
            (UInt256.sub (Solm.EVM.storageLoad evmSinSolm
              evmSinSolm.executionEnv.codeOwner (healDaiSlot I)) (healRad I))
          let evmViceSolm := Solm.EVM.storageStore evmDaiSolm
            evmDaiSolm.executionEnv.codeOwner healViceSlot
            (UInt256.sub (Solm.EVM.storageLoad evmDaiSolm
              evmDaiSolm.executionEnv.codeOwner healViceSlot) (healRad I))
          have hmapSinSolm :
              Eq evmSinSolm.accountMap
                (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew) := by
            have hsinNewSolmRaw :
                UInt256.sub
                    (Option.option ⟨0⟩ (fun acc : Account => acc.storage.findD (healSinSlot I) ⟨0⟩)
                      (σ.find? I.codeOwner))
                    (healRad I) = sinNew := by
              simpa [vatSlotWord, solcSlotWord, Account.lookupStorage] using hsinNewSolm
            dsimp [evmSinSolm, evm0Solm]
            rw [storageStore_accountMap]
            simp [initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
            rw [hsinNewSolmRaw]
          have hdaiEnoughSolmLoad :
              (healRad I).toNat ≤
                (Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner
                  (healDaiSlot I)).toNat := by
            have htmp := hdaiEnoughEvm
            simp [vatSlotWord, solcSlotWord] at htmp
            rw [← hmapSinSolm] at htmp
            simpa [evmSinSolm, Solm.EVM.storageLoad, storageStore_executionEnv] using htmp
          have hdaiNewSolmLoad :
              UInt256.sub
                  (Solm.EVM.storageLoad evmSinSolm evmSinSolm.executionEnv.codeOwner
                    (healDaiSlot I)) (healRad I) = daiNew := by
            have htmp := hdaiNewSolm
            simp [vatSlotWord, solcSlotWord] at htmp
            rw [← hmapSinSolm] at htmp
            simpa [evmSinSolm, Solm.EVM.storageLoad, storageStore_executionEnv] using htmp
          have hmapDaiSolm :
              Eq evmDaiSolm.accountMap
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
                  (healDaiSlot I) daiNew) := by
            dsimp [evmDaiSolm]
            rw [storageStore_accountMap]
            rw [hdaiNewSolmLoad]
            simpa [evmSinSolm, evm0Solm, storageStore_executionEnv, initState] using
              congrArg (fun accounts => sstoreAccountMap I.codeOwner accounts
                (healDaiSlot I) daiNew) hmapSinSolm
          have hviceEnoughSolmLoad :
              (healRad I).toNat ≤
                (Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner
                  healViceSlot).toNat := by
            have howner : evmSinSolm.executionEnv.codeOwner = I.codeOwner := by
              simp [evmSinSolm, evm0Solm, storageStore_executionEnv, initState]
            have htmp := hviceEnoughEvm
            simp [vatSlotWord, solcSlotWord] at htmp
            rw [← hmapDaiSolm] at htmp
            simpa [howner, evmDaiSolm, Solm.EVM.storageLoad, storageStore_executionEnv,
              State.lookupAccount, Account.lookupStorage] using htmp
          have hviceNewSolmLoad :
              UInt256.sub
                  (Solm.EVM.storageLoad evmDaiSolm evmDaiSolm.executionEnv.codeOwner
                    healViceSlot) (healRad I) = viceNew := by
            have howner : evmSinSolm.executionEnv.codeOwner = I.codeOwner := by
              simp [evmSinSolm, evm0Solm, storageStore_executionEnv, initState]
            have htmp := hviceNewSolm
            simp [vatSlotWord, solcSlotWord] at htmp
            rw [← hmapDaiSolm] at htmp
            simpa [howner, evmDaiSolm, Solm.EVM.storageLoad, storageStore_executionEnv,
              State.lookupAccount, Account.lookupStorage] using htmp
          have hmapViceSolm :
              Eq evmViceSolm.accountMap
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
                    (healDaiSlot I) daiNew)
                  healViceSlot viceNew) := by
            dsimp [evmViceSolm]
            rw [storageStore_accountMap]
            rw [hviceNewSolmLoad]
            simpa [evmDaiSolm, evmSinSolm, evm0Solm, storageStore_executionEnv, initState] using
              congrArg (fun accounts => sstoreAccountMap I.codeOwner accounts
                healViceSlot viceNew) hmapDaiSolm
          have hdebtSolm :
              (Solm.EVM.storageLoad evmViceSolm evmViceSolm.executionEnv.codeOwner
                  healDebtSlot).toNat < (healRad I).toNat := by
            have howner : evmDaiSolm.executionEnv.codeOwner = I.codeOwner := by
              simp [evmDaiSolm, evmSinSolm, evm0Solm, storageStore_executionEnv, initState]
            have htmp := hdebtEvm
            simp [vatSlotWord, solcSlotWord] at htmp
            rw [← hmapViceSolm] at htmp
            simpa [howner, evmViceSolm, Solm.EVM.storageLoad, storageStore_executionEnv,
              State.lookupAccount, Account.lookupStorage] using htmp
          have hbody :
              ExecTransitionBody config contract
                (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (healLocals I) healTransition.body .reverted := by
            exact vatHealSourceDebtUnderflow
              (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) (I := I)
              (by simpa [initState] using hwv)
              (by simp [initState])
              (by simpa [initState, Solm.EVM.storageLoad, vatSlotWord] using hsinEnoughEvm)
              hdaiEnoughSolmLoad
              hviceEnoughSolmLoad
              hdebtSolm
          have hrev := RD.vatHealDebtSubUnderflow
            (σ := σ) (σ₀ := σ₀) (A := A)
            (I := I) (g := g) (sel := sel) (rad := healRad I) (sinNew := sinNew)
            (daiNew := daiNew) (viceNew := viceNew) hperm hviceOk hdebtEvm
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hdebtEnoughEvm :
              (healRad I).toNat ≤
                (vatSlotWord healDebtSlot
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
                      (healDaiSlot I) daiNew)
                    healViceSlot viceNew) I).toNat :=
            le_of_not_gt hdebtEvm
          obtain ⟨_, _, hdebtOk⟩ := RD.vatHealDebtSubSuccess
            (σ := σ) (σ₀ := σ₀) (A := A)
            (I := I) (g := g) (sel := sel) (rad := healRad I) (sinNew := sinNew)
            (daiNew := daiNew) (viceNew := viceNew) hperm hviceOk hdebtEnoughEvm
          let debtNew := UInt256.sub
            (vatSlotWord healDebtSlot
              (sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ (healSinSlot I) sinNew)
                  (healDaiSlot I) daiNew)
                healViceSlot viceNew) I) (healRad I)
          exact vatHealAllSuccess
            (σ := σ)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
            (sinNew := sinNew) (daiNew := daiNew) (viceNew := viceNew)
            (debtNew := debtNew)
            hcode hperm hwv hdispatch hdecode
            (by simp [sinNew])
            hsinEnoughEvm
            (by simp [daiNew])
            hdaiEnoughEvm
            (by simp [viceNew])
            hviceEnoughEvm
            (by simp [debtNew])
            hdebtEnoughEvm
            hdebtOk

theorem vatHealBodyCore : VatBodyTheorem 14 := by
  intro σ σ₀ A I g hcode hsize hperm hwv hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 14) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some healTransition :=
    vatDispatchHeal hsel
  have hreach := vatReachHealBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact vatHealBodyCoreOk hcode hperm hwv hsz36 hsize hdispatch
      (vatDecode_heal_ok hsz36) hreach
  · exact vatHealShort hcode hsize hperm hwv hsz4 (by omega) hsel

end Benchmarks.Dss.Vat
