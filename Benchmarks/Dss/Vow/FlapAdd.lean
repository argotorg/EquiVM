import Benchmarks.Dss.Vow.Flap

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flap()` checked surplus additions -/

theorem RD.vowFlapSurplus0AddOverflow
    {σ σ₀ A I} {g sel vatSin : UInt256}
    {acc : AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨978⟩
      (vatSin :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hover : UInt256.size ≤ vatSin.toNat + (solcSlotWordAt ⟨10⟩ acc I).toNat) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let BumpVal := solcSlotWordAt ⟨10⟩ acc I
  have rd980 := rd.push1 ⟨10⟩ (by native_decide) (by evm_ov)
  obtain ⟨k981, C981, rd981Raw⟩ := rd980.sload (by native_decide) (by evm_ov)
  have rd981 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨981⟩
      (BumpVal :: vatSin :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k981 C981 := by
    simpa [BumpVal, solcSlotWordAt, solcSlotWord] using rd981Raw
  have rd984 := rd981.push2 ⟨5074⟩ (by native_decide) (by evm_ov)
  have rd5074 := rd984.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedAddEmptyRevertAnyWords
    (pc := ⟨5074⟩) (okPc := ⟨5090⟩) (a := vatSin) (b := BumpVal)
    (ret := ⟨985⟩) (R := [⟨993⟩, ⟨0⟩, ⟨357⟩, sel])
    (by simpa [BumpVal] using rd5074)
    (by
      unfold solcCheckedAddEmptyRevertWf solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [BumpVal] using hover)
    (by simp)

theorem RD.vowFlapSurplus0AddSuccess
    {σ σ₀ A I} {g sel vatSin : UInt256}
    {acc : AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨978⟩
      (vatSin :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hfit : vatSin.toNat + (solcSlotWordAt ⟨10⟩ acc I).toNat < UInt256.size) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨985⟩
      ((vatSin + solcSlotWordAt ⟨10⟩ acc I) :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  let BumpVal := solcSlotWordAt ⟨10⟩ acc I
  have rd980 := rd.push1 ⟨10⟩ (by native_decide) (by evm_ov)
  obtain ⟨k981, C981, rd981Raw⟩ := rd980.sload (by native_decide) (by evm_ov)
  have rd981 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨981⟩
      (BumpVal :: vatSin :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k981 C981 := by
    simpa [BumpVal, solcSlotWordAt, solcSlotWord] using rd981Raw
  have rd984 := rd981.push2 ⟨5074⟩ (by native_decide) (by evm_ov)
  have rd5074 := rd984.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨k', C', rd985⟩ :=
    RD.solcCheckedAddSuccess
      (pc := ⟨5074⟩) (okPc := ⟨5090⟩) (a := vatSin) (b := BumpVal)
      (ret := ⟨985⟩) (R := [⟨993⟩, ⟨0⟩, ⟨357⟩, sel])
      (by simpa [BumpVal] using rd5074)
      (by
        unfold solcCheckedAddSuccessWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [BumpVal] using hfit)
      (by jump_dest) (by jump_dest) (by simp)
  exact ⟨k', C', by simpa [BumpVal] using rd985⟩

theorem RD.vowFlapSurplusNeedAddOverflow
    {σ σ₀ A I} {g sel surplus0 : UInt256}
    {acc : AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨985⟩
      (surplus0 :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hover : UInt256.size ≤ surplus0.toNat + (solcSlotWordAt ⟨11⟩ acc I).toNat) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let HumpVal := solcSlotWordAt ⟨11⟩ acc I
  have rd986 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd988 := rd986.push1 ⟨11⟩ (by native_decide) (by evm_ov)
  obtain ⟨k989, C989, rd989Raw⟩ := rd988.sload (by native_decide) (by evm_ov)
  have rd989 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨989⟩
      (HumpVal :: surplus0 :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k989 C989 := by
    simpa [HumpVal, solcSlotWordAt, solcSlotWord] using rd989Raw
  have rd992 := rd989.push2 ⟨5074⟩ (by native_decide) (by evm_ov)
  have rd5074 := rd992.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedAddEmptyRevertAnyWords
    (pc := ⟨5074⟩) (okPc := ⟨5090⟩) (a := surplus0) (b := HumpVal)
    (ret := ⟨993⟩) (R := [⟨0⟩, ⟨357⟩, sel])
    (by simpa [HumpVal] using rd5074)
    (by
      unfold solcCheckedAddEmptyRevertWf solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [HumpVal] using hover)
    (by simp)

theorem RD.vowFlapSurplusNeedAddSuccess
    {σ σ₀ A I} {g sel surplus0 : UInt256}
    {acc : AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨985⟩
      (surplus0 :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hfit : surplus0.toNat + (solcSlotWordAt ⟨11⟩ acc I).toNat < UInt256.size) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨993⟩
      ((surplus0 + solcSlotWordAt ⟨11⟩ acc I) :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  let HumpVal := solcSlotWordAt ⟨11⟩ acc I
  have rd986 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd988 := rd986.push1 ⟨11⟩ (by native_decide) (by evm_ov)
  obtain ⟨k989, C989, rd989Raw⟩ := rd988.sload (by native_decide) (by evm_ov)
  have rd989 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨989⟩
      (HumpVal :: surplus0 :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k989 C989 := by
    simpa [HumpVal, solcSlotWordAt, solcSlotWord] using rd989Raw
  have rd992 := rd989.push2 ⟨5074⟩ (by native_decide) (by evm_ov)
  have rd5074 := rd992.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨k', C', rd993⟩ :=
    RD.solcCheckedAddSuccess
      (pc := ⟨5074⟩) (okPc := ⟨5090⟩) (a := surplus0) (b := HumpVal)
      (ret := ⟨993⟩) (R := [⟨0⟩, ⟨357⟩, sel])
      (by simpa [HumpVal] using rd5074)
      (by
        unfold solcCheckedAddSuccessWf
        repeat' first | apply And.intro | native_decide)
      (by simpa [HumpVal] using hfit)
      (by jump_dest) (by jump_dest) (by simp)
  exact ⟨k', C', by simpa [HumpVal] using rd993⟩

end Benchmarks.Dss.Vow
