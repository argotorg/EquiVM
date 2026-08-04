import Examples.Ripemd160Old.HashZero

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 200000

namespace Ripemd160Old

open Ripemd160

def runtimeMstore8Mem (mem : ByteArray) (addr value : UInt256) : ByteArray :=
  (⟨#[UInt8.ofNat value.toNat]⟩ : ByteArray).write 0 mem addr.toNat 1

def runtimeMstore8Aw (aw addr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat addr.toNat 1)

def runtimeMstore8Cost (aw addr : UInt256) : Nat :=
  Cₘ (runtimeMstore8Aw aw addr) - Cₘ aw

def runtimeStore8Cursor (c : RuntimeMemCursor) (addr value : UInt256) : RuntimeMemCursor :=
  ⟨runtimeMstore8Mem c.mem addr value, runtimeMstore8Aw c.aw addr⟩

theorem RD.runtimeMstore8 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {c : RuntimeMemCursor}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {addr value : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (addr :: value :: t) c.mem c.aw rdata acc k C)
    (hdec : decode code pc = some (.MSTORE8, .none)) (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t
      (runtimeStore8Cursor c addr value).mem (runtimeStore8Cursor c addr value).aw
      rdata acc (k + 1) (C + (runtimeMstore8Cost c.aw addr + 3)) := by
  apply RD.mstore8 (runtimeMstore8Cost c.aw addr)
    (runtimeMstore8Mem c.mem addr value) (runtimeMstore8Aw c.aw addr)
    h hdec
  · intro s haws hstk
    simp [runtimeMstore8Cost, runtimeMstore8Aw, memoryExpansionCost,
      memoryExpansionCost.μᵢ', haws, hstk]
  · rfl
  · rfl
  · exact hov

def oldMarkerAddr (I : ExecutionEnv) : UInt256 :=
  hashPadPtr I + calldataSizeWord I

def oldBitLengthLo (I : ExecutionEnv) : UInt256 :=
  UInt256.land (oldHashBitLength I) ⟨0xffffffff⟩

def oldBitLengthHi (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (oldHashBitLength I) ⟨32⟩

def oldLengthAddr (I : ExecutionEnv) : Nat → UInt256
  | 0 => hashPadPtr I + (hashPaddedLengthWord I - ⟨8⟩)
  | 1 => hashPadPtr I + (hashPaddedLengthWord I - ⟨7⟩)
  | 2 => hashPadPtr I + (hashPaddedLengthWord I - ⟨6⟩)
  | 3 => hashPadPtr I + (hashPaddedLengthWord I - ⟨5⟩)
  | 4 => hashPadPtr I + (hashPaddedLengthWord I - ⟨4⟩)
  | 5 => hashPadPtr I + (hashPaddedLengthWord I - ⟨3⟩)
  | 6 => hashPadPtr I + (hashPaddedLengthWord I - ⟨2⟩)
  | 7 => hashPadPtr I + (hashPaddedLengthWord I - ⟨1⟩)
  | _ => hashPadPtr I

def oldLengthByte (I : ExecutionEnv) : Nat → UInt256
  | 0 => UInt256.land (oldBitLengthLo I) ⟨255⟩
  | 1 => UInt256.land (UInt256.shiftRight (oldBitLengthLo I) ⟨8⟩) ⟨255⟩
  | 2 => UInt256.land (UInt256.shiftRight (oldBitLengthLo I) ⟨16⟩) ⟨255⟩
  | 3 => UInt256.land (UInt256.shiftRight (oldBitLengthLo I) ⟨24⟩) ⟨255⟩
  | 4 => UInt256.land (oldBitLengthHi I) ⟨255⟩
  | 5 => UInt256.land (UInt256.shiftRight (oldBitLengthHi I) ⟨8⟩) ⟨255⟩
  | 6 => UInt256.land (UInt256.shiftRight (oldBitLengthHi I) ⟨16⟩) ⟨255⟩
  | 7 => UInt256.land (UInt256.shiftRight (oldBitLengthHi I) ⟨24⟩) ⟨255⟩
  | _ => ⟨0⟩

def oldLengthStack (I : ExecutionEnv) : List UInt256 :=
  [oldBitLengthLo I, ⟨255⟩, oldBitLengthHi I, ⟨255⟩,
    hashPadPtr I, hashPaddedLengthWord I, ⟨254⟩]

def oldHighLengthStack (I : ExecutionEnv) : List UInt256 :=
  [oldBitLengthHi I, ⟨255⟩, hashPadPtr I, hashPaddedLengthWord I, ⟨254⟩]

noncomputable def oldMarkerCursor (I : ExecutionEnv) : RuntimeMemCursor :=
  runtimeStore8Cursor (oldZeroCursor I (oldZeroIterations I))
    (oldMarkerAddr I) ⟨128⟩

noncomputable def oldLengthCursor (I : ExecutionEnv) : Nat → RuntimeMemCursor
  | 0 => oldMarkerCursor I
  | q + 1 => runtimeStore8Cursor (oldLengthCursor I q)
      (oldLengthAddr I q) (oldLengthByte I q)

private theorem runtime_writeMarker {cA gh bl σ σ₀ A I} {g : Sat256}
    {c : RuntimeMemCursor} {k C : Nat}
    (h : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8368⟩
      [calldataSizeWord I, oldHashBitLength I, hashPadPtr I,
        hashPaddedLengthWord I, ⟨254⟩]
      c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8377⟩
      [oldHashBitLength I, ⟨255⟩, hashPadPtr I, hashPaddedLengthWord I, ⟨254⟩]
      (runtimeStore8Cursor c (oldMarkerAddr I) ⟨128⟩).mem
      (runtimeStore8Cursor c (oldMarkerAddr I) ⟨128⟩).aw
      ByteArray.empty (cA, σ) k' C' := by
  have rd := evm_run_rfl h with [
    swap1, push1 ⟨128⟩, push1 ⟨255⟩, swap3, dup5, add ]
  have rd' := RD.runtimeMstore8 rd (by old_decode) (by simp)
  exact ⟨_, _, by simpa only [oldMarkerAddr, u256_add_comm] using rd'⟩

private theorem runtime_writeLength0 {cA gh bl σ σ₀ A I} {g : Sat256}
    {c : RuntimeMemCursor} {k C : Nat}
    (h : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8377⟩
      [oldHashBitLength I, ⟨255⟩, hashPadPtr I, hashPaddedLengthWord I, ⟨254⟩]
      c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8400⟩ (oldLengthStack I)
      (runtimeStore8Cursor c (oldLengthAddr I 0) (oldLengthByte I 0)).mem
      (runtimeStore8Cursor c (oldLengthAddr I 0) (oldLengthByte I 0)).aw
      ByteArray.empty (cA, σ) k' C' := by
  have rd := evm_run_rfl h with [
    dup2, push4 ⟨0xffffffff⟩, dup3, and, swap2, push1 ⟨32⟩, shr,
    swap2, dup2, dup2, and, push1 ⟨8⟩, dup8, sub, dup7, add ]
  have rd' := RD.runtimeMstore8 rd (by old_decode) (by simp)
  exact ⟨_, _, rd'⟩

private theorem runtime_writeLength1 {cA gh bl σ σ₀ A I} {g : Sat256}
    {c : RuntimeMemCursor} {k C : Nat}
    (h : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8400⟩ (oldLengthStack I) c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8413⟩ (oldLengthStack I)
      (runtimeStore8Cursor c (oldLengthAddr I 1) (oldLengthByte I 1)).mem
      (runtimeStore8Cursor c (oldLengthAddr I 1) (oldLengthByte I 1)).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldLengthStack] at h ⊢
  have rd := evm_run_rfl h with [
    dup2, dup2, push1 ⟨8⟩, shr, and, push1 ⟨7⟩, dup8, sub, dup7, add ]
  have rd' := RD.runtimeMstore8 rd (by old_decode) (by simp)
  exact ⟨_, _, by simpa only [oldLengthAddr, oldLengthByte, Nat.reduceMul,
    u256_add_comm,
    u256_land_comm] using rd'⟩

private theorem runtime_writeLength2 {cA gh bl σ σ₀ A I} {g : Sat256}
    {c : RuntimeMemCursor} {k C : Nat}
    (h : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8413⟩ (oldLengthStack I) c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8426⟩ (oldLengthStack I)
      (runtimeStore8Cursor c (oldLengthAddr I 2) (oldLengthByte I 2)).mem
      (runtimeStore8Cursor c (oldLengthAddr I 2) (oldLengthByte I 2)).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldLengthStack] at h ⊢
  have rd := evm_run_rfl h with [
    dup2, dup2, push1 ⟨16⟩, shr, and, push1 ⟨6⟩, dup8, sub, dup7, add ]
  have rd' := RD.runtimeMstore8 rd (by old_decode) (by simp)
  exact ⟨_, _, by simpa only [oldLengthAddr, oldLengthByte, Nat.reduceMul,
    u256_add_comm,
    u256_land_comm] using rd'⟩

private theorem runtime_writeLength3 {cA gh bl σ σ₀ A I} {g : Sat256}
    {c : RuntimeMemCursor} {k C : Nat}
    (h : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8426⟩ (oldLengthStack I) c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8437⟩ (oldHighLengthStack I)
      (runtimeStore8Cursor c (oldLengthAddr I 3) (oldLengthByte I 3)).mem
      (runtimeStore8Cursor c (oldLengthAddr I 3) (oldLengthByte I 3)).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldLengthStack, oldHighLengthStack] at h ⊢
  have rd := evm_run_rfl h with [
    push1 ⟨24⟩, shr, and, push1 ⟨5⟩, dup6, sub, dup5, add ]
  have rd' := RD.runtimeMstore8 rd (by old_decode) (by simp)
  exact ⟨_, _, by simpa only [oldLengthAddr, oldLengthByte, Nat.reduceMul,
    u256_add_comm,
    u256_land_comm] using rd'⟩

private theorem runtime_writeLength4 {cA gh bl σ σ₀ A I} {g : Sat256}
    {c : RuntimeMemCursor} {k C : Nat}
    (h : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8437⟩ (oldHighLengthStack I) c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8447⟩ (oldHighLengthStack I)
      (runtimeStore8Cursor c (oldLengthAddr I 4) (oldLengthByte I 4)).mem
      (runtimeStore8Cursor c (oldLengthAddr I 4) (oldLengthByte I 4)).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldHighLengthStack] at h ⊢
  have rd := evm_run_rfl h with [dup2, dup2, and, push1 ⟨4⟩, dup6, sub, dup5, add]
  have rd' := RD.runtimeMstore8 rd (by old_decode) (by simp)
  exact ⟨_, _, by simpa only [oldBitLengthHi, oldLengthAddr, oldLengthByte,
    Nat.reduceMul,
    u256_add_comm, u256_land_comm] using rd'⟩

private theorem runtime_writeLength5 {cA gh bl σ σ₀ A I} {g : Sat256}
    {c : RuntimeMemCursor} {k C : Nat}
    (h : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8447⟩ (oldHighLengthStack I) c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8460⟩ (oldHighLengthStack I)
      (runtimeStore8Cursor c (oldLengthAddr I 5) (oldLengthByte I 5)).mem
      (runtimeStore8Cursor c (oldLengthAddr I 5) (oldLengthByte I 5)).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldHighLengthStack] at h ⊢
  have rd := evm_run_rfl h with [
    dup2, dup2, push1 ⟨8⟩, shr, and, push1 ⟨3⟩, dup6, sub, dup5, add ]
  have rd' := RD.runtimeMstore8 rd (by old_decode) (by simp)
  exact ⟨_, _, by simpa only [oldBitLengthHi, oldLengthAddr, oldLengthByte,
    Nat.reduceMul,
    u256_add_comm, u256_land_comm] using rd'⟩

private theorem runtime_writeLength6 {cA gh bl σ σ₀ A I} {g : Sat256}
    {c : RuntimeMemCursor} {k C : Nat}
    (h : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8460⟩ (oldHighLengthStack I) c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8473⟩ (oldHighLengthStack I)
      (runtimeStore8Cursor c (oldLengthAddr I 6) (oldLengthByte I 6)).mem
      (runtimeStore8Cursor c (oldLengthAddr I 6) (oldLengthByte I 6)).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldHighLengthStack] at h ⊢
  have rd := evm_run_rfl h with [
    dup2, dup2, push1 ⟨16⟩, shr, and, push1 ⟨2⟩, dup6, sub, dup5, add ]
  have rd' := RD.runtimeMstore8 rd (by old_decode) (by simp)
  exact ⟨_, _, by simpa only [oldBitLengthHi, oldLengthAddr, oldLengthByte,
    Nat.reduceMul,
    u256_add_comm, u256_land_comm] using rd'⟩

private theorem runtime_writeLength7 {cA gh bl σ σ₀ A I} {g : Sat256}
    {c : RuntimeMemCursor} {k C : Nat}
    (h : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8473⟩ (oldHighLengthStack I) c.mem c.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8484⟩ [hashPadPtr I, hashPaddedLengthWord I, ⟨254⟩]
      (runtimeStore8Cursor c (oldLengthAddr I 7) (oldLengthByte I 7)).mem
      (runtimeStore8Cursor c (oldLengthAddr I 7) (oldLengthByte I 7)).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldHighLengthStack] at h
  have rd := evm_run_rfl h with [
    push1 ⟨24⟩, shr, and, push1 ⟨1⟩, dup4, sub, dup3, add ]
  have rd' := RD.runtimeMstore8 rd (by old_decode) (by simp)
  exact ⟨_, _, by simpa only [oldBitLengthHi, oldLengthAddr, oldLengthByte,
    Nat.reduceMul,
    u256_add_comm, u256_land_comm] using rd'⟩

/-- Write the marker and the eight little-endian length bytes. -/
theorem runtime_writePaddingTail {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8484⟩ [hashPadPtr I, hashPaddedLengthWord I, ⟨254⟩]
      (oldLengthCursor I 8).mem (oldLengthCursor I 8).aw
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd8368⟩ := runtime_zeroPadding
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  obtain ⟨_, _, rd8377⟩ := runtime_writeMarker rd8368
  obtain ⟨_, _, rd8400⟩ := runtime_writeLength0 rd8377
  obtain ⟨_, _, rd8413⟩ := runtime_writeLength1 rd8400
  obtain ⟨_, _, rd8426⟩ := runtime_writeLength2 rd8413
  obtain ⟨_, _, rd8437⟩ := runtime_writeLength3 rd8426
  obtain ⟨_, _, rd8447⟩ := runtime_writeLength4 rd8437
  obtain ⟨_, _, rd8460⟩ := runtime_writeLength5 rd8447
  obtain ⟨_, _, rd8473⟩ := runtime_writeLength6 rd8460
  obtain ⟨k, C, rd8484⟩ := runtime_writeLength7 rd8473
  exact ⟨k, C, by simpa only [oldMarkerCursor, oldLengthCursor] using rd8484⟩

end Ripemd160Old
