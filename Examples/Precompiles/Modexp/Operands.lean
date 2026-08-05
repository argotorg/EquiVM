import Examples.Precompiles.Modexp.CalldataCopy

/-!
# Exact arbitrary-width operand setup

The general ModExp path allocates three bounded byte arrays and then fills them from calldata.
This file composes the compiler helpers while retaining the exact active-memory and gas state.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option Elab.async false

def operandBasePtr : Nat := 128
def operandExponentPtr (baseSize : Nat) : Nat :=
  operandBasePtr + bytesAllocationSize baseSize
def operandModulusPtr (baseSize exponentSize : Nat) : Nat :=
  operandExponentPtr baseSize + bytesAllocationSize exponentSize
def operandFreePtr (baseSize exponentSize modulusSize : Nat) : Nat :=
  operandModulusPtr baseSize exponentSize + bytesAllocationSize modulusSize

def operandBaseWords (baseSize : Nat) : Nat := 4 + bytesAllocationWords baseSize
def operandExponentWords (baseSize exponentSize : Nat) : Nat :=
  operandBaseWords baseSize + bytesAllocationWords exponentSize
def operandModulusWords (baseSize exponentSize modulusSize : Nat) : Nat :=
  operandExponentWords baseSize exponentSize + bytesAllocationWords modulusSize

def operandBaseActiveWords (baseSize : Nat) : UInt256 :=
  UInt256.ofNat (operandBaseWords baseSize)
def operandExponentActiveWords (baseSize exponentSize : Nat) : UInt256 :=
  UInt256.ofNat (operandExponentWords baseSize exponentSize)
def operandModulusActiveWords (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  UInt256.ofNat (operandModulusWords baseSize exponentSize modulusSize)

theorem bytesSize_le_roundedPayload (n : Nat) :
    n ≤ 32 * ((n + 31) / 32) := by
  have hdecomp := Nat.mod_add_div (n + 31) 32
  have hrem := Nat.mod_lt (n + 31) (by decide : 0 < 32)
  omega

theorem bytesHeaderAndSize_le_allocation (n : Nat) :
    32 + n ≤ bytesAllocationSize n := by
  unfold bytesAllocationSize
  exact Nat.add_le_add_left (bytesSize_le_roundedPayload n) 32

def operandBaseMemory (baseSize : Nat) : ByteArray :=
  storeBytesLength
    (setFreePtr solcFreePtrMem (operandExponentPtr baseSize)) operandBasePtr baseSize
def operandExponentMemory (baseSize exponentSize : Nat) : ByteArray :=
  storeBytesLength
    (setFreePtr (operandBaseMemory baseSize) (operandModulusPtr baseSize exponentSize))
    (operandExponentPtr baseSize) exponentSize
def operandAllocationMemory (baseSize exponentSize modulusSize : Nat) : ByteArray :=
  storeBytesLength
    (setFreePtr (operandExponentMemory baseSize exponentSize)
      (operandFreePtr baseSize exponentSize modulusSize))
    (operandModulusPtr baseSize exponentSize) modulusSize

theorem operandExponentPtr_eq (baseSize : Nat) :
    operandExponentPtr baseSize = 32 * operandBaseWords baseSize := by
  unfold operandExponentPtr operandBasePtr operandBaseWords
  rw [bytesAllocationSize_eq_words]
  omega

theorem operandModulusPtr_eq (baseSize exponentSize : Nat) :
    operandModulusPtr baseSize exponentSize =
      32 * operandExponentWords baseSize exponentSize := by
  unfold operandModulusPtr operandExponentWords
  rw [operandExponentPtr_eq, bytesAllocationSize_eq_words]
  omega

theorem operandFreePtr_eq (baseSize exponentSize modulusSize : Nat) :
    operandFreePtr baseSize exponentSize modulusSize =
      32 * operandModulusWords baseSize exponentSize modulusSize := by
  unfold operandFreePtr operandModulusWords
  rw [operandModulusPtr_eq, bytesAllocationSize_eq_words]
  omega

theorem operandBaseMemory_size (baseSize : Nat) :
    (operandBaseMemory baseSize).size = operandBasePtr + 32 := by
  unfold operandBaseMemory operandBasePtr
  rw [storeBytesLength_size]
  · rw [setFreePtr_size (by rw [solcFreePtrMem_size]), solcFreePtrMem_size]
    norm_num
  · rw [setFreePtr_size (by rw [solcFreePtrMem_size]), solcFreePtrMem_size]
    exact lt_usize _ (by norm_num)

theorem operandExponentMemory_size (baseSize exponentSize : Nat) (hb : baseSize ≤ 1024) :
    (operandExponentMemory baseSize exponentSize).size =
      operandExponentPtr baseSize + 32 := by
  unfold operandExponentMemory
  rw [storeBytesLength_size]
  · rw [setFreePtr_size (by rw [operandBaseMemory_size]; unfold operandBasePtr; omega),
      operandBaseMemory_size]
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  · rw [setFreePtr_size (by rw [operandBaseMemory_size]; unfold operandBasePtr; omega),
      operandBaseMemory_size]
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    exact lt_usize _ (by omega)

theorem operandAllocationMemory_size (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandAllocationMemory baseSize exponentSize modulusSize).size =
      operandModulusPtr baseSize exponentSize + 32 := by
  have hmem96 : 96 ≤ (operandExponentMemory baseSize exponentSize).size := by
    rw [operandExponentMemory_size _ _ hb]
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hsetSize :
      (setFreePtr (operandExponentMemory baseSize exponentSize)
        (operandFreePtr baseSize exponentSize modulusSize)).size =
        (operandExponentMemory baseSize exponentSize).size :=
    setFreePtr_size hmem96
  unfold operandAllocationMemory
  rw [storeBytesLength_size]
  · rw [hsetSize, operandExponentMemory_size _ _ hb]
    unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  · rw [hsetSize, operandExponentMemory_size _ _ hb]
    unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    exact lt_usize _ (by omega)

/-! The three Solidity `bytes` headers survive the later allocations.  These facts are used by
the arbitrary-width arithmetic helpers, whose first operations are `MLOAD` on these pointers. -/

theorem operandBaseMemory_readLength (baseSize : Nat) :
    (operandBaseMemory baseSize).readWithPadding operandBasePtr 32 =
      UInt256.toByteArray (UInt256.ofNat baseSize) := by
  unfold operandBaseMemory
  apply storeBytesLength_read_self
  rw [setFreePtr_size (by rw [solcFreePtrMem_size])]
  rw [solcFreePtrMem_size]
  exact lt_usize _ (by unfold operandBasePtr; norm_num)

theorem operandExponentMemory_readBaseLength (baseSize exponentSize : Nat)
    (hb : baseSize ≤ 1024) :
    (operandExponentMemory baseSize exponentSize).readWithPadding operandBasePtr 32 =
      UInt256.toByteArray (UInt256.ofNat baseSize) := by
  unfold operandExponentMemory
  have hbase96 : 96 ≤ (operandBaseMemory baseSize).size := by
    rw [operandBaseMemory_size]
    unfold operandBasePtr
    omega
  have hsetSize :
      (setFreePtr (operandBaseMemory baseSize)
        (operandModulusPtr baseSize exponentSize)).size =
        (operandBaseMemory baseSize).size := setFreePtr_size hbase96
  have hread : operandBasePtr + 32 ≤
      (setFreePtr (operandBaseMemory baseSize)
        (operandModulusPtr baseSize exponentSize)).size := by
    rw [hsetSize, operandBaseMemory_size]
  have hbelow : operandBasePtr + 32 ≤ operandExponentPtr baseSize := by
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hgap : operandExponentPtr baseSize -
      (setFreePtr (operandBaseMemory baseSize)
        (operandModulusPtr baseSize exponentSize)).size < USize.size := by
    rw [hsetSize, operandBaseMemory_size]
    exact lt_usize _ (by unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega)
  rw [storeBytesLength_read_below hread hbelow hgap]
  rw [setFreePtr_read_above hbase96 (by unfold operandBasePtr; omega)
    (by rw [operandBaseMemory_size])]
  exact operandBaseMemory_readLength baseSize

theorem operandExponentMemory_readLength (baseSize exponentSize : Nat)
    (hb : baseSize ≤ 1024) :
    (operandExponentMemory baseSize exponentSize).readWithPadding
        (operandExponentPtr baseSize) 32 =
      UInt256.toByteArray (UInt256.ofNat exponentSize) := by
  unfold operandExponentMemory
  apply storeBytesLength_read_self
  rw [setFreePtr_size (by rw [operandBaseMemory_size]; unfold operandBasePtr; omega),
    operandBaseMemory_size]
  unfold operandExponentPtr operandBasePtr bytesAllocationSize
  exact lt_usize _ (by omega)

theorem operandAllocationMemory_readBaseLength
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandAllocationMemory baseSize exponentSize modulusSize).readWithPadding
      operandBasePtr 32 = UInt256.toByteArray (UInt256.ofNat baseSize) := by
  unfold operandAllocationMemory
  have hexp96 : 96 ≤ (operandExponentMemory baseSize exponentSize).size := by
    rw [operandExponentMemory_size _ _ hb]
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hsetSize :
      (setFreePtr (operandExponentMemory baseSize exponentSize)
        (operandFreePtr baseSize exponentSize modulusSize)).size =
        (operandExponentMemory baseSize exponentSize).size := setFreePtr_size hexp96
  have hread : operandBasePtr + 32 ≤
      (setFreePtr (operandExponentMemory baseSize exponentSize)
        (operandFreePtr baseSize exponentSize modulusSize)).size := by
    rw [hsetSize, operandExponentMemory_size _ _ hb]
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hbelow : operandBasePtr + 32 ≤ operandModulusPtr baseSize exponentSize := by
    unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hgap : operandModulusPtr baseSize exponentSize -
      (setFreePtr (operandExponentMemory baseSize exponentSize)
        (operandFreePtr baseSize exponentSize modulusSize)).size < USize.size := by
    rw [hsetSize, operandExponentMemory_size _ _ hb]
    exact lt_usize _ (by
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
  rw [storeBytesLength_read_below hread hbelow hgap]
  rw [setFreePtr_read_above hexp96 (by unfold operandBasePtr; omega) (by
    rw [operandExponentMemory_size _ _ hb]
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega)]
  exact operandExponentMemory_readBaseLength baseSize exponentSize hb

theorem operandAllocationMemory_readExponentLength
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandAllocationMemory baseSize exponentSize modulusSize).readWithPadding
        (operandExponentPtr baseSize) 32 =
      UInt256.toByteArray (UInt256.ofNat exponentSize) := by
  unfold operandAllocationMemory
  have hexp96 : 96 ≤ (operandExponentMemory baseSize exponentSize).size := by
    rw [operandExponentMemory_size _ _ hb]
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hsetSize :
      (setFreePtr (operandExponentMemory baseSize exponentSize)
        (operandFreePtr baseSize exponentSize modulusSize)).size =
        (operandExponentMemory baseSize exponentSize).size := setFreePtr_size hexp96
  have hread : operandExponentPtr baseSize + 32 ≤
      (setFreePtr (operandExponentMemory baseSize exponentSize)
        (operandFreePtr baseSize exponentSize modulusSize)).size := by
    rw [hsetSize, operandExponentMemory_size _ _ hb]
  have hbelow : operandExponentPtr baseSize + 32 ≤
      operandModulusPtr baseSize exponentSize := by
    unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hgap : operandModulusPtr baseSize exponentSize -
      (setFreePtr (operandExponentMemory baseSize exponentSize)
        (operandFreePtr baseSize exponentSize modulusSize)).size < USize.size := by
    rw [hsetSize, operandExponentMemory_size _ _ hb]
    exact lt_usize _ (by
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
  rw [storeBytesLength_read_below hread hbelow hgap]
  rw [setFreePtr_read_above hexp96
    (by unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    (by rw [operandExponentMemory_size _ _ hb])]
  exact operandExponentMemory_readLength baseSize exponentSize hb

theorem operandAllocationMemory_readModulusLength
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandAllocationMemory baseSize exponentSize modulusSize).readWithPadding
        (operandModulusPtr baseSize exponentSize) 32 =
      UInt256.toByteArray (UInt256.ofNat modulusSize) := by
  unfold operandAllocationMemory
  apply storeBytesLength_read_self
  have hexp96 : 96 ≤ (operandExponentMemory baseSize exponentSize).size := by
    rw [operandExponentMemory_size _ _ hb]
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  rw [setFreePtr_size hexp96, operandExponentMemory_size _ _ hb]
  unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
  exact lt_usize _ (by omega)

/-- Every subwindow of the freshly allocated base payload is zero.  The concrete byte array only
stores the three length words; the compiler's logical allocation extent is represented by the
zero gaps between them. -/
theorem operandAllocationBasePayloadZero
    (baseSize exponentSize modulusSize start len : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hwindow : start + len ≤ baseSize) (hlen64 : len < 2 ^ 64) :
    (operandAllocationMemory baseSize exponentSize modulusSize).readWithPadding
        (operandBasePtr + 32 + start) len = ffi.ByteArray.zeroes len := by
  by_cases hz : len = 0
  · subst len
    rw [byteArray_readWithPadding_zero, zeroes_zero (n := 0) (by rfl)]
  · have hpos : 0 < len := Nat.pos_of_ne_zero hz
    have hExp96 : 96 ≤ (operandExponentMemory baseSize exponentSize).size := by
      rw [operandExponentMemory_size _ _ hb]
      unfold operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    have hSetExpSize :
        (setFreePtr (operandExponentMemory baseSize exponentSize)
          (operandFreePtr baseSize exponentSize modulusSize)).size =
          (operandExponentMemory baseSize exponentSize).size :=
      setFreePtr_size hExp96
    unfold operandAllocationMemory storeBytesLength
    rw [toByteArray_write_read_below_len_of_gap]
    · unfold setFreePtr
      rw [write32_read_above_len]
      · unfold operandExponentMemory storeBytesLength
        apply toByteArray_write_read_gap_of_gap
        · rw [setFreePtr_size (by rw [operandBaseMemory_size]; unfold operandBasePtr; omega),
            operandBaseMemory_size]
          unfold operandBasePtr
          omega
        · unfold operandExponentPtr operandBasePtr bytesAllocationSize
          omega
        · exact hpos
        · exact hlen64
        · rw [setFreePtr_size (by rw [operandBaseMemory_size]; unfold operandBasePtr; omega),
            operandBaseMemory_size]
          unfold operandExponentPtr operandBasePtr bytesAllocationSize
          exact lt_usize _ (by omega)
      · rw [toByteArray_size]
      · rw [operandExponentMemory_size _ _ hb]
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · unfold operandBasePtr
        omega
      · rw [operandExponentMemory_size _ _ hb]
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · exact hpos
      · exact hlen64
    · rw [hSetExpSize, operandExponentMemory_size _ _ hb]
      unfold operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · exact hpos
    · exact hlen64
    · rw [hSetExpSize, operandExponentMemory_size _ _ hb]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      exact lt_usize _ (by omega)

/-- Every subwindow of the freshly allocated exponent payload is zero. -/
theorem operandAllocationExponentPayloadZero
    (baseSize exponentSize modulusSize start len : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hwindow : start + len ≤ exponentSize) (hlen64 : len < 2 ^ 64) :
    (operandAllocationMemory baseSize exponentSize modulusSize).readWithPadding
        (operandExponentPtr baseSize + 32 + start) len = ffi.ByteArray.zeroes len := by
  by_cases hz : len = 0
  · subst len
    rw [byteArray_readWithPadding_zero, zeroes_zero (n := 0) (by rfl)]
  · have hExp96 : 96 ≤ (operandExponentMemory baseSize exponentSize).size := by
      rw [operandExponentMemory_size _ _ hb]
      unfold operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    have hSetExpSize :
        (setFreePtr (operandExponentMemory baseSize exponentSize)
          (operandFreePtr baseSize exponentSize modulusSize)).size =
          (operandExponentMemory baseSize exponentSize).size :=
      setFreePtr_size hExp96
    unfold operandAllocationMemory storeBytesLength
    apply toByteArray_write_read_gap_of_gap
    · rw [hSetExpSize, operandExponentMemory_size _ _ hb]
      omega
    · unfold operandModulusPtr
      have := bytesHeaderAndSize_le_allocation exponentSize
      omega
    · exact Nat.pos_of_ne_zero hz
    · exact hlen64
    · rw [hSetExpSize, operandExponentMemory_size _ _ hb]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      exact lt_usize _ (by omega)

/-- Every subwindow of the freshly allocated modulus payload is zero. -/
theorem operandAllocationModulusPayloadZero
    (baseSize exponentSize modulusSize start len : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hwindow : start + len ≤ modulusSize) (hlen64 : len < 2 ^ 64) :
    (operandAllocationMemory baseSize exponentSize modulusSize).readWithPadding
        (operandModulusPtr baseSize exponentSize + 32 + start) len =
      ffi.ByteArray.zeroes len := by
  by_cases hz : len = 0
  · subst len
    rw [byteArray_readWithPadding_zero, zeroes_zero (n := 0) (by rfl)]
  · apply readWithPadding_past_end
    · rw [operandAllocationMemory_size _ _ _ hb he]
      omega
    · exact hlen64

private theorem operandSetupAllocationDecodes :
    [decode runtimeBytecode ⟨105⟩, decode runtimeBytecode ⟨106⟩,
      decode runtimeBytecode ⟨107⟩, decode runtimeBytecode ⟨110⟩,
      decode runtimeBytecode ⟨111⟩, decode runtimeBytecode ⟨114⟩,
      decode runtimeBytecode ⟨115⟩, decode runtimeBytecode ⟨118⟩,
      decode runtimeBytecode ⟨121⟩, decode runtimeBytecode ⟨122⟩,
      decode runtimeBytecode ⟨125⟩,
      decode runtimeBytecode ⟨126⟩, decode runtimeBytecode ⟨127⟩,
      decode runtimeBytecode ⟨128⟩, decode runtimeBytecode ⟨131⟩,
      decode runtimeBytecode ⟨132⟩, decode runtimeBytecode ⟨135⟩,
      decode runtimeBytecode ⟨136⟩, decode runtimeBytecode ⟨137⟩,
      decode runtimeBytecode ⟨138⟩, decode runtimeBytecode ⟨141⟩,
      decode runtimeBytecode ⟨144⟩, decode runtimeBytecode ⟨145⟩,
      decode runtimeBytecode ⟨148⟩] =
    [some (.JUMPDEST, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨173⟩, 2)), some (.SWAP5, .none),
      some (.Push .PUSH2, some (⟨168⟩, 2)), some (.SWAP2, .none),
      some (.Push .PUSH2, some (⟨162⟩, 2)),
      some (.Push .PUSH2, some (⟨126⟩, 2)), some (.DUP8, .none),
      some (.Push .PUSH2, some (⟨581⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.SWAP5, .none),
      some (.Push .PUSH2, some (⟨136⟩, 2)), some (.DUP2, .none),
      some (.Push .PUSH2, some (⟨581⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.SWAP7, .none),
      some (.Push .PUSH2, some (⟨156⟩, 2)),
      some (.Push .PUSH2, some (⟨149⟩, 2)), some (.DUP7, .none),
      some (.Push .PUSH2, some (⟨581⟩, 2)), some (.JUMP, .none)] := by
  native_decide

def operandAllocationGas (baseSize exponentSize modulusSize : Nat) : Nat :=
  80 + newBytesGas (UInt256.ofNat 3) operandBasePtr baseSize +
    newBytesGas (operandBaseActiveWords baseSize) (operandExponentPtr baseSize) exponentSize +
    newBytesGas (operandExponentActiveWords baseSize exponentSize)
      (operandModulusPtr baseSize exponentSize) modulusSize

/-- Exact composition of the three `new bytes` calls, from the nontrivial dispatcher at PC 105
through the base-copy call site at PC 149. -/
theorem allocateOperandsExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize modOffset : Nat}
    {lastByte : UInt256} {tail : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hcalldata : I.calldata.size < 2 ^ 64) (htail : tail.length ≤ 1003)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨105⟩
      (lastByte :: UInt256.ofNat modOffset :: UInt256.ofNat exponentSize ::
        UInt256.ofNat (96 + baseSize) :: UInt256.ofNat baseSize ::
        UInt256.ofNat modulusSize :: tail)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨149⟩
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨156⟩ ::
        UInt256.ofNat (96 + baseSize) :: UInt256.ofNat exponentSize :: ⟨162⟩ ::
        UInt256.ofNat modOffset :: UInt256.ofNat modulusSize :: ⟨168⟩ ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat baseSize :: ⟨173⟩ :: tail)
      (operandAllocationMemory baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc (k + 276) (C + operandAllocationGas baseSize exponentSize modulusSize) := by
  have hd := operandSetupAllocationDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9,
    hd10, hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19,
    hd20, hd21, hd22, hd23⟩
  have hbaseBound : operandExponentPtr baseSize < 2 ^ 64 := by
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hmodBound : operandModulusPtr baseSize exponentSize < 2 ^ 64 := by
    unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hfreeBound : operandFreePtr baseSize exponentSize modulusSize < 2 ^ 64 := by
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hbaseWordsBound : operandBaseWords baseSize < UInt256.size := by
    apply lt_of_le_of_lt (show operandBaseWords baseSize ≤ 37 by
      unfold operandBaseWords bytesAllocationWords
      omega)
    decide
  have hexpWordsBound : operandExponentWords baseSize exponentSize < UInt256.size := by
    apply lt_of_le_of_lt (show operandExponentWords baseSize exponentSize ≤ 70 by
      unfold operandExponentWords operandBaseWords bytesAllocationWords
      omega)
    decide
  have hmodWordsBound : operandModulusWords baseSize exponentSize modulusSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
    decide
  have hbaseAW : newBytesWords (UInt256.ofNat 3) operandBasePtr baseSize =
      operandBaseActiveWords baseSize := by
    rw [show operandBasePtr = 128 by rfl, firstNewBytesWords hb]
    unfold operandBaseActiveWords operandBaseWords
    rw [bytesAllocationSize_eq_words]
    apply congrArg UInt256.ofNat
    omega
  have hexpAW : newBytesWords (operandBaseActiveWords baseSize)
      (operandExponentPtr baseSize) exponentSize =
      operandExponentActiveWords baseSize exponentSize := by
    unfold operandBaseActiveWords operandExponentActiveWords
    rw [operandExponentPtr_eq]
    exact newBytesWords_aligned hexpWordsBound
  have hmodAW : newBytesWords (operandExponentActiveWords baseSize exponentSize)
      (operandModulusPtr baseSize exponentSize) modulusSize =
      operandModulusActiveWords baseSize exponentSize modulusSize := by
    unfold operandExponentActiveWords operandModulusActiveWords
    rw [operandModulusPtr_eq]
    exact newBytesWords_aligned hmodWordsBound
  have rd581a := evm_run rd0 with [known jumpdest hd0, known pop hd1,
    known push2 hd2 ⟨173⟩, known swap5 hd3, known push2 hd4 ⟨168⟩,
    known swap2 hd5, known push2 hd6 ⟨162⟩, known push2 hd7 ⟨126⟩,
    known dup8 hd8, known push2 hd9 ⟨581⟩, known jump hd10 jumpDest_581]
  have rd126raw := newBytesExact hb (by decide) (by simpa [operandBasePtr] using hbaseBound)
    (by rw [solcFreePtrMem_size]) (by rw [solcFreePtrMem_size]; decide)
    (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))
    (by native_decide)
    (wordMul32_not_le64_of_ge3 (by native_decide) (by native_decide))
    solcFreePtrMem_read64 hcalldata (by simp only [List.length_cons]; omega)
    jumpDest_126 rd581a
  have hbaseAW128 : newBytesWords (UInt256.ofNat 3) 128 baseSize =
      operandBaseActiveWords baseSize := by simpa [operandBasePtr] using hbaseAW
  rw [hbaseAW128] at rd126raw
  have rd126 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨126⟩
      (UInt256.ofNat operandBasePtr :: ⟨162⟩ :: UInt256.ofNat modOffset ::
        UInt256.ofNat modulusSize :: ⟨168⟩ ::
        UInt256.ofNat exponentSize :: UInt256.ofNat (96 + baseSize) ::
        UInt256.ofNat baseSize :: ⟨173⟩ :: tail)
      (operandBaseMemory baseSize) (operandBaseActiveWords baseSize)
      ByteArray.empty acc (k + 95) (C + 35 + newBytesGas (UInt256.ofNat 3) operandBasePtr baseSize) := by
    simpa [operandBaseMemory, operandExponentPtr, operandBasePtr] using
      rd126raw.withIndices (by omega) (by simp [operandBasePtr])
  have hmem1Size : (operandBaseMemory baseSize).size = 160 := by
    simpa [operandBasePtr] using operandBaseMemory_size baseSize
  have hmem1Read : (operandBaseMemory baseSize).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat (operandExponentPtr baseSize)) := by
    unfold operandBaseMemory
    rw [storeBytesLength_read64]
    · exact setFreePtr_read64 (by rw [solcFreePtrMem_size])
    · rw [setFreePtr_size (by rw [solcFreePtrMem_size]), solcFreePtrMem_size]
    · decide
    · rw [setFreePtr_size (by rw [solcFreePtrMem_size]), solcFreePtrMem_size]
      unfold operandBasePtr
      exact lt_usize _ (by norm_num)
  have hbaseAWNat : (operandBaseActiveWords baseSize).toNat =
      operandBaseWords baseSize := by
    unfold operandBaseActiveWords
    rw [UInt256.toNat_ofNat_of_lt hbaseWordsBound]
  have rd581b := evm_run rd126 with [known jumpdest hd11, known swap5 hd12,
    known push2 hd13 ⟨136⟩, known dup2 hd14, known push2 hd15 ⟨581⟩,
    known jump hd16 jumpDest_581]
  have rd136raw := newBytesExact he (by
      unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    (by simpa [operandModulusPtr] using hmodBound)
    (by rw [hmem1Size]; omega) (by rw [hmem1Size]; unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    (by rw [hmem1Size]; exact lt_usize _ (by unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega))
    (by rw [hbaseAWNat]; unfold operandBaseWords bytesAllocationWords; omega)
    (wordMul32_not_le64_of_ge3
      (by rw [hbaseAWNat]; unfold operandBaseWords bytesAllocationWords; omega)
      (by
        rw [hbaseAWNat]
        have hsmall : operandBaseWords baseSize ≤ 37 := by
          unfold operandBaseWords bytesAllocationWords
          omega
        exact lt_of_le_of_lt (Nat.mul_le_mul_right 32 hsmall)
          (by decide : 37 * 32 < UInt256.size)))
    hmem1Read hcalldata (by simp only [List.length_cons]; omega) jumpDest_136 rd581b
  rw [hexpAW] at rd136raw
  have rd136 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨136⟩
      (UInt256.ofNat (operandExponentPtr baseSize) :: UInt256.ofNat exponentSize ::
        ⟨162⟩ :: UInt256.ofNat modOffset :: UInt256.ofNat modulusSize :: ⟨168⟩ ::
        UInt256.ofNat operandBasePtr :: UInt256.ofNat (96 + baseSize) ::
        UInt256.ofNat baseSize :: ⟨173⟩ :: tail)
      (operandExponentMemory baseSize exponentSize)
      (operandExponentActiveWords baseSize exponentSize) ByteArray.empty acc
      (k + 185)
      (C + 56 + newBytesGas (UInt256.ofNat 3) operandBasePtr baseSize +
        newBytesGas (operandBaseActiveWords baseSize) (operandExponentPtr baseSize) exponentSize) := by
    simpa [operandExponentMemory, operandModulusPtr] using
      rd136raw.withIndices (by omega) (by omega)
  have hmem2Size : (operandExponentMemory baseSize exponentSize).size =
      operandExponentPtr baseSize + 32 := by
    exact operandExponentMemory_size baseSize exponentSize hb
  have hmem2Read : (operandExponentMemory baseSize exponentSize).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) := by
    unfold operandExponentMemory
    rw [storeBytesLength_read64]
    · exact setFreePtr_read64 (by rw [hmem1Size]; omega)
    · rw [setFreePtr_size (by rw [hmem1Size]; omega), hmem1Size]
      norm_num
    · unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega
    · rw [setFreePtr_size (by rw [hmem1Size]; omega), hmem1Size]
      exact lt_usize _ (by unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega)
  have hexpAWNat : (operandExponentActiveWords baseSize exponentSize).toNat =
      operandExponentWords baseSize exponentSize := by
    unfold operandExponentActiveWords
    rw [UInt256.toNat_ofNat_of_lt hexpWordsBound]
  have rd581c := evm_run rd136 with [known jumpdest hd17, known swap7 hd18,
    known push2 hd19 ⟨156⟩, known push2 hd20 ⟨149⟩, known dup7 hd21,
    known push2 hd22 ⟨581⟩, known jump hd23 jumpDest_581]
  have rd149raw := newBytesExact hm
    (by unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    (by simpa [operandFreePtr] using hfreeBound)
    (by rw [hmem2Size]; unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    (by rw [hmem2Size]; unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    (by rw [hmem2Size]; exact lt_usize _ (by
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize; omega))
    (by rw [hexpAWNat]; unfold operandExponentWords operandBaseWords bytesAllocationWords; omega)
    (wordMul32_not_le64_of_ge3
      (by rw [hexpAWNat]; unfold operandExponentWords operandBaseWords bytesAllocationWords; omega)
      (by
        rw [hexpAWNat]
        have hsmall : operandExponentWords baseSize exponentSize ≤ 70 := by
          unfold operandExponentWords operandBaseWords bytesAllocationWords
          omega
        exact lt_of_le_of_lt (Nat.mul_le_mul_right 32 hsmall)
          (by decide : 70 * 32 < UInt256.size)))
    hmem2Read hcalldata (by simp only [List.length_cons]; omega) jumpDest_149 rd581c
  rw [hmodAW] at rd149raw
  simpa [operandAllocationMemory, operandFreePtr, operandAllocationGas,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    rd149raw.withIndices (by omega) (by omega)

def operandBaseCopiedMemory (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : ByteArray :=
  I.calldata.write 96 (operandAllocationMemory baseSize exponentSize modulusSize)
    (operandBasePtr + 32) (baseCalldataAvail I baseSize)

def operandExponentCopiedMemory (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : ByteArray :=
  I.calldata.write (96 + baseSize)
    (operandBaseCopiedMemory I baseSize exponentSize modulusSize)
    (operandExponentPtr baseSize + 32)
    (calldataSegmentAvail I (96 + baseSize) exponentSize)

def operandCopiedMemory (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : ByteArray :=
  I.calldata.write (96 + baseSize + exponentSize)
    (operandExponentCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusPtr baseSize exponentSize + 32)
    (calldataSegmentAvail I (96 + baseSize + exponentSize) modulusSize)

/-- Copying the available source prefix into an in-bounds, initially-zero destination window
produces exactly the trusted padded read of that source segment. -/
private theorem copyIntoZeroInBounds (src base : ByteArray) (off dest width : Nat)
    (hwidth64 : width < 2 ^ 64) (hdest : dest + width ≤ base.size)
    (hzero : ∀ start len, start + len ≤ width → len < 2 ^ 64 →
      base.readWithPadding (dest + start) len = ffi.ByteArray.zeroes len) :
    (src.write off base dest (min width (src.size - off))).readWithPadding dest width =
      Model.readPadded src off width := by
  let avail := min width (src.size - off)
  have havailLe : avail ≤ width := by unfold avail; exact min_le_left _ _
  have hrem : src.size - min off src.size = src.size - off := by omega
  by_cases hwidth0 : width = 0
  · subst width
    have havail0 : avail = 0 := by simp [avail]
    rw [show min 0 (src.size - off) = 0 by simp, byteArray_write_len_zero,
      byteArray_readWithPadding_zero]
    have hr := model_readPadded_size src off 0
    rw [byteArray_eq_empty_of_size_eq_zero _ hr]
  · have hwidthPos : 0 < width := Nat.pos_of_ne_zero hwidth0
    by_cases havail0 : avail = 0
    · have havail0' : min width (src.size - off) = 0 := by simpa [avail] using havail0
      rw [havail0', byteArray_write_len_zero]
      rw [show base.readWithPadding dest width = ffi.ByteArray.zeroes width by
        simpa using hzero 0 width (by omega) hwidth64]
      have hoffge : src.size ≤ off := by
        unfold avail at havail0
        omega
      unfold Model.readPadded
      simp [Nat.min_eq_right hoffge, ffi.ByteArray.zeroes]
    · have havailPos : 0 < avail := Nat.pos_of_ne_zero havail0
      have hoff : off < src.size := by
        unfold avail at havailPos
        omega
      have hsrc : off + avail ≤ src.size := by
        unfold avail
        omega
      have hwriteIn : dest + avail ≤ base.size := by omega
      by_cases havailFull : avail = width
      · have hminFull : min width (src.size - off) = width := by
          simpa [avail] using havailFull
        rw [hminFull]
        rw [write_read_back_from_gen src base off dest width hwidth0 (by
          simpa [havailFull] using hsrc) (by omega) hwidth64]
        unfold Model.readPadded
        simp only [Nat.min_eq_left hoff.le]
        rw [show (src.size - off).min width = width from
          (Nat.min_comm (src.size - off) width).trans hminFull]
        apply ByteArray.ext
        simp
      · have htailPos : 0 < width - avail := by omega
        have hsum : avail + (width - avail) = width := Nat.add_sub_of_le havailLe
        have hresultSize :
            (src.write off base dest avail).size = base.size := by
          rw [write_eq_gen_from src base off dest avail havail0 hsrc hwriteIn,
            ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
            ByteArray.size_extract, ByteArray.size_extract]
          omega
        have hfirst := write_read_back_from_gen src base off dest avail havail0 hsrc
          (by omega) (by omega : avail < 2 ^ 64)
        have hsecond := write_read_above_gen_from src base off dest avail
          (dest + avail) (width - avail) havail0 hsrc hwriteIn (by omega) (by omega)
          htailPos (by omega : width - avail < 2 ^ 64)
        have hbaseTail := hzero avail (width - avail) (by omega)
          (by omega : width - avail < 2 ^ 64)
        rw [show min width (src.size - off) = avail from rfl]
        rw [show width = avail + (width - avail) from hsum.symm]
        rw [byteArray_readWithPadding_split _ dest avail (width - avail)
          havailPos htailPos (by omega) (by omega) (by omega) (by
            rw [hresultSize]
            omega)]
        rw [hfirst, hsecond, hbaseTail]
        unfold Model.readPadded
        simp only [Nat.min_eq_left hoff.le]
        rw [show (src.size - off).min (avail + (width - avail)) = avail by
          rw [hsum]
          exact (Nat.min_comm (src.size - off) width).trans rfl]
        rw [hsum]
        unfold ffi.ByteArray.zeroes
        rfl

/-- Copying at the concrete end of memory gives the same trusted padded segment: the copied
prefix extends the byte array and the unprovided suffix remains implicit zero memory. -/
private theorem copyIntoZeroAtEnd (src base : ByteArray) (off width : Nat)
    (hbase64 : base.size < 2 ^ 64) (hwidth64 : width < 2 ^ 64) :
    (src.write off base base.size (min width (src.size - off))).readWithPadding
        base.size width = Model.readPadded src off width := by
  let avail := min width (src.size - off)
  have havailLe : avail ≤ width := by unfold avail; exact min_le_left _ _
  have hrem : src.size - min off src.size = src.size - off := by omega
  by_cases hwidth0 : width = 0
  · subst width
    rw [show min 0 (src.size - off) = 0 by simp, byteArray_write_len_zero,
      byteArray_readWithPadding_zero]
    have hr := model_readPadded_size src off 0
    rw [byteArray_eq_empty_of_size_eq_zero _ hr]
  · by_cases havail0 : avail = 0
    · have havail0' : min width (src.size - off) = 0 := by simpa [avail] using havail0
      rw [havail0', byteArray_write_len_zero,
        readWithPadding_past_end base base.size width (by omega) hwidth64]
      have hoffge : src.size ≤ off := by
        unfold avail at havail0
        omega
      unfold Model.readPadded
      simp only [Nat.min_eq_right hoffge, Nat.sub_self, Nat.zero_min, Nat.zero_add]
      have hempty : src.extract src.size src.size = ByteArray.empty := by
        apply ByteArray.ext
        simp
      rw [show src.size + 0 = src.size by omega, hempty]
      simp [ffi.ByteArray.zeroes]
    · have havailPos : 0 < avail := Nat.pos_of_ne_zero havail0
      have hoff : off < src.size := by
        unfold avail at havailPos
        omega
      have hsrc : off + avail ≤ src.size := by
        unfold avail
        omega
      by_cases havailFull : avail = width
      · have hminFull : min width (src.size - off) = width := by
          simpa [avail] using havailFull
        rw [hminFull]
        rw [write_read_back_from_gen src base off base.size width hwidth0 (by
          simpa [havailFull] using hsrc) (by omega) hwidth64]
        unfold Model.readPadded
        simp only [Nat.min_eq_left hoff.le]
        rw [show (src.size - off).min width = width from
          (Nat.min_comm (src.size - off) width).trans hminFull]
        apply ByteArray.ext
        simp
      · have htailPos : 0 < width - avail := by omega
        have hsum : avail + (width - avail) = width := Nat.add_sub_of_le havailLe
        have hresultSize :
            (src.write off base base.size avail).size = base.size + avail :=
          write_end_size_from src base off avail havail0 hsrc
        have hfirst := write_read_back_from_gen src base off base.size avail havail0 hsrc
          (by omega) (by omega : avail < 2 ^ 64)
        have hsecond :
            (src.write off base base.size avail).readWithPadding
                (base.size + avail) (width - avail) =
              ffi.ByteArray.zeroes (width - avail) := by
          apply readWithPadding_past_end
          · rw [hresultSize]
          · omega
        rw [show min width (src.size - off) = avail from rfl]
        rw [readWithPadding_eq_model_readPadded _ base.size width hbase64 hwidth64]
        unfold Model.readPadded
        rw [hresultSize]
        simp only [Nat.min_eq_left (by omega : base.size ≤ base.size + avail),
          Nat.add_sub_cancel_left]
        simp only [min_eq_left havailLe]
        have hfirstExtract :
            (src.write off base base.size avail).extract base.size (base.size + avail) =
              src.extract off (off + avail) := by
          rw [← hfirst]
          exact (readWithPadding_eq_extract' _ _ _ havailPos (by omega) (by
            rw [hresultSize])).symm
        rw [hfirstExtract]
        simp only [Nat.min_eq_left hoff.le]
        rw [show (src.size - off).min width = avail from
          (Nat.min_comm (src.size - off) width).trans rfl]

theorem operandBaseCopiedMemory_size (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandBaseCopiedMemory I baseSize exponentSize modulusSize).size =
      operandModulusPtr baseSize exponentSize + 32 := by
  unfold operandBaseCopiedMemory
  by_cases hz : baseCalldataAvail I baseSize = 0
  · rw [hz, byteArray_write_len_zero, operandAllocationMemory_size _ _ _ hb he]
  · rw [← operandAllocationMemory_size baseSize exponentSize modulusSize hb he]
    apply write_size_of_inBounds_from
    · exact hz
    · unfold baseCalldataAvail at hz ⊢
      omega
    · rw [operandAllocationMemory_size _ _ _ hb he]
      unfold baseCalldataAvail operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega

/-- The first copied buffer is exactly the trusted padded base operand. -/
theorem operandBaseCopiedPayload (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandBaseCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandBasePtr + 32) baseSize = Model.readPadded I.calldata 96 baseSize := by
  unfold operandBaseCopiedMemory baseCalldataAvail
  apply copyIntoZeroInBounds
  · omega
  · rw [operandAllocationMemory_size _ _ _ hb he]
    unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  · intro start len hwindow hlen64
    simpa [Nat.add_assoc] using
      operandAllocationBasePayloadZero baseSize exponentSize modulusSize start len
        hb he hwindow hlen64

/-- Copying the base cannot change any subwindow of the later exponent payload. -/
theorem operandBaseCopiedExponentPayloadZero (I : ExecutionEnv)
    (baseSize exponentSize modulusSize start len : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hwindow : start + len ≤ exponentSize) (hlen64 : len < 2 ^ 64) :
    (operandBaseCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandExponentPtr baseSize + 32 + start) len = ffi.ByteArray.zeroes len := by
  by_cases hlen0 : len = 0
  · subst len
    rw [byteArray_readWithPadding_zero, zeroes_zero (n := 0) (by rfl)]
  · unfold operandBaseCopiedMemory
    by_cases hz : baseCalldataAvail I baseSize = 0
    · rw [hz, byteArray_write_len_zero]
      exact operandAllocationExponentPayloadZero _ _ _ _ _ hb he hwindow hlen64
    · rw [write_read_above_gen_from]
      · exact operandAllocationExponentPayloadZero _ _ _ _ _ hb he hwindow hlen64
      · exact hz
      · unfold baseCalldataAvail at hz ⊢
        omega
      · rw [operandAllocationMemory_size _ _ _ hb he]
        unfold baseCalldataAvail operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega
      · unfold baseCalldataAvail operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · rw [operandAllocationMemory_size _ _ _ hb he]
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · exact Nat.pos_of_ne_zero hlen0
      · exact hlen64

theorem operandExponentCopiedMemory_size (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandExponentCopiedMemory I baseSize exponentSize modulusSize).size =
      operandModulusPtr baseSize exponentSize + 32 := by
  unfold operandExponentCopiedMemory
  by_cases hz : calldataSegmentAvail I (96 + baseSize) exponentSize = 0
  · rw [hz, byteArray_write_len_zero, operandBaseCopiedMemory_size _ _ _ _ hb he]
  · rw [← operandBaseCopiedMemory_size I baseSize exponentSize modulusSize hb he]
    apply write_size_of_inBounds_from
    · exact hz
    · unfold calldataSegmentAvail at hz ⊢
      omega
    · rw [operandBaseCopiedMemory_size _ _ _ _ hb he]
      unfold calldataSegmentAvail operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega

theorem operandCopiedMemory_size_ge (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    operandModulusPtr baseSize exponentSize + 32 ≤
      (operandCopiedMemory I baseSize exponentSize modulusSize).size := by
  have hsize := operandExponentCopiedMemory_size I baseSize exponentSize modulusSize hb he
  unfold operandCopiedMemory
  by_cases hz : calldataSegmentAvail I (96 + baseSize + exponentSize) modulusSize = 0
  · rw [hz, byteArray_write_len_zero, hsize]
  · rw [← hsize]
    rw [write_end_size_from]
    · omega
    · exact hz
    · unfold calldataSegmentAvail at hz ⊢
      omega

/-- The concrete copied operand buffer never extends beyond its logically allocated free
pointer.  Any uncopied calldata suffix remains represented by the EVM's implicit zero padding. -/
theorem operandCopiedMemory_size_le_freePtr (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandCopiedMemory I baseSize exponentSize modulusSize).size ≤
      operandFreePtr baseSize exponentSize modulusSize := by
  have hsize := operandExponentCopiedMemory_size I baseSize exponentSize modulusSize hb he
  unfold operandCopiedMemory
  by_cases hz : calldataSegmentAvail I (96 + baseSize + exponentSize) modulusSize = 0
  · rw [hz, byteArray_write_len_zero, hsize]
    have halloc := bytesHeaderAndSize_le_allocation modulusSize
    unfold operandFreePtr
    omega
  · rw [← hsize, write_end_size_from]
    · have havail : calldataSegmentAvail I (96 + baseSize + exponentSize) modulusSize ≤
          modulusSize := by
        unfold calldataSegmentAvail
        omega
      have halloc := bytesHeaderAndSize_le_allocation modulusSize
      unfold operandFreePtr
      omega
    · exact hz
    · unfold calldataSegmentAvail at hz ⊢
      omega

private theorem writePreservesDisjointWord
    (src mem : ByteArray) (srcAddr dest written read : Nat)
    (hsrc : written ≠ 0 → srcAddr + written ≤ src.size)
    (hwriteIn : written ≠ 0 → dest + written ≤ read →
      dest + written ≤ mem.size)
    (hreadIn : read + 32 ≤ mem.size)
    (hdest : dest ≤ mem.size)
    (hdisjoint : written ≠ 0 → dest + written ≤ read ∨ read + 32 ≤ dest) :
    (src.write srcAddr mem dest written).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  by_cases hz : written = 0
  · subst written
    rw [byteArray_write_len_zero]
  · rcases hdisjoint hz with habove | hbelow
    · exact write_read_above_gen_from src mem srcAddr dest written read 32 hz
        (hsrc hz) (hwriteIn hz habove) habove hreadIn (by decide) (by decide)
    · exact write_read_below_gen_from_extend src mem srcAddr dest written read 32 hz
        (hsrc hz) hdest hbelow hreadIn (by decide) (by decide)

/-- The final operand buffer retains Solidity's free-memory pointer.  This is the allocation
contract needed by both arithmetic callers after the three calldata copies. -/
theorem operandCopiedMemory_read64 (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding 64 32 =
      UInt256.toByteArray
        (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize)) := by
  have halloc :
      (operandAllocationMemory baseSize exponentSize modulusSize).readWithPadding 64 32 =
        UInt256.toByteArray
          (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize)) := by
    unfold operandAllocationMemory
    rw [storeBytesLength_read64]
    · exact setFreePtr_read64 (by
        rw [operandExponentMemory_size _ _ hb]
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
    · rw [setFreePtr_size (by
          rw [operandExponentMemory_size _ _ hb]
          unfold operandExponentPtr operandBasePtr bytesAllocationSize
          omega), operandExponentMemory_size _ _ hb]
      unfold operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · rw [setFreePtr_size (by
          rw [operandExponentMemory_size _ _ hb]
          unfold operandExponentPtr operandBasePtr bytesAllocationSize
          omega), operandExponentMemory_size _ _ hb]
      exact lt_usize _ (by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
  have hbase :
      (operandBaseCopiedMemory I baseSize exponentSize modulusSize).readWithPadding 64 32 =
        (operandAllocationMemory baseSize exponentSize modulusSize).readWithPadding 64 32 := by
    unfold operandBaseCopiedMemory
    apply writePreservesDisjointWord
    · intro hz
      have hoff : 96 < I.calldata.size := by
        by_contra h
        apply hz
        unfold baseCalldataAvail
        omega
      unfold baseCalldataAvail
      omega
    · intro _ hfalse
      unfold operandBasePtr at hfalse
      omega
    · rw [operandAllocationMemory_size _ _ _ hb he]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · rw [operandAllocationMemory_size _ _ _ hb he]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · intro _
      right
      unfold operandBasePtr
      omega
  have hexponent :
      (operandExponentCopiedMemory I baseSize exponentSize modulusSize).readWithPadding 64 32 =
        (operandBaseCopiedMemory I baseSize exponentSize modulusSize).readWithPadding 64 32 := by
    unfold operandExponentCopiedMemory
    apply writePreservesDisjointWord
    · intro hz
      have hoff : 96 + baseSize < I.calldata.size := by
        by_contra h
        apply hz
        unfold calldataSegmentAvail
        omega
      unfold calldataSegmentAvail
      omega
    · intro _ hfalse
      unfold operandExponentPtr operandBasePtr bytesAllocationSize at hfalse
      omega
    · rw [operandBaseCopiedMemory_size I baseSize exponentSize modulusSize hb he]
      simp only [operandModulusPtr, operandExponentPtr, operandBasePtr,
        bytesAllocationSize]
      omega
    · rw [operandBaseCopiedMemory_size I baseSize exponentSize modulusSize hb he]
      simp only [operandModulusPtr, operandExponentPtr, operandBasePtr,
        bytesAllocationSize]
      omega
    · intro _
      right
      unfold operandExponentPtr operandBasePtr bytesAllocationSize
      omega
  have hmodulus :
      (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding 64 32 =
        (operandExponentCopiedMemory I baseSize exponentSize modulusSize).readWithPadding 64 32 := by
    unfold operandCopiedMemory
    apply writePreservesDisjointWord
    · intro hz
      have hoff : 96 + baseSize + exponentSize < I.calldata.size := by
        by_contra h
        apply hz
        unfold calldataSegmentAvail
        omega
      unfold calldataSegmentAvail
      omega
    · intro _ hfalse
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize at hfalse
      omega
    · rw [operandExponentCopiedMemory_size I baseSize exponentSize modulusSize hb he]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · rw [operandExponentCopiedMemory_size I baseSize exponentSize modulusSize hb he]
    · intro _
      right
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
  exact hmodulus.trans (hexponent.trans (hbase.trans halloc))

/-- All three calldata payload copies preserve the base array's length header. -/
theorem operandCopiedMemory_readBaseLength (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
        operandBasePtr 32 = UInt256.toByteArray (UInt256.ofNat baseSize) := by
  have hmod :
      (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          operandBasePtr 32 =
        (operandExponentCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          operandBasePtr 32 := by
    unfold operandCopiedMemory
    apply writePreservesDisjointWord
    · intro hn
      unfold calldataSegmentAvail at hn ⊢
      omega
    · intro _ habove
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize at habove
      omega
    · rw [operandExponentCopiedMemory_size _ _ _ _ hb he]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · rw [operandExponentCopiedMemory_size _ _ _ _ hb he]
    · intro _
      right
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
  have hexp :
      (operandExponentCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          operandBasePtr 32 =
        (operandBaseCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          operandBasePtr 32 := by
    unfold operandExponentCopiedMemory
    apply writePreservesDisjointWord
    · intro hn
      unfold calldataSegmentAvail at hn ⊢
      omega
    · intro _ habove
      unfold operandExponentPtr operandBasePtr bytesAllocationSize at habove
      omega
    · rw [operandBaseCopiedMemory_size _ _ _ _ hb he]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · rw [operandBaseCopiedMemory_size _ _ _ _ hb he]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · intro _
      right
      unfold operandExponentPtr operandBasePtr bytesAllocationSize
      omega
  have hbase :
      (operandBaseCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          operandBasePtr 32 =
        (operandAllocationMemory baseSize exponentSize modulusSize).readWithPadding
          operandBasePtr 32 := by
    unfold operandBaseCopiedMemory
    apply writePreservesDisjointWord
    · intro hn
      unfold baseCalldataAvail at hn ⊢
      omega
    · intro _ habove
      omega
    · rw [operandAllocationMemory_size _ _ _ hb he]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · rw [operandAllocationMemory_size _ _ _ hb he]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · intro _
      right
      omega
  rw [hmod, hexp, hbase]
  exact operandAllocationMemory_readBaseLength baseSize exponentSize modulusSize hb he

/-- All three calldata payload copies preserve the exponent array's length header. -/
theorem operandCopiedMemory_readExponentLength (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandExponentPtr baseSize) 32 =
      UInt256.toByteArray (UInt256.ofNat exponentSize) := by
  have hmod :
      (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandExponentPtr baseSize) 32 =
        (operandExponentCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandExponentPtr baseSize) 32 := by
    unfold operandCopiedMemory
    apply writePreservesDisjointWord
    · intro hn
      unfold calldataSegmentAvail at hn ⊢
      omega
    · intro _ habove
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize at habove
      omega
    · rw [operandExponentCopiedMemory_size _ _ _ _ hb he]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · rw [operandExponentCopiedMemory_size _ _ _ _ hb he]
    · intro _
      right
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
  have hexp :
      (operandExponentCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandExponentPtr baseSize) 32 =
        (operandBaseCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandExponentPtr baseSize) 32 := by
    unfold operandExponentCopiedMemory
    apply writePreservesDisjointWord
    · intro hn
      unfold calldataSegmentAvail at hn ⊢
      omega
    · intro _ habove
      unfold operandExponentPtr operandBasePtr bytesAllocationSize at habove
      omega
    · rw [operandBaseCopiedMemory_size _ _ _ _ hb he]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · rw [operandBaseCopiedMemory_size _ _ _ _ hb he]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · intro _
      right
      omega
  have hbase :
      (operandBaseCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandExponentPtr baseSize) 32 =
        (operandAllocationMemory baseSize exponentSize modulusSize).readWithPadding
          (operandExponentPtr baseSize) 32 := by
    unfold operandBaseCopiedMemory
    apply writePreservesDisjointWord
    · intro hn
      unfold baseCalldataAvail at hn ⊢
      omega
    · intro _ _
      rw [operandAllocationMemory_size _ _ _ hb he]
      unfold baseCalldataAvail operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
    · rw [operandAllocationMemory_size _ _ _ hb he]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · rw [operandAllocationMemory_size _ _ _ hb he]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · intro _
      left
      unfold baseCalldataAvail operandExponentPtr operandBasePtr bytesAllocationSize
      omega
  rw [hmod, hexp, hbase]
  exact operandAllocationMemory_readExponentLength baseSize exponentSize modulusSize hb he

/-- All three calldata payload copies preserve the modulus array's length header. -/
theorem operandCopiedMemory_readModulusLength (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandModulusPtr baseSize exponentSize) 32 =
      UInt256.toByteArray (UInt256.ofNat modulusSize) := by
  have hmod :
      (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandModulusPtr baseSize exponentSize) 32 =
        (operandExponentCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandModulusPtr baseSize exponentSize) 32 := by
    unfold operandCopiedMemory
    apply writePreservesDisjointWord
    · intro hn
      unfold calldataSegmentAvail at hn ⊢
      omega
    · intro _ habove
      omega
    · rw [operandExponentCopiedMemory_size _ _ _ _ hb he]
    · rw [operandExponentCopiedMemory_size _ _ _ _ hb he]
    · intro _
      right
      omega
  have hexp :
      (operandExponentCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandModulusPtr baseSize exponentSize) 32 =
        (operandBaseCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandModulusPtr baseSize exponentSize) 32 := by
    unfold operandExponentCopiedMemory
    apply writePreservesDisjointWord
    · intro hn
      unfold calldataSegmentAvail at hn ⊢
      omega
    · intro _ _
      rw [operandBaseCopiedMemory_size _ _ _ _ hb he]
      unfold calldataSegmentAvail operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
    · rw [operandBaseCopiedMemory_size _ _ _ _ hb he]
    · rw [operandBaseCopiedMemory_size _ _ _ _ hb he]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · intro _
      left
      unfold calldataSegmentAvail operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
  have hbase :
      (operandBaseCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandModulusPtr baseSize exponentSize) 32 =
        (operandAllocationMemory baseSize exponentSize modulusSize).readWithPadding
          (operandModulusPtr baseSize exponentSize) 32 := by
    unfold operandBaseCopiedMemory
    apply writePreservesDisjointWord
    · intro hn
      unfold baseCalldataAvail at hn ⊢
      omega
    · intro _ _
      rw [operandAllocationMemory_size _ _ _ hb he]
      unfold baseCalldataAvail operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
    · rw [operandAllocationMemory_size _ _ _ hb he]
    · rw [operandAllocationMemory_size _ _ _ hb he]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · intro _
      left
      unfold baseCalldataAvail operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
  rw [hmod, hexp, hbase]
  exact operandAllocationMemory_readModulusLength baseSize exponentSize modulusSize hb he

/-- The second copied buffer is exactly the trusted padded exponent operand. -/
theorem operandExponentCopiedPayload (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandExponentCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandExponentPtr baseSize + 32) exponentSize =
      Model.readPadded I.calldata (96 + baseSize) exponentSize := by
  unfold operandExponentCopiedMemory calldataSegmentAvail
  apply copyIntoZeroInBounds
  · omega
  · rw [operandBaseCopiedMemory_size _ _ _ _ hb he]
    unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  · intro start len hwindow hlen64
    simpa [Nat.add_assoc] using
      operandBaseCopiedExponentPayloadZero I baseSize exponentSize modulusSize start len
        hb he hwindow hlen64

/-- Before the last copy, the modulus payload starts exactly at the concrete end of memory and is
therefore entirely zero under padded reads. -/
theorem operandExponentCopiedModulusPayloadZero (I : ExecutionEnv)
    (baseSize exponentSize modulusSize start len : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hwindow : start + len ≤ modulusSize) (hlen64 : len < 2 ^ 64) :
    (operandExponentCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandModulusPtr baseSize exponentSize + 32 + start) len =
      ffi.ByteArray.zeroes len := by
  by_cases hz : len = 0
  · subst len
    rw [byteArray_readWithPadding_zero, zeroes_zero (n := 0) (by rfl)]
  · apply readWithPadding_past_end
    · rw [operandExponentCopiedMemory_size _ _ _ _ hb he]
      omega
    · exact hlen64

/-- The exponent copy leaves the already-copied base operand unchanged. -/
theorem operandExponentCopiedBasePayload (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandExponentCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandBasePtr + 32) baseSize = Model.readPadded I.calldata 96 baseSize := by
  by_cases hbase0 : baseSize = 0
  · subst baseSize
    rw [byteArray_readWithPadding_zero]
    have hr := model_readPadded_size I.calldata 96 0
    rw [byteArray_eq_empty_of_size_eq_zero _ hr]
  · unfold operandExponentCopiedMemory
    by_cases hz : calldataSegmentAvail I (96 + baseSize) exponentSize = 0
    · rw [hz, byteArray_write_len_zero]
      exact operandBaseCopiedPayload I baseSize exponentSize modulusSize hb he
    · rw [write_read_below_gen_from_extend]
      · exact operandBaseCopiedPayload I baseSize exponentSize modulusSize hb he
      · exact hz
      · unfold calldataSegmentAvail at hz ⊢
        omega
      · rw [operandBaseCopiedMemory_size _ _ _ _ hb he]
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · rw [operandBaseCopiedMemory_size _ _ _ _ hb he]
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · exact Nat.pos_of_ne_zero hbase0
      · omega

/-- The final copied memory's base payload is the trusted padded base operand. -/
theorem operandCopiedBasePayload (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandBasePtr + 32) baseSize = Model.readPadded I.calldata 96 baseSize := by
  by_cases hbase0 : baseSize = 0
  · subst baseSize
    rw [byteArray_readWithPadding_zero]
    have hr := model_readPadded_size I.calldata 96 0
    rw [byteArray_eq_empty_of_size_eq_zero _ hr]
  · unfold operandCopiedMemory
    by_cases hz : calldataSegmentAvail I (96 + baseSize + exponentSize) modulusSize = 0
    · rw [hz, byteArray_write_len_zero]
      exact operandExponentCopiedBasePayload I baseSize exponentSize modulusSize hb he
    · rw [write_read_below_gen_from_extend]
      · exact operandExponentCopiedBasePayload I baseSize exponentSize modulusSize hb he
      · exact hz
      · unfold calldataSegmentAvail at hz ⊢
        omega
      · rw [operandExponentCopiedMemory_size _ _ _ _ hb he]
      · unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · rw [operandExponentCopiedMemory_size _ _ _ _ hb he]
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · exact Nat.pos_of_ne_zero hbase0
      · omega

/-- The final copied memory's exponent payload is the trusted padded exponent operand. -/
theorem operandCopiedExponentPayload (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandExponentPtr baseSize + 32) exponentSize =
      Model.readPadded I.calldata (96 + baseSize) exponentSize := by
  by_cases hexp0 : exponentSize = 0
  · subst exponentSize
    rw [byteArray_readWithPadding_zero]
    have hr := model_readPadded_size I.calldata (96 + baseSize) 0
    rw [byteArray_eq_empty_of_size_eq_zero _ hr]
  · unfold operandCopiedMemory
    by_cases hz : calldataSegmentAvail I (96 + baseSize + exponentSize) modulusSize = 0
    · rw [hz, byteArray_write_len_zero]
      exact operandExponentCopiedPayload I baseSize exponentSize modulusSize hb he
    · rw [write_read_below_gen_from_extend]
      · exact operandExponentCopiedPayload I baseSize exponentSize modulusSize hb he
      · exact hz
      · unfold calldataSegmentAvail at hz ⊢
        omega
      · rw [operandExponentCopiedMemory_size _ _ _ _ hb he]
      · unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · rw [operandExponentCopiedMemory_size _ _ _ _ hb he]
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · exact Nat.pos_of_ne_zero hexp0
      · omega

/-- The final copied memory's modulus payload is the trusted padded modulus operand. -/
theorem operandCopiedModulusPayload (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandModulusPtr baseSize exponentSize + 32) modulusSize =
      Model.readPadded I.calldata (96 + baseSize + exponentSize) modulusSize := by
  have hsize := operandExponentCopiedMemory_size I baseSize exponentSize modulusSize hb he
  unfold operandCopiedMemory calldataSegmentAvail
  rw [← hsize]
  exact copyIntoZeroAtEnd I.calldata
    (operandExponentCopiedMemory I baseSize exponentSize modulusSize)
    (96 + baseSize + exponentSize) modulusSize
    (by rw [hsize]; unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    (by omega)

private theorem copiedPayloadWindow {mem src : ByteArray} {dest off width start len : Nat}
    (hfull : mem.readWithPadding dest width = Model.readPadded src off width)
    (hdest : dest < 2 ^ 64) (hwidth : width < 2 ^ 64)
    (hshift : dest + start < 2 ^ 64) (hlen : len < 2 ^ 64)
    (hwindow : start + len ≤ width) :
    mem.readWithPadding (dest + start) len = Model.readPadded src (off + start) len := by
  have h := congrArg (fun b : ByteArray => b.extract start (start + len)) hfull
  dsimp only at h
  rw [readWithPadding_window mem dest width start len hdest hwidth hshift hlen hwindow,
    model_readPadded_window src off width start len hwindow] at h
  exact h

/-- Every subwindow of the copied base buffer agrees with the correspondingly shifted trusted
padded calldata read. -/
theorem operandCopiedBaseWindow (I : ExecutionEnv)
    (baseSize exponentSize modulusSize start len : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hwindow : start + len ≤ baseSize) :
    (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandBasePtr + 32 + start) len =
      Model.readPadded I.calldata (96 + start) len := by
  simpa [Nat.add_assoc] using copiedPayloadWindow
    (operandCopiedBasePayload I baseSize exponentSize modulusSize hb he)
    (by unfold operandBasePtr; omega) (by omega)
    (by unfold operandBasePtr; omega) (by omega) hwindow

/-- Every subwindow of the copied exponent buffer agrees with the correspondingly shifted trusted
padded calldata read. -/
theorem operandCopiedExponentWindow (I : ExecutionEnv)
    (baseSize exponentSize modulusSize start len : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hwindow : start + len ≤ exponentSize) :
    (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandExponentPtr baseSize + 32 + start) len =
      Model.readPadded I.calldata (96 + baseSize + start) len := by
  simpa [Nat.add_assoc] using copiedPayloadWindow
    (operandCopiedExponentPayload I baseSize exponentSize modulusSize hb he)
    (by unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega) (by omega)
    (by unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    (by omega) hwindow

/-- Every subwindow of the copied modulus buffer agrees with the correspondingly shifted trusted
padded calldata read. -/
theorem operandCopiedModulusWindow (I : ExecutionEnv)
    (baseSize exponentSize modulusSize start len : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hwindow : start + len ≤ modulusSize) :
    (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandModulusPtr baseSize exponentSize + 32 + start) len =
      Model.readPadded I.calldata (96 + baseSize + exponentSize + start) len := by
  simpa [Nat.add_assoc] using copiedPayloadWindow
    (operandCopiedModulusPayload I baseSize exponentSize modulusSize hb he hm)
    (by unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    (by omega)
    (by unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    (by omega) hwindow

/-- Big-endian decoding of the prepared base buffer is the trusted base operand. -/
theorem operandCopiedBaseValue (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    fromByteArrayBigEndian
        ((operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandBasePtr + 32) baseSize) =
      Model.bytesToNatPadded I.calldata 96 baseSize := by
  rw [operandCopiedBasePayload I baseSize exponentSize modulusSize hb he]
  unfold Model.bytesToNatPadded
  exact (bytesToBigEndianNat_eq_fromByteArrayBigEndian _).symm

/-- Big-endian decoding of the prepared exponent buffer is the trusted exponent operand. -/
theorem operandCopiedExponentValue (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) :
    fromByteArrayBigEndian
        ((operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandExponentPtr baseSize + 32) exponentSize) =
      Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize := by
  rw [operandCopiedExponentPayload I baseSize exponentSize modulusSize hb he]
  unfold Model.bytesToNatPadded
  exact (bytesToBigEndianNat_eq_fromByteArrayBigEndian _).symm

/-- Big-endian decoding of the prepared modulus buffer is the trusted modulus operand. -/
theorem operandCopiedModulusValue (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    fromByteArrayBigEndian
        ((operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandModulusPtr baseSize exponentSize + 32) modulusSize) =
      Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize := by
  rw [operandCopiedModulusPayload I baseSize exponentSize modulusSize hb he hm]
  unfold Model.bytesToNatPadded
  exact (bytesToBigEndianNat_eq_fromByteArrayBigEndian _).symm

private theorem operandCopyActive {words dst avail : Nat}
    (hwords : words < UInt256.size) (hend : dst + 32 + avail ≤ 32 * words) :
    UInt256.ofNat
      (MachineState.M (UInt256.ofNat words).toNat (dst + 32) avail) =
      UInt256.ofNat words := by
  rw [UInt256.toNat_ofNat_of_lt hwords]
  unfold MachineState.M
  by_cases hz : avail = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    have hceil : (dst + 32 + avail + 31) / 32 ≤ words := by omega
    rw [max_eq_left hceil]

private theorem operandCopyCallDecodes :
    [decode runtimeBytecode ⟨149⟩, decode runtimeBytecode ⟨150⟩,
      decode runtimeBytecode ⟨151⟩, decode runtimeBytecode ⟨152⟩,
      decode runtimeBytecode ⟨155⟩,
      decode runtimeBytecode ⟨156⟩, decode runtimeBytecode ⟨157⟩,
      decode runtimeBytecode ⟨158⟩, decode runtimeBytecode ⟨161⟩,
      decode runtimeBytecode ⟨162⟩, decode runtimeBytecode ⟨163⟩,
      decode runtimeBytecode ⟨164⟩, decode runtimeBytecode ⟨167⟩,
      decode runtimeBytecode ⟨168⟩, decode runtimeBytecode ⟨169⟩,
      decode runtimeBytecode ⟨172⟩] =
    [some (.JUMPDEST, .none), some (.SWAP10, .none), some (.DUP9, .none),
      some (.Push .PUSH2, some (⟨836⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.DUP8, .none),
      some (.Push .PUSH2, some (⟨924⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.DUP6, .none),
      some (.Push .PUSH2, some (⟨924⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.Push .PUSH2, some (⟨1183⟩, 2)),
      some (.JUMP, .none)] := by
  native_decide

def operandCopyGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  60 + baseCalldataCopyGas I baseSize +
    calldataSegmentGas I (96 + baseSize) exponentSize +
    calldataSegmentGas I (96 + baseSize + exponentSize) modulusSize

def operandSetupGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  operandAllocationGas baseSize exponentSize modulusSize +
    operandCopyGas I baseSize exponentSize modulusSize

/-- Complete exact operand-buffer preparation.  At PC 1183 the stack holds pointers to the base,
exponent, and modulus arrays; each payload is the trusted zero-padded calldata segment. -/
theorem prepareOperandsExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat} {lastByte : UInt256}
    {tail : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hcalldata : I.calldata.size < 2 ^ 64) (htail : tail.length ≤ 1003)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨105⟩
      (lastByte :: UInt256.ofNat (96 + baseSize + exponentSize) ::
        UInt256.ofNat exponentSize :: UInt256.ofNat (96 + baseSize) ::
        UInt256.ofNat baseSize :: UInt256.ofNat modulusSize :: tail)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1183⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨173⟩ :: tail)
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc
      (k + 292 + baseCalldataCopySteps I baseSize +
        calldataSegmentSteps I (96 + baseSize) exponentSize +
        calldataSegmentSteps I (96 + baseSize + exponentSize) modulusSize)
      (C + operandSetupGas I baseSize exponentSize modulusSize) := by
  have hd := operandCopyCallDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8,
    hd9, hd10, hd11, hd12, hd13, hd14, hd15⟩
  have hwords : operandModulusWords baseSize exponentSize modulusSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandModulusWords baseSize exponentSize modulusSize ≤ 103 by
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
    decide
  have hbaseEnd : operandBasePtr + 32 + baseCalldataAvail I baseSize ≤
      32 * operandModulusWords baseSize exponentSize modulusSize := by
    unfold baseCalldataAvail operandBasePtr operandModulusWords operandExponentWords
      operandBaseWords bytesAllocationWords
    have havail := min_le_left baseSize (I.calldata.size - 96)
    omega
  have hexpEnd : operandExponentPtr baseSize + 32 +
      calldataSegmentAvail I (96 + baseSize) exponentSize ≤
      32 * operandModulusWords baseSize exponentSize modulusSize := by
    have havail := min_le_left exponentSize (I.calldata.size - (96 + baseSize))
    have hround := bytesSize_le_roundedPayload exponentSize
    rw [operandExponentPtr_eq]
    unfold calldataSegmentAvail operandModulusWords operandExponentWords bytesAllocationWords
    omega
  have hmodEnd : operandModulusPtr baseSize exponentSize + 32 +
      calldataSegmentAvail I (96 + baseSize + exponentSize) modulusSize ≤
      32 * operandModulusWords baseSize exponentSize modulusSize := by
    unfold calldataSegmentAvail operandModulusWords
    rw [operandModulusPtr_eq]
    unfold bytesAllocationWords
    have havail := min_le_left modulusSize
      (I.calldata.size - (96 + baseSize + exponentSize))
    have hround := bytesSize_le_roundedPayload modulusSize
    omega
  have hbaseActive := operandCopyActive hwords hbaseEnd
  have hexpActive := operandCopyActive hwords hexpEnd
  have hmodActive := operandCopyActive hwords hmodEnd
  have rd149 := allocateOperandsExact hb he hm hcalldata htail rd0
  have rd836 := evm_run rd149 with [known jumpdest hd0, known swap10 hd1,
    known dup9 hd2, known push2 hd3 ⟨836⟩, known jump hd4 jumpDest_836]
  have rd156 := baseCalldataCopyExact hcalldata hb
    (by unfold operandBasePtr; omega) hbaseActive
    (by simp only [List.length_cons]; omega) jumpDest_156 rd836
  have rd924e := evm_run rd156 with [known jumpdest hd5, known dup8 hd6,
    known push2 hd7 ⟨924⟩, known jump hd8 jumpDest_924]
  have rd162 := calldataSegmentCopyExact hcalldata
    (by omega : 96 + baseSize < 2 ^ 64) he
    (by unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    hexpActive (by simp only [List.length_cons]; omega) jumpDest_162 rd924e
  have rd924m := evm_run rd162 with [known jumpdest hd9, known dup6 hd10,
    known push2 hd11 ⟨924⟩, known jump hd12 jumpDest_924]
  have rd168 := calldataSegmentCopyExact
    (tail := UInt256.ofNat operandBasePtr ::
      UInt256.ofNat (operandExponentPtr baseSize) ::
      UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: ⟨173⟩ :: tail)
    hcalldata
    (by omega : 96 + baseSize + exponentSize < 2 ^ 64) hm
    (by unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    hmodActive (by simp only [List.length_cons]; omega) jumpDest_operand168 rd924m
  have rd1183 := evm_run rd168 with [known jumpdest hd13,
    known push2 hd14 ⟨1183⟩, known jump hd15 jumpDest_1183]
  have rd1183' := rd1183.withIndices
    (k' := k + 292 + baseCalldataCopySteps I baseSize +
      calldataSegmentSteps I (96 + baseSize) exponentSize +
      calldataSegmentSteps I (96 + baseSize + exponentSize) modulusSize)
    (C' := C + operandSetupGas I baseSize exponentSize modulusSize)
    (by omega)
    (by simp [operandSetupGas, operandCopyGas]; omega)
  simpa [operandBaseCopiedMemory, operandExponentCopiedMemory, operandCopiedMemory,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rd1183'

end Modexp
