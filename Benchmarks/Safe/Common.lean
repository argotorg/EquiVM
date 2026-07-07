import Benchmarks.Safe.Bytecode
import Reasoning.ABI
import Reasoning.Theory
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Memory
import Reasoning.Storage
import Reasoning.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# Safe shared proof foundation

Contract-wide selector notation and constants for the optimized Safe runtime.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Safe

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev safeSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def safeSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xff, 0xa1, 0xad, 0x74]⟩  -- VERSION()
  | 1 => ⟨#[0x0d, 0x58, 0x2f, 0x13]⟩  -- addOwnerWithThreshold(address,uint256)
  | 2 => ⟨#[0xd4, 0xd9, 0xbd, 0xcd]⟩  -- approveHash(bytes32)
  | 3 => ⟨#[0x7d, 0x83, 0x29, 0x74]⟩  -- approvedHashes(address,bytes32)
  | 4 => ⟨#[0x69, 0x4e, 0x80, 0xc3]⟩  -- changeThreshold(uint256)
  | 5 => ⟨#[0x12, 0xfb, 0x68, 0xe0]⟩  -- checkNSignatures(bytes32,bytes,bytes,uint256)
  | 6 => ⟨#[0x1f, 0xca, 0xc7, 0xf3]⟩  -- checkNSignatures(address,bytes32,bytes,uint256)
  | 7 => ⟨#[0x93, 0x4f, 0x3a, 0x11]⟩  -- checkSignatures(bytes32,bytes,bytes)
  | 8 => ⟨#[0xf8, 0x55, 0x43, 0x8b]⟩  -- checkSignatures(address,bytes32,bytes)
  | 9 => ⟨#[0xe0, 0x09, 0xcf, 0xde]⟩  -- disableModule(address,address)
  | 10 => ⟨#[0xf6, 0x98, 0xda, 0x25]⟩ -- domainSeparator()
  | 11 => ⟨#[0x61, 0x0b, 0x59, 0x25]⟩ -- enableModule(address)
  -- execTransaction(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,bytes)
  | 12 => ⟨#[0x6a, 0x76, 0x12, 0x02]⟩
  | 13 => ⟨#[0x46, 0x87, 0x21, 0xa7]⟩ -- execTransactionFromModule(address,uint256,bytes,uint8)
  -- execTransactionFromModuleReturnData(address,uint256,bytes,uint8)
  | 14 => ⟨#[0x52, 0x29, 0x07, 0x3f]⟩
  | 15 => ⟨#[0xcc, 0x2f, 0x84, 0x52]⟩ -- getModulesPaginated(address,uint256)
  | 16 => ⟨#[0xa0, 0xe6, 0x7e, 0x2b]⟩ -- getOwners()
  | 17 => ⟨#[0x56, 0x24, 0xb2, 0x5b]⟩ -- getStorageAt(uint256,uint256)
  | 18 => ⟨#[0xe7, 0x52, 0x35, 0xb8]⟩ -- getThreshold()
  -- getTransactionHash(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,uint256)
  | 19 => ⟨#[0xd8, 0xd1, 0x1f, 0x78]⟩
  | 20 => ⟨#[0x2d, 0x9a, 0xd5, 0x3d]⟩ -- isModuleEnabled(address)
  | 21 => ⟨#[0x2f, 0x54, 0xbf, 0x6e]⟩ -- isOwner(address)
  | 22 => ⟨#[0xaf, 0xfe, 0xd0, 0xe0]⟩ -- nonce()
  | 23 => ⟨#[0xf8, 0xdc, 0x5d, 0xd9]⟩ -- removeOwner(address,address,uint256)
  | 24 => ⟨#[0xf0, 0x8a, 0x03, 0x23]⟩ -- setFallbackHandler(address)
  | 25 => ⟨#[0xe1, 0x9a, 0x9d, 0xd9]⟩ -- setGuard(address)
  | 26 => ⟨#[0xe0, 0x68, 0xdf, 0x37]⟩ -- setModuleGuard(address)
  -- setup(address[],uint256,address,bytes,address,address,uint256,address)
  | 27 => ⟨#[0xb6, 0x3e, 0x80, 0x0d]⟩
  | 28 => ⟨#[0x5a, 0xe6, 0xbd, 0x37]⟩ -- signedMessages(bytes32)
  | 29 => ⟨#[0xb4, 0xfa, 0xba, 0x09]⟩ -- simulateAndRevert(address,bytes)
  | _ => ⟨#[0xe3, 0x18, 0xb5, 0x2b]⟩  -- swapOwner(address,address,address)

-- LIBRARY CANDIDATE: reversed write-order variant of `Reasoning.Memory.twoWordHashMem_read0_64`.
set_option maxHeartbeats 800000 in
theorem wordAt0Mem_after_wordAt32Mem_read0_64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (wordAt0Mem key (wordAt32Mem slot mem)).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [wordAt0Mem_size_96 key (wordAt32Mem_size_96 slot hmem)]; omega)]
  have hleft :
      (wordAt0Mem key (wordAt32Mem slot mem)).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [wordAt0Mem_size_96 key (wordAt32Mem_size_96 slot hmem)]; omega),
      wordAt0Mem_read0 key (wordAt32Mem slot mem)]
  have hright :
      (wordAt0Mem key (wordAt32Mem slot mem)).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [wordAt0Mem_size_96 key (wordAt32Mem_size_96 slot hmem)]; omega)]
    unfold wordAt0Mem
    rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
        (by rw [wordAt32Mem_size_96 slot hmem]; omega) (by omega)
        (by rw [wordAt32Mem_size_96 slot hmem]; omega)]
    unfold wordAt32Mem
    rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
      toByteArray_extract_all]
  rw [show (wordAt0Mem key (wordAt32Mem slot mem)).extract 0 64 =
      (wordAt0Mem key (wordAt32Mem slot mem)).extract 0 32 ++
        (wordAt0Mem key (wordAt32Mem slot mem)).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

-- LIBRARY CANDIDATE: standard preservation of the solc free-pointer word by a word write at 0.
theorem wordAt0Mem_read64 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (wordAt0Mem word mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega)
      (by norm_num) (by norm_num [hmem])]
  exact hread64

-- LIBRARY CANDIDATE: standard preservation of the solc free-pointer word by a word write at 32.
theorem wordAt32Mem_read64 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (wordAt32Mem word mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size]) (by omega)
      (by norm_num) (by norm_num [hmem])]
  exact hread64

end Benchmarks.Safe
