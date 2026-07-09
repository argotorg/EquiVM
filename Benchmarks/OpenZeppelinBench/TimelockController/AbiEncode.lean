import Benchmarks.OpenZeppelinBench.TimelockController.Return
import Benchmarks.OpenZeppelinBench.TimelockController.Storage

/-!
# OpenZeppelin TimelockController ABI-encode-in-memory reconciliation (for `hashOperation`)

Reusable pieces connecting the EVM `abi_encode_tuple(address,uint256,bytes,bytes32,bytes32)`
encoder (runtime @5933) to the Solm spec `ABI.encodeReturnValues? [addr,uint256,bytes,bytes32,bytes32]`.

LIBRARY CANDIDATEs: the `tlcAbiEnc…` lemmas below generalize to any solc tuple encoder with a single
dynamic `bytes` member and a `0xa0` head offset.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-! ## Pure ABI-encode characterization of the `hashOperation` tuple -/

-- LIBRARY CANDIDATE: `Reasoning.ABI` — encode of `[addr,uint256,bytes,bytes32,bytes32]` (0xa0 head).
/-- `encodeReturnValues?` of the `hashOperation` argument tuple: the canonical
    head `target ‖ value ‖ 0xa0 ‖ predecessor ‖ salt` followed by the tail `len ‖ padded data`. -/
theorem tlcAbiEncHashOperation (a : EVM.Address) (i : Int) (hi : 0 ≤ i ∧ i < 2 ^ 256)
    (ba : ByteArray) (pbs sbs : List UInt8) (hp : pbs.length = 32) (hs : sbs.length = 32) :
    ABI.encodeReturnValues? [addr, uint256, bytesTy, bytes32, bytes32]
        [.address a, .int i, .bytes ba,
          .fixedBytes ⟨31, by decide⟩ pbs, .fixedBytes ⟨31, by decide⟩ sbs]
      = some ⟨((EVM.word a).toBytesBE ++ (EVM.word i.toNat).toBytesBE
            ++ ABI.natBytes 160 ++ pbs ++ sbs
            ++ (ABI.natBytes ba.size ++ ABI.padRightToWord ba.toList)).toArray⟩ := by
  have hlt : i < ↑(EVM.twoPow 256) := by
    rw [show EVM.twoPow 256 = 2 ^ 256 from rfl]; exact_mod_cast hi.2
  simp [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
    encodeABIValue?, encodeABIWord?, isDynamicABIType, staticABIEncodedSize?,
    addr, uint256, uint256Int, bytesTy, bytes32, bytes32Width, natBytes, zeroBytes,
    hlt, hi.1, hp, hs, List.append_assoc]

/-- The canonical `hashOperation` preimage bytes as a plain `List UInt8`
    (`target ‖ value ‖ 0xa0 ‖ predecessor ‖ salt ‖ len ‖ padded data`). This is the exact byte
    string the EVM encoder writes to `mem[0xa0 ..]` and hands to `KECCAK256`. -/
def tlcAbiEncHashOperationBytes (a : EVM.Address) (n : Nat) (ba : ByteArray)
    (pbs sbs : List UInt8) : List UInt8 :=
  (EVM.word a).toBytesBE ++ (EVM.word n).toBytesBE ++ ABI.natBytes 160 ++ pbs ++ sbs
    ++ (ABI.natBytes ba.size ++ ABI.padRightToWord ba.toList)

-- LIBRARY CANDIDATE: the encoded byte length `= 5·32 (head) + 32 (len word) + roundUp₃₂(|data|)`.
/-- The canonical preimage length is `192 + paddedSize |data|`, i.e. the second (length) operand of
    the `KECCAK256` opcode at runtime @2354 (`endPtr − 0xa0`). -/
theorem tlcAbiEncHashOperationBytes_length (a : EVM.Address) (n : Nat) (ba : ByteArray)
    (pbs sbs : List UInt8) (hp : pbs.length = 32) (hs : sbs.length = 32) :
    (tlcAbiEncHashOperationBytes a n ba pbs sbs).length = 192 + ABI.paddedSize ba.size := by
  have hw : ∀ w : EVM.Word, (EVM.Word.toBytesBE w).length = 32 := fun w => by
    simpa using word_toBytesBE_toByteArray_size w
  have hbalen : ba.toList.length = ba.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hpad : (ABI.padRightToWord ba.toList).length = ABI.paddedSize ba.size := by
    unfold ABI.padRightToWord ABI.zeroBytes
    rw [List.length_append, List.length_replicate, hbalen]
    have : ba.size ≤ ABI.paddedSize ba.size := by unfold ABI.paddedSize; omega
    omega
  simp only [tlcAbiEncHashOperationBytes, List.length_append, hw, hp, hs, ABI.natBytes, hpad]
  omega

end OpenZeppelinBench.TimelockController
