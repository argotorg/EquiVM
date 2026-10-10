import Benchmarks.Morpho.MetaMorphoV1_1.EcrecoverOutput
import Benchmarks.Morpho.MetaMorphoV1_1.PackedSource
import Benchmarks.EAS.Attester.WordSequenceMemory

/-! The four input words and the canonical address returned by signature recovery. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def ecrecoverInput (hash sigV sigR sigS : UInt256) : ByteArray :=
  wordBytes [hash, sigV, sigR, sigS]

def ecrecoverSigner (out : ByteArray) : AccountAddress :=
  AccountAddress.ofNat (uInt256OfByteArray out).toNat

theorem ecrecoverSigner_empty : ecrecoverSigner ByteArray.empty = AccountAddress.ofNat 0 := rfl

theorem ecrecoverAddressDecode {out : ByteArray} (hsize : out.size = 32)
    (hcanon : (uInt256OfByteArray out).toNat < 2 ^ 160) :
    decodeReturnValue? abiAddress out = some (.address (ecrecoverSigner out)) := by
  have hlen : out.toList.length = 32 := by
    rw [byteArray_toList_eq, Array.length_toList]; exact hsize
  have hword : ABI.bytesToWord (out.toList.take 32) = uInt256OfByteArray out := by
    rw [bytesToWord_take32_eq_extract0_32, ← hsize, byteArray_extract_self]
    exact (uInt256OfByteArray_eq out).symm
  have hd := decodeScalarWords_address_ok (bytes := out.toList)
    (by rw [List.length_take, hlen, Nat.min_self]) (by rw [hword]; exact hcanon)
  rw [hword] at hd
  rw [decodeReturnValue?, decodeReturnValues_scalarWords_eq (by decide),
    if_neg (by rw [hlen]; decide), hd]
  rfl

theorem ecrecoverInputSource {cfg : Config} {frame : Frame} {evm : State}
    {hash sigV sigR sigS : UInt256} {hashExpr vExpr rExpr sExpr : Expr}
    (hh : evalExpr? cfg frame evm hashExpr = .ok (wordBytes32Value hash))
    (hv : evalExpr? cfg frame evm vExpr = .ok (uint256Value sigV))
    (hr : evalExpr? cfg frame evm rExpr = .ok (wordBytes32Value sigR))
    (hs : evalExpr? cfg frame evm sExpr = .ok (wordBytes32Value sigS)) :
    evalExpr? cfg frame evm (.abiEncodePacked
      [(abiBytes32, hashExpr), (abiUInt256, vExpr), (abiBytes32, rExpr), (abiBytes32, sExpr)]) =
      .ok (.bytes (ecrecoverInput hash sigV sigR sigS)) := by
  have hpack := evalExpr_packed (evalPackedArgs_cons hh (encodePacked_bytes32 hash)
    (evalPackedArgs_cons hv (encodePacked_uint256 sigV)
      (evalPackedArgs_cons hr (encodePacked_bytes32 sigR)
        (evalPackedArgs_cons (args := []) (tail := []) hs (encodePacked_bytes32 sigS)
          (by simp only [evalPackedArgs?, pure])))))
  simpa only [ecrecoverInput, wordBytes, List.append_nil, List.toByteArray_append,
    word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.append_empty] using hpack

end Benchmarks.Morpho.MetaMorphoV1_1
