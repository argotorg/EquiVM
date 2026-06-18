import Examples.ERC20.Bytecode
import Reasoning.ABIDecode
import Reasoning.Dispatch
import Reasoning.Solc
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace ERC20

/-! ## ERC20-local storage and ABI helpers -/

/-- `ByteArray` `==` reflects equality. -/
theorem erc20ByteArray_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  apply ByteArray.ext
  exact eq_of_beq (by simpa [BEq.beq, ByteArray.instBEq] using h)

/-- The little-endian serialization used by `storageLocLoad` round-trips for a full EVM word. -/
theorem fromBytesLE_roundtrip (w : UInt256) :
    fromBytes' (EVM.Word.toBytesLEWithSizeProof w).1 = w.toNat := by
  show fromBytes' (toBytes' w.val ++ List.replicate (32 - (toBytes' w.val).length) 0) = w.toNat
  rw [fromBytes'_append_zeros, fromBytes'_toBytes']; rfl

/-- Loading an ERC20 full-slot `uint256` location is the source-level integer value of the same word. -/
theorem erc20StorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (erc20Uint256Loc slot)
      = .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  have htake :
      (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 0 (32 : Fin 33).val =
        (EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1 := by
    rw [List.extract_eq_take_drop, List.drop_zero]
    exact List.take_of_length_le (by
      rw [(EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
      norm_num)
  unfold storageLocLoad erc20Uint256Loc wordToElem
  simp only [uint256Int, Fin.val_zero, Nat.zero_add]
  congr
  rw [htake, fromBytesLE_roundtrip]
  rfl

/-- ABI-encoding a Solm `uint256` return value produces exactly the EVM's returned word bytes. -/
theorem erc20Uint256ReturnEncoding (v : UInt256) :
    encodeReturnValue? uint256 (.int (Int.ofNat v.toNat)) =
      some (UInt256.toByteArray v) := by
  have hlt : Int.ofNat v.toNat < Int.ofNat (EVM.twoPow 256) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_lt, EVM.twoPow]
    exact v.val.isLt
  have hword : EVM.word v.toNat = v := by
    show UInt256.ofNat v.toNat = v
    exact u256_ofNat_toNat v
  have hval : encodeABIValue? uint256 (.int (Int.ofNat v.toNat))
                = some (EVM.Word.toBytesBE v) := by
    have hltNat : v.toNat < EVM.twoPow 256 := by
      change v.val.val < EVM.twoPow 256
      exact v.val.isLt
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hltNat]
  have hdyn : isDynamicABIType uint256 = false := rfl
  have hhead : abiTupleHeadSize? [uint256] = some 32 := by
    simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, uint256, bind,
      Option.bind]
    decide
  rw [toByteArray_eq_toBytesBE,
    show encodeReturnValue? uint256 (.int (Int.ofNat v.toNat))
        = encodeReturnValues? [uint256] [.int (Int.ofNat v.toNat)] from rfl]
  simp only [encodeReturnValues?, encodeABIValues?, hhead, encodeABIValuesFrom?, hval, hdyn,
    bind, Option.bind, if_false, Bool.false_eq_true, List.nil_append, List.append_nil]

/-- The shared solc return wrapper computes the fixed one-word return length. -/
theorem erc20SubRet32_toNat :
    (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 := by
  decide

/-! ## Single-address calldata decoding -/

theorem decodeScalarWords_address_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat)] := by
  change decodeScalarWords? [.elem .address] bytes 0 =
    some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat)]
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon)]
  rfl

theorem decodeScalarWords_address_none_noncanon {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr] bytes 0 = none := by
  change decodeScalarWords? [.elem .address] bytes 0 = none
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc)]
  simp only [Option.bind, bind]

theorem decodeScalarWords_address_none_short {bytes : List UInt8}
    (hshort : bytes.length < 32) :
    decodeScalarWords? [addr] bytes 0 = none := by
  change decodeScalarWords? [.elem .address] bytes 0 = none
  simp only [decodeScalarWords?]
  have htake0n : ¬ (bytes.take 32).length = 32 := by
    rw [List.length_take]
    omega
  rw [decodeScalarWord_address_none_short (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem decodeCalldata_address_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x] [addr] cd =
      some ((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [addr]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_ok (bytes := cd.toList.drop 4) htake4
    (by rw [hword4]; exact hcanon)]
  change decodeCalldata.insertValues [x]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4]

theorem decodeCalldata_address_none_noncanon {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x] [addr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [addr]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_none_noncanon (bytes := cd.toList.drop 4) htake4
    (by rw [hword4]; exact hnc)]

theorem decodeCalldata_address_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldata [x] [addr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [addr]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_address_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]
    omega)]

theorem decodeCalldata_address_none_huge {cd : ByteArray} {x : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x] [addr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [addr]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

end ERC20

namespace Reasoning.Reach

/-- ERC20's solc `cleanup_t_uint256` identity routine at pc 1894. -/
theorem RD.erc20Routine0766 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {v ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨1894⟩ (v :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J erc20Bytecode 0).contains ret = true) (hov : R.length + 4 ≤ 1024) :
    RD erc20Bytecode ee g s0 ret (v :: R) mem aw rdata acc (k + 9) (C + 27) :=
  evm_run h with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop,
    jump hret ]

/-- ERC20's shared solc ABI encoder for one `uint256` word at pc 2073. -/
theorem RD.erc20RoutineEncodeUint256 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨2073⟩ (⟨128⟩ :: val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hret : (D_J erc20Bytecode 0).contains ret = true) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD erc20Bytecode ee g s0 ret ((⟨128⟩ + ⟨32⟩) :: R)
      (solcReturnMem val) (UInt256.ofNat 5) rdata acc k' C' := by
  let rd := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨2092⟩, push0, dup4, add, dup5, push2 ⟨2058⟩,
    jump (by jump_dest),
    jumpdest, push2 ⟨2067⟩, dup2, push2 ⟨1894⟩,
    jump (by jump_dest),
    raw erc20Routine0766 (by jump_dest) (by evm_ov),
    jumpdest, dup3,
    raw mstore 6 (solcReturnMem val) (UInt256.ofNat 5) (by decide) mem_cost
      (by rw [show ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    pop, pop,
    jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop,
    jump hret ]
  exact ⟨_, _, rd⟩

end Reasoning.Reach
