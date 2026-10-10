import Benchmarks.CompoundIII.Comet.ScalarTupleDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

abbrev ThreeAddressUintCalldataValid (I : ExecutionEnv) : Prop :=
  132 ≤ I.calldata.size ∧ I.calldata.size < 2^255 + 4 ∧
    (calldataWord I.calldata 4).toNat < EVM.addressModulus ∧
    (calldataWord I.calldata 36).toNat < EVM.addressModulus ∧
    (calldataWord I.calldata 68).toNat < EVM.addressModulus

-- LIBRARY CANDIDATE: decode an address word at a fixed offset in calldata's argument area.
theorem decodeScalarWord_calldata_address (cd : ByteArray) (n : Nat)
    (hn : 4 + n + 32 ≤ cd.size) (h64 : 4 + n < 2^64) :
    decodeScalarWord? (.elem .address) (cd.toList.drop 4) n =
      if (calldataWord cd (4+n)).toNat < EVM.addressModulus then
        some (.address (AccountAddress.ofNat (calldataWord cd (4+n)).toNat), n+32)
      else none := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have ht : (((cd.toList.drop 4).drop n).take 32).length = 32 := by
    rw [List.drop_drop, List.length_take, List.length_drop, hlen]; omega
  rw [decodeScalarWord_address_result ht]
  have hw : ABI.bytesToWord (((cd.toList.drop 4).drop n).take 32) = calldataWord cd (4+n) := by
    rw [List.drop_drop]
    exact decode_word_at_eq cd (4+n) hn h64
  rw [hw]

-- GENERALIZES the library's two-address-plus-uint256 decoder by one address field.
theorem decodeCalldata_threeAddressUint (I : ExecutionEnv) (x y z w : Ident)
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata [x,y,z,w] [.elem .address, .elem .address, .elem .address, abiUInt256] I.calldata =
      if ThreeAddressUintCalldataValid I then
        some (((((∅ : Store).insert x (.address (AccountAddress.ofNat
          (calldataWord I.calldata 4).toNat))).insert y (.address (AccountAddress.ofNat
          (calldataWord I.calldata 36).toNat))).insert z (.address (AccountAddress.ofNat
          (calldataWord I.calldata 68).toNat))).insert w (.int (calldataWord I.calldata 100).toNat))
      else none := by
  have hlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (by decide), if_neg (by omega)]
  by_cases hhi : I.calldata.size < 2^255+4
  · rw [if_neg (by rintro ⟨_, he⟩; rw [List.length_drop, hlen] at he; omega)]
    by_cases hlo : 132 ≤ I.calldata.size
    · have hu : decodeScalarWord? abiUInt256 (I.calldata.toList.drop 4) 96 =
          some (.int (calldataWord I.calldata 100).toNat, 128) := by
        rw [decodeScalarWord_uint256_ok (by
          rw [List.drop_drop, List.length_take, List.length_drop, hlen]; omega)]
        have hw : ABI.bytesToWord (((I.calldata.toList.drop 4).drop 96).take 32) =
            calldataWord I.calldata 100 := by
          rw [List.drop_drop]
          exact decode_word_at_eq _ 100 hlo (by decide)
        rw [hw]
        rfl
      have h0 := decodeScalarWord_calldata_address I.calldata 0 (by omega) (by decide)
      have h1 := decodeScalarWord_calldata_address I.calldata 32 (by omega) (by decide)
      have h2 := decodeScalarWord_calldata_address I.calldata 64 (by omega) (by decide)
      simp only [decodeScalarWords?, h0, h1, h2, hu, ThreeAddressUintCalldataValid, hlo, hhi,
        true_and]
      split_ifs <;> simp_all only [Nat.reduceAdd, bind, Option.bind, decodeCalldata.insertValues,
        and_self, and_false, false_and, true_and, and_true, not_true_eq_false, if_true, if_false]
    · rw [if_neg (fun h ↦ hlo h.1)]
      cases hd : decodeScalarWords?
          [.elem .address, .elem .address, .elem .address, abiUInt256] (I.calldata.toList.drop 4) 0 with
      | none => rfl
      | some vals =>
        have hl := decodeScalarWords?_some_length (Nat.zero_le _) hd
        simp only [List.length_cons, List.length_nil, List.length_drop, hlen] at hl
        omega
  · rw [if_pos ⟨rfl, by rw [List.length_drop, hlen]; omega⟩,
      if_neg (fun h ↦ hhi h.2.1)]

end Benchmarks.CompoundIII.Comet
