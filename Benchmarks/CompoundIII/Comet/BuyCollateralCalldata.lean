import Benchmarks.CompoundIII.Comet.ThreeAddressUintCalldata

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

abbrev BuyCollateralCalldataValid (I : ExecutionEnv) : Prop :=
  132 ≤ I.calldata.size ∧ I.calldata.size < 2^255 + 4 ∧
    (calldataWord I.calldata 4).toNat < EVM.addressModulus ∧
    (calldataWord I.calldata 100).toNat < EVM.addressModulus

-- LIBRARY CANDIDATE: decode a uint256 at any fixed offset in calldata's argument area.
theorem decodeScalarWord_calldata_uint256 (cd : ByteArray) (n : Nat)
    (hn : 4 + n + 32 ≤ cd.size) (h64 : 4 + n < 2^64) :
    decodeScalarWord? abiUInt256 (cd.toList.drop 4) n =
      some (.int (calldataWord cd (4+n)).toNat, n+32) := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeScalarWord_uint256_ok (by
    rw [List.drop_drop, List.length_take, List.length_drop, hlen]; omega)]
  have hw : ABI.bytesToWord (((cd.toList.drop 4).drop n).take 32) = calldataWord cd (4+n) := by
    rw [List.drop_drop]
    exact decode_word_at_eq cd (4+n) hn h64
  rw [hw]
  rfl

-- LIBRARY CANDIDATE: static calldata tuple (address, uint256, uint256, address).
theorem decodeCalldata_addressUintUintAddress (I : ExecutionEnv) (x y z w : Ident)
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata [x,y,z,w] [.elem .address, abiUInt256, abiUInt256, .elem .address] I.calldata =
      if BuyCollateralCalldataValid I then
        some (((((∅ : Store).insert x (.address (AccountAddress.ofNat
          (calldataWord I.calldata 4).toNat))).insert y (.int
          (calldataWord I.calldata 36).toNat)).insert z (.int
          (calldataWord I.calldata 68).toNat)).insert w (.address (AccountAddress.ofNat
          (calldataWord I.calldata 100).toNat)))
      else none := by
  have hlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (by decide), if_neg (by omega)]
  by_cases hhi : I.calldata.size < 2^255+4
  · rw [if_neg (by rintro ⟨_, he⟩; rw [List.length_drop, hlen] at he; omega)]
    by_cases hlo : 132 ≤ I.calldata.size
    · have h0 := decodeScalarWord_calldata_address I.calldata 0 (by omega) (by decide)
      have h1 := decodeScalarWord_calldata_uint256 I.calldata 32 (by omega) (by decide)
      have h2 := decodeScalarWord_calldata_uint256 I.calldata 64 (by omega) (by decide)
      have h3 := decodeScalarWord_calldata_address I.calldata 96 (by omega) (by decide)
      simp only [decodeScalarWords?, h0, h1, h2, h3, BuyCollateralCalldataValid, hlo, hhi, true_and]
      split_ifs <;> simp_all only [Nat.reduceAdd, bind, Option.bind, decodeCalldata.insertValues,
        and_self, and_false, and_true, not_true_eq_false, if_true, if_false]
    · rw [if_neg (fun h ↦ hlo h.1)]
      cases hd : decodeScalarWords?
          [.elem .address, abiUInt256, abiUInt256, .elem .address] (I.calldata.toList.drop 4) 0 with
      | none => rfl
      | some vals =>
        have hl := decodeScalarWords?_some_length (Nat.zero_le _) hd
        simp only [List.length_cons, List.length_nil, List.length_drop, hlen] at hl
        omega
  · rw [if_pos ⟨rfl, by rw [List.length_drop, hlen]; omega⟩,
      if_neg (fun h ↦ hhi h.2.1)]

end Benchmarks.CompoundIII.Comet
