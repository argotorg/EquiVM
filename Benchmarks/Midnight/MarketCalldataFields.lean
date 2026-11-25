import Benchmarks.Midnight.CollateralCalldataValue
import Benchmarks.Midnight.MarketValueDecode

/-! Scalar fields of the materialized market calldata tuple. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: a bounded scalar calldata load is the canonical ABI word decoder.
theorem solcDecodeValue_word (ty : ElemType) {bytes : ByteArray} {start : Nat}
    (plan : CalldataPlan) (tailAccess : Bool)
    (hty : isABIScalarWordType (.elem ty) = true)
    (hbound : start + 32 ≤ bytes.size) (hsize : bytes.size < EVM.wordModulus) :
    decodeValue? (.elem ty) bytes.toList start plan tailAccess =
      decodeABIWord? (.elem ty) (calldataWord bytes start) := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have ht : ((bytes.toList.drop start).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hl]
    omega
  rw [decodeValue?, solcReadBytes_bounded (by rw [hl]; exact hbound)
    (by rw [hl]; exact hsize), decodeABIValue_scalarWord_eq hty]
  simp only [decodeScalarWord?, readWord?, readBytes?, List.drop_zero, List.take_take,
    Nat.min_self, ht, if_true, bind, Option.bind,
    decode_word_at_eq_any bytes start hbound]
  cases decodeABIWord? (.elem ty) (calldataWord bytes start) <;> rfl

-- LIBRARY CANDIDATE: separate a materialized scalar tuple head from its remaining fields.
theorem solcDecodeFields_word (ty : ABIType) {types : List ABIType} {bytes : ByteArray}
    {base cursor : Nat} {plans : List CalldataPlan}
    (hty : isABIScalarWordType ty = true)
    (hplan : plans.headD {} = {}) (hbound : base + cursor + 32 ≤ bytes.size)
    (hsize : bytes.size < EVM.wordModulus) :
    decodeFields? (ty :: types) bytes.toList base cursor plans true = (do
      let value ← decodeABIWord? ty (calldataWord bytes (base + cursor))
      let rest ← decodeFields? types bytes.toList base (cursor + 32) plans.tail true
      pure (value :: rest)) := by
  cases ty <;> try { cases hty }
  rename_i ty
  have ha : solcAdd base cursor = base + cursor := Nat.mod_eq_of_lt (by omega)
  rw [decodeFields?]
  simp only [stride?, isDynamicABIType, Bool.false_eq_true, if_false,
    staticABIEncodedSize?, bind, Option.bind, hplan, ha, Bool.false_and]
  rw [solcDecodeValue_word ty {} false hty hbound hsize]
  rfl

-- LIBRARY CANDIDATE: a materialized dynamic head retains Solidity's uint64 offset cap.
theorem solcDecodeFields_dynamic (ty : ABIType) {types : List ABIType} {bytes : ByteArray}
    {base cursor : Nat} {plans : List CalldataPlan}
    (hty : isDynamicABIType ty = true) (hplan : plans.headD {} = {})
    (hbound : base + cursor + 32 ≤ bytes.size) (hsize : bytes.size < EVM.wordModulus)
    (hbase : base + 2^64 < EVM.wordModulus) :
    decodeFields? (ty :: types) bytes.toList base cursor plans true = (do
      let relative := (calldataWord bytes (base + cursor)).toNat
      if solcMaxU64 < relative then none else do
        let value ← decodeValue? ty bytes.toList (base + relative) {} false
        let rest ← decodeFields? types bytes.toList base (cursor + 32) plans.tail true
        pure (value :: rest)) := by
  have ha : solcAdd base cursor = base + cursor := Nat.mod_eq_of_lt (by omega)
  rw [decodeFields?]
  simp only [stride?, hty, if_true, bind, Option.bind, hplan, ha, Bool.not_true,
    solcTailTarget?, Bool.false_eq_true, if_false, solcReadNat_bounded hbound hsize,
    Bool.and_false]
  by_cases hc : solcMaxU64 < (calldataWord bytes (base + cursor)).toNat
  · simp [hc, retainFailure]
  · have hb : solcAdd base (calldataWord bytes (base + cursor)).toNat =
        base + (calldataWord bytes (base + cursor)).toNat := Nat.mod_eq_of_lt (by
      change ¬ (2^64 - 1 < _) at hc
      omega)
    simp only [hc, if_false, bind, Option.bind, hb]
    rfl

theorem solcMarketValue_shape (bytes : ByteArray) (start : Nat) :
    decodeValue? Model.marketABI bytes.toList start {} =
      (if solcSLT (solcSub bytes.toList.length start) 256 then none else do
        let values ← decodeFields? [Model.u256, Model.addr, Model.addr,
          .dynamicArray Model.collateralABI, Model.u256, Model.u256, Model.addr, Model.addr]
          bytes.toList start 0 [{}, {}, {}, {}, {}, {}, {}, {}] true
        pure (.tuple values)) := by
  have hhead : abiTupleHeadSize? [Model.u256, Model.addr, Model.addr,
      .dynamicArray Model.collateralABI, Model.u256, Model.u256, Model.addr, Model.addr] =
      some 256 := by
    simp [abiTupleHeadSize?, Model.u256, Model.addr, isDynamicABIType, staticABIEncodedSize?]
  have hd : isDynamicABIType Model.marketABI = true := by decide +kernel
  rw [Model.marketABI, decodeValue?]
  simp only [hhead, bind, Option.bind, show isMemory ({} : CalldataPlan) = true from rfl,
    Bool.not_false, Bool.true_or, Bool.true_and,
    show isDynamicABIType (.tuple [Model.u256, Model.addr, Model.addr,
      .dynamicArray Model.collateralABI, Model.u256, Model.u256, Model.addr, Model.addr]) = true
      from hd, Bool.not_true, Bool.false_eq_true, if_false]
  rfl

theorem solcDecodeMarketTail {bytes : ByteArray} {start : Nat}
    (hlen : start + 256 ≤ bytes.size) (hsize : bytes.size < EVM.wordModulus) :
    decodeFields? [Model.u256, Model.u256, Model.addr, Model.addr] bytes.toList
      start 128 [{}, {}, {}, {}] true =
      if (calldataWord bytes (start + 192)).toNat < EVM.addressModulus ∧
          (calldataWord bytes (start + 224)).toNat < EVM.addressModulus then
        some [.int (Int.ofNat (calldataWord bytes (start + 128)).toNat),
          .int (Int.ofNat (calldataWord bytes (start + 160)).toNat),
          .address (AccountAddress.ofNat (calldataWord bytes (start + 192)).toNat),
          .address (AccountAddress.ofNat (calldataWord bytes (start + 224)).toNat)] else none := by
  rw [solcDecodeFields_word Model.u256
    (base := start) (cursor := 128) (plans := [{}, {}, {}, {}]) rfl rfl (by omega) hsize,
    decodeABIWord_u256]
  simp only [bind, Option.bind, Nat.reduceAdd, List.tail_cons]
  rw [solcDecodeFields_word Model.u256
    (base := start) (cursor := 160) (plans := [{}, {}, {}]) rfl rfl (by omega) hsize,
    decodeABIWord_u256]
  simp only [bind, Option.bind, Nat.reduceAdd, List.tail_cons]
  rw [solcDecodeFields_word Model.addr (base := start) (cursor := 192)
    (plans := [{}, {}]) rfl rfl (by omega) hsize, decodeABIWord_address]
  by_cases he : (calldataWord bytes (start + 192)).toNat < EVM.addressModulus
  · simp only [he, if_true, bind, Option.bind, Nat.reduceAdd, List.tail_cons]
    rw [solcDecodeFields_word Model.addr (base := start) (cursor := 224)
      (plans := [{}]) rfl rfl (by omega) hsize, decodeABIWord_address]
    by_cases hl : (calldataWord bytes (start + 224)).toNat < EVM.addressModulus
    · simp only [hl, if_true, bind, Option.bind, decodeFields?, and_self]
      rfl
    · simp [hl]
  · simp [he]

end Benchmarks.Midnight
