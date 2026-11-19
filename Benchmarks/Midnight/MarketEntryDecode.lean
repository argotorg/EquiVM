import Benchmarks.Midnight.MarketCalldataHead
import Benchmarks.Midnight.PairDecode

/-! External calldata containing a market, an identifier, and an account. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

theorem calldataSelector_of_selIs {I : ExecutionEnv} {selector : ByteArray}
    (hsel : selIs I selector) :
    bytesToWord (I.calldata.toList.take 4) = bytesToWord selector.toList := by
  have he : selector = I.calldata.extract 0 4 := byteArray_eq_of_beq hsel
  rw [he, extract_toList, List.drop_zero, Nat.sub_zero]

theorem solcDecodeFields_bytes32 {types : List ABIType} {bytes : ByteArray}
    {base cursor : Nat} {plans : List CalldataPlan}
    (hplan : plans.headD {} = {}) (hbound : base + cursor + 32 ≤ bytes.size)
    (hsize : bytes.size < EVM.wordModulus) :
    decodeFields? (Model.b32 :: types) bytes.toList base cursor plans true = (do
      let rest ← decodeFields? types bytes.toList base (cursor + 32) plans.tail true
      pure (wordBytes32Value (calldataWord bytes (base + cursor)) :: rest)) := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have ha : solcAdd base cursor = base + cursor := Nat.mod_eq_of_lt (by omega)
  rw [decodeFields?]
  simp only [Model.b32, stride?, isDynamicABIType, Bool.false_eq_true, if_false,
    staticABIEncodedSize?, bind, Option.bind, hplan, ha, Bool.false_and]
  have hw : decodeABIValue? (.elem (.bytes ⟨31, by decide⟩))
      ((bytes.toList.drop (base + cursor)).take 32) 0 =
      some (wordBytes32Value (calldataWord bytes (base + cursor)), 32) :=
    decodeBytes32Word hbound
  rw [decodeValue?, solcReadBytes_bounded (by rw [hl]; exact hbound)
    (by rw [hl]; exact hsize), hw]
  rfl

def marketIdUserArguments (market : MarketData) (id : UInt256) (user : AccountAddress) : Store :=
  ((((∅ : Store).insert "market" market.value).insert "id" (wordBytes32Value id)).insert
    "user" (.address user)).insert "market" (Model.marketValue market.value)

theorem midnightDecodeMarketIdUser_none_check {bytes : ByteArray}
    (h4 : 4 ≤ bytes.size) (hcheck : solcSLT (solcSub bytes.size 4) 96 = true) :
    config.externalABI.decodeCalldata? ["market", "id", "user"]
      [Model.marketABI, Model.b32, Model.addr] bytes = none := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hd : isDynamicABIType Model.marketABI = true := by decide +kernel
  have hhead : abiTupleHeadSize? [Model.marketABI, Model.b32, Model.addr] = some 96 := by
    simp [abiTupleHeadSize?, hd, Model.b32, Model.addr, staticABIEncodedSize?, isDynamicABIType]
  change Model.decodeCalldata _ _ bytes = _
  simp only [Model.decodeCalldata, decodeCalldataWithMode, decodeCalldata, hl,
    show ¬ bytes.size < 4 from by omega, if_false, Model.calldataMode, List.any_cons,
    List.any_nil, hd, Bool.true_or, decodeArgs?, List.isEmpty_cons, Bool.false_eq_true,
    hhead, bind, Option.bind, hcheck, if_true, ite_self]

theorem decodeSolcMarketIdUser {bytes : ByteArray}
    (h100 : 100 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 96 = false) :
    decodeCalldataWithMode Model.calldataMode ["market", "id", "user"]
      [Model.marketABI, Model.b32, Model.addr] bytes = (do
        let market ← decodeCalldataMarket bytes 4
        if (calldataWord bytes 68).toNat < EVM.addressModulus then
          pure ((((∅ : Store).insert "market" market.value).insert "id"
            (wordBytes32Value (calldataWord bytes 36))).insert "user"
              (.address (AccountAddress.ofNat (calldataWord bytes 68).toNat)))
        else none) := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  have hd : isDynamicABIType Model.marketABI = true := by decide +kernel
  have hhead : abiTupleHeadSize? [Model.marketABI, Model.b32, Model.addr] = some 96 := by
    simp [abiTupleHeadSize?, hd, Model.b32, Model.addr, staticABIEncodedSize?, isDynamicABIType]
  simp only [decodeCalldataWithMode, decodeCalldata, hl, show ¬ bytes.size < 4 from by omega,
    if_false, Model.calldataMode, List.any_cons, List.any_nil, hd, Bool.true_or,
    decodeArgs?, List.isEmpty_cons, Bool.false_eq_true, hhead, bind, Option.bind, hcheck, ite_self]
  have hbe : (0xac9650d8 == (bytesToWord (bytes.toList.take 4)).toNat) = false := by
    exact beq_eq_false_iff_ne.mpr hselector
  have hp : ((([(0xac9650d8, [{ materialize := [] }])] : List (Nat × List CalldataPlan)).find?
      (fun entry ↦ entry.1 == (bytesToWord (bytes.toList.take 4)).toNat)).map Prod.snd).getD [] =
      [] := by simp [List.find?, hbe]
  rw [hp, solcDecodeFields_market (plans := []) rfl (by omega) hsize]
  simp only [Nat.add_zero, List.tail_nil]
  rw [solcDecodeFields_bytes32 (base := 4) (cursor := 32) (plans := []) rfl (by omega) hsize]
  simp only [Nat.reduceAdd, List.tail_nil]
  rw [solcDecodeFields_word Model.addr (base := 4) (cursor := 64) (plans := [])
    rfl rfl (by omega) hsize, decodeABIWord_address]
  simp only [Nat.reduceAdd]
  cases hm : decodeCalldataMarket bytes 4 with
  | none => rfl
  | some market =>
    by_cases hu : (calldataWord bytes 68).toNat < EVM.addressModulus
    · simp only [hu, if_true, bind, Option.bind, decodeFields?, decodeCalldata.insertValues]
      rfl
    · simp only [hu, if_false, bind, Option.bind]

theorem midnightDecodeMarketIdUser {bytes : ByteArray}
    (h100 : 100 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (bytes.toList.take 4)).toNat)
    (hcheck : solcSLT (solcSub bytes.size 4) 96 = false) :
    config.externalABI.decodeCalldata? ["market", "id", "user"]
      [Model.marketABI, Model.b32, Model.addr] bytes = (do
        let market ← decodeCalldataMarket bytes 4
        if (calldataWord bytes 68).toNat < EVM.addressModulus ∧
            1120 + 160 * market.collaterals.length < 2^64 then
          pure (marketIdUserArguments market (calldataWord bytes 36)
            (AccountAddress.ofNat (calldataWord bytes 68).toNat))
        else none) := by
  change Model.decodeCalldata _ _ bytes = _
  unfold Model.decodeCalldata
  rw [decodeSolcMarketIdUser h100 hsize hselector hcheck]
  cases hm : decodeCalldataMarket bytes 4 with
  | none => rfl
  | some market =>
    by_cases hu : (calldataWord bytes 68).toNat < EVM.addressModulus
    · simp only [hu, if_true, bind, Option.bind, true_and]
      by_cases hf : 1120 + 160 * market.collaterals.length < 2^64 <;>
        simp only [Nat.reducePow] at hf <;>
        simp [Model.inputSizesFit, Model.collateralCount?, MarketData.value,
          marketIdUserArguments, Std.HashMap.getElem_insert, hf]
    · simp only [hu, false_and, if_false, bind, Option.bind]

end Benchmarks.Midnight
