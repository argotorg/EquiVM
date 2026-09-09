import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

def auctionPackedBidderWord (packed : UInt256) : UInt256 :=
  UInt256.land packed solcAddrMask

def auctionPackedSettledBaseWord (packed : UInt256) : UInt256 :=
  UInt256.div packed (UInt256.ofNat (256 ^ 20))

def auctionPackedSettledWord (packed : UInt256) : UInt256 :=
  UInt256.land (auctionPackedSettledBaseWord packed) ⟨255⟩

def auctionPackedSettledEVMWord (packed : UInt256) : UInt256 :=
  UInt256.land ⟨255⟩ (auctionPackedSettledBaseWord packed)

def auctionPackedSettledReturnWord (packed : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.isZero (auctionPackedSettledWord packed))

def auctionPackedSettledEVMReturnWord (packed : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.isZero (auctionPackedSettledEVMWord packed))

def auctionAuctionNounWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  auctionSlotWord ⟨207⟩ σ I

def auctionAuctionAmountWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  auctionSlotWord ⟨208⟩ σ I

def auctionAuctionStartWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  auctionSlotWord ⟨209⟩ σ I

def auctionAuctionEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  auctionSlotWord ⟨210⟩ σ I

def auctionAuctionPackedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  auctionSlotWord ⟨211⟩ σ I

def auctionAuctionReturnValues (σ : AccountMap) (I : ExecutionEnv) : List Value :=
  [.int (Int.ofNat (auctionAuctionNounWord σ I).toNat),
    .int (Int.ofNat (auctionAuctionAmountWord σ I).toNat),
    .int (Int.ofNat (auctionAuctionStartWord σ I).toNat),
    .int (Int.ofNat (auctionAuctionEndWord σ I).toNat),
    .address (AccountAddress.ofNat (auctionPackedBidderWord (auctionAuctionPackedWord σ I)).toNat),
    wordToElem .bool (auctionPackedSettledWord (auctionAuctionPackedWord σ I))]

def auctionAuctionReturnData (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  UInt256.toByteArray (auctionAuctionNounWord σ I) ++
    UInt256.toByteArray (auctionAuctionAmountWord σ I) ++
    UInt256.toByteArray (auctionAuctionStartWord σ I) ++
    UInt256.toByteArray (auctionAuctionEndWord σ I) ++
    UInt256.toByteArray (auctionPackedBidderWord (auctionAuctionPackedWord σ I)) ++
    UInt256.toByteArray (auctionPackedSettledReturnWord (auctionAuctionPackedWord σ I))

def auctionAuctionReturnValuesState (evm : EVM.State) : List Value :=
  [.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat),
    .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat),
    .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩).toNat),
    .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat),
    .address (AccountAddress.ofNat
      (auctionPackedBidderWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat),
    wordToElem .bool
      (auctionPackedSettledWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩))]

noncomputable def auctionAuctionReturnNounMem (noun : UInt256) : ByteArray :=
  (UInt256.toByteArray noun).write 0 solcFreePtrMem 128 32

noncomputable def auctionAuctionReturnAmountMem (noun amount : UInt256) : ByteArray :=
  (UInt256.toByteArray amount).write 0 (auctionAuctionReturnNounMem noun) 160 32

noncomputable def auctionAuctionReturnStartMem
    (noun amount start : UInt256) : ByteArray :=
  (UInt256.toByteArray start).write 0 (auctionAuctionReturnAmountMem noun amount) 192 32

noncomputable def auctionAuctionReturnEndMem
    (noun amount start finish : UInt256) : ByteArray :=
  (UInt256.toByteArray finish).write 0
    (auctionAuctionReturnStartMem noun amount start) 224 32

noncomputable def auctionAuctionReturnBidderMem
    (noun amount start finish bidder : UInt256) : ByteArray :=
  (UInt256.toByteArray bidder).write 0
    (auctionAuctionReturnEndMem noun amount start finish) 256 32

noncomputable def auctionAuctionReturnMem
    (noun amount start finish bidder settled : UInt256) : ByteArray :=
  (UInt256.toByteArray settled).write 0
    (auctionAuctionReturnBidderMem noun amount start finish bidder) 288 32

theorem auctionAuctionReturnNounMem_size (noun : UInt256) :
    (auctionAuctionReturnNounMem noun).size = 160 := by
  unfold auctionAuctionReturnNounMem
  exact toByteArray_write32_size_of_ge solcFreePtrMem noun 128 96 160
    solcFreePtrMem_size (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionAuctionReturnAmountMem_size (noun amount : UInt256) :
    (auctionAuctionReturnAmountMem noun amount).size = 192 := by
  unfold auctionAuctionReturnAmountMem
  exact toByteArray_write32_size_of_ge (auctionAuctionReturnNounMem noun) amount 160 160 192
    (auctionAuctionReturnNounMem_size noun) (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionAuctionReturnStartMem_size (noun amount start : UInt256) :
    (auctionAuctionReturnStartMem noun amount start).size = 224 := by
  unfold auctionAuctionReturnStartMem
  exact toByteArray_write32_size_of_ge
    (auctionAuctionReturnAmountMem noun amount) start 192 192 224
    (auctionAuctionReturnAmountMem_size noun amount) (by omega) (lt_usize _ (by norm_num)) rfl

theorem auctionAuctionReturnEndMem_size (noun amount start finish : UInt256) :
    (auctionAuctionReturnEndMem noun amount start finish).size = 256 := by
  unfold auctionAuctionReturnEndMem
  exact toByteArray_write32_size_of_ge
    (auctionAuctionReturnStartMem noun amount start) finish 224 224 256
    (auctionAuctionReturnStartMem_size noun amount start) (by omega)
    (lt_usize _ (by norm_num)) rfl

theorem auctionAuctionReturnBidderMem_size (noun amount start finish bidder : UInt256) :
    (auctionAuctionReturnBidderMem noun amount start finish bidder).size = 288 := by
  unfold auctionAuctionReturnBidderMem
  exact toByteArray_write32_size_of_ge
    (auctionAuctionReturnEndMem noun amount start finish) bidder 256 256 288
    (auctionAuctionReturnEndMem_size noun amount start finish) (by omega)
    (lt_usize _ (by norm_num)) rfl

theorem auctionAuctionReturnMem_size (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionReturnMem noun amount start finish bidder settled).size = 320 := by
  unfold auctionAuctionReturnMem
  exact toByteArray_write32_size_of_ge
    (auctionAuctionReturnBidderMem noun amount start finish bidder) settled 288 288 320
    (auctionAuctionReturnBidderMem_size noun amount start finish bidder) (by omega)
    (lt_usize _ (by norm_num)) rfl

theorem auctionAuctionReturnMem_read64
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionReturnMem noun amount start finish bidder settled).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold auctionAuctionReturnMem
  rw [toByteArray_write_read_below_of_gap settled _ 288 64
    (by rw [auctionAuctionReturnBidderMem_size]; omega) (by omega)
    (by rw [auctionAuctionReturnBidderMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnBidderMem
  rw [toByteArray_write_read_below_of_gap bidder _ 256 64
    (by rw [auctionAuctionReturnEndMem_size]; omega) (by omega)
    (by rw [auctionAuctionReturnEndMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnEndMem
  rw [toByteArray_write_read_below_of_gap finish _ 224 64
    (by rw [auctionAuctionReturnStartMem_size]; omega) (by omega)
    (by rw [auctionAuctionReturnStartMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnStartMem
  rw [toByteArray_write_read_below_of_gap start _ 192 64
    (by rw [auctionAuctionReturnAmountMem_size]; omega) (by omega)
    (by rw [auctionAuctionReturnAmountMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnAmountMem
  rw [toByteArray_write_read_below_of_gap amount _ 160 64
    (by rw [auctionAuctionReturnNounMem_size]; omega) (by omega)
    (by rw [auctionAuctionReturnNounMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnNounMem
  rw [toByteArray_write_read_below_of_gap noun solcFreePtrMem 128 64
    (by rw [solcFreePtrMem_size]) (by omega)
    (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))]
  exact solcFreePtrMem_read64

theorem auctionAuctionReturnMem_mload64
    (noun amount start finish bidder settled : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (auctionAuctionReturnMem noun amount start finish bidder settled).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionAuctionReturnMem noun amount start finish bidder settled).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [auctionAuctionReturnMem_size]; decide) (by decide)
    (auctionAuctionReturnMem_read64 noun amount start finish bidder settled)

theorem auctionAuctionReturnMem_read128_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionReturnMem noun amount start finish bidder settled).readWithPadding 128 32 =
      UInt256.toByteArray noun := by
  unfold auctionAuctionReturnMem
  rw [toByteArray_write_read_below_of_gap settled _ 288 128
    (by rw [auctionAuctionReturnBidderMem_size]; omega) (by omega)
    (by rw [auctionAuctionReturnBidderMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnBidderMem
  rw [toByteArray_write_read_below_of_gap bidder _ 256 128
    (by rw [auctionAuctionReturnEndMem_size]; omega) (by omega)
    (by rw [auctionAuctionReturnEndMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnEndMem
  rw [toByteArray_write_read_below_of_gap finish _ 224 128
    (by rw [auctionAuctionReturnStartMem_size]; omega) (by omega)
    (by rw [auctionAuctionReturnStartMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnStartMem
  rw [toByteArray_write_read_below_of_gap start _ 192 128
    (by rw [auctionAuctionReturnAmountMem_size]; omega) (by omega)
    (by rw [auctionAuctionReturnAmountMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnAmountMem
  rw [toByteArray_write_read_below_of_gap amount _ 160 128
    (by rw [auctionAuctionReturnNounMem_size]) (by omega)
    (by rw [auctionAuctionReturnNounMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnNounMem
  exact toByteArray_write_read_back_of_gap noun solcFreePtrMem 128
    (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))

theorem auctionAuctionReturnMem_read160_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionReturnMem noun amount start finish bidder settled).readWithPadding 160 32 =
      UInt256.toByteArray amount := by
  unfold auctionAuctionReturnMem
  rw [toByteArray_write_read_below_of_gap settled _ 288 160
    (by rw [auctionAuctionReturnBidderMem_size]; omega) (by omega)
    (by rw [auctionAuctionReturnBidderMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnBidderMem
  rw [toByteArray_write_read_below_of_gap bidder _ 256 160
    (by rw [auctionAuctionReturnEndMem_size]; omega) (by omega)
    (by rw [auctionAuctionReturnEndMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnEndMem
  rw [toByteArray_write_read_below_of_gap finish _ 224 160
    (by rw [auctionAuctionReturnStartMem_size]; omega) (by omega)
    (by rw [auctionAuctionReturnStartMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnStartMem
  rw [toByteArray_write_read_below_of_gap start _ 192 160
    (by rw [auctionAuctionReturnAmountMem_size]) (by omega)
    (by rw [auctionAuctionReturnAmountMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnAmountMem
  exact toByteArray_write_read_back_of_gap amount (auctionAuctionReturnNounMem noun) 160
    (by rw [auctionAuctionReturnNounMem_size]; exact lt_usize _ (by norm_num))

theorem auctionAuctionReturnMem_read192_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionReturnMem noun amount start finish bidder settled).readWithPadding 192 32 =
      UInt256.toByteArray start := by
  unfold auctionAuctionReturnMem
  rw [toByteArray_write_read_below_of_gap settled _ 288 192
    (by rw [auctionAuctionReturnBidderMem_size]; omega) (by omega)
    (by rw [auctionAuctionReturnBidderMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnBidderMem
  rw [toByteArray_write_read_below_of_gap bidder _ 256 192
    (by rw [auctionAuctionReturnEndMem_size]; omega) (by omega)
    (by rw [auctionAuctionReturnEndMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnEndMem
  rw [toByteArray_write_read_below_of_gap finish _ 224 192
    (by rw [auctionAuctionReturnStartMem_size]) (by omega)
    (by rw [auctionAuctionReturnStartMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnStartMem
  exact toByteArray_write_read_back_of_gap start
    (auctionAuctionReturnAmountMem noun amount) 192
    (by rw [auctionAuctionReturnAmountMem_size]; exact lt_usize _ (by norm_num))

theorem auctionAuctionReturnMem_read224_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionReturnMem noun amount start finish bidder settled).readWithPadding 224 32 =
      UInt256.toByteArray finish := by
  unfold auctionAuctionReturnMem
  rw [toByteArray_write_read_below_of_gap settled _ 288 224
    (by rw [auctionAuctionReturnBidderMem_size]; omega) (by omega)
    (by rw [auctionAuctionReturnBidderMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnBidderMem
  rw [toByteArray_write_read_below_of_gap bidder _ 256 224
    (by rw [auctionAuctionReturnEndMem_size]) (by omega)
    (by rw [auctionAuctionReturnEndMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnEndMem
  exact toByteArray_write_read_back_of_gap finish
    (auctionAuctionReturnStartMem noun amount start) 224
    (by rw [auctionAuctionReturnStartMem_size]; exact lt_usize _ (by norm_num))

theorem auctionAuctionReturnMem_read256_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionReturnMem noun amount start finish bidder settled).readWithPadding 256 32 =
      UInt256.toByteArray bidder := by
  unfold auctionAuctionReturnMem
  rw [toByteArray_write_read_below_of_gap settled _ 288 256
    (by rw [auctionAuctionReturnBidderMem_size]) (by omega)
    (by rw [auctionAuctionReturnBidderMem_size]; exact lt_usize _ (by norm_num))]
  unfold auctionAuctionReturnBidderMem
  exact toByteArray_write_read_back_of_gap bidder
    (auctionAuctionReturnEndMem noun amount start finish) 256
    (by rw [auctionAuctionReturnEndMem_size]; exact lt_usize _ (by norm_num))

theorem auctionAuctionReturnMem_read288_word
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionReturnMem noun amount start finish bidder settled).readWithPadding 288 32 =
      UInt256.toByteArray settled := by
  unfold auctionAuctionReturnMem
  exact toByteArray_write_read_back_of_gap settled
    (auctionAuctionReturnBidderMem noun amount start finish bidder) 288
    (by rw [auctionAuctionReturnBidderMem_size]; exact lt_usize _ (by norm_num))

theorem auctionAuctionReturnMem_read128_192
    (noun amount start finish bidder settled : UInt256) :
    (auctionAuctionReturnMem noun amount start finish bidder settled).readWithPadding 128 192 =
      UInt256.toByteArray noun ++ UInt256.toByteArray amount ++ UInt256.toByteArray start ++
        UInt256.toByteArray finish ++ UInt256.toByteArray bidder ++ UInt256.toByteArray settled := by
  rw [byteArray_readWithPadding_split _ 128 32 160 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by rw [auctionAuctionReturnMem_size])]
  rw [byteArray_readWithPadding_split _ 160 32 128 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by rw [auctionAuctionReturnMem_size])]
  rw [byteArray_readWithPadding_split _ 192 32 96 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by rw [auctionAuctionReturnMem_size])]
  rw [byteArray_readWithPadding_split _ 224 32 64 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by rw [auctionAuctionReturnMem_size])]
  rw [byteArray_readWithPadding_split _ 256 32 32 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by rw [auctionAuctionReturnMem_size])]
  rw [auctionAuctionReturnMem_read128_word, auctionAuctionReturnMem_read160_word,
    auctionAuctionReturnMem_read192_word, auctionAuctionReturnMem_read224_word,
    auctionAuctionReturnMem_read256_word, auctionAuctionReturnMem_read288_word]
  simp [ByteArray.append_assoc]

theorem auctionAuctionSubRet192_toNat :
    (UInt256.sub ((⟨192⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 192 := by
  decide

theorem auctionAuctionReturnEncoding (noun amount start finish packed : UInt256) :
    encodeReturnValues? [uint256, uint256, uint256, uint256, addr, boolTy]
      [.int (Int.ofNat noun.toNat), .int (Int.ofNat amount.toNat),
        .int (Int.ofNat start.toNat), .int (Int.ofNat finish.toNat),
        .address (AccountAddress.ofNat (auctionPackedBidderWord packed).toNat),
        wordToElem .bool (auctionPackedSettledWord packed)] =
      some (UInt256.toByteArray noun ++ UInt256.toByteArray amount ++
        UInt256.toByteArray start ++ UInt256.toByteArray finish ++
        UInt256.toByteArray (auctionPackedBidderWord packed) ++
        UInt256.toByteArray (auctionPackedSettledReturnWord packed)) := by
  have hnoun : EVM.word noun.toNat = noun := u256_ofNat_toNat noun
  have hamount : EVM.word amount.toNat = amount := u256_ofNat_toNat amount
  have hstart : EVM.word start.toNat = start := u256_ofNat_toNat start
  have hfinish : EVM.word finish.toNat = finish := u256_ofNat_toNat finish
  have hnounLt : noun.toNat < EVM.twoPow 256 := by
    change noun.val.val < EVM.twoPow 256
    exact noun.val.isLt
  have hamountLt : amount.toNat < EVM.twoPow 256 := by
    change amount.val.val < EVM.twoPow 256
    exact amount.val.isLt
  have hstartLt : start.toNat < EVM.twoPow 256 := by
    change start.val.val < EVM.twoPow 256
    exact start.val.isLt
  have hfinishLt : finish.toNat < EVM.twoPow 256 := by
    change finish.val.val < EVM.twoPow 256
    exact finish.val.isLt
  have hbidderCanon := solcAddrMask_result_canonical packed
  have hbidderMod :
      (auctionPackedBidderWord packed).toNat % AccountAddress.size =
        (auctionPackedBidderWord packed).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [auctionPackedBidderWord, EVM.addressModulus, EVM.twoPow,
      AccountAddress.size] using hbidderCanon
  have hbidderWord : EVM.word (auctionPackedBidderWord packed).toNat =
      auctionPackedBidderWord packed :=
    u256_ofNat_toNat _
  have hencNoun :
      encodeABIValue? uint256 (.int (Int.ofNat noun.toNat)) =
        some (EVM.Word.toBytesBE noun) := by
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hnoun, hnounLt]
  have hencAmount :
      encodeABIValue? uint256 (.int (Int.ofNat amount.toNat)) =
        some (EVM.Word.toBytesBE amount) := by
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hamount, hamountLt]
  have hencStart :
      encodeABIValue? uint256 (.int (Int.ofNat start.toNat)) =
        some (EVM.Word.toBytesBE start) := by
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hstart, hstartLt]
  have hencFinish :
      encodeABIValue? uint256 (.int (Int.ofNat finish.toNat)) =
        some (EVM.Word.toBytesBE finish) := by
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hfinish, hfinishLt]
  have hencBidder :
      encodeABIValue? addr (.address (AccountAddress.ofNat
        (auctionPackedBidderWord packed).toNat)) =
        some (EVM.Word.toBytesBE (auctionPackedBidderWord packed)) := by
    simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, hbidderMod,
      hbidderWord]
  have hencSettled :
      encodeABIValue? boolTy (wordToElem .bool (auctionPackedSettledWord packed)) =
        some (EVM.Word.toBytesBE (auctionPackedSettledReturnWord packed)) := by
    simpa [boolTy, auctionPackedSettledWord, auctionPackedSettledBaseWord,
      auctionPackedSettledReturnWord] using
      abiBoolWordEncoding (auctionPackedSettledBaseWord packed)
  have hhead :
      abiTupleHeadSize? [uint256, uint256, uint256, uint256, addr, boolTy] =
        some 192 := by
    native_decide
  have hdynUint : isDynamicABIType uint256 = false := by native_decide
  have hdynAddr : isDynamicABIType addr = false := by native_decide
  have hdynBool : isDynamicABIType boolTy = false := by native_decide
  rw [toByteArray_eq_toBytesBE noun, toByteArray_eq_toBytesBE amount,
    toByteArray_eq_toBytesBE start, toByteArray_eq_toBytesBE finish,
    toByteArray_eq_toBytesBE (auctionPackedBidderWord packed),
    toByteArray_eq_toBytesBE (auctionPackedSettledReturnWord packed)]
  simp only [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?, hhead, hencNoun,
    hencAmount, hencStart, hencFinish, hencBidder, hencSettled, hdynUint, hdynAddr, hdynBool,
    bind, Option.bind, Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem auctionAuctionBodyReturns (evm : EVM.State)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody auctionConfig auctionContract evm (∅ : Store) auctionGetter.body
      (.returned { contract := auctionContract, locals := ∅ } evm
        (some (auctionAuctionReturnValuesState evm))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).run <|
      ExecBlock.consReturn <| ExecStmt.return (by
        have hbase (f : Ident) : (∅ : Store).get? (aField f).base = none := by
          simp [aField]
        have her (f : Ident) :
            evalStorageRef auctionConfig { contract := auctionContract, locals := (∅ : Store) } evm
              (aField f) =
            .ok ({ base := "auction", steps := [.field f] } : EvaledStorageRef) := by
          simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, aField, auctionConfig,
            auctionContract, storageDecls, auctionStructTy, uint256St, addrSt, boolSt,
            EvalResult.bind, bind, pure]
        have htyNoun : storageTypeAt? auctionContract.storage
            ({ base := "auction", steps := [.field "nounId"] } : EvaledStorageRef) =
            some (.elem (.int uint256Int)) := by
          simp [storageTypeAt?, storageTypeStep?, auctionContract, storageDecls,
            auctionStructTy, uint256St]
        have htyAmount : storageTypeAt? auctionContract.storage
            ({ base := "auction", steps := [.field "amount"] } : EvaledStorageRef) =
            some (.elem (.int uint256Int)) := by
          simp [storageTypeAt?, storageTypeStep?, auctionContract, storageDecls,
            auctionStructTy, uint256St]
        have htyStart : storageTypeAt? auctionContract.storage
            ({ base := "auction", steps := [.field "startTime"] } : EvaledStorageRef) =
            some (.elem (.int uint256Int)) := by
          simp [storageTypeAt?, storageTypeStep?, auctionContract, storageDecls,
            auctionStructTy, uint256St]
        have htyEnd : storageTypeAt? auctionContract.storage
            ({ base := "auction", steps := [.field "endTime"] } : EvaledStorageRef) =
            some (.elem (.int uint256Int)) := by
          simp [storageTypeAt?, storageTypeStep?, auctionContract, storageDecls,
            auctionStructTy, uint256St]
        have htyBidder : storageTypeAt? auctionContract.storage
            ({ base := "auction", steps := [.field "bidder"] } : EvaledStorageRef) =
            some (.elem .address) := by
          simp [storageTypeAt?, storageTypeStep?, auctionContract, storageDecls,
            auctionStructTy, addrSt]
        have htySettled : storageTypeAt? auctionContract.storage
            ({ base := "auction", steps := [.field "settled"] } : EvaledStorageRef) =
            some (.elem .bool) := by
          simp [storageTypeAt?, storageTypeStep?, auctionContract, storageDecls,
            auctionStructTy, boolSt]
        have hlocNoun : auctionConfig.storage.layout
            ({ base := "auction", steps := [.field "nounId"] } : EvaledStorageRef) =
            fun _ => some (auctionUint256Loc ⟨207⟩) := by
          funext evm'
          simp [auctionConfig, auctionStorageLayout]
        have hlocAmount : auctionConfig.storage.layout
            ({ base := "auction", steps := [.field "amount"] } : EvaledStorageRef) =
            fun _ => some (auctionUint256Loc ⟨208⟩) := by
          funext evm'
          simp [auctionConfig, auctionStorageLayout]
        have hlocStart : auctionConfig.storage.layout
            ({ base := "auction", steps := [.field "startTime"] } : EvaledStorageRef) =
            fun _ => some (auctionUint256Loc ⟨209⟩) := by
          funext evm'
          simp [auctionConfig, auctionStorageLayout]
        have hlocEnd : auctionConfig.storage.layout
            ({ base := "auction", steps := [.field "endTime"] } : EvaledStorageRef) =
            fun _ => some (auctionUint256Loc ⟨210⟩) := by
          funext evm'
          simp [auctionConfig, auctionStorageLayout]
        have hlocBidder : auctionConfig.storage.layout
            ({ base := "auction", steps := [.field "bidder"] } : EvaledStorageRef) =
            fun _ => some (auctionAddrLoc ⟨211⟩) := by
          funext evm'
          simp [auctionConfig, auctionStorageLayout]
        have hlocSettled : auctionConfig.storage.layout
            ({ base := "auction", steps := [.field "settled"] } : EvaledStorageRef) =
            fun _ => some (auctionBoolLocAt ⟨211⟩ 20) := by
          funext evm'
          simp [auctionConfig, auctionStorageLayout]
        have hloadNoun : storageLocLoad evm (auctionUint256Loc ⟨207⟩) =
            .int (Int.ofNat
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨207⟩).toNat) := by
          simpa using auctionStorageLocLoad_uint256 evm ⟨207⟩
        have hloadAmount : storageLocLoad evm (auctionUint256Loc ⟨208⟩) =
            .int (Int.ofNat
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨208⟩).toNat) := by
          simpa using auctionStorageLocLoad_uint256 evm ⟨208⟩
        have hloadStart : storageLocLoad evm (auctionUint256Loc ⟨209⟩) =
            .int (Int.ofNat
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨209⟩).toNat) := by
          simpa using auctionStorageLocLoad_uint256 evm ⟨209⟩
        have hloadEnd : storageLocLoad evm (auctionUint256Loc ⟨210⟩) =
            .int (Int.ofNat
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨210⟩).toNat) := by
          simpa using auctionStorageLocLoad_uint256 evm ⟨210⟩
        have hloadBidder : storageLocLoad evm (auctionAddrLoc ⟨211⟩) =
            .address (AccountAddress.ofNat
              (auctionPackedBidderWord
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)).toNat) := by
          simpa [auctionAddrLoc, auctionPackedBidderWord] using
            auctionStorageLocLoad_address_offset0 evm ⟨211⟩
        have hloadSettled : storageLocLoad evm (auctionBoolLocAt ⟨211⟩ 20) =
            wordToElem .bool
              (auctionPackedSettledWord
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)) := by
          simpa [auctionPackedSettledWord, auctionPackedSettledBaseWord] using
            auctionStorageLocLoad_bool_offset evm ⟨211⟩ ⟨20, by decide⟩
        simp only [Solm.evalExprs?.eq_def,
          evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase "nounId")
            (her := her "nounId") (hty := htyNoun) (hloc := hlocNoun),
          evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase "amount")
            (her := her "amount") (hty := htyAmount) (hloc := hlocAmount),
          evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase "startTime")
            (her := her "startTime") (hty := htyStart) (hloc := hlocStart),
          evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase "endTime")
            (her := her "endTime") (hty := htyEnd) (hloc := hlocEnd),
          evalExpr_storage_scalar (t := .address) (hbase := hbase "bidder")
            (her := her "bidder") (hty := htyBidder) (hloc := hlocBidder),
          evalExpr_storage_scalar (t := .bool) (hbase := hbase "settled")
            (her := her "settled") (hty := htySettled) (hloc := hlocSettled),
          EvalResult.bind, bind, pure, hloadNoun, hloadAmount, hloadStart, hloadEnd,
          hloadBidder, hloadSettled, auctionAuctionReturnValuesState])

theorem auctionDispatch_auction {I : ExecutionEnv} (hsel : selIs I (auctionSelBytes 9)) :
    dispatchMsg auctionContract I.calldata = some auctionGetter := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [initializeTransition, createBidTransition, settleAndCreateTransition,
      settleAuctionTransition, pauseTransition, unpauseTransition, setTimeBufferTransition,
      setReservePriceTransition, setMinBidIncTransition, transferOwnershipTransition,
      renounceOwnershipTransition, ownerGetter, pausedGetter, nounsGetter, wethGetter,
      timeBufferGetter, reservePriceGetter, minBidIncGetter, durationGetter])
    (post := [])
    (ti := auctionGetter)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = auctionSelBytes 9 := (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, initializeSelectorBytes, createBidSelectorBytes,
        settleAndCreateSelectorBytes, settleAuctionSelectorBytes, pauseSelectorBytes,
        unpauseSelectorBytes, setTimeBufferSelectorBytes, setReservePriceSelectorBytes,
        setMinBidIncSelectorBytes, transferOwnershipSelectorBytes, renounceOwnershipSelectorBytes,
        ownerSelectorBytes, pausedSelectorBytes, nounsSelectorBytes, wethSelectorBytes,
        timeBufferSelectorBytes, reservePriceSelectorBytes, minBidIncSelectorBytes,
        durationSelectorBytes, hcd, auctionSelBytes]
      native_decide
  · rw [selectorOf, auctionGetterSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

theorem auctionDecode_auction {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode (auctionGetter.params.map Param.name)
      (transitionSignature auctionGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode auctionConfig.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem auctionReachAuctionBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 9)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨570⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0x7d, 0x9f, 0x6d, 0xb5]⟩ : ByteArray) ==
      I.calldata.extract 0 4) = true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0x7d9f6db5⟩ :=
    auctionSelWord_eq_of_beq I hsz 0x7d 0x9f 0x6d 0xb5 ⟨0x7d9f6db5⟩
      (by native_decide) hsel'
  obtain ⟨_, _, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hroot : UInt256.gt (armSelNat auctionBytecode auctionSplitPc) (auctionSelWord I) ≠
      ⟨0⟩ := by
    rw [hword]
    native_decide
  have h157 := auctionSelectorSplitTakenTo hsplit auctionSplitWellFormed hroot
      auctionRootSplitTargetPc
    (by jump_dest) (by simp)
  have h158 := h157.jumpdest (by native_decide) (by simp)
  have hlower : UInt256.gt (armSelNat auctionBytecode auctionLowerSplitPc) (auctionSelWord I) =
      ⟨0⟩ := by
    rw [hword]
    native_decide
  have h169 := auctionSelectorSplitNotTakenTo h158 auctionLowerSplitWellFormed hlower
      auctionLowerSplitNextPc (by simp)
  have heq0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionLowerMidFirstArmPc j))
        (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionLowerMidFirstArmPc 4))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo (code := auctionBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I) (selWord := auctionSelWord I)
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (acc := (cA, σ)) ⟨570⟩ 4 h169
    (fun j hj => auctionLowerMidArmsWellFormed j (by omega)) heq0 htake
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem auctionX_auction_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨570⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd570⟩ := hreach
  exact evm_run rd570 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨581⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem auctionX_auction {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨570⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret auctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (auctionAuctionReturnData σ I) := by
  obtain ⟨_, _, rd570⟩ := hreach
  have rd583 := evm_run rd570 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨581⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push1 ⟨207⟩]
  obtain ⟨_, _, rd586⟩ := rd583.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd588⟩ := (evm_run rd586 with [push1 ⟨208⟩]).sload
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd591⟩ := (evm_run rd588 with [push1 ⟨209⟩]).sload
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd594⟩ := (evm_run rd591 with [push1 ⟨210⟩]).sload
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd597⟩ := (evm_run rd594 with [push1 ⟨211⟩]).sload
    (by native_decide) (by evm_ov)
  have rd629 := evm_run rd597 with [
    push2 ⟨629⟩, swap5, swap4, swap3, swap2, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    swap1, push1 ⟨1⟩, push1 ⟨160⟩, shl, swap1, div, push1 ⟨255⟩, and,
    dup7, jump (by jump_dest)]
  have rd637 := evm_run rd629 with [
    jumpdest, push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    swap7, dup8]
  have rd637' := evm_run rd637 with [
    raw mstore 6
      (auctionAuctionReturnNounMem (auctionAuctionNounWord σ I))
      (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov)]
  have rd645 := evm_run rd637' with [
    push1 ⟨32⟩, dup8, add, swap6, swap1, swap6]
  have rd645' := evm_run rd645 with [
    raw mstore 3
      (auctionAuctionReturnAmountMem (auctionAuctionNounWord σ I)
        (auctionAuctionAmountWord σ I))
      (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov)]
  have rd652 := evm_run rd645' with [
    swap4, dup6, add, swap3, swap1, swap3]
  have rd652' := evm_run rd652 with [
    raw mstore 3
      (auctionAuctionReturnStartMem (auctionAuctionNounWord σ I)
        (auctionAuctionAmountWord σ I) (auctionAuctionStartWord σ I))
      (UInt256.ofNat 7) (by native_decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov)]
  have rd657 := evm_run rd652' with [
    push1 ⟨96⟩, dup5, add]
  have rd657' := evm_run rd657 with [
    raw mstore 3
      (auctionAuctionReturnEndMem (auctionAuctionNounWord σ I)
        (auctionAuctionAmountWord σ I) (auctionAuctionStartWord σ I)
        (auctionAuctionEndWord σ I))
      (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov)]
  have rd671 := evm_run rd657' with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and,
    push1 ⟨128⟩, dup4, add]
  have hbidderClean :
      UInt256.land solcAddrMask (auctionPackedBidderWord (auctionAuctionPackedWord σ I)) =
        auctionPackedBidderWord (auctionAuctionPackedWord σ I) := by
    unfold auctionPackedBidderWord
    rw [u256_land_comm solcAddrMask
      (UInt256.land (auctionAuctionPackedWord σ I) solcAddrMask)]
    exact solcAddrMask_clean (solcAddrMask_result_canonical (auctionAuctionPackedWord σ I))
  have rd671' := evm_run rd671 with [
    raw mstore 3
      (auctionAuctionReturnBidderMem (auctionAuctionNounWord σ I)
        (auctionAuctionAmountWord σ I) (auctionAuctionStartWord σ I)
        (auctionAuctionEndWord σ I) (auctionPackedBidderWord (auctionAuctionPackedWord σ I)))
      (UInt256.ofNat 9) (by native_decide)
      mem_cost
      (by
        change (UInt256.toByteArray
            (UInt256.land solcAddrMask
              (auctionPackedBidderWord (auctionAuctionPackedWord σ I)))).write 0
            (auctionAuctionReturnEndMem (auctionAuctionNounWord σ I)
              (auctionAuctionAmountWord σ I) (auctionAuctionStartWord σ I)
              (auctionAuctionEndWord σ I)) 256 32 =
          auctionAuctionReturnBidderMem (auctionAuctionNounWord σ I)
            (auctionAuctionAmountWord σ I) (auctionAuctionStartWord σ I)
            (auctionAuctionEndWord σ I)
            (auctionPackedBidderWord (auctionAuctionPackedWord σ I))
        rw [hbidderClean]
        rfl)
      (by decide) (by evm_ov)]
  have rd678 := evm_run rd671' with [
    iszero, iszero, push1 ⟨160⟩, dup3, add]
  have rd678' := evm_run rd678 with [
    raw mstore 3
      (auctionAuctionReturnMem (auctionAuctionNounWord σ I)
        (auctionAuctionAmountWord σ I) (auctionAuctionStartWord σ I)
        (auctionAuctionEndWord σ I) (auctionPackedBidderWord (auctionAuctionPackedWord σ I))
        (auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord σ I)))
      (UInt256.ofNat 10) (by native_decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov)]
  have rd318 := evm_run rd678' with [
    push1 ⟨192⟩, add, push2 ⟨318⟩, jump (by jump_dest)]
  have hret := evm_run rd318 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost
      (auctionAuctionReturnMem_mload64 (auctionAuctionNounWord σ I)
        (auctionAuctionAmountWord σ I) (auctionAuctionStartWord σ I)
        (auctionAuctionEndWord σ I) (auctionPackedBidderWord (auctionAuctionPackedWord σ I))
        (auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord σ I)))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0
      (UInt256.toByteArray (auctionAuctionNounWord σ I) ++
        UInt256.toByteArray (auctionAuctionAmountWord σ I) ++
        UInt256.toByteArray (auctionAuctionStartWord σ I) ++
        UInt256.toByteArray (auctionAuctionEndWord σ I) ++
        UInt256.toByteArray (auctionPackedBidderWord (auctionAuctionPackedWord σ I)) ++
        UInt256.toByteArray (auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord σ I)))
      (by native_decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          auctionAuctionSubRet192_toNat]
        exact auctionAuctionReturnMem_read128_192 (auctionAuctionNounWord σ I)
          (auctionAuctionAmountWord σ I) (auctionAuctionStartWord σ I)
          (auctionAuctionEndWord σ I) (auctionPackedBidderWord (auctionAuctionPackedWord σ I))
          (auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord σ I)))
      (by evm_ov)]
  have hsettled :
      auctionPackedSettledEVMReturnWord (auctionAuctionPackedWord σ I) =
        auctionPackedSettledReturnWord (auctionAuctionPackedWord σ I) := by
    unfold auctionPackedSettledEVMReturnWord auctionPackedSettledReturnWord
      auctionPackedSettledEVMWord auctionPackedSettledWord
    rw [u256_land_comm]
  simpa [auctionAuctionReturnData, hsettled] using hret

theorem auctionAuctionBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 9))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 9) rfl _hsel
  have hdispatch := auctionDispatch_auction _hsel
  have hdecode := auctionDecode_auction (I := I) hsz
  have hreach := auctionReachAuctionBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hcode hsz _hsize _hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have h207 : auctionSlotWord ⟨207⟩ σ_evm I = auctionSlotWord ⟨207⟩ σ_solm I :=
      accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨207⟩ ⟨0⟩
    have h208 : auctionSlotWord ⟨208⟩ σ_evm I = auctionSlotWord ⟨208⟩ σ_solm I :=
      accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨208⟩ ⟨0⟩
    have h209 : auctionSlotWord ⟨209⟩ σ_evm I = auctionSlotWord ⟨209⟩ σ_solm I :=
      accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨209⟩ ⟨0⟩
    have h210 : auctionSlotWord ⟨210⟩ σ_evm I = auctionSlotWord ⟨210⟩ σ_solm I :=
      accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨210⟩ ⟨0⟩
    have h211 : auctionSlotWord ⟨211⟩ σ_evm I = auctionSlotWord ⟨211⟩ σ_solm I :=
      accountMapEquiv_storage_findD _hAccounts I.codeOwner ⟨211⟩ ⟨0⟩
    have hval :
        some (auctionAuctionReturnValues σ_solm I) =
          some (auctionAuctionReturnValues σ_evm I) := by
      simp [auctionAuctionReturnValues, auctionAuctionNounWord, auctionAuctionAmountWord,
        auctionAuctionStartWord, auctionAuctionEndWord, auctionAuctionPackedWord, h207, h208,
        h209, h210, h211]
    have hbody :
        ExecTransitionBody auctionConfig auctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ auctionGetter.body
          (.returned { contract := auctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some (auctionAuctionReturnValues σ_solm I))) := by
      simpa [auctionAuctionReturnValues, auctionAuctionReturnValuesState,
        auctionAuctionNounWord, auctionAuctionAmountWord, auctionAuctionStartWord,
        auctionAuctionEndWord, auctionAuctionPackedWord, auctionSlotWord, initState,
        Solm.EVM.storageLoad, State.lookupAccount] using
        auctionAuctionBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (by simp only [initState]; exact hwv)
    have henc :
        returnEquiv (auctionAuctionReturnData σ_evm I)
          (some (auctionAuctionReturnValues σ_evm I)) auctionGetter.returnType := by
      rw [auctionGetter]
      exact returnEquiv.returned rfl
        (by
          simpa [auctionAuctionReturnValues, auctionAuctionReturnData, auctionAuctionNounWord,
            auctionAuctionAmountWord, auctionAuctionStartWord, auctionAuctionEndWord,
            auctionAuctionPackedWord] using
            auctionAuctionReturnEncoding (auctionAuctionNounWord σ_evm I)
              (auctionAuctionAmountWord σ_evm I) (auctionAuctionStartWord σ_evm I)
              (auctionAuctionEndWord σ_evm I) (auctionAuctionPackedWord σ_evm I))
    exact (auctionX_auction hreach hwv).reEquivExecutionTransport _hcode hdispatch hdecode
      hbody hval _hAccounts henc
  · have hbody :
        ExecTransitionBody auctionConfig auctionContract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ auctionGetter.body
          .reverted := by
      simpa [auctionGetter, nonpayable] using
        bodyReverts_nonPayable (cfg := auctionConfig) (contract := auctionContract)
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (locals := ∅)
          (rest := [.return
            [.storage (aField "nounId"), .storage (aField "amount"),
              .storage (aField "startTime"), .storage (aField "endTime"),
              .storage (aField "bidder"), .storage (aField "settled")]])
          (by simpa only [initState] using hwv)
    exact (auctionX_auction_callvalue_ne hreach hwv).reEquivExecutionRevert _hcode
      hdispatch hdecode hbody

end Auction
