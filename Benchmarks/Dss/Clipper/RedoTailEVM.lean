import Reasoning.Stepping
import Reasoning.Reach
import Benchmarks.Dss.Clipper.RedoSuckEVM

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Reasoning.Theory


end Reasoning.Theory

namespace Reasoning.Reach


end Reasoning.Reach

namespace Benchmarks.Dss.Clipper

abbrev clipperRedoEventMem0 (mem : ByteArray) (top : UInt256) : ByteArray :=
  top.toByteArray.write 0 mem 128 32

abbrev clipperRedoEventMem1 (mem : ByteArray) (top tab : UInt256) : ByteArray :=
  tab.toByteArray.write 0 (clipperRedoEventMem0 mem top) 160 32

abbrev clipperRedoEventMem2 (mem : ByteArray)
    (top tab lot : UInt256) : ByteArray :=
  lot.toByteArray.write 0 (clipperRedoEventMem1 mem top tab) 192 32

abbrev clipperRedoEventMem (mem : ByteArray)
    (top tab lot coin : UInt256) : ByteArray :=
  coin.toByteArray.write 0 (clipperRedoEventMem2 mem top tab lot) 224 32

theorem clipperRedoEventMem0_size {mem : ByteArray} (top : UInt256)
    (hmem : mem.size = 228) :
    (clipperRedoEventMem0 mem top).size = 228 := by
  unfold clipperRedoEventMem0
  exact toByteArray_write32_size_of_le mem top 128 228 228 hmem
    (by rw [hmem]; omega) (by native_decide)

theorem clipperRedoEventMem1_size {mem : ByteArray} (top tab : UInt256)
    (hmem : mem.size = 228) :
    (clipperRedoEventMem1 mem top tab).size = 228 := by
  unfold clipperRedoEventMem1
  exact toByteArray_write32_size_of_le (clipperRedoEventMem0 mem top) tab
    160 228 228 (clipperRedoEventMem0_size top hmem)
    (by rw [clipperRedoEventMem0_size top hmem]; omega) (by native_decide)

theorem clipperRedoEventMem2_size {mem : ByteArray} (top tab lot : UInt256)
    (hmem : mem.size = 228) :
    (clipperRedoEventMem2 mem top tab lot).size = 228 := by
  unfold clipperRedoEventMem2
  exact toByteArray_write32_size_of_le (clipperRedoEventMem1 mem top tab) lot
    192 228 228 (clipperRedoEventMem1_size top tab hmem)
    (by rw [clipperRedoEventMem1_size top tab hmem]; omega) (by native_decide)

theorem clipperRedoEventMem_size {mem : ByteArray} (top tab lot coin : UInt256)
    (hmem : mem.size = 228) :
    (clipperRedoEventMem mem top tab lot coin).size = 256 := by
  unfold clipperRedoEventMem
  exact toByteArray_write32_size_of_le (clipperRedoEventMem2 mem top tab lot) coin
    224 228 256 (clipperRedoEventMem2_size top tab lot hmem)
    (by rw [clipperRedoEventMem2_size top tab lot hmem]; omega) (by native_decide)

theorem clipperRedoEventMem_read64 {mem : ByteArray} (top tab lot coin : UInt256)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperRedoEventMem mem top tab lot coin).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperRedoEventMem clipperRedoEventMem2 clipperRedoEventMem1
    clipperRedoEventMem0
  rw [toByteArray_write_read_below_of_gap coin _ 224 64
    (by rw [clipperRedoEventMem2_size top tab lot hmem]; omega)
    (by omega)
    (by rw [clipperRedoEventMem2_size top tab lot hmem]; native_decide)]
  rw [toByteArray_write_read_below_of_gap lot _ 192 64
    (by rw [clipperRedoEventMem1_size top tab hmem]; omega)
    (by omega)
    (by rw [clipperRedoEventMem1_size top tab hmem]; native_decide)]
  rw [toByteArray_write_read_below_of_gap tab _ 160 64
    (by rw [clipperRedoEventMem0_size top hmem]; omega)
    (by omega)
    (by rw [clipperRedoEventMem0_size top hmem]; native_decide)]
  rw [toByteArray_write_read_below_of_gap top _ 128 64
    (by rw [hmem]; omega) (by omega) (by rw [hmem]; native_decide)]
  exact hread64

theorem clipperRedoEventMem0_size_196 {mem : ByteArray} (top : UInt256)
    (hmem : mem.size = 196) :
    (clipperRedoEventMem0 mem top).size = 196 := by
  unfold clipperRedoEventMem0
  exact toByteArray_write32_size_of_le mem top 128 196 196 hmem
    (by rw [hmem]; omega) (by native_decide)

theorem clipperRedoEventMem1_size_196 {mem : ByteArray} (top tab : UInt256)
    (hmem : mem.size = 196) :
    (clipperRedoEventMem1 mem top tab).size = 196 := by
  unfold clipperRedoEventMem1
  exact toByteArray_write32_size_of_le (clipperRedoEventMem0 mem top) tab
    160 196 196 (clipperRedoEventMem0_size_196 top hmem)
    (by rw [clipperRedoEventMem0_size_196 top hmem]; omega) (by native_decide)

theorem clipperRedoEventMem2_size_196 {mem : ByteArray} (top tab lot : UInt256)
    (hmem : mem.size = 196) :
    (clipperRedoEventMem2 mem top tab lot).size = 224 := by
  unfold clipperRedoEventMem2
  exact toByteArray_write32_size_of_le (clipperRedoEventMem1 mem top tab) lot
    192 196 224 (clipperRedoEventMem1_size_196 top tab hmem)
    (by rw [clipperRedoEventMem1_size_196 top tab hmem]; omega) (by native_decide)

theorem clipperRedoEventMem_size_196 {mem : ByteArray}
    (top tab lot coin : UInt256) (hmem : mem.size = 196) :
    (clipperRedoEventMem mem top tab lot coin).size = 256 := by
  unfold clipperRedoEventMem
  exact toByteArray_write32_size_of_le (clipperRedoEventMem2 mem top tab lot) coin
    224 224 256 (clipperRedoEventMem2_size_196 top tab lot hmem)
    (by rw [clipperRedoEventMem2_size_196 top tab lot hmem]) (by native_decide)

theorem clipperRedoEventMem_read64_196 {mem : ByteArray}
    (top tab lot coin : UInt256) (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperRedoEventMem mem top tab lot coin).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperRedoEventMem clipperRedoEventMem2 clipperRedoEventMem1
    clipperRedoEventMem0
  rw [toByteArray_write_read_below_of_gap coin _ 224 64
    (by rw [clipperRedoEventMem2_size_196 top tab lot hmem]; omega)
    (by omega)
    (by rw [clipperRedoEventMem2_size_196 top tab lot hmem]; native_decide)]
  rw [toByteArray_write_read_below_of_gap lot _ 192 64
    (by rw [clipperRedoEventMem1_size_196 top tab hmem]; omega)
    (by omega)
    (by rw [clipperRedoEventMem1_size_196 top tab hmem]; native_decide)]
  rw [toByteArray_write_read_below_of_gap tab _ 160 64
    (by rw [clipperRedoEventMem0_size_196 top hmem]; omega)
    (by omega)
    (by rw [clipperRedoEventMem0_size_196 top hmem]; native_decide)]
  rw [toByteArray_write_read_below_of_gap top _ 128 64
    (by rw [hmem]; omega) (by omega) (by rw [hmem]; native_decide)]
  exact hread64

set_option maxHeartbeats 1000000 in
theorem RD.clipperRedoEventUnlockSuccess {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {σ : AccountMap}
    {coin chip tip feedPrice lot tab done topNew tic usr two kpr id sel : UInt256}
    {R : List UInt256} {mem out : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8118⟩
      (coin :: chip :: tip :: feedPrice :: lot :: tab :: done :: topNew :: tic :: usr ::
        two :: kpr :: id :: ⟨502⟩ :: sel :: R)
      mem (UInt256.ofNat 8) out σ k C)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : ee.perm = true) (hov : R.length + 50 ≤ 1024) :
    RDret code g s0 (sstoreAccountMap ee.codeOwner σ ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  let eventTopic : UInt256 :=
    ⟨0x275de7ecdd375b5e8049319f8b350686131c219dd4dc450a08e9cf83b03c865f⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (mem := mem)
      (by rw [hmem]; norm_num) hread64
  have rd8119 := rd.jumpdest (by clipper_runtime_decode) (by evm_ov)
  have rd8120 := RD.dup12 rd8119 (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rd8140pre := evm_run rd8120 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw dup11 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw dup15 (by clipper_runtime_decode) (by evm_ov)]
  have rd8173 := rd8140pre.pushConst eventTopic
    (width := 32) (op := .PUSH32) (by decide)
    (by simpa [eventTopic] using
      (show decode code ⟨8140⟩ = some (.PUSH32, some (eventTopic, 32)) by
        clipper_runtime_decode))
    (by evm_ov)
  have rd8174 := RD.dup12 rd8173 (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rdMloadPre := evm_run rd8174 with [
    raw dup11 (by clipper_runtime_decode) (by evm_ov),
    raw dup11 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd8180 := rdMloadPre.mload 0 ⟨128⟩ (UInt256.ofNat 8)
    (by clipper_runtime_decode) mem_cost hmload64 (by native_decide) (by evm_ov)
  have rdTopPre := evm_run rd8180 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rdTop := rdTopPre.mstore 0 (clipperRedoEventMem0 mem topNew)
    (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rdTabPre := evm_run rdTop with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨128⟩ = ⟨160⟩ from by native_decide] at rdTabPre
  have rdTab := rdTabPre.mstore 0 (clipperRedoEventMem1 mem topNew tab)
    (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rdLotPre := evm_run rdTab with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨160⟩ = ⟨192⟩ from by native_decide] at rdLotPre
  have rdLot := rdLotPre.mstore 0 (clipperRedoEventMem2 mem topNew tab lot)
    (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rdCoinPre := evm_run rdLot with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨192⟩ = ⟨224⟩ from by native_decide] at rdCoinPre
  have rdCoin := rdCoinPre.mstore 0 (clipperRedoEventMem mem topNew tab lot coin)
    (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have hmloadEvent64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (clipperRedoEventMem mem topNew tab lot coin).size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((clipperRedoEventMem mem topNew tab lot coin).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
    exact mloadFreePtrValue
      (mem := clipperRedoEventMem mem topNew tab lot coin)
      (by rw [clipperRedoEventMem_size topNew tab lot coin hmem]; norm_num)
      (clipperRedoEventMem_read64 topNew tab lot coin hmem hread64)
  have rdLogPre0 := evm_run rdCoin with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap5 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rdLogPre1 := rdLogPre0.mload 0 ⟨128⟩ (UInt256.ofNat 8)
    (by clipper_runtime_decode) mem_cost hmloadEvent64 (by native_decide) (by evm_ov)
  have rdLogPre := evm_run rdLogPre1 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rdLog := RD.log4 0 (UInt256.ofNat 8) rdLogPre
    (by clipper_runtime_decode) hperm
    (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdUnlockPre := evm_run rdLog with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdUnlock⟩ := rdUnlockPre.sstore hperm (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rdReturn := evm_run rdUnlock with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  have rd502 := rdReturn.jump (by clipper_runtime_decode)
    (clipperRelyReturnJumpDest v hpatch) (by evm_ov)
  have rd503 := rd502.jumpdest (by clipper_decode) (by evm_ov)
  exact RD.stop rd503 (by clipper_decode) (by evm_ov)

-- The inactive-incentive branch has not built the `vat.suck` calldata, so it
-- reaches the shared event tail with the smaller 196-byte, seven-word memory.
-- The event stores below expand it to the same final eight-word memory.
set_option maxHeartbeats 1000000 in
theorem RD.clipperRedoEventUnlockSuccessFrom196 {code : ByteArray}
    (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {σ : AccountMap}
    {coin chip tip feedPrice lot tab done topNew tic usr two kpr id sel : UInt256}
    {R : List UInt256} {mem out : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨8118⟩
      (coin :: chip :: tip :: feedPrice :: lot :: tab :: done :: topNew :: tic :: usr ::
        two :: kpr :: id :: ⟨502⟩ :: sel :: R)
      mem (UInt256.ofNat 7) out σ k C)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : ee.perm = true) (hov : R.length + 50 ≤ 1024) :
    RDret code g s0 (sstoreAccountMap ee.codeOwner σ ⟨13⟩ ⟨0⟩)
      ByteArray.empty := by
  let eventTopic : UInt256 :=
    ⟨0x275de7ecdd375b5e8049319f8b350686131c219dd4dc450a08e9cf83b03c865f⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (mem := mem)
      (by rw [hmem]; norm_num) hread64
  have rd8119 := rd.jumpdest (by clipper_runtime_decode) (by evm_ov)
  have rd8120 := RD.dup12 rd8119 (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rd8140pre := evm_run rd8120 with [
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw dup11 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw dup15 (by clipper_runtime_decode) (by evm_ov)]
  have rd8173 := rd8140pre.pushConst eventTopic
    (width := 32) (op := .PUSH32) (by decide)
    (by simpa [eventTopic] using
      (show decode code ⟨8140⟩ = some (.PUSH32, some (eventTopic, 32)) by
        clipper_runtime_decode))
    (by evm_ov)
  have rd8174 := RD.dup12 rd8173 (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rdMloadPre := evm_run rd8174 with [
    raw dup11 (by clipper_runtime_decode) (by evm_ov),
    raw dup11 (by clipper_runtime_decode) (by evm_ov),
    raw dup8 (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd8180 := rdMloadPre.mload 0 ⟨128⟩ (UInt256.ofNat 7)
    (by clipper_runtime_decode) mem_cost hmload64 (by native_decide) (by evm_ov)
  have rdTopPre := evm_run rd8180 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rdTop := rdTopPre.mstore 0 (clipperRedoEventMem0 mem topNew)
    (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rdTabPre := evm_run rdTop with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨128⟩ = ⟨160⟩ from by native_decide] at rdTabPre
  have rdTab := rdTabPre.mstore 0 (clipperRedoEventMem1 mem topNew tab)
    (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rdLotPre := evm_run rdTab with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨160⟩ = ⟨192⟩ from by native_decide] at rdLotPre
  have rdLot := rdLotPre.mstore 0 (clipperRedoEventMem2 mem topNew tab lot)
    (UInt256.ofNat 7) (by clipper_runtime_decode) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have rdCoinPre := evm_run rdLot with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨32⟩ : UInt256) + ⟨192⟩ = ⟨224⟩ from by native_decide] at rdCoinPre
  have rdCoin := rdCoinPre.mstore 3 (clipperRedoEventMem mem topNew tab lot coin)
    (UInt256.ofNat 8) (by clipper_runtime_decode) mem_cost
    (by rfl) (by native_decide) (by evm_ov)
  have hmloadEvent64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (clipperRedoEventMem mem topNew tab lot coin).size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((clipperRedoEventMem mem topNew tab lot coin).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
    exact mloadFreePtrValue
      (mem := clipperRedoEventMem mem topNew tab lot coin)
      (by rw [clipperRedoEventMem_size_196 topNew tab lot coin hmem]; norm_num)
      (clipperRedoEventMem_read64_196 topNew tab lot coin hmem hread64)
  have rdLogPre0 := evm_run rdCoin with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap5 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rdLogPre1 := rdLogPre0.mload 0 ⟨128⟩ (UInt256.ofNat 8)
    (by clipper_runtime_decode) mem_cost hmloadEvent64 (by native_decide) (by evm_ov)
  have rdLogPre := evm_run rdLogPre1 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rdLog := RD.log4 0 (UInt256.ofNat 8) rdLogPre
    (by clipper_runtime_decode) hperm
    (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdUnlockPre := evm_run rdLog with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rdUnlock⟩ := rdUnlockPre.sstore hperm (by clipper_runtime_decode)
    (by simp only [List.length_cons]; omega)
  have rdReturn := evm_run rdUnlock with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov)]
  have rd502 := rdReturn.jump (by clipper_runtime_decode)
    (clipperRelyReturnJumpDest v hpatch) (by evm_ov)
  have rd503 := rd502.jumpdest (by clipper_decode) (by evm_ov)
  exact RD.stop rd503 (by clipper_decode) (by evm_ov)

end Benchmarks.Dss.Clipper
