import Benchmarks.Dss.Clipper.TakeCallback
import Benchmarks.Dss.Clipper.TakeDogDigs

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

theorem clipperDup16_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP16, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
        nn :: oo :: pp :: t)
    (hov : t.length + 17 ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
       else .ok
        (stSwap s
          (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk ::
            ll :: mm :: nn :: oo :: pp :: t),
          .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP16, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup16 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll ::
          mm :: nn :: oo :: pp :: t).length - 16 + 17 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem RD.clipperDup16 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
        nn :: oo :: pp :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP16, .none))
    (hov : t.length + 17 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll ::
        mm :: nn :: oo :: pp :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => clipperDup16_xstep hc hp hdec hs hov)

noncomputable abbrev clipperTakeEventMem0 (mem : ByteArray) (max : UInt256) : ByteArray :=
  (UInt256.toByteArray max).write 0 mem 128 32

noncomputable abbrev clipperTakeEventMem1 (mem : ByteArray) (max price : UInt256) :
    ByteArray :=
  (UInt256.toByteArray price).write 0 (clipperTakeEventMem0 mem max) 160 32

noncomputable abbrev clipperTakeEventMem2 (mem : ByteArray) (max price owe : UInt256) :
    ByteArray :=
  (UInt256.toByteArray owe).write 0 (clipperTakeEventMem1 mem max price) 192 32

noncomputable abbrev clipperTakeEventMem3 (mem : ByteArray)
    (max price owe tabNew : UInt256) : ByteArray :=
  (UInt256.toByteArray tabNew).write 0 (clipperTakeEventMem2 mem max price owe) 224 32

noncomputable abbrev clipperTakeEventMem (mem : ByteArray)
    (max price owe tabNew lotNew : UInt256) : ByteArray :=
  (UInt256.toByteArray lotNew).write 0
    (clipperTakeEventMem3 mem max price owe tabNew) 256 32

theorem clipperTakeEventMem0_size {mem : ByteArray} (max : UInt256)
    (hmem : mem.size = 260) :
    (clipperTakeEventMem0 mem max).size = 260 := by
  unfold clipperTakeEventMem0
  exact toByteArray_write32_size_of_le mem max 128 260 260 hmem
    (by rw [hmem]; omega) (by native_decide)

theorem clipperTakeEventMem1_size {mem : ByteArray} (max price : UInt256)
    (hmem : mem.size = 260) :
    (clipperTakeEventMem1 mem max price).size = 260 := by
  unfold clipperTakeEventMem1
  exact toByteArray_write32_size_of_le (clipperTakeEventMem0 mem max) price 160
    260 260 (clipperTakeEventMem0_size max hmem)
    (by rw [clipperTakeEventMem0_size max hmem]; omega) (by native_decide)

theorem clipperTakeEventMem2_size {mem : ByteArray}
    (max price owe : UInt256) (hmem : mem.size = 260) :
    (clipperTakeEventMem2 mem max price owe).size = 260 := by
  unfold clipperTakeEventMem2
  exact toByteArray_write32_size_of_le (clipperTakeEventMem1 mem max price) owe
    192 260 260 (clipperTakeEventMem1_size max price hmem)
    (by rw [clipperTakeEventMem1_size max price hmem]; omega) (by native_decide)

theorem clipperTakeEventMem3_size {mem : ByteArray}
    (max price owe tabNew : UInt256) (hmem : mem.size = 260) :
    (clipperTakeEventMem3 mem max price owe tabNew).size = 260 := by
  unfold clipperTakeEventMem3
  exact toByteArray_write32_size_of_le
    (clipperTakeEventMem2 mem max price owe) tabNew 224 260 260
    (clipperTakeEventMem2_size max price owe hmem)
    (by rw [clipperTakeEventMem2_size max price owe hmem]; omega)
    (by native_decide)

theorem clipperTakeEventMem_size {mem : ByteArray}
    (max price owe tabNew lotNew : UInt256) (hmem : mem.size = 260) :
    (clipperTakeEventMem mem max price owe tabNew lotNew).size = 288 := by
  unfold clipperTakeEventMem
  exact toByteArray_write32_size_of_le
    (clipperTakeEventMem3 mem max price owe tabNew) lotNew 256 260 288
    (clipperTakeEventMem3_size max price owe tabNew hmem)
    (by rw [clipperTakeEventMem3_size max price owe tabNew hmem]; omega)
    (by native_decide)

theorem clipperTakeEventMem_read64 {mem : ByteArray}
    (max price owe tabNew lotNew : UInt256)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperTakeEventMem mem max price owe tabNew lotNew).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperTakeEventMem clipperTakeEventMem3 clipperTakeEventMem2
    clipperTakeEventMem1 clipperTakeEventMem0
  rw [toByteArray_write_read_below_of_gap lotNew _ 256 64
    (by rw [clipperTakeEventMem3_size max price owe tabNew hmem]; omega)
    (by omega)
    (by rw [clipperTakeEventMem3_size max price owe tabNew hmem]; native_decide)]
  rw [toByteArray_write_read_below_of_gap tabNew _ 224 64
    (by rw [clipperTakeEventMem2_size max price owe hmem]; omega)
    (by omega)
    (by rw [clipperTakeEventMem2_size max price owe hmem]; native_decide)]
  rw [toByteArray_write_read_below_of_gap owe _ 192 64
    (by rw [clipperTakeEventMem1_size max price hmem]; omega)
    (by omega)
    (by rw [clipperTakeEventMem1_size max price hmem]; native_decide)]
  rw [toByteArray_write_read_below_of_gap price _ 160 64
    (by rw [clipperTakeEventMem0_size max hmem]; omega)
    (by omega)
    (by rw [clipperTakeEventMem0_size max hmem]; native_decide)]
  rw [toByteArray_write_read_below_of_gap max _ 128 64
    (by rw [hmem]; omega) (by omega) (by rw [hmem]; native_decide)]
  exact hread64

set_option maxHeartbeats 1000000 in
theorem RD.clipperTakeEventTailSuccess {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {owe tabNew lotNew price tic packed stopped dataLen dataStart who max amt id sel : UInt256}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD code ee g s0 ⟨5250⟩
      (owe :: tabNew :: lotNew :: price :: tic :: packed :: stopped :: dataLen ::
        dataStart :: who :: max :: amt :: id :: ⟨502⟩ :: [sel])
      mem (UInt256.ofNat 9) o (cA, σ) k C)
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : ee.perm = true) :
    RDret code g s0 (cA, sstoreAccountMap ee.codeOwner σ ⟨13⟩ ⟨0⟩) ByteArray.empty := by
  let eventTopic : UInt256 :=
    ⟨2662707474673484271508566864567884168301912169458095775925153504702713661105⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (mem := mem) (aw := UInt256.ofNat 9)
      (by rw [hmem]; norm_num) (by native_decide) hread64
  have rd5255 := evm_run rd with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost
      hmload64 (by native_decide) (by evm_ov)]
  have rd5257pre := evm_run rd5255 with [
    raw dup13 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov)]
  have rd5258 := evm_run rd5257pre with [
    raw mstore 0 (clipperTakeEventMem0 mem max) (UInt256.ofNat 9)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd5264pre := evm_run rd5258 with [
    raw push1 ⟨32⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup7 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨32⟩ = ⟨160⟩ from by native_decide] at rd5264pre
  have rd5265 := evm_run rd5264pre with [
    raw mstore 0 (clipperTakeEventMem1 mem max price) (UInt256.ofNat 9)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd5270pre := evm_run rd5265 with [
    raw dup1 (by clipper_runtime_decode) (by evm_ov),
    raw dup3 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨64⟩ : UInt256) + ⟨128⟩ = ⟨192⟩ from by native_decide] at rd5270pre
  have rd5271 := evm_run rd5270pre with [
    raw mstore 0 (clipperTakeEventMem2 mem max price owe) (UInt256.ofNat 9)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd5277pre := evm_run rd5271 with [
    raw push1 ⟨96⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨96⟩ = ⟨224⟩ from by native_decide] at rd5277pre
  have rd5278 := evm_run rd5277pre with [
    raw mstore 0 (clipperTakeEventMem3 mem max price owe tabNew) (UInt256.ofNat 9)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have rd5284pre := evm_run rd5278 with [
    raw push1 ⟨128⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw dup6 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  rw [show (⟨128⟩ : UInt256) + ⟨128⟩ = ⟨256⟩ from by native_decide] at rd5284pre
  have rd5285 := evm_run rd5284pre with [
    raw mstore 0 (clipperTakeEventMem mem max price owe tabNew lotNew) (UInt256.ofNat 9)
      (by clipper_runtime_decode) mem_cost (by rfl) (by native_decide) (by evm_ov)]
  have hmloadEvent64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (clipperTakeEventMem mem max price owe tabNew lotNew).size ∨
          (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((clipperTakeEventMem mem max price owe tabNew lotNew).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
    exact mloadFreePtrValue
      (mem := clipperTakeEventMem mem max price owe tabNew lotNew) (aw := UInt256.ofNat 9)
      (by rw [clipperTakeEventMem_size max price owe tabNew lotNew hmem]; norm_num)
      (by native_decide)
      (clipperTakeEventMem_read64 max price owe tabNew lotNew hmem hread64)
  have rd5298pre := evm_run rd5285 with [
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by clipper_runtime_decode) mem_cost
      hmloadEvent64 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw shl (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw dup9 (by clipper_runtime_decode) (by evm_ov),
    raw and (by clipper_runtime_decode) (by evm_ov),
    raw swap2 (by clipper_runtime_decode) (by evm_ov)]
  have rd5299pre0 := RD.clipperDup16 rd5298pre
    (by clipper_runtime_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5299pre := evm_run rd5299pre0 with [
    raw swap2 (by clipper_runtime_decode) (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by native_decide] at rd5299pre
  have rd5333 := rd5299pre.pushConst eventTopic
    (width := 32) (op := .PUSH32) (by decide)
    (by simpa [eventTopic] using
      (show decode code ⟨5300⟩ = some (.PUSH32, some (eventTopic, 32)) by
        clipper_runtime_decode))
    (by evm_ov)
  have rd5341pre := evm_run rd5333 with [
    raw swap2 (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov),
    raw sub (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by clipper_runtime_decode) (by evm_ov),
    raw add (by clipper_runtime_decode) (by evm_ov),
    raw swap1 (by clipper_runtime_decode) (by evm_ov)]
  have rd5342 := RD.log3 0 (UInt256.ofNat 9) rd5341pre
    (by clipper_runtime_decode) hperm
    (by
      intro s hawEq hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawEq, hstk]
      native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5348pre := evm_run rd5342 with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨13⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd5349⟩ := rd5348pre.sstore hperm (by clipper_runtime_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5360 := evm_run rd5349 with [
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
  have rd502 := rd5360.jump (by clipper_runtime_decode)
    (clipperRelyReturnJumpDest v hpatch) (by evm_ov)
  have rd503 := rd502.jumpdest (by clipper_decode) (by evm_ov)
  exact RD.stop rd503 (by clipper_decode) (by evm_ov)

end Benchmarks.Dss.Clipper
