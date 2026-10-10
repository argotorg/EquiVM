import Benchmarks.UniswapV4PoolManager.PoolModifyTickResultTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyTickMemory
import Benchmarks.UniswapV4PoolManager.PoolUpdateTickLowerCorrect
import Benchmarks.UniswapV4PoolManager.PoolUpdateTickUpperCorrect

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyTwoTicksNormal (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 evm : State) (mem rdata : ByteArray) (id ptr x0 x1 x2 x4 x5 : UInt256)
    (p : PoolModifyParams) (R : List UInt256) (_ : Frame) (post : State) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧
  (EVM.wordOfInt (tickGrossAfterInt (poolModifyLowerPacked evm id p) p.delta)).toNat < 2^128 ∧
  (EVM.wordOfInt (tickGrossAfterInt (poolModifyUpperPacked evm id p) p.delta)).toNat < 2^128 ∧
  ∃ aw k C, RD (deployedRuntime v) I g s0 (if 0 ≤ p.delta then ⟨7329⟩ else ⟨7256⟩)
    (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: R)
    (poolModifyTwoTicksMemory mem ptr id p evm) aw rdata post.accountMap k C

def poolModifyTwoTicksActiveWords (aw ptr id : UInt256) (p : PoolModifyParams) (evm : State) : UInt256 :=
  tickUpperUpdateActiveWords (tickLowerUpdateActiveWords aw ptr) ptr (poolModifyUpperPacked evm id p)

def poolModifyTwoTicksNormalAtAW (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 evm : State) (mem rdata : ByteArray) (id ptr x0 x1 x2 x4 x5 : UInt256)
    (p : PoolModifyParams) (R : List UInt256) (aw : UInt256) (_ : Frame) (post : State) : Prop :=
  post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧
  (EVM.wordOfInt (tickGrossAfterInt (poolModifyLowerPacked evm id p) p.delta)).toNat < 2^128 ∧
  (EVM.wordOfInt (tickGrossAfterInt (poolModifyUpperPacked evm id p) p.delta)).toNat < 2^128 ∧
  ∃ k C, RD (deployedRuntime v) I g s0 (if 0 ≤ p.delta then ⟨7329⟩ else ⟨7256⟩)
    (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: R)
    (poolModifyTwoTicksMemory mem ptr id p evm) aw rdata post.accountMap k C

theorem poolModifyTwoTicksExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id ptr x0 x1 x2 x4 x5 : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+21 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hptr : 160 ≤ ptr.toNat) (hfit : ptr.toNat+32 < UInt256.size)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hd : signedFits ⟨128, by decide⟩ p.delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6949⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (poolModifyTwoTicksNormalAtAW v I g s0 evm mem rdata id ptr x0 x1 x2 x4 x5 p R (poolModifyTwoTicksActiveWords aw ptr id p evm))
      (fun _ _ => False) (poolModifyTwoTicksResult f evm id p) := by
  have hlo := poolUpdateTickLowerExactResultTrace (poolModifyTickAliasFrame f id false) v hstack hI hm hmem hl hu hd h
  apply blockResultTrace_continueBlock (poolModifyTickResultTrace hlo)
  intro f1 mid hmid ht
  have hmideq := (poolModifyTickResult_normal hmid).2
  dsimp only [tickLowerReturnTraceAtAW] at ht
  obtain ⟨hImid, hσmid, hgl, k1, C1, rd1⟩ := ht
  simp only [wordOfInt_ofNat_toNat] at rd1
  have hm1 : memLoad (UInt256.ofNat 128) (poolModifyLowerMemory mem ptr id p evm) = poolSlot id :=
    (poolModifyLowerMemory_loadWord mem ptr id p evm (UInt256.ofNat 128) (by decide) hmem hptr hfit).trans hm
  have hup := poolUpdateTickUpperExactResultTrace (poolModifyTickAliasFrame f1 id true) v
    (by simp only [List.length_cons]; omega) hImid hm1 hd rd1
  have huTrace := poolModifyTickResultTrace
    (fl := tickFlipped (poolModifyLowerPacked evm id p) p.delta)
    (gl := EVM.wordOfInt (tickGrossAfterInt (poolModifyLowerPacked evm id p) p.delta))
    (fu := false) (gu := ⟨0⟩) hup
  apply blockResultTrace_mono huTrace
  intro f2 post hpost ht2
  dsimp only [tickUpperReturnTraceAtAW] at ht2
  obtain ⟨hIpost, hσpost, hgu, k2, C2, rd2⟩ := ht2
  simp only [wordOfInt_ofNat_toNat] at rd2
  have hglo : (EVM.wordOfInt (tickGrossAfterInt (poolModifyLowerPacked evm id p) p.delta)).toNat < 2^128 := by
    have hg := hgl.2
    change (Int.ofNat _) < (2^128 : Int) at hg
    simp only [Int.ofNat_eq_natCast] at hg
    exact_mod_cast hg
  have hgup : (EVM.wordOfInt (tickGrossAfterInt (poolModifyUpperPacked evm id p) p.delta)).toNat < 2^128 := by
    have hg := hgu.2
    rw [hmideq] at hg
    change (Int.ofNat _) < (2^128 : Int) at hg
    simp only [Int.ofNat_eq_natCast] at hg
    exact_mod_cast hg
  refine ⟨hIpost, hσpost.trans hσmid, hglo, hgup, k2, C2, ?_⟩
  simpa only [hmideq, poolModifyTwoTicksMemory, poolModifyLowerMemory, poolModifyLowerPacked,
    poolModifyUpperPacked, poolModifyTwoTicksActiveWords] using rd2

theorem poolModifyTwoTicksTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id ptr x0 x1 x2 x4 x5 : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+21 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hptr : 160 ≤ ptr.toNat) (hfit : ptr.toNat+32 < UInt256.size)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hd : signedFits ⟨128, by decide⟩ p.delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6949⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (poolModifyTwoTicksNormal v I g s0 evm mem rdata id ptr x0 x1 x2 x4 x5 p R)
      (fun _ _ => False) (poolModifyTwoTicksResult f evm id p) := by
  have hr := poolModifyTwoTicksExactTrace f v hstack hI hm hmem hptr hfit hl hu hd h
  apply blockResultTrace_mono hr
  intro f1 post _ ht
  exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, _, ht.2.2.2.2⟩

end Benchmarks.UniswapV4PoolManager
