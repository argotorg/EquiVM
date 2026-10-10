import Benchmarks.UniswapV4PoolManager.PoolModifyFeesTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyFeesPreludePaidTrace
import Benchmarks.UniswapV4PoolManager.BlockTraceCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyFeesTailExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id x0 x1 x2 ptr x4 x5 x9 : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+31 ≤ 1024) (hI : evm.executionEnv = I)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127)
    (h : RD (deployedRuntime v) I g s0 ⟨5915⟩
      (positionUpdateInputStack evm id (poolModifyPositionKey p) p.delta (poolModifyFeeWord evm id p false)
        p.upper x0 x1 x2 ptr x4 x5 p.lower x9 (poolModifyFeeWord evm id p true) R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (fun _ post => post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ kr Cr,
        RD (deployedRuntime v) I g s0 (if p.delta < 0 then ⟨6620⟩ else ⟨6036⟩)
          (poolModifyFeesOutputStack (poolModifyFeeDeltaWord evm id p) ptr x0 x1 x2 x4 x5 x9 p R)
          mem aw rdata post.accountMap kr Cr)
      (fun _ _ => False) (poolModifyFeesResult f evm id p) := by
  have hpos := poolModifyPositionTrace (poolModifyFeesPreludeFrame f evm id p) v hstack hI hdlo hdhi h
  apply blockResultTrace_continueBlock hpos
  intro f1 mid _ ht1
  obtain ⟨hImid, hσmid, k2, C2, rd2⟩ := ht1
  dsimp only [positionUpdateContinuation] at rd2
  have hfee := poolModifyFeeDeltaTrace f1 v (by simp only [List.length_cons]; omega) hdlo hdhi rd2
  apply blockResultTrace_mono hfee
  intro f2 post _ ht2
  obtain ⟨rfl, k3, C3, rd3⟩ := ht2
  exact ⟨hImid, hσmid, k3, C3, rd3⟩

theorem poolModifyFeesPaidTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free id params x0 x1 x2 ptr x4 x5 x9 : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+31 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hdlo : -(2^127 : Int) ≤ p.delta) (hdhi : p.delta < 2^127)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) (hfl : 160 ≤ free.toNat)
    (hfh : free.toNat+64 < UInt256.size)
    (ha : UInt256.land (memLoad params mem) solcAddrMask = accountWord p.owner)
    (hs : memLoad (params+UInt256.ofNat 160) mem = p.salt)
    (hp : 64 ≤ params.toNat) (hps : params.toNat+192 ≤ mem.size) (hpf : params.toNat+160 < UInt256.size)
    (h5 : 5 ≤ aw.toNat) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨5722⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0
      (fun _ post => post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧ ∃ aw' kr Cr,
        Cₘ aw' ≤ Cr ∧ aw.toNat ≤ aw'.toNat ∧
        RD (deployedRuntime v) I g s0 (if p.delta < 0 then ⟨6620⟩ else ⟨6036⟩)
          (poolModifyFeesOutputStack (poolModifyFeeDeltaWord evm id p) ptr x0 x1 x2 x4 x5 x9 p R)
          (poolModifyFeesMemory mem free id p) aw' rdata post.accountMap kr Cr)
      (fun _ _ => False) (poolModifyFeesResult f evm id p) := by
  obtain ⟨aw1, k1, C1, hpaid1, haw1, rd1⟩ := poolModifyFeesPreludePaidTrace v (by omega) hI hm hmem hl hu
    hfree hfl hfh ha hs hp hps hpf h5 hpaid h
  have hcost := blockResultTrace_retainCost
    (facts := fun _ post => post.executionEnv = I ∧ post.σ₀ = evm.σ₀)
    (entry := ⟨⟨5915⟩,
      positionUpdateInputStack evm id (poolModifyPositionKey p) p.delta (poolModifyFeeWord evm id p false)
        p.upper x0 x1 x2 ptr x4 x5 p.lower x9 (poolModifyFeeWord evm id p true) R,
      poolModifyFeesMemory mem free id p, aw1, rdata, evm.accountMap⟩)
    (next := fun _ post => ⟨if p.delta < 0 then ⟨6620⟩ else ⟨6036⟩,
      poolModifyFeesOutputStack (poolModifyFeeDeltaWord evm id p) ptr x0 x1 x2 x4 x5 x9 p R,
      poolModifyFeesMemory mem free id p, aw1, rdata, post.accountMap⟩)
    (fun budget start ki Ci hin => by
      have hr := poolModifyFeesTailExactTrace f v hstack hI hdlo hdhi hin
      apply blockResultTrace_mono hr
      intro f' post _ ht'
      exact ⟨⟨ht'.1, ht'.2.1⟩, ht'.2.2⟩) rd1
  apply blockResultTrace_mono hcost
  intro f' post _ ht'
  obtain ⟨⟨hIpost, hσpost⟩, kr, Cr, hle, rd⟩ := ht'
  exact ⟨hIpost, hσpost, aw1, kr, Cr, hpaid1.trans hle, haw1, rd⟩

end Benchmarks.UniswapV4PoolManager
