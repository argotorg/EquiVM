import Examples.UniswapV2Pair.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Dispatcher reach lemmas for state-changing placeholder bodies -/

/-- Reach the `swap(uint256,uint256,address,bytes)` body entry through the optimized dispatcher. -/
theorem uniswapReachSwapBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x02, 0x2c, 0x0d, 0x9f]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨430⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x022c0d9f⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x02 0x2c 0x0d 0x9f ⟨0x022c0d9f⟩ (by decide) hsel
  exact uniswapReachLowestBody 0 (by decide) ⟨430⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => False.elim ((Nat.not_lt_zero j) hj))
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `mint(address)` body entry through the optimized dispatcher. -/
theorem uniswapReachMintBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x6a, 0x62, 0x78, 0x42]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1041⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x6a627842⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x6a 0x62 0x78 0x42 ⟨0x6a627842⟩ (by decide) hsel
  exact uniswapReachHighLowestBody 0 (by decide) ⟨1041⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => False.elim ((Nat.not_lt_zero j) hj))
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `burn(address)` body entry through the optimized dispatcher. -/
theorem uniswapReachBurnBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x89, 0xaf, 0xcb, 0x44]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1163⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0x89afcb44⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0x89 0xaf 0xcb 0x44 ⟨0x89afcb44⟩ (by decide) hsel
  exact uniswapReachHighLowerBody 1 (by decide) ⟨1163⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

/-- Reach the `permit(address,address,uint256,uint256,uint8,bytes32,bytes32)` body entry through
    the optimized dispatcher. -/
theorem uniswapReachPermitBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xd5, 0x05, 0xac, 0xcf]⟩) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1340⟩
        [uniswapSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : uniswapSelWord I = ⟨0xd505accf⟩ :=
    uniswapSelWord_eq_of_beq I hsz 0xd5 0x05 0xac 0xcf ⟨0xd505accf⟩ (by decide) hsel
  exact uniswapReachHighUpperBody 1 (by decide) ⟨1340⟩ hcode hwv hsz hsize
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (by rw [hword]; decide)
    (fun j hj => by
      rw [hword]
      interval_cases j
      all_goals decide)
    (by
      rw [hword]
      decide)
    (by jump_dest)
    (by decide)

end UniswapV2Pair
