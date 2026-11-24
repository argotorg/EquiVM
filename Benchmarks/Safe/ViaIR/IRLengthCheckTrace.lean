import Benchmarks.Safe.ViaIR.IRLengthCheck

variable {fork : Ethereum.Fork}

/-! Exact execution certificate for the new zero-argument length-failure path.

The finite trace checks each actual opcode against `safeBytecode`, including the dispatcher.
It takes 111 instructions and 460 gas. Calldata remains symbolic: only its size and selector
word are used. The final theorems instantiate the symbolic array from `IRLengthCheck` and
match the bytecode's revert with the artifact-specific decoder's rejection.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

private def irCursor (I : ExecutionEnv) (k pc gas : ℕ) (stack : List UInt256)
    (initialized : Bool) : State :=
  { (default : State) with
    executionEnv := I
    machineState := { (default : MachineState) with
      pc := UInt256.ofNat pc
      stack := stack
      execLength := k
      gasAvailable := .ofUInt256 (UInt256.ofNat gas)
      memory := if initialized then solcFreePtrMem else ByteArray.empty
      activeWords := if initialized then ⟨3⟩ else ⟨0⟩ } }

private theorem exactNonceHuge {I : ExecutionEnv}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size = 2 ^ 255 + 4)
    (hvalue : I.weiValue = ⟨0⟩)
    (hword : UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ =
      ⟨0xaffed0e0⟩) :
    X fork 1001 (D_J safeBytecode 0) (irCursor I 0 0 1000 [] false) =
      .ok (.revert ⟨540⟩ ByteArray.empty) := by
  have h0 : Xstep fork (D_J safeBytecode 0) (irCursor I 0 0 1000 [] false) =
      .ok ((irCursor I 1 2 997 [⟨128⟩] false), .none) := by
    rw [push1_xstep (s := (irCursor I 0 0 1000 [] false)) (code := safeBytecode) (pcv := ⟨0⟩) (argv
      := ⟨128⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h1 : Xstep fork (D_J safeBytecode 0) (irCursor I 1 2 997 [⟨128⟩] false) =
      .ok ((irCursor I 2 4 994 [⟨64⟩, ⟨128⟩] false), .none) := by
    rw [push1_xstep (s := (irCursor I 1 2 997 [⟨128⟩] false)) (code := safeBytecode) (pcv := ⟨2⟩)
      (argv := ⟨64⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h2 : Xstep fork (D_J safeBytecode 0) (irCursor I 2 4 994 [⟨64⟩, ⟨128⟩] false) =
      .ok ((irCursor I 3 5 982 [] true), .none) := by
    rw [mstore_xstep (s := (irCursor I 2 4 994 [⟨64⟩, ⟨128⟩] false)) (code := safeBytecode) (pcv :=
      ⟨4⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    simp only [stMStore, irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
    rfl
  have h3 : Xstep fork (D_J safeBytecode 0) (irCursor I 3 5 982 [] true) =
      .ok ((irCursor I 4 7 979 [⟨4⟩] true), .none) := by
    rw [push1_xstep (s := (irCursor I 3 5 982 [] true)) (code := safeBytecode) (pcv := ⟨5⟩) (argv :=
      ⟨4⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h4 : Xstep fork (D_J safeBytecode 0) (irCursor I 4 7 979 [⟨4⟩] true) =
      .ok ((irCursor I 5 8 977 [(UInt256.ofNat (2 ^ 255 + 4)), ⟨4⟩] true), .none) := by
    rw [calldatasize_xstep (s := (irCursor I 4 7 979 [⟨4⟩] true)) (code := safeBytecode) (pcv :=
      ⟨7⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    simp only [stCalldatasize, irCursor, hsize]
    rfl
  have h5 : Xstep fork (D_J safeBytecode 0) (irCursor I 5 8 977 [(UInt256.ofNat (2 ^ 255 + 4)), ⟨4⟩]
    true) =
      .ok ((irCursor I 6 9 974 [⟨0⟩] true), .none) := by
    rw [lt_xstep (s := (irCursor I 5 8 977 [(UInt256.ofNat (2 ^ 255 + 4)), ⟨4⟩] true)) (code :=
      safeBytecode) (pcv := ⟨8⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h6 : Xstep fork (D_J safeBytecode 0) (irCursor I 6 9 974 [⟨0⟩] true) =
      .ok ((irCursor I 7 10 971 [⟨1⟩] true), .none) := by
    rw [iszero_xstep (s := (irCursor I 6 9 974 [⟨0⟩] true)) (code := safeBytecode) (pcv := ⟨9⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h7 : Xstep fork (D_J safeBytecode 0) (irCursor I 7 10 971 [⟨1⟩] true) =
      .ok ((irCursor I 8 13 968 [⟨161⟩, ⟨1⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 7 10 971 [⟨1⟩] true)) (code := safeBytecode) (pcv := ⟨10⟩)
      (argv := ⟨161⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h8 : Xstep fork (D_J safeBytecode 0) (irCursor I 8 13 968 [⟨161⟩, ⟨1⟩] true) =
      .ok ((irCursor I 9 161 958 [] true), .none) := by
    rw [jumpi_t_xstep (s := (irCursor I 8 13 968 [⟨161⟩, ⟨1⟩] true)) (code := safeBytecode) (pcv :=
      ⟨13⟩)
      hcode rfl (by native_decide) rfl (by decide +kernel) (by jump_dest)
        (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h9 : Xstep fork (D_J safeBytecode 0) (irCursor I 9 161 958 [] true) =
      .ok ((irCursor I 10 162 957 [] true), .none) := by
    rw [jumpdest_xstep (s := (irCursor I 9 161 958 [] true)) (code := safeBytecode) (pcv := ⟨161⟩)
      hcode rfl (by native_decide) (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h10 : Xstep fork (D_J safeBytecode 0) (irCursor I 10 162 957 [] true) =
      .ok ((irCursor I 11 163 955 [⟨0⟩] true), .none) := by
    rw [push0_xstep (s := (irCursor I 10 162 957 [] true)) (code := safeBytecode) (pcv := ⟨162⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h11 : Xstep fork (D_J safeBytecode 0) (irCursor I 11 163 955 [⟨0⟩] true) =
      .ok ((irCursor I 12 164 953 [⟨0⟩, ⟨0⟩] true), .none) := by
    rw [push0_xstep (s := (irCursor I 11 163 955 [⟨0⟩] true)) (code := safeBytecode) (pcv := ⟨163⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h12 : Xstep fork (D_J safeBytecode 0) (irCursor I 12 164 953 [⟨0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 13 165 950 [(uInt256OfByteArray (I.calldata.readBytes 0 32)), ⟨0⟩] true),
        .none) := by
    rw [calldataload_xstep (s := (irCursor I 12 164 953 [⟨0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨164⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h13 : Xstep fork (D_J safeBytecode 0) (irCursor I 13 165 950 [(uInt256OfByteArray
    (I.calldata.readBytes 0 32)), ⟨0⟩] true) =
      .ok ((irCursor I 14 167 947 [⟨224⟩, (uInt256OfByteArray (I.calldata.readBytes 0 32)), ⟨0⟩]
        true), .none) := by
    rw [push1_xstep (s := (irCursor I 13 165 950 [(uInt256OfByteArray (I.calldata.readBytes 0 32)),
      ⟨0⟩] true)) (code := safeBytecode) (pcv := ⟨165⟩) (argv := ⟨224⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h14 : Xstep fork (D_J safeBytecode 0) (irCursor I 14 167 947 [⟨224⟩, (uInt256OfByteArray
    (I.calldata.readBytes 0 32)), ⟨0⟩] true) =
      .ok ((irCursor I 15 168 944 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [shr_xstep (s := (irCursor I 14 167 947 [⟨224⟩, (uInt256OfByteArray (I.calldata.readBytes 0
      32)), ⟨0⟩] true)) (code := safeBytecode) (pcv := ⟨167⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    simp only [stBinop, irCursor, hword]
    rfl
  have h15 : Xstep fork (D_J safeBytecode 0) (irCursor I 15 168 944 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 16 169 941 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 15 168 944 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨168⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h16 : Xstep fork (D_J safeBytecode 0) (irCursor I 16 169 941 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 17 174 938 [⟨223883027⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push4_xstep (s := (irCursor I 16 169 941 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨169⟩) (argv := ⟨223883027⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h17 : Xstep fork (D_J safeBytecode 0) (irCursor I 17 174 938 [⟨223883027⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 18 175 935 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 17 174 938 [⟨223883027⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨174⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h18 : Xstep fork (D_J safeBytecode 0) (irCursor I 18 175 935 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 19 178 932 [⟨6678⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 18 175 935 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨175⟩) (argv := ⟨6678⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h19 : Xstep fork (D_J safeBytecode 0) (irCursor I 19 178 932 [⟨6678⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 20 179 922 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 19 178 932 [⟨6678⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨178⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h20 : Xstep fork (D_J safeBytecode 0) (irCursor I 20 179 922 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 21 180 919 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 20 179 922 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨179⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h21 : Xstep fork (D_J safeBytecode 0) (irCursor I 21 180 919 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 22 185 916 [⟨318466272⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push4_xstep (s := (irCursor I 21 180 919 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨180⟩) (argv := ⟨318466272⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h22 : Xstep fork (D_J safeBytecode 0) (irCursor I 22 185 916 [⟨318466272⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 23 186 913 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 22 185 916 [⟨318466272⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨185⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h23 : Xstep fork (D_J safeBytecode 0) (irCursor I 23 186 913 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 24 189 910 [⟨6581⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 23 186 913 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨186⟩) (argv := ⟨6581⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h24 : Xstep fork (D_J safeBytecode 0) (irCursor I 24 189 910 [⟨6581⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 25 190 900 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 24 189 910 [⟨6581⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨189⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h25 : Xstep fork (D_J safeBytecode 0) (irCursor I 25 190 900 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 26 191 897 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 25 190 900 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨190⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h26 : Xstep fork (D_J safeBytecode 0) (irCursor I 26 191 897 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 27 196 894 [⟨533383155⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push4_xstep (s := (irCursor I 26 191 897 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨191⟩) (argv := ⟨533383155⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h27 : Xstep fork (D_J safeBytecode 0) (irCursor I 27 196 894 [⟨533383155⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 28 197 891 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 27 196 894 [⟨533383155⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨196⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h28 : Xstep fork (D_J safeBytecode 0) (irCursor I 28 197 891 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 29 200 888 [⟨6508⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 28 197 891 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨197⟩) (argv := ⟨6508⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h29 : Xstep fork (D_J safeBytecode 0) (irCursor I 29 200 888 [⟨6508⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 30 201 878 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 29 200 888 [⟨6508⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨200⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h30 : Xstep fork (D_J safeBytecode 0) (irCursor I 30 201 878 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 31 202 875 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 30 201 878 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨201⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h31 : Xstep fork (D_J safeBytecode 0) (irCursor I 31 202 875 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 32 207 872 [⟨765121853⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push4_xstep (s := (irCursor I 31 202 875 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨202⟩) (argv := ⟨765121853⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h32 : Xstep fork (D_J safeBytecode 0) (irCursor I 32 207 872 [⟨765121853⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 33 208 869 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 32 207 872 [⟨765121853⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨207⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h33 : Xstep fork (D_J safeBytecode 0) (irCursor I 33 208 869 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 34 211 866 [⟨6473⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 33 208 869 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨208⟩) (argv := ⟨6473⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h34 : Xstep fork (D_J safeBytecode 0) (irCursor I 34 211 866 [⟨6473⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 35 212 856 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 34 211 866 [⟨6473⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨211⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h35 : Xstep fork (D_J safeBytecode 0) (irCursor I 35 212 856 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 36 213 853 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 35 212 856 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨212⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h36 : Xstep fork (D_J safeBytecode 0) (irCursor I 36 213 853 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 37 218 850 [⟨794083182⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push4_xstep (s := (irCursor I 36 213 853 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨213⟩) (argv := ⟨794083182⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h37 : Xstep fork (D_J safeBytecode 0) (irCursor I 37 218 850 [⟨794083182⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 38 219 847 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 37 218 850 [⟨794083182⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨218⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h38 : Xstep fork (D_J safeBytecode 0) (irCursor I 38 219 847 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 39 222 844 [⟨6387⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 38 219 847 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨219⟩) (argv := ⟨6387⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h39 : Xstep fork (D_J safeBytecode 0) (irCursor I 39 222 844 [⟨6387⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 40 223 834 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 39 222 844 [⟨6387⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨222⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h40 : Xstep fork (D_J safeBytecode 0) (irCursor I 40 223 834 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 41 224 831 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 40 223 834 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨223⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h41 : Xstep fork (D_J safeBytecode 0) (irCursor I 41 224 831 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 42 229 828 [⟨1183261095⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) :=
        by
    rw [push4_xstep (s := (irCursor I 41 224 831 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨224⟩) (argv := ⟨1183261095⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h42 : Xstep fork (D_J safeBytecode 0) (irCursor I 42 229 828 [⟨1183261095⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 43 230 825 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 42 229 828 [⟨1183261095⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨229⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h43 : Xstep fork (D_J safeBytecode 0) (irCursor I 43 230 825 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 44 233 822 [⟨6323⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 43 230 825 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨230⟩) (argv := ⟨6323⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h44 : Xstep fork (D_J safeBytecode 0) (irCursor I 44 233 822 [⟨6323⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 45 234 812 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 44 233 822 [⟨6323⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨233⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h45 : Xstep fork (D_J safeBytecode 0) (irCursor I 45 234 812 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 46 235 809 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 45 234 812 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨234⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h46 : Xstep fork (D_J safeBytecode 0) (irCursor I 46 235 809 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 47 240 806 [⟨1378420543⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) :=
        by
    rw [push4_xstep (s := (irCursor I 46 235 809 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨235⟩) (argv := ⟨1378420543⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h47 : Xstep fork (D_J safeBytecode 0) (irCursor I 47 240 806 [⟨1378420543⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 48 241 803 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 47 240 806 [⟨1378420543⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨240⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h48 : Xstep fork (D_J safeBytecode 0) (irCursor I 48 241 803 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 49 244 800 [⟨6217⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 48 241 803 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨241⟩) (argv := ⟨6217⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h49 : Xstep fork (D_J safeBytecode 0) (irCursor I 49 244 800 [⟨6217⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 50 245 790 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 49 244 800 [⟨6217⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨244⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h50 : Xstep fork (D_J safeBytecode 0) (irCursor I 50 245 790 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 51 246 787 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 50 245 790 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨245⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h51 : Xstep fork (D_J safeBytecode 0) (irCursor I 51 246 787 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 52 251 784 [⟨1445245531⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) :=
        by
    rw [push4_xstep (s := (irCursor I 51 246 787 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨246⟩) (argv := ⟨1445245531⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h52 : Xstep fork (D_J safeBytecode 0) (irCursor I 52 251 784 [⟨1445245531⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 53 252 781 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 52 251 784 [⟨1445245531⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨251⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h53 : Xstep fork (D_J safeBytecode 0) (irCursor I 53 252 781 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 54 255 778 [⟨6090⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 53 252 781 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨252⟩) (argv := ⟨6090⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h54 : Xstep fork (D_J safeBytecode 0) (irCursor I 54 255 778 [⟨6090⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 55 256 768 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 54 255 778 [⟨6090⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨255⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h55 : Xstep fork (D_J safeBytecode 0) (irCursor I 55 256 768 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 56 257 765 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 55 256 768 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨256⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h56 : Xstep fork (D_J safeBytecode 0) (irCursor I 56 257 765 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 57 262 762 [⟨1525071159⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) :=
        by
    rw [push4_xstep (s := (irCursor I 56 257 765 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨257⟩) (argv := ⟨1525071159⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h57 : Xstep fork (D_J safeBytecode 0) (irCursor I 57 262 762 [⟨1525071159⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 58 263 759 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 57 262 762 [⟨1525071159⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨262⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h58 : Xstep fork (D_J safeBytecode 0) (irCursor I 58 263 759 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 59 266 756 [⟨6048⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 58 263 759 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨263⟩) (argv := ⟨6048⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h59 : Xstep fork (D_J safeBytecode 0) (irCursor I 59 266 756 [⟨6048⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 60 267 746 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 59 266 756 [⟨6048⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨266⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h60 : Xstep fork (D_J safeBytecode 0) (irCursor I 60 267 746 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 61 268 743 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 60 267 746 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨267⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h61 : Xstep fork (D_J safeBytecode 0) (irCursor I 61 268 743 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 62 273 740 [⟨1628133669⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) :=
        by
    rw [push4_xstep (s := (irCursor I 61 268 743 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨268⟩) (argv := ⟨1628133669⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h62 : Xstep fork (D_J safeBytecode 0) (irCursor I 62 273 740 [⟨1628133669⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 63 274 737 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 62 273 740 [⟨1628133669⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨273⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h63 : Xstep fork (D_J safeBytecode 0) (irCursor I 63 274 737 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 64 277 734 [⟨5785⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 63 274 737 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨274⟩) (argv := ⟨5785⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h64 : Xstep fork (D_J safeBytecode 0) (irCursor I 64 277 734 [⟨5785⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 65 278 724 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 64 277 734 [⟨5785⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨277⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h65 : Xstep fork (D_J safeBytecode 0) (irCursor I 65 278 724 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 66 279 721 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 65 278 724 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨278⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h66 : Xstep fork (D_J safeBytecode 0) (irCursor I 66 279 721 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 67 284 718 [⟨1766752451⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) :=
        by
    rw [push4_xstep (s := (irCursor I 66 279 721 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨279⟩) (argv := ⟨1766752451⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h67 : Xstep fork (D_J safeBytecode 0) (irCursor I 67 284 718 [⟨1766752451⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 68 285 715 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 67 284 718 [⟨1766752451⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨284⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h68 : Xstep fork (D_J safeBytecode 0) (irCursor I 68 285 715 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 69 288 712 [⟨5693⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 68 285 715 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨285⟩) (argv := ⟨5693⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h69 : Xstep fork (D_J safeBytecode 0) (irCursor I 69 288 712 [⟨5693⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 70 289 702 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 69 288 712 [⟨5693⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨288⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h70 : Xstep fork (D_J safeBytecode 0) (irCursor I 70 289 702 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 71 290 699 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 70 289 702 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨289⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h71 : Xstep fork (D_J safeBytecode 0) (irCursor I 71 290 699 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 72 295 696 [⟨1786122754⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) :=
        by
    rw [push4_xstep (s := (irCursor I 71 290 699 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨290⟩) (argv := ⟨1786122754⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h72 : Xstep fork (D_J safeBytecode 0) (irCursor I 72 295 696 [⟨1786122754⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 73 296 693 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 72 295 696 [⟨1786122754⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨295⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h73 : Xstep fork (D_J safeBytecode 0) (irCursor I 73 296 693 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 74 299 690 [⟨4354⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 73 296 693 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨296⟩) (argv := ⟨4354⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h74 : Xstep fork (D_J safeBytecode 0) (irCursor I 74 299 690 [⟨4354⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 75 300 680 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 74 299 690 [⟨4354⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨299⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h75 : Xstep fork (D_J safeBytecode 0) (irCursor I 75 300 680 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 76 301 677 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 75 300 680 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨300⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h76 : Xstep fork (D_J safeBytecode 0) (irCursor I 76 301 677 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 77 306 674 [⟨2105747828⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) :=
        by
    rw [push4_xstep (s := (irCursor I 76 301 677 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨301⟩) (argv := ⟨2105747828⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h77 : Xstep fork (D_J safeBytecode 0) (irCursor I 77 306 674 [⟨2105747828⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 78 307 671 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 77 306 674 [⟨2105747828⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨306⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h78 : Xstep fork (D_J safeBytecode 0) (irCursor I 78 307 671 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 79 310 668 [⟨4287⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 78 307 671 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨307⟩) (argv := ⟨4287⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h79 : Xstep fork (D_J safeBytecode 0) (irCursor I 79 310 668 [⟨4287⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 80 311 658 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 79 310 668 [⟨4287⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨310⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h80 : Xstep fork (D_J safeBytecode 0) (irCursor I 80 311 658 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 81 312 655 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 80 311 658 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨311⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h81 : Xstep fork (D_J safeBytecode 0) (irCursor I 81 312 655 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 82 317 652 [⟨2471442961⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) :=
        by
    rw [push4_xstep (s := (irCursor I 81 312 655 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨312⟩) (argv := ⟨2471442961⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h82 : Xstep fork (D_J safeBytecode 0) (irCursor I 82 317 652 [⟨2471442961⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 83 318 649 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 82 317 652 [⟨2471442961⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨317⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h83 : Xstep fork (D_J safeBytecode 0) (irCursor I 83 318 649 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 84 321 646 [⟨4193⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 83 318 649 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨318⟩) (argv := ⟨4193⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h84 : Xstep fork (D_J safeBytecode 0) (irCursor I 84 321 646 [⟨4193⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 85 322 636 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 84 321 646 [⟨4193⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨321⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h85 : Xstep fork (D_J safeBytecode 0) (irCursor I 85 322 636 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 86 323 633 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 85 322 636 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨322⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h86 : Xstep fork (D_J safeBytecode 0) (irCursor I 86 323 633 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 87 328 630 [⟨2699460139⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) :=
        by
    rw [push4_xstep (s := (irCursor I 86 323 633 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨323⟩) (argv := ⟨2699460139⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h87 : Xstep fork (D_J safeBytecode 0) (irCursor I 87 328 630 [⟨2699460139⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 88 329 627 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 87 328 630 [⟨2699460139⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨328⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h88 : Xstep fork (D_J safeBytecode 0) (irCursor I 88 329 627 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 89 332 624 [⟨4048⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 88 329 627 [⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨329⟩) (argv := ⟨4048⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h89 : Xstep fork (D_J safeBytecode 0) (irCursor I 89 332 624 [⟨4048⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 90 333 614 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 89 332 624 [⟨4048⟩, ⟨0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨332⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h90 : Xstep fork (D_J safeBytecode 0) (irCursor I 90 333 614 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 91 334 611 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 90 333 614 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨333⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h91 : Xstep fork (D_J safeBytecode 0) (irCursor I 91 334 611 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 92 339 608 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) :=
        by
    rw [push4_xstep (s := (irCursor I 91 334 611 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨334⟩) (argv := ⟨0xaffed0e0⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h92 : Xstep fork (D_J safeBytecode 0) (irCursor I 92 339 608 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩,
    ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 93 340 605 [⟨1⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [eq_xstep (s := (irCursor I 92 339 608 [⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true))
      (code := safeBytecode) (pcv := ⟨339⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h93 : Xstep fork (D_J safeBytecode 0) (irCursor I 93 340 605 [⟨1⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 94 343 602 [⟨4018⟩, ⟨1⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 93 340 605 [⟨1⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨340⟩) (argv := ⟨4018⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h94 : Xstep fork (D_J safeBytecode 0) (irCursor I 94 343 602 [⟨4018⟩, ⟨1⟩, ⟨0xaffed0e0⟩, ⟨0⟩]
    true) =
      .ok ((irCursor I 95 4018 592 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpi_t_xstep (s := (irCursor I 94 343 602 [⟨4018⟩, ⟨1⟩, ⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨343⟩)
      hcode rfl (by native_decide) rfl (by decide +kernel) (by jump_dest)
        (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h95 : Xstep fork (D_J safeBytecode 0) (irCursor I 95 4018 592 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 96 4019 591 [⟨0xaffed0e0⟩, ⟨0⟩] true), .none) := by
    rw [jumpdest_xstep (s := (irCursor I 95 4018 592 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code :=
      safeBytecode) (pcv := ⟨4018⟩)
      hcode rfl (by native_decide) (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h96 : Xstep fork (D_J safeBytecode 0) (irCursor I 96 4019 591 [⟨0xaffed0e0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 97 4020 589 [⟨0⟩] true), .none) := by
    rw [pop_xstep (s := (irCursor I 96 4019 591 [⟨0xaffed0e0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨4019⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h97 : Xstep fork (D_J safeBytecode 0) (irCursor I 97 4020 589 [⟨0⟩] true) =
      .ok ((irCursor I 98 4021 587 [⟨0⟩, ⟨0⟩] true), .none) := by
    rw [callvalue_xstep (s := (irCursor I 97 4020 589 [⟨0⟩] true)) (code := safeBytecode) (pcv :=
      ⟨4020⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    simp only [stCallvalue, irCursor, hvalue]
    rfl
  have h98 : Xstep fork (D_J safeBytecode 0) (irCursor I 98 4021 587 [⟨0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 99 4024 584 [⟨589⟩, ⟨0⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 98 4021 587 [⟨0⟩, ⟨0⟩] true)) (code := safeBytecode) (pcv :=
      ⟨4021⟩) (argv := ⟨589⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h99 : Xstep fork (D_J safeBytecode 0) (irCursor I 99 4024 584 [⟨589⟩, ⟨0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 100 4025 574 [⟨0⟩] true), .none) := by
    rw [jumpi_nt_xstep (s := (irCursor I 99 4024 584 [⟨589⟩, ⟨0⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨4024⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h100 : Xstep fork (D_J safeBytecode 0) (irCursor I 100 4025 574 [⟨0⟩] true) =
      .ok ((irCursor I 101 4026 571 [⟨0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 100 4025 574 [⟨0⟩] true)) (code := safeBytecode) (pcv :=
      ⟨4025⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h101 : Xstep fork (D_J safeBytecode 0) (irCursor I 101 4026 571 [⟨0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 102 4028 568 [⟨3⟩, ⟨0⟩, ⟨0⟩] true), .none) := by
    rw [push1_xstep (s := (irCursor I 101 4026 571 [⟨0⟩, ⟨0⟩] true)) (code := safeBytecode) (pcv :=
      ⟨4026⟩) (argv := ⟨3⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h102 : Xstep fork (D_J safeBytecode 0) (irCursor I 102 4028 568 [⟨3⟩, ⟨0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 103 4029 565 [(UInt256.ofNat (2 ^ 256 - 4)), ⟨0⟩, ⟨0⟩] true), .none) := by
    rw [not_xstep (s := (irCursor I 102 4028 568 [⟨3⟩, ⟨0⟩, ⟨0⟩] true)) (code := safeBytecode) (pcv
      := ⟨4028⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h103 : Xstep fork (D_J safeBytecode 0) (irCursor I 103 4029 565 [(UInt256.ofNat (2 ^ 256 - 4)),
    ⟨0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 104 4030 563 [(UInt256.ofNat (2 ^ 255 + 4)), (UInt256.ofNat (2 ^ 256 - 4)),
        ⟨0⟩, ⟨0⟩] true), .none) := by
    rw [calldatasize_xstep (s := (irCursor I 103 4029 565 [(UInt256.ofNat (2 ^ 256 - 4)), ⟨0⟩, ⟨0⟩]
      true)) (code := safeBytecode) (pcv := ⟨4029⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    simp only [stCalldatasize, irCursor, hsize]
    rfl
  have h104 : Xstep fork (D_J safeBytecode 0) (irCursor I 104 4030 563 [(UInt256.ofNat (2 ^ 255 + 4)),
    (UInt256.ofNat (2 ^ 256 - 4)), ⟨0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 105 4031 560 [(UInt256.ofNat (2 ^ 255)), ⟨0⟩, ⟨0⟩] true), .none) := by
    rw [add_xstep (s := (irCursor I 104 4030 563 [(UInt256.ofNat (2 ^ 255 + 4)), (UInt256.ofNat (2 ^
      256 - 4)), ⟨0⟩, ⟨0⟩] true)) (code := safeBytecode) (pcv := ⟨4030⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h105 : Xstep fork (D_J safeBytecode 0) (irCursor I 105 4031 560 [(UInt256.ofNat (2 ^ 255)), ⟨0⟩,
    ⟨0⟩] true) =
      .ok ((irCursor I 106 4032 557 [⟨1⟩, ⟨0⟩] true), .none) := by
    rw [slt_xstep (s := (irCursor I 105 4031 560 [(UInt256.ofNat (2 ^ 255)), ⟨0⟩, ⟨0⟩] true)) (code
      := safeBytecode) (pcv := ⟨4031⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h106 : Xstep fork (D_J safeBytecode 0) (irCursor I 106 4032 557 [⟨1⟩, ⟨0⟩] true) =
      .ok ((irCursor I 107 4035 554 [⟨589⟩, ⟨1⟩, ⟨0⟩] true), .none) := by
    rw [push2_xstep (s := (irCursor I 106 4032 557 [⟨1⟩, ⟨0⟩] true)) (code := safeBytecode) (pcv :=
      ⟨4032⟩) (argv := ⟨589⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h107 : Xstep fork (D_J safeBytecode 0) (irCursor I 107 4035 554 [⟨589⟩, ⟨1⟩, ⟨0⟩] true) =
      .ok ((irCursor I 108 589 544 [⟨0⟩] true), .none) := by
    rw [jumpi_t_xstep (s := (irCursor I 107 4035 554 [⟨589⟩, ⟨1⟩, ⟨0⟩] true)) (code := safeBytecode)
      (pcv := ⟨4035⟩)
      hcode rfl (by native_decide) rfl (by decide +kernel) (by jump_dest)
        (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h108 : Xstep fork (D_J safeBytecode 0) (irCursor I 108 589 544 [⟨0⟩] true) =
      .ok ((irCursor I 109 590 543 [⟨0⟩] true), .none) := by
    rw [jumpdest_xstep (s := (irCursor I 108 589 544 [⟨0⟩] true)) (code := safeBytecode) (pcv :=
      ⟨589⟩)
      hcode rfl (by native_decide) (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h109 : Xstep fork (D_J safeBytecode 0) (irCursor I 109 590 543 [⟨0⟩] true) =
      .ok ((irCursor I 110 591 540 [⟨0⟩, ⟨0⟩] true), .none) := by
    rw [dup1_xstep (s := (irCursor I 109 590 543 [⟨0⟩] true)) (code := safeBytecode) (pcv := ⟨590⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    rfl
  have h110 : Xstep fork (D_J safeBytecode 0) (irCursor I 110 591 540 [⟨0⟩, ⟨0⟩] true) =
      .ok ((irCursor I 111 592 540 [] true), .some (.revert, ByteArray.empty)) := by
    rw [revert_xstep (s := (irCursor I 110 591 540 [⟨0⟩, ⟨0⟩] true)) (code := safeBytecode) (pcv :=
      ⟨591⟩)
      hcode rfl (by native_decide) rfl (by dsimp [irCursor]; decide +kernel)]
    rw [if_neg (by
      dsimp [irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
      decide +kernel)]
    simp only [stRevert, irCursor, memoryExpansionCost, memoryExpansionCost.μᵢ']
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, byteArray_readWithPadding_zero]
    rfl
  apply Xstep_X_X_continue _ _ _ _ _ h0
  apply Xstep_X_X_continue _ _ _ _ _ h1
  apply Xstep_X_X_continue _ _ _ _ _ h2
  apply Xstep_X_X_continue _ _ _ _ _ h3
  apply Xstep_X_X_continue _ _ _ _ _ h4
  apply Xstep_X_X_continue _ _ _ _ _ h5
  apply Xstep_X_X_continue _ _ _ _ _ h6
  apply Xstep_X_X_continue _ _ _ _ _ h7
  apply Xstep_X_X_continue _ _ _ _ _ h8
  apply Xstep_X_X_continue _ _ _ _ _ h9
  apply Xstep_X_X_continue _ _ _ _ _ h10
  apply Xstep_X_X_continue _ _ _ _ _ h11
  apply Xstep_X_X_continue _ _ _ _ _ h12
  apply Xstep_X_X_continue _ _ _ _ _ h13
  apply Xstep_X_X_continue _ _ _ _ _ h14
  apply Xstep_X_X_continue _ _ _ _ _ h15
  apply Xstep_X_X_continue _ _ _ _ _ h16
  apply Xstep_X_X_continue _ _ _ _ _ h17
  apply Xstep_X_X_continue _ _ _ _ _ h18
  apply Xstep_X_X_continue _ _ _ _ _ h19
  apply Xstep_X_X_continue _ _ _ _ _ h20
  apply Xstep_X_X_continue _ _ _ _ _ h21
  apply Xstep_X_X_continue _ _ _ _ _ h22
  apply Xstep_X_X_continue _ _ _ _ _ h23
  apply Xstep_X_X_continue _ _ _ _ _ h24
  apply Xstep_X_X_continue _ _ _ _ _ h25
  apply Xstep_X_X_continue _ _ _ _ _ h26
  apply Xstep_X_X_continue _ _ _ _ _ h27
  apply Xstep_X_X_continue _ _ _ _ _ h28
  apply Xstep_X_X_continue _ _ _ _ _ h29
  apply Xstep_X_X_continue _ _ _ _ _ h30
  apply Xstep_X_X_continue _ _ _ _ _ h31
  apply Xstep_X_X_continue _ _ _ _ _ h32
  apply Xstep_X_X_continue _ _ _ _ _ h33
  apply Xstep_X_X_continue _ _ _ _ _ h34
  apply Xstep_X_X_continue _ _ _ _ _ h35
  apply Xstep_X_X_continue _ _ _ _ _ h36
  apply Xstep_X_X_continue _ _ _ _ _ h37
  apply Xstep_X_X_continue _ _ _ _ _ h38
  apply Xstep_X_X_continue _ _ _ _ _ h39
  apply Xstep_X_X_continue _ _ _ _ _ h40
  apply Xstep_X_X_continue _ _ _ _ _ h41
  apply Xstep_X_X_continue _ _ _ _ _ h42
  apply Xstep_X_X_continue _ _ _ _ _ h43
  apply Xstep_X_X_continue _ _ _ _ _ h44
  apply Xstep_X_X_continue _ _ _ _ _ h45
  apply Xstep_X_X_continue _ _ _ _ _ h46
  apply Xstep_X_X_continue _ _ _ _ _ h47
  apply Xstep_X_X_continue _ _ _ _ _ h48
  apply Xstep_X_X_continue _ _ _ _ _ h49
  apply Xstep_X_X_continue _ _ _ _ _ h50
  apply Xstep_X_X_continue _ _ _ _ _ h51
  apply Xstep_X_X_continue _ _ _ _ _ h52
  apply Xstep_X_X_continue _ _ _ _ _ h53
  apply Xstep_X_X_continue _ _ _ _ _ h54
  apply Xstep_X_X_continue _ _ _ _ _ h55
  apply Xstep_X_X_continue _ _ _ _ _ h56
  apply Xstep_X_X_continue _ _ _ _ _ h57
  apply Xstep_X_X_continue _ _ _ _ _ h58
  apply Xstep_X_X_continue _ _ _ _ _ h59
  apply Xstep_X_X_continue _ _ _ _ _ h60
  apply Xstep_X_X_continue _ _ _ _ _ h61
  apply Xstep_X_X_continue _ _ _ _ _ h62
  apply Xstep_X_X_continue _ _ _ _ _ h63
  apply Xstep_X_X_continue _ _ _ _ _ h64
  apply Xstep_X_X_continue _ _ _ _ _ h65
  apply Xstep_X_X_continue _ _ _ _ _ h66
  apply Xstep_X_X_continue _ _ _ _ _ h67
  apply Xstep_X_X_continue _ _ _ _ _ h68
  apply Xstep_X_X_continue _ _ _ _ _ h69
  apply Xstep_X_X_continue _ _ _ _ _ h70
  apply Xstep_X_X_continue _ _ _ _ _ h71
  apply Xstep_X_X_continue _ _ _ _ _ h72
  apply Xstep_X_X_continue _ _ _ _ _ h73
  apply Xstep_X_X_continue _ _ _ _ _ h74
  apply Xstep_X_X_continue _ _ _ _ _ h75
  apply Xstep_X_X_continue _ _ _ _ _ h76
  apply Xstep_X_X_continue _ _ _ _ _ h77
  apply Xstep_X_X_continue _ _ _ _ _ h78
  apply Xstep_X_X_continue _ _ _ _ _ h79
  apply Xstep_X_X_continue _ _ _ _ _ h80
  apply Xstep_X_X_continue _ _ _ _ _ h81
  apply Xstep_X_X_continue _ _ _ _ _ h82
  apply Xstep_X_X_continue _ _ _ _ _ h83
  apply Xstep_X_X_continue _ _ _ _ _ h84
  apply Xstep_X_X_continue _ _ _ _ _ h85
  apply Xstep_X_X_continue _ _ _ _ _ h86
  apply Xstep_X_X_continue _ _ _ _ _ h87
  apply Xstep_X_X_continue _ _ _ _ _ h88
  apply Xstep_X_X_continue _ _ _ _ _ h89
  apply Xstep_X_X_continue _ _ _ _ _ h90
  apply Xstep_X_X_continue _ _ _ _ _ h91
  apply Xstep_X_X_continue _ _ _ _ _ h92
  apply Xstep_X_X_continue _ _ _ _ _ h93
  apply Xstep_X_X_continue _ _ _ _ _ h94
  apply Xstep_X_X_continue _ _ _ _ _ h95
  apply Xstep_X_X_continue _ _ _ _ _ h96
  apply Xstep_X_X_continue _ _ _ _ _ h97
  apply Xstep_X_X_continue _ _ _ _ _ h98
  apply Xstep_X_X_continue _ _ _ _ _ h99
  apply Xstep_X_X_continue _ _ _ _ _ h100
  apply Xstep_X_X_continue _ _ _ _ _ h101
  apply Xstep_X_X_continue _ _ _ _ _ h102
  apply Xstep_X_X_continue _ _ _ _ _ h103
  apply Xstep_X_X_continue _ _ _ _ _ h104
  apply Xstep_X_X_continue _ _ _ _ _ h105
  apply Xstep_X_X_continue _ _ _ _ _ h106
  apply Xstep_X_X_continue _ _ _ _ _ h107
  apply Xstep_X_X_continue _ _ _ _ _ h108
  apply Xstep_X_X_continue _ _ _ _ _ h109
  exact Xstep_X_X_halt_revert 890 _ _ _ _ h110

def safeIRHugeNonceEnv : ExecutionEnv :=
  { (default : ExecutionEnv) with
    code := safeBytecode
    calldata := safeIRHugeNonceCalldata
    weiValue := ⟨0⟩ }

/-- The huge, well-dispatched input reverts with 540 of its initial 1,000 gas left. -/
theorem safeIRHugeNonceExecution :
    Ξ fork default default ⟨1000⟩ default safeIRHugeNonceEnv =
      .ok (.revert ⟨540⟩ ByteArray.empty) := by
  apply Xi_revert_of_X
  change X fork 1001 (D_J safeBytecode 0) (irCursor safeIRHugeNonceEnv 0 0 1000 [] false) = _
  apply exactNonceHuge rfl safeIRHugeNonceCalldata_size rfl
  exact (selectorDispatchFacts (I := safeIRHugeNonceEnv) 0xaf 0xfe 0xd0 0xe0 ⟨0xaffed0e0⟩
    safeIRHugeNonceCalldata_dispatch nonceSelectorBytes (by decide)).2

/-- The former counterexample now refines the spec through its ABI decoding-failure case. -/
theorem safeIRHugeNonceRefines :
    runtimeRefinementFor fork config contract default default ⟨1000⟩ default safeIRHugeNonceEnv := by
  exact .execution safeIRHugeNonceExecution
    (.decodingFailed safeIRHugeNonceCalldata_dispatch safeIRHugeNonceCalldata_decodingFailed)
    (.decodingFailed rfl rfl)

end Benchmarks.Safe.ViaIR
