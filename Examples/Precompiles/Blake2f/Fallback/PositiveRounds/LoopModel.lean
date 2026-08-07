import Examples.Precompiles.Blake2f.Model

/-!
# BLAKE2F positive-round pure loop model

This file does not replace the trusted model in `Examples.Precompiles.Blake2f.Model`.  It factors
the copied `Model.compress` body into named pieces that are easier to use as bytecode loop
invariants:

* `initialV` is the working-vector state before the compression-round loop;
* `roundStep` is one full BLAKE2F round, i.e. the eight `mixG` calls for `SIGMA[r % 10]`;
* `roundsState` is the state after `n` rounds, exposed recursively in the direction needed by
  `RDx.whileLoopCarryGas`;
* `finalize` computes the eight returned words from the final working vector.

The bridge theorems at the bottom connect these factored definitions back to the copied
`Model.compress`, `Model.compressBytes`, and `Model.output` definitions.
-/

open Ethereum Ethereum.EVM

namespace Blake2f.Model

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Parsed chaining-value words `h[0..7]` from a 213-byte BLAKE2F input. -/
def parsedH (input : ByteArray) : Array UInt64 := Id.run do
  let mut h : Array UInt64 := Array.mkEmpty 8
  for i in [0:8] do
    h := h.push (readLE64 input (4 + i * 8))
  return h

@[simp] theorem parsedH_size (input : ByteArray) :
    (parsedH input).size = 8 := by
  simp [parsedH, List.range']

theorem parsedH_getElem! (input : ByteArray) {i : Nat} (hi : i < 8) :
    (parsedH input)[i]! = readLE64 input (4 + i * 8) := by
  have hcases :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [parsedH, List.range']

/-- Parsed message words `m[0..15]` from a 213-byte BLAKE2F input. -/
def parsedM (input : ByteArray) : Array UInt64 := Id.run do
  let mut m : Array UInt64 := Array.mkEmpty 16
  for i in [0:16] do
    m := m.push (readLE64 input (68 + i * 8))
  return m

@[simp] theorem parsedM_size (input : ByteArray) :
    (parsedM input).size = 16 := by
  simp [parsedM, List.range']

theorem parsedM_getElem! (input : ByteArray) {i : Nat} (hi : i < 16) :
    (parsedM input)[i]! = readLE64 input (68 + i * 8) := by
  have hcases :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by
    omega
  rcases hcases with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [parsedM, List.range']

/-- Parsed offset counter word `t[0]`. -/
def parsedT0 (input : ByteArray) : UInt64 :=
  readLE64 input 196

/-- Parsed offset counter word `t[1]`. -/
def parsedT1 (input : ByteArray) : UInt64 :=
  readLE64 input 204

/-- Parsed final-block flag as used by the trusted model. -/
def parsedFinalFlag (input : ByteArray) : Bool :=
  input[212]! == 1

/-- Working vector immediately before the compression-round loop. -/
def initialV (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) : Array UInt64 := Id.run do
  let mut v : Array UInt64 := Array.mkEmpty 16
  for i in [0:8] do
    v := v.push h[i]!
  for i in [0:8] do
    v := v.push IV[i]!
  v := v.set! 12 (v[12]! ^^^ t0)
  v := v.set! 13 (v[13]! ^^^ t1)
  if f then
    v := v.set! 14 (v[14]! ^^^ 0xffffffffffffffff)
  return v

@[simp] theorem initialV_size (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f).size = 16 := by
  cases f <;> simp [initialV, List.range']

@[simp] theorem initialV_getElem!_0 (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f)[0]! = h[0]! := by
  cases f <;> simp [initialV, List.range']

@[simp] theorem initialV_getElem!_1 (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f)[1]! = h[1]! := by
  cases f <;> simp [initialV, List.range']

@[simp] theorem initialV_getElem!_2 (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f)[2]! = h[2]! := by
  cases f <;> simp [initialV, List.range']

@[simp] theorem initialV_getElem!_3 (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f)[3]! = h[3]! := by
  cases f <;> simp [initialV, List.range']

@[simp] theorem initialV_getElem!_4 (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f)[4]! = h[4]! := by
  cases f <;> simp [initialV, List.range']

@[simp] theorem initialV_getElem!_5 (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f)[5]! = h[5]! := by
  cases f <;> simp [initialV, List.range']

@[simp] theorem initialV_getElem!_6 (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f)[6]! = h[6]! := by
  cases f <;> simp [initialV, List.range']

@[simp] theorem initialV_getElem!_7 (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f)[7]! = h[7]! := by
  cases f <;> simp [initialV, List.range']

@[simp] theorem initialV_getElem!_8 (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f)[8]! = IV[0]! := by
  cases f <;> simp [initialV, List.range']

@[simp] theorem initialV_getElem!_9 (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f)[9]! = IV[1]! := by
  cases f <;> simp [initialV, List.range']

@[simp] theorem initialV_getElem!_10 (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f)[10]! = IV[2]! := by
  cases f <;> simp [initialV, List.range']

@[simp] theorem initialV_getElem!_11 (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f)[11]! = IV[3]! := by
  cases f <;> simp [initialV, List.range']

@[simp] theorem initialV_getElem!_12 (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f)[12]! = IV[4]! ^^^ t0 := by
  cases f <;> simp [initialV, List.range']

@[simp] theorem initialV_getElem!_13 (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f)[13]! = IV[5]! ^^^ t1 := by
  cases f <;> simp [initialV, List.range']

@[simp] theorem initialV_getElem!_14_false (h : Array UInt64) (t0 t1 : UInt64) :
    (initialV h t0 t1 false)[14]! = IV[6]! := by
  simp [initialV, List.range']

@[simp] theorem initialV_getElem!_14_true (h : Array UInt64) (t0 t1 : UInt64) :
    (initialV h t0 t1 true)[14]! = IV[6]! ^^^ 0xffffffffffffffff := by
  simp [initialV, List.range']

@[simp] theorem initialV_getElem!_15 (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    (initialV h t0 t1 f)[15]! = IV[7]! := by
  cases f <;> simp [initialV, List.range']

/-- One complete BLAKE2F compression round. -/
def roundStep (m : Array UInt64) (r : Nat) (v : Array UInt64) : Array UInt64 := Id.run do
  let s := SIGMA[r % 10]!
  let mut v := v
  v := mixG v 0 4  8 12 m[s[0]!]!  m[s[1]!]!
  v := mixG v 1 5  9 13 m[s[2]!]!  m[s[3]!]!
  v := mixG v 2 6 10 14 m[s[4]!]!  m[s[5]!]!
  v := mixG v 3 7 11 15 m[s[6]!]!  m[s[7]!]!
  v := mixG v 0 5 10 15 m[s[8]!]!  m[s[9]!]!
  v := mixG v 1 6 11 12 m[s[10]!]! m[s[11]!]!
  v := mixG v 2 7  8 13 m[s[12]!]! m[s[13]!]!
  v := mixG v 3 4  9 14 m[s[14]!]! m[s[15]!]!
  return v

/-- State after executing `n` compression rounds from working vector `v`.

The recursive shape is chosen to match the induction needed for the bytecode loop:
the `(n + 1)` state is obtained by applying round index `n` to the `n`-round state. -/
def roundsState (m : Array UInt64) : Nat → Array UInt64 → Array UInt64
  | 0, v => v
  | n + 1, v => roundStep m n (roundsState m n v)

/-- The final eight BLAKE2F output words from the chaining value and working vector. -/
def finalize (h v : Array UInt64) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := Array.mkEmpty 8
  for i in [0:8] do
    out := out.push (h[i]! ^^^ v[i]! ^^^ v[i + 8]!)
  return out

/-- Factored form of `compress`. -/
def compressLoop (rounds : Nat) (h m : Array UInt64) (t0 t1 : UInt64)
    (f : Bool) : Array UInt64 :=
  finalize h (roundsState m rounds (initialV h t0 t1 f))

@[simp] theorem roundsState_zero (m : Array UInt64) (v : Array UInt64) :
    roundsState m 0 v = v := by
  simp [roundsState]

theorem roundsState_succ (m : Array UInt64) (n : Nat) (v : Array UInt64) :
    roundsState m (n + 1) v = roundStep m n (roundsState m n v) := by
  rfl

theorem range'_zero_succ_eq_append (n : Nat) :
    List.range' 0 (n + 1) = List.range' 0 n ++ [n] := by
  simpa using (List.range'_concat (s := 0) (n := n) (step := 1))

/-- Recursive `roundsState` agrees with the fold generated by Lean's `[0:rounds]` loop. -/
theorem roundsState_eq_foldl_range'
    (m : Array UInt64) (n : Nat) (v : Array UInt64) :
    roundsState m n v =
      (List.range' 0 n).foldl (fun v r => roundStep m r v) v := by
  induction n with
  | zero =>
      simp [roundsState]
  | succ n ih =>
      rw [roundsState_succ, ih, range'_zero_succ_eq_append, List.foldl_append]
      simp

/-- The factored loop model agrees with the trusted copied `Model.compress`. -/
theorem compress_eq_compressLoop
    (rounds : Nat) (h m : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    compress rounds h m t0 t1 f = compressLoop rounds h m t0 t1 f := by
  unfold compress compressLoop finalize initialV
  cases f <;>
    simp [roundsState_eq_foldl_range', roundStep]

/-- Factored form of `compressBytes`, exposing parser and loop state names. -/
def compressBytesLoop (input : ByteArray) (rounds : Nat) : ByteArray := Id.run do
  let h := parsedH input
  let m := parsedM input
  let t0 := parsedT0 input
  let t1 := parsedT1 input
  let f := parsedFinalFlag input
  let out := compressLoop rounds h m t0 t1 f
  let mut res : ByteArray := ByteArray.empty
  for i in [0:8] do
    res := writeLE64 res out[i]!
  return res

/-- Byte-level trusted model bridge for the factored loop model. -/
theorem compressBytes_eq_compressBytesLoop (input : ByteArray) (rounds : Nat) :
    compressBytes input rounds = compressBytesLoop input rounds := by
  unfold compressBytes compressBytesLoop parsedH parsedM parsedT0 parsedT1 parsedFinalFlag
  simp [compress_eq_compressLoop]

theorem output_eq_compressBytesLoop (input : ByteArray) :
    output input = compressBytesLoop input (rounds input) := by
  unfold output
  exact compressBytes_eq_compressBytesLoop input (rounds input)

end Blake2f.Model
