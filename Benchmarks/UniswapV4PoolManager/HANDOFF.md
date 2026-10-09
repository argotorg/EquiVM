# PoolManager scaffold hand-off

The scaffold is ready for the proving session. All 33 selector arms and the
constructor have been checked against the pinned bytecode. Function refinements
remain generated proof obligations; a successful build does not discharge them.

## Compiler settings and provenance

- Upstream: `Uniswap/v4-core`, commit `46c6834698c48bc4a463a86d8420f4eb1d7f3b75`.
- Main contract: `src/PoolManager.sol:PoolManager`; 45 source units in `contracts/`.
- Solmate: `4b47a19038b798b4a33d9749d25e570443520647`.
- Compiler: `0.8.26+commit.8a97fa7a.Linux.g++`; binary SHA-256
  `d5f23436f443edb85d8e76906d12f0a86ce0490e7663a9e608efeb7a93f149ef`.
- Settings from the pinned `foundry.toml`: optimizer enabled, 44,444,444 runs,
  via IR, Cancun, metadata bytecode hash `none`. The build manifest records the
  six upstream remappings. The exact 0.8.26 pragma and upstream settings take
  precedence over the scaffold prompt's general compiler advice.
- Runtime: 24,009 bytes, including 12 metadata bytes. Creation: 24,194 bytes;
  its executable prefix is 185 bytes.
- Repository generator baseline: `57ab07976ac45cf5aa4c26fb1d3063dd998a5739`.
  Source changes are confined to this directory. Generation used `--no-register`.

The initial command, run at the repository root with the import closure already
in `contracts/`, was:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/scaffold.py all \
  --dir Benchmarks/UniswapV4PoolManager \
  --solc /tmp/equivm-solc-0.8.26 --main src/PoolManager.sol --contract PoolManager \
  --runs 44444444 --via-ir --evm-version cancun \
  --module Benchmarks.UniswapV4PoolManager --metadata-hash none \
  --remapping @ensdomains/=node_modules/@ensdomains/ \
  --remapping @openzeppelin/=lib/openzeppelin-contracts/ \
  --remapping ds-test/=lib/forge-std/lib/ds-test/src/ \
  --remapping forge-std/=lib/forge-std/src/ \
  --remapping hardhat/=node_modules/hardhat/ \
  --remapping solmate/=lib/solmate/ --no-register
```

Final checks:

```text
python3 scripts/scaffold.py check --dir Benchmarks/UniswapV4PoolManager
ok   poolManagerBytecode matches the hex artifact
ok   validJumps: matches the JUMPDEST scan
ok   poolManagerCreationBytecode matches the hex artifact
ok   creationValidJumps: matches the JUMPDEST scan
ok   Selectors.lean: 33 entries match the ABI in SpecSyntax order
ok   Immutables.lean offsets match immutableReferences
ok   sources.sha256 verified

lake build Benchmarks.UniswapV4PoolManager.Correct
Build completed successfully (3585 jobs).
```

## Differential run

The full run used seed **2026**, count **50**, before the final bytecode walk and
again after adding the refinement hypotheses. Its command and results are:

```sh
# In the isolated package described below:
lake --log-level=error exe solm-difftest --only PoolManager --count 50 --seed 2026
```

```text
PoolManager: 1875 cases: 1856 agree (634 successful), 0 disagree, 0 stuck, 15 EVM out of gas, 0 spec out of fuel, 4 unsupported (allocation cap)
```

The coverage line, wrapped at transition boundaries, reports `successful/cases`:

```text
constructor 17/25; balanceOf(address,uint256) 44/56;
supportsInterface(bytes4) 33/52; transfer(address,uint256,uint256) 8/53;
settle() 0/51; initialize((address,address,uint24,int24,address),uint160) 1/52;
mint(address,uint256,uint256) 0/54; extsload(bytes32) 46/53;
extsload(bytes32,uint256) 25/54; extsload(bytes32[]) 41/53;
take(address,address,uint256) 0/56; setProtocolFeeController(address) 10/50;
collectProtocolFees(address,address,uint256) 3/53; settleFor(address) 0/57;
approve(address,uint256,uint256) 36/52; unlock(bytes) 0/53;
donate((address,address,uint24,int24,address),uint256,uint256,bytes) 0/53;
setOperator(address,bool) 35/51; allowance(address,address,uint256) 41/51;
modifyLiquidity((address,address,uint24,int24,address),(int24,int24,int256,bytes32),bytes) 0/52;
sync(address) 11/53; owner() 48/53;
updateDynamicLPFee((address,address,uint24,int24,address),uint24) 0/55;
exttload(bytes32[]) 43/52; exttload(bytes32) 45/55;
swap((address,address,uint24,int24,address),(bool,int256,uint160),bytes) 0/51;
isOperator(address,address) 46/57; clear(address,uint256) 0/53;
setProtocolFee((address,address,uint24,int24,address),uint24) 0/52;
protocolFeeController() 47/52; transferOwnership(address) 3/50;
burn(address,uint256,uint256) 0/53; protocolFeesAccrued(address) 45/54;
transferFrom(address,address,uint256,uint256) 6/54; stray 0/100.
```

The random generator does not seed the hashed transient lock word or an initialized
pool at the matching pool-key hash. Those guards explain the zero-success locked
operations, fee setter, and dynamic-fee update. Its standard callees do not return
ABI-encoded `bytes` for `unlockCallback`, explaining `unlock`. Unmatched selectors
always revert, so `stray` correctly has no success. The 19 inconclusive cases are
gas exhaustion or the interpreter's allocation cap, not specification failures.

Two focused sequences supplemented that coverage. A constructor plus 21 successful
runtime calls covered unlock, initialization, protocol fee setup, adding/removing
liquidity, both swap directions and amount signs, donation, fee collection,
mint/burn, take, native/ERC20 settlement, settleFor, clear, sync, and dynamic-fee
updates. A second constructor plus seven successful calls exercised all ten hook
callbacks, dirty selector padding, and nonzero hook deltas. Every comparison agreed
on success. These fixtures seed the lock to exercise valid mid-unlock entry states;
they do not simulate an entire reentrant unlock transaction.

Additional arithmetic diagnostics checked all 256 single-bit positions and adjacent
intervals for BitMath, selected TickMath boundaries and round trips, and 294 FullMath
boundary combinations. These supplement the bytecode review, not the proofs.

To reproduce the full run without changing the global target registry, run this
setup at the repository root, then run the command above in the printed directory.
It uses the repository CLI and harness with only this target registered. Running
`--only PoolManager` at the repository root alone does not register it.

```python
from pathlib import Path
import json

repo = Path.cwd().resolve()
test_dir = Path('/tmp/uniswap-v4-difftest')
test_dir.mkdir(exist_ok=True)
test_dir.joinpath('lakefile.toml').write_text(
    'name = "PoolManagerDiff"\nversion = "0.1.0"\n'
    '[[require]]\nname = "EquiVM"\npath = ' + json.dumps(str(repo)) + '\n'
    '[[lean_exe]]\nname = "solm-difftest"\nroot = "Main"\n')
test_dir.joinpath('lean-toolchain').write_text(repo.joinpath('lean-toolchain').read_text())
main = repo.joinpath('Tests/DiffTest/Main.lean').read_text()
main = main.replace('import Tests.DiffTest.Targets',
    'import Benchmarks.UniswapV4PoolManager.DiffTarget')
main = main.replace('open Solm.DiffTest Tests.DiffTest',
    'open Solm.DiffTest\n\ndef allTargets : List Target :=\n'
    '  [Benchmarks.UniswapV4PoolManager.diffTarget]')
test_dir.joinpath('Main.lean').write_text(main)
manifest = json.loads(repo.joinpath('lake-manifest.json').read_text())
manifest['name'] = 'PoolManagerDiff'
manifest['packagesDir'] = str(repo / '.lake/packages')
manifest['packages'].append(dict(type='path', name='EquiVM', dir=str(repo),
    manifestFile='lake-manifest.json', configFile='lakefile.toml', inherited=False))
test_dir.joinpath('lake-manifest.json').write_text(json.dumps(manifest))
# The evmlean FFI build expects its test corpus relative to the working directory.
corpus = test_dir / 'EthereumTests'
if not corpus.exists():
    corpus.symlink_to(repo / '.lake/packages/evmlean/EthereumTests', target_is_directory=True)
print(test_dir)
```

<details>
<summary>Focused successful-path fixture</summary>

Save as `/tmp/uniswap-v4-focused.lean` and run
`lake env lean --run /tmp/uniswap-v4-focused.lean` at the repository root after
`lake build Benchmarks.UniswapV4PoolManager.DiffTarget`.

```lean
import Benchmarks.UniswapV4PoolManager.DiffTarget
open Solm Solm.DiffTest Solm.Interp ABI Ethereum Ethereum.EVM
open Benchmarks.UniswapV4PoolManager

def addressValue (n : Nat) : Value := .address (EVM.address n)
def intValue (n : Int) : Value := .int n
def zeroSalt : Value := .fixedBytes ⟨31, by decide⟩ (List.replicate 32 0)
def poolKeyValue (fee := 3000) (hooks := 0) : Value :=
  .tuple [addressValue 0, addressValue 0x5000, intValue fee, intValue 60, addressValue hooks]
def liqParams (n : Int) : Value := .tuple [intValue (-120), intValue 120, intValue n, zeroSalt]
def swapParams (direction : Bool) (n : Int) (limit : Nat) : Value :=
  .tuple [.bool direction, intValue n, intValue limit]

def setTransient (t : Target) (σ : AccountMap) (slot value : Nat) : AccountMap :=
  let evm := initialState σ σ (.ofNat t.gas) default (t.env t.runtime t.selfAddress 0 .empty true)
  match t.config.transientBackend.write
    { base := "rawTransient", steps := [.aindex (.int slot)] }
    (.elem (.int (.uint ⟨256, by decide⟩))) (.int value) evm with
  | .ok e => e.accountMap
  | _ => σ

def invoke (t : Target) (σ : AccountMap) (name : String) (args : List Value)
    (caller := 0x2000) (value := 0) : IO AccountMap := do
  let some tr := t.contract.transitions.find? (·.name == name) | throw (IO.userError s!"no transition {name}")
  let some cd := encodeCallWithSelector? ((Ethereum.KEC (String.toByteArray (transitionSigStr tr))).extract 0 4) (tr.params.map Param.ty) args
    | throw (IO.userError s!"encoding {name}")
  let c : Case := {
    label := name
    σ := transferValue σ (EVM.address caller) t.selfAddress value
    I := t.env t.runtime (EVM.address caller) value cd true
  }
  let result := runCase t c
  IO.println s!"{name}: {result.verdict.describe}"
  match result.verdict with
  | .agree "success" => return result.postState.getD σ
  | .agree why => throw (IO.userError s!"{name} unexpectedly {why}; calldata {hex cd}")
  | _ => throw (IO.userError s!"{name} failed; calldata {hex cd}")

def main : IO Unit := do
  let (target, _) := diffTarget.resolveRuntime (Rng.ofSeed 2026)
  let target := { target with callees := target.callees ++ [(EVM.address 0x6000, callee (wordBytes 32 ++ wordBytes 0))] }
  let (ctor, σ?) := runConstructor target poolManagerCreationBytecode [addressValue 0x2000] 0 (EVM.address 0x2000)
  IO.println s!"constructor: {ctor.describe}"
  let mut σ := σ?.getD target.world
  σ ← invoke target σ "unlock" [.bytes .empty] 0x6000
  σ ← invoke target σ "initialize" [poolKeyValue, intValue (2^96)]
  σ ← invoke target σ "setProtocolFeeController" [addressValue 0x2000]
  σ ← invoke target σ "setProtocolFee" [poolKeyValue, intValue 500]
  σ := setTransient target σ 0xc090fc4683624cfc3884e9d8de5eca132f2d0ec062aff75d43c0465d5ceeab23 1
  σ ← invoke target σ "modifyLiquidity" [poolKeyValue, liqParams 1000000, .bytes .empty]
  σ ← invoke target σ "swap" [poolKeyValue, swapParams true (-100) 4295128740, .bytes .empty]
  σ ← invoke target σ "swap" [poolKeyValue, swapParams false 50 1461446703485210103287273052203988822378723970341, .bytes .empty]
  σ ← invoke target σ "donate" [poolKeyValue, intValue 100, intValue 200, .bytes .empty]
  σ ← invoke target σ "modifyLiquidity" [poolKeyValue, liqParams 0, .bytes .empty]
  σ ← invoke target σ "mint" [addressValue 0x2000, intValue 0x5000, intValue 1]
  σ ← invoke target σ "burn" [addressValue 0x2000, intValue 0x5000, intValue 1]
  σ ← invoke target σ "take" [addressValue 0, addressValue 0x3000, intValue 1]
  σ ← invoke target σ "settle" [] 0x2000 1
  σ ← invoke target σ "settleFor" [addressValue 0x3000] 0x2000 1
  σ ← invoke target σ "clear" [addressValue 0, intValue 1] 0x3000
  σ ← invoke target σ "sync" [addressValue 0x5000]
  σ ← invoke target σ "settle" []
  σ ← invoke target σ "collectProtocolFees" [addressValue 0x3000, addressValue 0, intValue 0]
  σ ← invoke target σ "modifyLiquidity" [poolKeyValue, liqParams (-1000000), .bytes .empty]
  σ ← invoke target σ "initialize" [poolKeyValue 8388608 0x2000, intValue (2^96)]
  σ ← invoke target σ "updateDynamicLPFee" [poolKeyValue 8388608 0x2000, intValue 1000]
  IO.println s!"Focused successful-path sequence complete; accounts: {σ.size}"
```

</details>

<details>
<summary>Focused hook fixture</summary>

Save as `/tmp/uniswap-v4-hooks.lean` and run
`lake env lean --run /tmp/uniswap-v4-hooks.lean` at the repository root.

```lean
import Benchmarks.UniswapV4PoolManager.DiffTarget
open Solm Solm.DiffTest Solm.Interp ABI Ethereum Ethereum.EVM
open Benchmarks.UniswapV4PoolManager

def addressValue (n : Nat) : Value := .address (EVM.address n)
def intValue (n : Int) : Value := .int n
def zeroSalt : Value := .fixedBytes ⟨31, by decide⟩ (List.replicate 32 0)
def poolKeyValue (fee := 3000) (hooks := 0) : Value :=
  .tuple [addressValue 0, addressValue 0x5000, intValue fee, intValue 60, addressValue hooks]
def liqParams (n : Int) : Value := .tuple [intValue (-120), intValue 120, intValue n, zeroSalt]
def swapParams (direction : Bool) (n : Int) (limit : Nat) : Value :=
  .tuple [.bool direction, intValue n, intValue limit]

def setTransient (t : Target) (σ : AccountMap) (slot value : Nat) : AccountMap :=
  let evm := initialState σ σ (.ofNat t.gas) default (t.env t.runtime t.selfAddress 0 .empty true)
  match t.config.transientBackend.write
    { base := "rawTransient", steps := [.aindex (.int slot)] }
    (.elem (.int (.uint ⟨256, by decide⟩))) (.int value) evm with
  | .ok e => e.accountMap
  | _ => σ

def invoke (t : Target) (σ : AccountMap) (name : String) (args : List Value)
    (caller := 0x2000) (value := 0) : IO AccountMap := do
  let some tr := t.contract.transitions.find? (·.name == name) | throw (IO.userError s!"no transition {name}")
  let some cd := encodeCallWithSelector? ((Ethereum.KEC (String.toByteArray (transitionSigStr tr))).extract 0 4) (tr.params.map Param.ty) args
    | throw (IO.userError s!"encoding {name}")
  let c : Case := {
    label := name
    σ := transferValue σ (EVM.address caller) t.selfAddress value
    I := t.env t.runtime (EVM.address caller) value cd true
  }
  let result := runCase t c
  IO.println s!"{name}: {result.verdict.describe}"
  match result.verdict with
  | .agree "success" => return result.postState.getD σ
  | .agree why => throw (IO.userError s!"{name} unexpectedly {why}; calldata {hex cd}")
  | _ => throw (IO.userError s!"{name} failed; calldata {hex cd}")

-- Echo the requested hook selector with deliberately dirty bytes4 padding;
-- beforeSwap returns three words, the other callbacks return two.
def hookCode : ByteArray := ⟨#[
  0x5f,0x35,0x60,0xe0,0x1c,0x63,0x57,0x5e,0x24,0xb4,0x14,
  0x60,0x24,0x57,
  0x5f,0x35,0x60,0xe0,0x1c,0x60,0xe0,0x1b,0x60,0xab,0x17,0x5f,0x52,
  0x60,0x01,0x60,0x20,0x52,0x60,0x40,0x5f,0xf3,
  0x5b,0x5f,0x35,0x60,0xe0,0x1c,0x60,0xe0,0x1b,0x60,0xab,0x17,0x5f,0x52,
  0x60,0x01,0x60,0x20,0x52,0x60,0x60,0x5f,0xf3]⟩

def main : IO Unit := do
  let (target, _) := diffTarget.resolveRuntime (Rng.ofSeed 2026)
  let target := { target with callees := target.callees ++ [(EVM.address 0x7fff, hookCode)] }
  let (ctor, σ?) := runConstructor target poolManagerCreationBytecode [addressValue 0x2000] 0 (EVM.address 0x2000)
  IO.println s!"constructor: {ctor.describe}"
  let mut σ := σ?.getD target.world
  let key := poolKeyValue 3000 0x7fff
  σ ← invoke target σ "initialize" [key, intValue (2^96)]
  σ := setTransient target σ 0xc090fc4683624cfc3884e9d8de5eca132f2d0ec062aff75d43c0465d5ceeab23 1
  σ ← invoke target σ "modifyLiquidity" [key, liqParams 1000000, .bytes (wordBytes 123)]
  σ ← invoke target σ "swap" [key, swapParams true (-100) 4295128740, .bytes (wordBytes 456)]
  σ ← invoke target σ "swap" [key, swapParams false 50 1461446703485210103287273052203988822378723970341, .bytes .empty]
  σ ← invoke target σ "donate" [key, intValue 100, intValue 200, .bytes .empty]
  σ ← invoke target σ "modifyLiquidity" [key, liqParams 0, .bytes .empty]
  σ ← invoke target σ "modifyLiquidity" [key, liqParams (-1000000), .bytes .empty]
  IO.println s!"All hook callbacks completed with dirty selector padding and nonzero deltas; accounts: {σ.size}"
```

</details>

## Bytecode and source differences

`extsload(bytes32,uint256)`, selector `0x35fd631a`, shifts the count by five and
adds the return prefix with wrapping EVM arithmetic (arm PC 9693; span arithmetic
PCs 9768–9770; shared RETURN at PC 2516). Counts such as `2^251` can return
successfully with a declared array length that does not match the returned data.
A direct run of the unmodified bytecode reproduced this in 2,599 gas out of 10,000.
A gas bound above `2^24` cannot exclude this behavior.

The user authorized a well-formedness condition in the DSS Common style.
`Syntax.poolManagerWF` requires `224 + 32*n < 2^256` for nonpayable range-`extsload`
calldata satisfying the entry length guards. It is a refinement hypothesis, not a
runtime `require`: the bytecode does not enforce it. Generated function stubs,
runtime theorems, and the contract theorem carry it. This explicitly restricts
the call domain, including some cheap calls, without a mapping-slot noncollision
assumption. The available repository example is `Benchmarks/Dss/Cure/Common.lean`
(`cureStorageWF`).

The specification follows these compiled details where direct typed translation
would lose information:

- Empty array forms of raw `extsload`/`exttload` still perform the assembly
  do-while loop's first read. Range `extsload` also reads its first slot at count zero.
- Hook reply validation checks length and the first four bytes, allowing dirty
  bytes4 padding. `beforeSwap` truncates its fee word to uint24. Raw reply handling
  retains these rules; strict typed tuple decoding would reject valid replies.
- Packed tick writes, cached pool slot0/liquidity values, sequential fee-growth
  reads/writes, and transient reserve updates preserve bytecode ordering even when
  derived storage slots alias.
- PoolId hashing uses sign-extended tick spacing in a 256-bit word; position hashing
  uses packed 20/3/3/32-byte fields. FullMath/Newton operations wrap where compiled
  arithmetic wraps; liquidity/delta operations retain their checked arithmetic.
- ABI tuple parameters are unpacked into Solm struct values at entry. Casts are
  explicit where a notation type annotation alone would not perform conversion.

These are modeling corrections, not claims of new source vulnerabilities.
`PoolManager.spec.json` retains the original translator diagnostics and draft call
facts. Its library-call entries are not the authoritative external ABI.

## Guidance for the proving session

`SpecSyntax.lean` is authoritative. `Spec.lean` selects its 12-entry
`Syntax.externalABI`: `balanceOf(address)`, `unlockCallback(bytes)`, and before/after
initialize, add liquidity, remove liquidity, swap, and donate. The first two use
typed return decoding; hooks use raw calls and explicit validation. Currency
transfers use raw native/ERC20 calls with the bytecode's success rules.

`original` is the sole immutable, at runtime offset 13606. The constructor sets
it to `address(this)`; generated immutable plumbing patches that word. The
constructor preserves the high bits of owner slot zero and emits the ownership
event. There is no receive or fallback function.

Assembly's arbitrary persistent and transient words are modeled by static arrays
spanning the 256-bit slot space. They are storage aliases, not memory
representations. Persistent declarations keep slots 0 through 6 modulo `2^256`.
`TickInfo.liquidityPacked` represents one packed word. Prove the slot-layout
identities; do not assume hash noncollision.

Exactly 35 generated `sorry` sites remain: 33 function bodies, the constructor,
and `restrictImmutables_of_fit` in `Common.lean`. Dispatch and block summaries
build without `sorry`. Runtime summaries have 67 shards (1,346 units); creation
summaries have 68 shards (1,358 units). Swap/modifyLiquidity, TickMath/FullMath,
arbitrary slot aliases, callback reentrancy, and the gas argument below will need
the most proof work. Keep shared helpers shared across entry proofs.

The adapter below reproduces generated files without changing repository scripts.
It disambiguates scalar/array overloads, recognizes the leading-zero `balanceOf`
selector's PUSH3, selects the reviewed ABI, and threads WF/gas hypotheses. Smaller
summaries at the specified repeated-squaring block starts (runtime and its embedded
creation copy) avoid exponential symbolic-expression growth. Save the adapter as
`/tmp/uniswap-v4-regenerate.py` and invoke from the repository root:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 /tmp/uniswap-v4-regenerate.py lean
PYTHONDONTWRITEBYTECODE=1 python3 /tmp/uniswap-v4-regenerate.py report
PYTHONDONTWRITEBYTECODE=1 python3 /tmp/uniswap-v4-regenerate.py blocks
PYTHONDONTWRITEBYTECODE=1 python3 /tmp/uniswap-v4-regenerate.py proof
lake build Benchmarks.UniswapV4PoolManager.Correct
```

Use `proof` alone after specification edits. It overwrites generated stubs, so
preserve completed proofs before using it in a later session. Do not rerun
`sol2solm.py` over the finished specification.

<details>
<summary>Generator adapter</summary>

```python
"""Contract-local generator adapters; repository scripts remain unchanged."""
from pathlib import Path
import inspect
import re
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path.cwd() / 'scripts'))
import evm_tools
_original_names = evm_tools.overload_names

def names(signatures):
    result = _original_names(signatures)
    duplicates = {v for v in result.values() if list(result.values()).count(v) > 1}
    for sig, name in list(result.items()):
        if name in duplicates and '[]' in sig:
            result[sig] = name + '_array'
    assert len(set(result.values())) == len(result)
    return result

evm_tools.overload_names = names
# Include selectors with leading zero bytes, e.g. PUSH3 0xfdd58e.
source = inspect.getsource(evm_tools.selector_compares)
source = source.replace('if ins.opcode != 0x63:', 'if not (ins.opcode == 0x63 or ins.opcode == 0x62 and ins.argument == 0xfdd58e):')
exec(source, evm_tools.__dict__)

D = Path('Benchmarks/UniswapV4PoolManager')
M = 'Benchmarks.UniswapV4PoolManager'
mode = sys.argv[1]
if mode == 'blocks':
    import scaffold
    import generate_rd_blocks as rd
    _segments = rd.bounded_supported_segments
    def segments(block, max_instructions=rd.MAX_SUMMARY_INSTRUCTIONS):
        # Repeated squaring duplicates symbolic terms. Bound just this run more
        # tightly in both runtime and creation's embedded runtime.
        if block and block[0].pc in (18089, 18274):
            max_instructions = min(max_instructions, 16)
        return _segments(block, max_instructions)
    rd.bounded_supported_segments = segments
    raise SystemExit(scaffold.main(['blocks', '--dir', str(D), '--module', M, '--force']))
if mode == 'lean':
    import scaffold
    raise SystemExit(scaffold.main(['lean', '--dir', str(D), '--module', M, '--force']))
if mode == 'report':
    import bytecode_report
    raise SystemExit(bytecode_report.main([str(D), '--output', str(D/'PoolManager.report.md')]))
if mode == 'proof':
    import proof_skeleton as p
    _spec = p.render_spec
    def spec(c):
        calls, c.external_calls = c.external_calls, []
        result = _spec(c)
        c.external_calls = calls
        result = result.replace('/-! ## Config -/',
          '/-- Audited against the pinned interfaces; defined with the specification. -/\n'
          'def externalABI : ExternalCallABI := Syntax.externalABI\n\n/-! ## Config -/')
        return result.replace('externalABI := defaultExternalCallABI', 'externalABI := externalABI')
    p.render_spec = spec
    _signature = p.body_signature
    def signature(c, t, global_guard):
        result = _signature(c, t, global_guard)
        return result.replace('    (hsel :',
          '    (hWF : Syntax.poolManagerWF σ I)\n'
          '    (hGas : Syntax.poolManagerGasBound g)\n    (hsel :')
    p.body_signature = signature
    _correct = p.render_correct
    def correct(c, global_guard):
        result = _correct(c, global_guard)
        result = result.replace('runtimeRefinement config',
          'runtimeRefinementWithWF Syntax.poolManagerWF Syntax.poolManagerGasBound config')
        result = result.replace('contractRefinement config',
          'contractRefinementWF Syntax.poolManagerWF Syntax.poolManagerGasBound config')
        result = result.replace('fun σ σ₀ g A I hcode hsize ↦', 'fun σ σ₀ g A I hcode hsize hWF hGas ↦')
        for t in c.transitions:
            before = f'{c.prefix}{t.cap}Body v hcode hsize'
            result = result.replace(before, before+' hWF hGas')
        return result
    p.render_correct = correct
    raise SystemExit(p.main(['--dir', str(D), '--module', M, '--force']))
raise SystemExit('unknown mode')
```

</details>

## Gas bound

Runtime theorems use `Syntax.poolManagerGasBound g`, meaning:

```text
g.toNat < B
B = 324518553658429321982441292826060
K = 2^58
C(n) = 3*n + floor(n*n/512)
B = C(K+3) + C(K-2) + 3*(K-2) + 1487
```

This is strictly above `2^24`. It abstracts compiler memory-capacity bookkeeping
and the consequent safety of pointer/size arithmetic. Individual ABI length and
offset validation remains in the modern decoder and specification guards. The
cheap range-`extsload` wrap is covered separately by WF.

The binding path is the second allocation while decoding a successful
`unlockCallback(bytes)` reply. Let `R` be raw reply size, `L` decoded byte length,
and `ceil32` round bytes up to a multiple of 32. The raw reply is copied at byte
160 (RETURNDATACOPY at PC 9249). Both allocations use the capacity check at PC
11822; the second is called from PC 9373. With return offset 32, `R >= L+64`, and
the aggregate end is `192 + ceil32(R) + ceil32(L)`. The first rounded sizes crossing
`2^64` are:

```text
L = 2^63 - 159
R = L + 64 = 2^63 - 95
ceil(R/32) = K-2
ceil(L/32) = K-4
parent active memory words after copying = K+3
```

Offset zero forces a zero decoded length. Offsets 1 through 7 force length below
`2^59` because the head words overlap; offsets 8 through 31 force length above the
uint64 decoder limit. Thus a large valid length needs offset at least 32. Trailing
data or larger offsets cannot reduce raw reply size. Larger input cannot reduce
parent cost.

The parent spends `C(K+3)` on memory, `3*(K-2)` on copying reply words, and 1,469 on
other operations, including warm CALL, TLOAD, TSTORE, dispatch, decoding, and the
panic path. A fresh EVM callee producing this reply spends at least `C(K-2)` on
memory and 18 on forming the two ABI head words and returning. Their sum is `B`.
Cold calls, nonempty input, extra callback work, and larger replies increase cost.

The 18-gas callback is attainable. Install these nine opcodes, padded with 23 zero
bytes to make code size 32, at address `L`; set the block timestamp to `R`:

```text
CODESIZE PUSH0 MSTORE ADDRESS MSIZE MSTORE TIMESTAMP PUSH0 RETURN
38 5f 52 30 59 52 42 5f f3
```

Call unlock with selector `48c89491` followed by a zero word (valid empty bytes via
offset zero), zero value, a warm caller, and zero initial lock/delta count. The
callback returns head `[32,L]` followed by zero bytes. At starting gas `B` the
bytecode can finish with allocation panic `0x41` although the value-level decode
is valid. EIP-150's call cap leaves enough callback gas at this size. Thus a larger
upper interval would admit the behavior being abstracted: the strict cutoff is
necessary.

Native precompiles give no cheaper counterexample: fixed outputs are too small;
identity echoes a callback selector that fails ABI offset validation; modexp's
cost for such a large output exceeds `B`. Other capacity-check paths require
copying/encoding near `2^64` bytes before an omitted aggregate guard can fail.
Fixed allocations between these writes are bounded (at most 256 bytes each), and
the swap loop reuses its step object. Their memory cost alone exceeds `B`. Raw hook
replies must also be copied before driving later allocations. A 256-bit span
wrap requires still greater expansion, except for the range getter restricted by
WF. Within the bound a path violating these abstractions therefore exhausts gas
before a conflicting completed result. Proving the inequalities on each relevant
path is part of the refinement obligations, not an extra axiom.

An exact sparse trace of the original runtime confirmed the 327-step panic path,
1,469 parent operation cost, and the arithmetic above without allocating the huge
buffer. Native EVM runs checked scaled versions with only the PUSH8 capacity
constant reduced, retaining all opcode costs:

| Capacity bits | Cutoff | At cutoff minus one | At cutoff / cutoff plus one |
| --- | ---: | --- | --- |
| 12 | 2,075 | out of gas | panic `0x41`, 2,075 gas used |
| 16 | 14,800 | out of gas | panic `0x41`, 14,800 gas used |
| 20 | 1,197,580 | out of gas | panic `0x41`, 1,197,580 gas used |

These scaled runs validate the gas accounting. They do not execute an actual
`2^63`-byte reply and do not replace a proof of the full bound.

<details>
<summary>Scaled native EVM gas diagnostic</summary>

Save as `/tmp/uniswap-v4-capacity.lean` and run
`lake env lean --run /tmp/uniswap-v4-capacity.lean` at the repository root.

```lean
import Solm.DiffTest.Trace
open Ethereum Ethereum.EVM Solm.DiffTest Solm.Interp

def cm (n : Nat) : Nat := 3*n + n*n/512

def main : IO Unit := do
  let text ← IO.FS.readFile "Benchmarks/UniswapV4PoolManager/runtime.hex"
  let hex := text.trimAscii.toString
  let template ← match ByteArray.ofBlob (getBlob! (if hex.startsWith "0x" then hex else "0x" ++ hex)) with
    | .ok code => pure code
    | .error e => throw (IO.userError e)
  let callback : ByteArray := ⟨#[0x38,0x5f,0x52,0x30,0x59,0x52,0x42,0x5f,0xf3] ++ Array.replicate 23 0⟩
  for bits in [12,16,20] do
    let k := 2^(bits-6)
    let length := 2^(bits-1)-159
    let replySize := length+64
    let bound := cm (k+3) + cm (k-2) + 3*(k-2) + 1487
    let mut code := template
    let limit := (UInt256.ofNat (2^bits-1)).toByteArray
    for j in [:8] do
      code := code.set! (11868+j) limit[24+j]!
    let self := EVM.address 0x1000
    let caller := EVM.address length
    let σ := (∅ : AccountMap).insert self { (default : Account) with code := code }
      |>.insert caller { (default : Account) with code := callback }
    let calldata : ByteArray := ⟨#[0x48,0xc8,0x94,0x91]⟩ ++ (UInt256.ofNat 0).toByteArray
    let I := { (default : ExecutionEnv) with
      codeOwner := self
      sender := caller
      source := caller
      code := code
      calldata := calldata
      perm := true
      header := { (default : BlockHeader) with timestamp := replySize }
    }
    let A := { (default : Substate) with accessedAccounts := (default : Substate).accessedAccounts.insert caller }
    for g in [bound-1,bound,bound+1] do
      let trace := runTrace (initialState σ σ (.ofNat g) A I) (g+1)
      match trace.result with
      | .error error => IO.println s!"bits={bits} gas={g} bound={bound}: {repr error}"
      | .ok (.revert state out) =>
          IO.println s!"bits={bits} gas={g} bound={bound}: revert, used={g-state.toNat}, payload={Ethereum.toHex out}"
      | .ok (.success _ _) => throw (IO.userError "unexpected success")
```

</details>
