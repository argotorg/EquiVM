#!/usr/bin/env python3
# Generate the truth() success EVM trace as flat segment lemmas (bounded nesting).
# Each segment: entry-state hyps -> (OOG  v  exit-state existential), chained at top level.

# ---- step table (0-indexed). stk = stack BEFORE (top first). ----
steps = []
def add(**k): steps.append(k)

add(op="push1", arg=128, pcn=2, stk=[], after=[128])
add(op="push1", arg=64, pcn=4, stk=[128], after=[64,128])
add(op="mstore", off=64, val=128, pcn=5, stk=[64,128], after=[], memcost=9, awb=0, awa=3, memb="mem0", mema="mem1")
add(op="callvalue", pcn=6, stk=[], after=[0])
add(op="dup1", pcn=7, stk=[0], after=[0,0])
add(op="iszero", a=0, res=1, pcn=8, stk=[0,0], after=[1,0])
add(op="push1", arg=14, pcn=10, stk=[1,0], after=[14,1,0])
add(op="jumpi_t", dest=14, pcn=14, stk=[14,1,0], after=[0])
add(op="jumpdest", pcn=15, stk=[0], after=[0])
add(op="pop", pcn=16, stk=[0], after=[])
add(op="push1", arg=4, pcn=18, stk=[], after=[4])
add(op="calldatasize", pcn=19, stk=[4], after=["SZ",4])
add(op="lt_sz", pcn=20, stk=["SZ",4], after=[0])
add(op="push1", arg=38, pcn=22, stk=[0], after=[38,0])
add(op="jumpi_nt", pcn=23, stk=[38,0], after=[])
add(op="push0", pcn=24, stk=[], after=[0])
add(op="calldataload", pcn=25, stk=[0], after=["cdw"])
add(op="push1", arg=224, pcn=27, stk=["cdw"], after=[224,"cdw"])
add(op="shr", pcn=28, stk=[224,"cdw"], after=["sel"])
add(op="dup1", pcn=29, stk=["sel"], after=["sel","sel"])
add(op="push4", arg=2661241298, pcn=34, stk=["sel","sel"], after=[2661241298,"sel","sel"])
add(op="eq_sel", pcn=35, stk=[2661241298,"sel","sel"], after=[1,"sel"])
add(op="push1", arg=42, pcn=37, stk=[1,"sel"], after=[42,1,"sel"])
add(op="jumpi_t", dest=42, pcn=42, stk=[42,1,"sel"], after=["sel"])
add(op="jumpdest", pcn=43, stk=["sel"], after=["sel"])
add(op="push1", arg=48, pcn=45, stk=["sel"], after=[48,"sel"])
add(op="push1", arg=68, pcn=47, stk=[48,"sel"], after=[68,48,"sel"])
add(op="jump", dest=68, pcn=68, stk=[68,48,"sel"], after=[48,"sel"])
add(op="jumpdest", pcn=69, stk=[48,"sel"], after=[48,"sel"])
add(op="push0", pcn=70, stk=[48,"sel"], after=[0,48,"sel"])
add(op="push1", arg=1, pcn=72, stk=[0,48,"sel"], after=[1,0,48,"sel"])
add(op="swap1", pcn=73, stk=[1,0,48,"sel"], after=[0,1,48,"sel"])
add(op="pop", pcn=74, stk=[0,1,48,"sel"], after=[1,48,"sel"])
add(op="swap1", pcn=75, stk=[1,48,"sel"], after=[48,1,"sel"])
add(op="jump", dest=48, pcn=48, stk=[48,1,"sel"], after=[1,"sel"])
add(op="jumpdest", pcn=49, stk=[1,"sel"], after=[1,"sel"])
add(op="push1", arg=64, pcn=51, stk=[1,"sel"], after=[64,1,"sel"])
add(op="mload", a=64, val=128, pcn=52, stk=[64,1,"sel"], after=[128,1,"sel"], mem="mem1", awval=3)
add(op="push1", arg=59, pcn=54, stk=[128,1,"sel"], after=[59,128,1,"sel"])
add(op="swap2", pcn=55, stk=[59,128,1,"sel"], after=[1,128,59,"sel"])
add(op="swap1", pcn=56, stk=[1,128,59,"sel"], after=[128,1,59,"sel"])
add(op="push1", arg=100, pcn=58, stk=[128,1,59,"sel"], after=[100,128,1,59,"sel"])
add(op="jump", dest=100, pcn=100, stk=[100,128,1,59,"sel"], after=[128,1,59,"sel"])
add(op="jumpdest", pcn=101, stk=[128,1,59,"sel"], after=[128,1,59,"sel"])
add(op="push0", pcn=102, stk=[128,1,59,"sel"], after=[0,128,1,59,"sel"])
add(op="push1", arg=32, pcn=104, stk=[0,128,1,59,"sel"], after=[32,0,128,1,59,"sel"])
add(op="dup3", pcn=105, stk=[32,0,128,1,59,"sel"], after=[128,32,0,128,1,59,"sel"])
add(op="add", a=128, b=32, res=160, pcn=106, stk=[128,32,0,128,1,59,"sel"], after=[160,0,128,1,59,"sel"])
add(op="swap1", pcn=107, stk=[160,0,128,1,59,"sel"], after=[0,160,128,1,59,"sel"])
add(op="pop", pcn=108, stk=[0,160,128,1,59,"sel"], after=[160,128,1,59,"sel"])
add(op="push1", arg=117, pcn=110, stk=[160,128,1,59,"sel"], after=[117,160,128,1,59,"sel"])
add(op="push0", pcn=111, stk=[117,160,128,1,59,"sel"], after=[0,117,160,128,1,59,"sel"])
add(op="dup4", pcn=112, stk=[0,117,160,128,1,59,"sel"], after=[128,0,117,160,128,1,59,"sel"])
add(op="add", a=128, b=0, res=128, pcn=113, stk=[128,0,117,160,128,1,59,"sel"], after=[128,117,160,128,1,59,"sel"])
add(op="dup5", pcn=114, stk=[128,117,160,128,1,59,"sel"], after=[1,128,117,160,128,1,59,"sel"])
add(op="push1", arg=87, pcn=116, stk=[1,128,117,160,128,1,59,"sel"], after=[87,1,128,117,160,128,1,59,"sel"])
add(op="jump", dest=87, pcn=87, stk=[87,1,128,117,160,128,1,59,"sel"], after=[1,128,117,160,128,1,59,"sel"])
add(op="jumpdest", pcn=88, stk=[1,128,117,160,128,1,59,"sel"], after=[1,128,117,160,128,1,59,"sel"])
add(op="push1", arg=94, pcn=90, stk=[1,128,117,160,128,1,59,"sel"], after=[94,1,128,117,160,128,1,59,"sel"])
add(op="dup2", pcn=91, stk=[94,1,128,117,160,128,1,59,"sel"], after=[1,94,1,128,117,160,128,1,59,"sel"])
add(op="push1", arg=76, pcn=93, stk=[1,94,1,128,117,160,128,1,59,"sel"], after=[76,1,94,1,128,117,160,128,1,59,"sel"])
add(op="jump", dest=76, pcn=76, stk=[76,1,94,1,128,117,160,128,1,59,"sel"], after=[1,94,1,128,117,160,128,1,59,"sel"])
add(op="jumpdest", pcn=77, stk=[1,94,1,128,117,160,128,1,59,"sel"], after=[1,94,1,128,117,160,128,1,59,"sel"])
add(op="push0", pcn=78, stk=[1,94,1,128,117,160,128,1,59,"sel"], after=[0,1,94,1,128,117,160,128,1,59,"sel"])
add(op="dup2", pcn=79, stk=[0,1,94,1,128,117,160,128,1,59,"sel"], after=[1,0,1,94,1,128,117,160,128,1,59,"sel"])
add(op="iszero", a=1, res=0, pcn=80, stk=[1,0,1,94,1,128,117,160,128,1,59,"sel"], after=[0,0,1,94,1,128,117,160,128,1,59,"sel"])
add(op="iszero", a=0, res=1, pcn=81, stk=[0,0,1,94,1,128,117,160,128,1,59,"sel"], after=[1,0,1,94,1,128,117,160,128,1,59,"sel"])
add(op="swap1", pcn=82, stk=[1,0,1,94,1,128,117,160,128,1,59,"sel"], after=[0,1,1,94,1,128,117,160,128,1,59,"sel"])
add(op="pop", pcn=83, stk=[0,1,1,94,1,128,117,160,128,1,59,"sel"], after=[1,1,94,1,128,117,160,128,1,59,"sel"])
add(op="swap2", pcn=84, stk=[1,1,94,1,128,117,160,128,1,59,"sel"], after=[94,1,1,1,128,117,160,128,1,59,"sel"])
add(op="swap1", pcn=85, stk=[94,1,1,1,128,117,160,128,1,59,"sel"], after=[1,94,1,1,128,117,160,128,1,59,"sel"])
add(op="pop", pcn=86, stk=[1,94,1,1,128,117,160,128,1,59,"sel"], after=[94,1,1,128,117,160,128,1,59,"sel"])
add(op="jump", dest=94, pcn=94, stk=[94,1,1,128,117,160,128,1,59,"sel"], after=[1,1,128,117,160,128,1,59,"sel"])
add(op="jumpdest", pcn=95, stk=[1,1,128,117,160,128,1,59,"sel"], after=[1,1,128,117,160,128,1,59,"sel"])
add(op="dup3", pcn=96, stk=[1,1,128,117,160,128,1,59,"sel"], after=[128,1,1,128,117,160,128,1,59,"sel"])
add(op="mstore", off=128, val=1, pcn=97, stk=[128,1,1,128,117,160,128,1,59,"sel"], after=[1,128,117,160,128,1,59,"sel"], memcost=6, awb=3, awa=5, memb="mem1", mema="mem2")
add(op="pop", pcn=98, stk=[1,128,117,160,128,1,59,"sel"], after=[128,117,160,128,1,59,"sel"])
add(op="pop", pcn=99, stk=[128,117,160,128,1,59,"sel"], after=[117,160,128,1,59,"sel"])
add(op="jump", dest=117, pcn=117, stk=[117,160,128,1,59,"sel"], after=[160,128,1,59,"sel"])
add(op="jumpdest", pcn=118, stk=[160,128,1,59,"sel"], after=[160,128,1,59,"sel"])
add(op="swap3", pcn=119, stk=[160,128,1,59,"sel"], after=[59,128,1,160,"sel"])
add(op="swap2", pcn=120, stk=[59,128,1,160,"sel"], after=[1,128,59,160,"sel"])
add(op="pop", pcn=121, stk=[1,128,59,160,"sel"], after=[128,59,160,"sel"])
add(op="pop", pcn=122, stk=[128,59,160,"sel"], after=[59,160,"sel"])
add(op="jump", dest=59, pcn=59, stk=[59,160,"sel"], after=[160,"sel"])
add(op="jumpdest", pcn=60, stk=[160,"sel"], after=[160,"sel"])
add(op="push1", arg=64, pcn=62, stk=[160,"sel"], after=[64,160,"sel"])
add(op="mload", a=64, val=128, pcn=63, stk=[64,160,"sel"], after=[128,160,"sel"], mem="mem2", awval=5)
add(op="dup1", pcn=64, stk=[128,160,"sel"], after=[128,128,160,"sel"])
add(op="swap2", pcn=65, stk=[128,128,160,"sel"], after=[160,128,128,"sel"])
add(op="sub", a=160, b=128, res=32, pcn=66, stk=[160,128,128,"sel"], after=[32,128,"sel"])
add(op="swap1", pcn=67, stk=[32,128,"sel"], after=[128,32,"sel"])
add(op="return", off=128, length=32, pcn=68, stk=[128,32,"sel"], mem="mem2", awval=5)

def cost_of(s):
    o=s["op"]
    if o in ("push1","push4","dup1","dup2","dup3","dup4","dup5","swap1","swap2","swap3",
             "iszero","shr","sub","add","eq_sel","lt_sz","calldataload"): return 3
    if o in ("push0","pop","callvalue","calldatasize"): return 2
    if o=="jumpdest": return 1
    if o=="jump": return 8
    if o in ("jumpi_t","jumpi_nt"): return 10
    if o=="mstore": return s["memcost"]+3
    if o=="mload": return 3
    if o=="return": return 0
    raise Exception(o)
C=0
for s in steps:
    s["Cbef"]=C; s["cost"]=cost_of(s); C+=s["cost"]; s["Caf"]=C
TOTAL=C

# ---- rendering helpers ----
def rv(x):
    if x=="sel": return "sel"
    if x=="cdw": return "cdw"
    if x=="SZ": return "(UInt256.ofNat I.calldata.size)"
    return f"⟨{x}⟩"
def rstk(xs): return "[" + ", ".join(rv(x) for x in xs) + "]"
def aw(v): return f"UInt256.ofNat {v}"
def mem(m): return {"mem0":"ByteArray.empty","mem1":"truthMem1","mem2":"truthMem2"}[m]

# Track memory/aw symbol across the trace so each step knows current values.
cur_mem="mem0"; cur_aw=0
for s in steps:
    s["mem_in"]=cur_mem; s["aw_in"]=cur_aw
    if s["op"]=="mstore":
        cur_mem=s["mema"]; cur_aw=s["awa"]
    s["mem_out"]=cur_mem; s["aw_out"]=cur_aw

import sys
MAXST = int(sys.argv[1]) if len(sys.argv) > 1 else len(steps)

def rv(x):
    if x=="sel": return "(UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩)"
    if x=="cdw": return "(uInt256OfByteArray (I.calldata.readBytes 0 32))"
    if x=="SZ": return "(UInt256.ofNat I.calldata.size)"
    return f"⟨{x}⟩"
def rstk(xs): return "[" + ", ".join(rv(x) for x in xs) + "]"
def aw(v): return f"(UInt256.ofNat {v})"
def memx(m): return {"mem0":"ByteArray.empty","mem1":"truthMem1","mem2":"truthMem2"}[m]

L=[]
def P(ind,s): L.append("  "*ind + s)

# header (indent 1)
P(1,"set s0 := initState cA gh bl σ σ₀ g A I with hs0")
P(1,"have hee0 : s0.executionEnv = I := by rw [hs0]; simp [initState]")
P(1,"have hcode0 : s0.executionEnv.code = truthBytecode := by rw [hee0]; exact hcode")
P(1,"have hpc0 : s0.machineState.pc = ⟨0⟩ := by rw [hs0]; simp [initState]; rfl")
P(1,"have hgas0 : s0.machineState.gasAvailable.toNat = g.toNat - 0 := by rw [hs0]; simp [initState]")
P(1,"have hstk0 : s0.machineState.stack = [] := by rw [hs0]; simp [initState]; rfl")
P(1,"have haw0 : s0.machineState.activeWords = UInt256.ofNat 0 := by rw [hs0]; simp [initState]; rfl")
P(1,"have hmem0 : s0.machineState.memory = ByteArray.empty := by rw [hs0]; simp [initState]; rfl")
P(1,"have hX0 : X (g.toNat + 1) (D_J truthBytecode ⟨0⟩) s0 = X (g.toNat + 1 - 0) (D_J truthBytecode ⟨0⟩) s0 := rfl")

def emit_simple(ind,n,st):
    n1=n+1; Caf=st["Caf"]; Cbef=st["Cbef"]; pcn=st["pcn"]; op=st["op"]
    aw_in=st["aw_in"]; mem_in=st["mem_in"]
    # wrapper, stdef, stdefname, hstk_tac
    if op in ("push1","push4"):
        wn = "push1_xstep" if op=="push1" else "push4_xstep"
        sd = ("stPush1" if op=="push1" else "stPush4")
        W=f"{wn} (argv := ⟨{st['arg']}⟩) hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)"
        SD=f"{sd} s{n} ⟨{st['arg']}⟩"; SDN=sd
        HSTK=f"by rw [hs{n1}]; simp only [{sd}, hstk{n}]"
    elif op=="push0":
        W=f"push0_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)"
        SD=f"stPush0 s{n}"; SDN="stPush0"; HSTK=f"by rw [hs{n1}]; simp only [stPush0, hstk{n}]"
    elif op=="pop":
        W=f"pop_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)"
        SD=f"stPop s{n} {rstk(st['after'])}"; SDN="stPop"; HSTK=f"by rw [hs{n1}]; simp only [stPop]"
    elif op=="dup1":
        a=st['stk'][0]; t=st['stk'][1:]
        W=f"dup1_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)"
        SD=f"stDup1 s{n} {rv(a)} {rstk(t)}"; SDN="stDup1"; HSTK=f"by rw [hs{n1}]; simp only [stDup1]"
    elif op in ("dup2","dup3","dup4","dup5","swap1","swap2","swap3"):
        W=f"{op}_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)"
        SD=f"stSwap s{n} {rstk(st['after'])}"; SDN="stSwap"; HSTK=f"by rw [hs{n1}]; simp only [stSwap]"
    elif op=="iszero":
        a=st['stk'][0]; t=st['stk'][1:]
        W=f"iszero_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)"
        SD=f"stIsZero s{n} ⟨{a}⟩ {rstk(t)}"; SDN="stIsZero"
        HSTK=f"by rw [hs{n1}]; simp only [stIsZero]; rw [show (UInt256.isZero ⟨{a}⟩) = ⟨{st['res']}⟩ from by decide]"
    elif op=="callvalue":
        W=f"callvalue_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)"
        SD=f"stCallvalue s{n}"; SDN="stCallvalue"
        HSTK=f"by rw [hs{n1}]; simp only [stCallvalue, hee{n}, hwv, hstk{n}]"
    elif op=="calldatasize":
        W=f"calldatasize_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)"
        SD=f"stCalldatasize s{n}"; SDN="stCalldatasize"
        HSTK=f"by rw [hs{n1}]; simp only [stCalldatasize, hee{n}, hstk{n}]"
    elif op=="calldataload":
        t=st['stk'][1:]
        W=f"calldataload_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)"
        SD=f"stCalldataload s{n} ⟨0⟩ {rstk(t)}"; SDN="stCalldataload"
        HSTK=f"by rw [hs{n1}]; simp only [stCalldataload, hee{n}]; rfl"
    elif op=="shr":
        t=st['stk'][2:]
        W=f"shr_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)"
        SD=f"stBinop s{n} {rv('sel')} {rstk(t)}"; SDN="stBinop"
        HSTK=f"by rw [hs{n1}]; simp only [stBinop]"
    elif op=="add":
        t=st['stk'][2:]
        W=f"add_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)"
        SD=f"stBinop s{n} (⟨{st['a']}⟩ + ⟨{st['b']}⟩) {rstk(t)}"; SDN="stBinop"
        HSTK=f"by rw [hs{n1}]; simp only [stBinop]; rw [show ((⟨{st['a']}⟩:UInt256) + ⟨{st['b']}⟩) = ⟨{st['res']}⟩ from by decide]"
    elif op=="sub":
        t=st['stk'][2:]
        W=f"sub_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)"
        SD=f"stBinop s{n} (UInt256.sub ⟨{st['a']}⟩ ⟨{st['b']}⟩) {rstk(t)}"; SDN="stBinop"
        HSTK=f"by rw [hs{n1}]; simp only [stBinop]; rw [show (UInt256.sub ⟨{st['a']}⟩ ⟨{st['b']}⟩) = ⟨{st['res']}⟩ from by decide]"
    elif op=="lt_sz":
        t=st['stk'][2:]
        W=f"lt_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)"
        SD=f"stBinop s{n} (UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩) {rstk(t)}"; SDN="stBinop"
        HSTK=f"by rw [hs{n1}]; simp only [stBinop]; rw [show (UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩) = ⟨0⟩ from lt_four_eq_zero_of_ge hsz hsize]"
    elif op=="eq_sel":
        t=st['stk'][2:]
        W=f"eq_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)"
        SD=f"stBinop s{n} (UInt256.eq ⟨2661241298⟩ {rv('sel')}) {rstk(t)}"; SDN="stBinop"
        HSTK=f"by rw [hs{n1}]; simp only [stBinop]; rw [show (UInt256.eq ⟨2661241298⟩ {rv('sel')}) = ⟨1⟩ from by rw [truthEvmSelector]; simp [hmatch]]"
    elif op=="jumpdest":
        W=f"jumpdest_xstep hcode{n} hpc{n} (by decide) (by rw [hstk{n}]; simp)"
        SD=f"stJumpdest s{n}"; SDN="stJumpdest"; HSTK=f"by rw [hs{n1}]; simp only [stJumpdest]; exact hstk{n}"
    elif op=="jump":
        t=st['stk'][1:]
        W=f"jump_xstep hcode{n} hpc{n} (by decide) hstk{n} (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)"
        SD=f"stJump s{n} ⟨{st['dest']}⟩ {rstk(t)}"; SDN="stJump"; HSTK=f"by rw [hs{n1}]; simp only [stJump]"
    elif op=="jumpi_t":
        t=st['stk'][2:]
        W=f"jumpi_t_xstep hcode{n} hpc{n} (by decide) hstk{n} (by decide) (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)) (by norm_num)"
        SD=f"stJumpiT s{n} ⟨{st['dest']}⟩ {rstk(t)}"; SDN="stJumpiT"; HSTK=f"by rw [hs{n1}]; simp only [stJumpiT]"
    elif op=="jumpi_nt":
        t=st['stk'][2:]
        W=f"jumpi_nt_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)"
        SD=f"stJumpiNT s{n} {rstk(t)}"; SDN="stJumpiNT"; HSTK=f"by rw [hs{n1}]; simp only [stJumpiNT]"
    else:
        raise Exception("simple? "+op)
    # pc tactic
    if op in ("jump","jumpi_t"):
        PCT=f"by rw [hs{n1}]; simp only [{SDN}]"
    else:
        PCT=f"by rw [hs{n1}]; simp only [{SDN}]; rw [hpc{n}]; rfl"
    # gas
    GAST=f"by rw [hs{n1}]; simp only [{SDN}]; rw [toNat_sub_ofNat (by omega)]; omega"
    # aw / mem (preserved by simple ops)
    AWT=f"by rw [hs{n1}]; simp only [{SDN}]; exact haw{n}"
    MEMT=f"by rw [hs{n1}]; simp only [{SDN}]; exact hmem{n}"
    P(ind, f"-- step {n}: {op}")
    P(ind, f"have hstep{n} := {W}")
    P(ind, f"by_cases h{n} : g.toNat < {Caf}")
    P(ind, f"· exact Or.inl (by rw [hX{n}]; exact stepOOG hgas{n} hstep{n} (by norm_num) (by omega) (by omega))")
    P(ind, f"· set s{n1} := {SD} with hs{n1}")
    P(ind+1, f"have hX{n1} := hX{n}.trans (stepContinue (k := {n}) (C := {Cbef}) hgas{n} hstep{n} (by norm_num) (by omega))")
    P(ind+1, f"have hee{n1} : s{n1}.executionEnv = I := by rw [hs{n1}]; simp only [{SDN}]; exact hee{n}")
    P(ind+1, f"have hcode{n1} : s{n1}.executionEnv.code = truthBytecode := by rw [hee{n1}]; exact hcode")
    P(ind+1, f"have hpc{n1} : s{n1}.machineState.pc = ⟨{pcn}⟩ := {PCT}")
    P(ind+1, f"have hgas{n1} : s{n1}.machineState.gasAvailable.toNat = g.toNat - {Caf} := {GAST}")
    P(ind+1, f"have hstk{n1} : s{n1}.machineState.stack = {rstk(st['after'])} := {HSTK}")
    P(ind+1, f"have haw{n1} : s{n1}.machineState.activeWords = {aw(st['aw_out'])} := {AWT}")
    P(ind+1, f"have hmem{n1} : s{n1}.machineState.memory = {memx(st['mem_out'])} := {MEMT}")


def emit_mstore(ind,n,st):
    n1=n+1; Caf=st["Caf"]; Cbef=st["Cbef"]; pcn=st["pcn"]; mc=st["memcost"]
    off=st["off"]; val=st["val"]; awa=st["awa"]; mema=st["mema"]
    P(ind, f"-- step {n}: mstore")
    P(ind, f"have hmc{n} : memoryExpansionCost s{n} .MSTORE = {mc} := by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw{n}, hstk{n}, Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide")
    P(ind, f"have hstep{n} := mstore_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)")
    P(ind, f"rw [hmc{n}] at hstep{n}")
    P(ind, f"by_cases h{n} : g.toNat < {Caf}")
    P(ind, f"· exact Or.inl (by rw [hX{n}]; exact stepOOG (cost := {mc} + 3) hgas{n} hstep{n} (by norm_num) (by omega) (by omega))")
    P(ind, f"· set s{n1} := stMStore s{n} ⟨{off}⟩ ⟨{val}⟩ {rstk(st['after'])} with hs{n1}")
    P(ind+1, f"have hX{n1} := hX{n}.trans (stepContinue (k := {n}) (C := {Cbef}) (cost := {mc} + 3) hgas{n} hstep{n} (by norm_num) (by omega))")
    P(ind+1, f"have hee{n1} : s{n1}.executionEnv = I := by rw [hs{n1}]; simp only [stMStore]; exact hee{n}")
    P(ind+1, f"have hcode{n1} : s{n1}.executionEnv.code = truthBytecode := by rw [hee{n1}]; exact hcode")
    P(ind+1, f"have hpc{n1} : s{n1}.machineState.pc = ⟨{pcn}⟩ := by rw [hs{n1}]; simp only [stMStore]; rw [hpc{n}]; rfl")
    P(ind+1, f"have hgas{n1} : s{n1}.machineState.gasAvailable.toNat = g.toNat - {Caf} := by rw [hs{n1}]; simp only [stMStore, hmc{n}]; rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]; omega")
    P(ind+1, f"have hstk{n1} : s{n1}.machineState.stack = {rstk(st['after'])} := by rw [hs{n1}]; simp [stMStore]")
    P(ind+1, f"have haw{n1} : s{n1}.machineState.activeWords = {aw(awa)} := by rw [hs{n1}]; simp only [stMStore, haw{n}]; decide")
    P(ind+1, f"have hmem{n1} : s{n1}.machineState.memory = {memx(mema)} := by rw [hs{n1}]; simp only [stMStore]; rw [hmem{n}, show (⟨{off}⟩:UInt256).toNat = {off} from by decide]; rfl")

def emit_mload(ind,n,st):
    n1=n+1; Caf=st["Caf"]; Cbef=st["Cbef"]; pcn=st["pcn"]; a=st["a"]; val=st["val"]; awval=st["awval"]
    t=st['stk'][1:]
    mm=st["mem"]; readl={"mem1":"truthMem1_read64","mem2":"truthMem2_read64"}[mm]
    sizel={"mem1":"truthMem1_size","mem2":"truthMem2_size"}[mm]
    P(ind, f"-- step {n}: mload")
    P(ind, f"have hmc{n} : memoryExpansionCost s{n} .MLOAD = 0 := by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw{n}, hstk{n}, Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide")
    P(ind, f"have hstep{n} := mload_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)")
    P(ind, f"rw [hmc{n}] at hstep{n}")
    P(ind, f"by_cases h{n} : g.toNat < {Caf}")
    P(ind, f"· exact Or.inl (by rw [hX{n}]; exact stepOOG (cost := 0 + 3) hgas{n} hstep{n} (by norm_num) (by omega) (by omega))")
    P(ind, f"· set s{n1} := stMLoad s{n} ⟨{a}⟩ {rstk(t)} with hs{n1}")
    P(ind+1, f"have hX{n1} := hX{n}.trans (stepContinue (k := {n}) (C := {Cbef}) (cost := 0 + 3) hgas{n} hstep{n} (by norm_num) (by omega))")
    P(ind+1, f"have hee{n1} : s{n1}.executionEnv = I := by rw [hs{n1}]; simp only [stMLoad]; exact hee{n}")
    P(ind+1, f"have hcode{n1} : s{n1}.executionEnv.code = truthBytecode := by rw [hee{n1}]; exact hcode")
    P(ind+1, f"have hpc{n1} : s{n1}.machineState.pc = ⟨{pcn}⟩ := by rw [hs{n1}]; simp only [stMLoad]; rw [hpc{n}]; rfl")
    P(ind+1, f"have hgas{n1} : s{n1}.machineState.gasAvailable.toNat = g.toNat - {Caf} := by rw [hs{n1}]; simp only [stMLoad, hmc{n}]; rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]; omega")
    P(ind+1, f"have hstk{n1} : s{n1}.machineState.stack = {rstk(st['after'])} := by rw [hs{n1}]; simp only [stMLoad]; rw [if_neg (by rw [hmem{n}, {sizel}, haw{n}]; decide)]; rw [hmem{n}, show (⟨{a}⟩:UInt256).toNat = {a} from by decide, {readl}, fromByteArrayBigEndian_toByteArray, show UInt256.ofNat ((⟨{val}⟩:UInt256).toNat) = ⟨{val}⟩ from by decide]")
    P(ind+1, f"have haw{n1} : s{n1}.machineState.activeWords = {aw(awval)} := by rw [hs{n1}]; simp only [stMLoad, haw{n}]; decide")
    P(ind+1, f"have hmem{n1} : s{n1}.machineState.memory = {memx(st['mem_out'])} := by rw [hs{n1}]; simp only [stMLoad]; exact hmem{n}")

def emit_return(ind,n,st):
    Cbef=st["Cbef"]; off=st["off"]; ln=st["length"]; t=st['stk'][2:]
    P(ind, f"-- step {n}: return (halt success)")
    P(ind, f"have hmc{n} : memoryExpansionCost s{n} .RETURN = 0 := by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw{n}, hstk{n}, Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide")
    P(ind, f"have hstep{n} := return_xstep hcode{n} hpc{n} (by decide) hstk{n} (by norm_num)")
    P(ind, f"rw [hmc{n}] at hstep{n}")
    P(ind, f"have houtput{n} : s{n}.machineState.memory.readWithPadding (⟨{off}⟩:UInt256).toNat (⟨{ln}⟩:UInt256).toNat = UInt256.toByteArray ⟨1⟩ := by rw [hmem{n}, show (⟨{off}⟩:UInt256).toNat = {off} from by decide, show (⟨{ln}⟩:UInt256).toNat = {ln} from by decide, truthMem2_read128]")
    P(ind, f"rw [houtput{n}] at hstep{n}")
    P(ind, f"exact Or.inr ⟨stReturn s{n} ⟨{off}⟩ ⟨{ln}⟩ {rstk(t)}, by rw [hX{n}]; exact stepHaltSuccess (k := {n}) (C := {Cbef}) hgas{n} hstep{n} (by norm_num) (by omega), rfl, rfl, rfl⟩")

# main loop
ind=1
for n,st in enumerate(steps):
    if n>=MAXST:
        P(ind,"sorry"); break
    op=st["op"]
    if op=="mstore":
        emit_mstore(ind,n,st); ind+=1
    elif op=="mload":
        emit_mload(ind,n,st); ind+=1
    elif op=="return":
        emit_return(ind,n,st)
    else:
        emit_simple(ind,n,st); ind+=1
print("\n".join(L))
