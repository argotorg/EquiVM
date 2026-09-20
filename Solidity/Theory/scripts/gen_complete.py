import json, sys
SP=__import__('os').path.dirname(__import__('os').path.abspath(__file__))+'/'
R=json.load(open(SP+'rules.json'))
FAM={
 'EvalExpr':('evalExpr_complete','evalExpr','fr m e','toRes'),
 'EvalValueOpt':('evalValueOpt_complete','evalValueOpt','fr m e','toRes'),
 'EvalSaltOpt':('evalSaltOpt_complete','evalSaltOpt','fr m e','toRes'),
 'EvalGasOpt':('evalGasOpt_complete','evalGasOpt','fr m e','toRes'),
 'EvalExprs':('evalExprs_complete','evalExprs','fr m es','toRes'),
 'EvalLValue':('evalLValue_complete','evalLValue','fr m e','toRes'),
 'AssignTuple':('assignTuple_complete','assignTuple','fr m ls vs','toUnit'),
 'ExecStmt':('execStmt_complete','execStmt','fr m s','toExec'),
 'DeclareTuple':('declareTuple_complete','declareTuple','fr m bs vs','toUnit'),
 'ExecLoop':('execLoop_complete','execLoop','fr m c post body','toExec'),
 'ExecBlock':('execBlock_complete','execBlock','fr m ss','toExec'),
 'ExecChain':('execChain_complete','execChain','fr m mods body','toExec'),
 'EvalMods':('evalMods_complete','evalMods','fr m mis','toRes'),
 'CallFn':('callFn_complete','callFn','fr m fn args','toFn'),
}
OFF2=set('memberField memberStorageLength memberStorageLengthPanic memberMemField memberMemLength memberBalance memberBytesLength memberRevert convert convertPanic convertRevert newArray newArrayRevert newContract newContractFailed newContractAbiPanic newContractArgsRevert newContractSaltRevert newContractValueRevert superCall superCallRevert superArgsRevert libraryCall libraryCallRevert libraryArgsRevert baseCall baseCallRevert baseArgsRevert'.split())
OFF3=set('requireTrue requireFalse requireMsg requireMsgRevert requireCustom requireCustomArgsRevert requireCustomPanic requireCondRevert assertTrue assertFalse assertRevert revertEmpty revertMsg revertMsgRevert keccak keccakRevert gasleft addmod mulmod modZero modArgsRevert ecrecover ecrecoverFailed ecrecoverAbiPanic ecrecoverArgsRevert abiEncode abiEncodePacked abiEncodeWithSelector abiEncodeWithSignature abiDecode abiDecodeFail abiEncodeRevert abiDecodeRevert internalCall internalCallRevert internalArgsRevert structLit structLitRevert structLitPanic convertUser usingForCall usingForArgsRevert usingForCallRevert push1 push1Revert push1Panic push0 push0Panic pop popPanic externalCall externalCallNoCode externalCallFailed externalCallDecodeFail externalValueRevert externalGasRevert externalArgsRevert externalAbiPanic lowLevelCall lowLevelValueRevert lowLevelGasRevert lowLevelDataRevert delegateCall delegateCallGasRevert delegateCallDataRevert transfer transferFailed send transferAmtRevert callRecvRevert'.split())
EXTRA={
 'msgData':['directMember','isEnvObj'], 'indexMemRaw':['isRaw'], 'indexMemRawRevert':['isRaw'], 'envMember':['directMember'], 'enumMember':['directMember'], 'typeMember':['directMember'],
 'assignTuple':['isTupleExpr'], 'assignTupleRevert':['isTupleExpr'],
 'deleteLocal':['isIncDec'], 'deleteStorage':['isIncDec'], 'deleteStoragePanic':['isIncDec'], 'deleteRevert':['isIncDec'],
 'requireCustom':['isCustomError'], 'requireCustomArgsRevert':['isCustomError'], 'requireCustomPanic':['isCustomError'],
 'superCall':['isSuperExpr'], 'superCallRevert':['isSuperExpr'], 'superArgsRevert':['isSuperExpr'],
 'libraryCall':['isSuperExpr','headIdent','libraryRecv'], 'libraryCallRevert':['isSuperExpr','headIdent','libraryRecv'], 'libraryArgsRevert':['isSuperExpr','headIdent','libraryRecv'],
 'baseCall':['isSuperExpr','headIdent','libraryRecv','baseRecv'], 'baseCallRevert':['isSuperExpr','headIdent','libraryRecv','baseRecv'], 'baseArgsRevert':['isSuperExpr','headIdent','libraryRecv','baseRecv'],
}
for a in 'push1 push1Revert push1Panic push0 push0Panic pop popPanic externalCall externalCallNoCode externalCallFailed externalCallDecodeFail externalValueRevert externalGasRevert externalArgsRevert externalAbiPanic'.split():
    EXTRA[a]=['specialMemberCall']
for a in 'abiEncode abiEncodePacked abiEncodeWithSelector abiEncodeWithSignature abiDecode abiDecodeFail abiEncodeRevert abiDecodeRevert'.split():
    EXTRA[a]=['isSuperExpr','headIdent','isEnvObj','isAbiFn']
for b in 'requireTrue requireFalse requireMsg requireMsgRevert requireCustom requireCustomArgsRevert requireCustomPanic requireCondRevert assertTrue assertFalse assertRevert revertEmpty revertMsg revertMsgRevert keccak keccakRevert gasleft addmod mulmod modZero modArgsRevert ecrecover ecrecoverFailed ecrecoverAbiPanic ecrecoverArgsRevert'.split():
    EXTRA[b]=EXTRA.get(b,[])+['isBuiltinFn']
KW={'local','while','break','continue','return','for','if','then','else','do','match','fun','let','have','show','from','at','by','in','with','end','open','import','where','instance','structure','class','def','theorem','private','section','namespace','variable','unsafe','partial','try','catch','finally','throw','unless','calc','some','none','skip'}
MANUAL=json.load(open(SP+'manual.json'))
LOOPBODY=set('iterate iterateContinue postRevert postRevertContinue breakOut returnOut bodyRevert'.split())
def offset(fam,name):
    if fam=='ExecLoop' and name in LOOPBODY: return 2
    if fam=='EvalExpr':
        if name in OFF3: return 3
        if name in OFF2: return 2
    return 1
out=[]
for fam,rules in R.items():
    if fam in ('EvalCond','ExecPost'): continue
    lemma,fn,args,conv=FAM[fam]
    out.append(f'theorem {lemma} {{{args} r}} (h : {fam} cfg o fc {args} r) :\n    ∃ n, ∀ k, n ≤ k → ({fn} cfg o fc k {args}).run = some ({conv} r) :=\n  match h with')
    for rule in rules:
        name=rule['name']; kinds=rule['kinds']
        names=[f'p{i+1}' for i in range(len(kinds))]
        key=f'{fam}.{name}'
        lname = f'«{name}»' if name in KW else name
        head=f'  | .{lname}'+(' '+' '.join(names) if names else '')+' => by'
        if key in MANUAL:
            mv=MANUAL[key]
            if isinstance(mv, dict):
                head=f'  | .{lname} {mv["named"]}'+(' '+' '.join(names) if names else '')+' => by'
                out.append(head+'\n'+mv['body'])
            else:
                out.append(head+'\n'+mv)
            continue
        if any(k[0]=='der' and k[1] in ('EvalCond','ExecPost') for k in kinds):
            # nested constructor patterns keep the sub-derivations structural
            off=offset(fam,name)
            alts=[([],[],[])]
            for i,(k,pt) in enumerate(zip(kinds,rule['prem'])):
                if k[0]=='der' and k[1] in ('EvalCond','ExecPost'):
                    opts=[]
                    if '.reverted' in pt:
                        opts.append((f'(.revert hp{i+1})', f'hp{i+1}'))
                    else:
                        opts.append(('.none', None)); opts.append((f'(.some hp{i+1})', f'hp{i+1}'))
                    # the condition runs at fuel k'+1: rewrite it before the unfolding simp set sees it
                    if k[1]=='EvalCond':
                        alts=[(ps+[pat], obs+([f'    obtain ⟨n{i+1}, ih{i+1}⟩ := evalExpr_complete {hv}',
                                               f"    simp only [execLoop, IM.run_bind, toRes, ih{i+1} (k' + 1) (by omega)]"] if hv else []),
                               ihs+([(f'n{i+1}', None)] if hv else []))
                              for (ps,obs,ihs) in alts for (pat,hv) in opts]
                    else:
                        alts=[(ps+[pat], obs+([f'    obtain ⟨n{i+1}, ih{i+1}⟩ := evalExpr_complete {hv}'] if hv else []),
                               ihs+([(f'n{i+1}', f"ih{i+1} k' (by omega)")] if hv else []))
                              for (ps,obs,ihs) in alts for (pat,hv) in opts]
                elif k[0]=='der':
                    alts=[(ps+[f'p{i+1}'], obs+[f'    obtain ⟨n{i+1}, ih{i+1}⟩ := {FAM[k[1]][0]} p{i+1}'],
                           ihs+[(f'n{i+1}', f"ih{i+1} k' (by omega)")]) for (ps,obs,ihs) in alts]
                else:
                    alts=[(ps+[f'p{i+1}'], obs, ihs) for (ps,obs,ihs) in alts]
            for (ps,obs,ihs) in alts:
                pre=[l for l in obs if l.lstrip().startswith('simp only')]
                lines=[f'  | .{lname} '+' '.join(ps)+' => by']+[l for l in obs if l not in pre]
                ns=[n for n,_ in ihs]
                lines.append(f'    refine ⟨{" + ".join(ns+[str(off)])}, fun k hk => ?_⟩')
                lines.append(f"    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := {off}) (by omega)")
                lines+=pre
                facts=[f'p{i+1}' for i,k in enumerate(kinds) if k[0]=='fact']+[ih for _,ih in ihs if ih]
                lines.append('    interp_simp'+(f' [{", ".join(facts)}]' if facts else ''))
                out.append('\n'.join(lines))
            continue
        lines=[]; ns=[]; facts=list(EXTRA.get(name,[]))
        for i,pt in enumerate(rule['prem']):
            if pt.startswith('memberCallDirect fc fr recv = false'):
                lines.append(f'    obtain ⟨hmd1, hmd2, hmd3, hmd4⟩ := memberCallDirect_false p{i+1}')
                facts += ['hmd1','hmd2','hmd3','hmd4']
            if pt.startswith('envMember m obj f = some'):
                lines.append(f'    have hnd := envMember_not_data p{i+1}')
                facts.append('hnd')
            if pt.startswith('(d.returns = [] →'):
                lines.append(f'    have hnc := noCode_false p{i+1}')
                facts.append('hnc')
        for i,k in enumerate(kinds):
            if k[0]=='der':
                lines.append(f'    obtain ⟨n{i+1}, ih{i+1}⟩ := {FAM[k[1]][0]} p{i+1}')
                ns.append(f'n{i+1}')
            elif k[0]=='bridge':
                lines.append(f'    have hb{i+1} := {k[1]}_det p{i+1}')
                facts.append(f'hb{i+1}')
            else:
                facts.append(f'p{i+1}')
        off=offset(fam,name)
        if ns:
            lines.append(f'    refine ⟨{" + ".join(ns)} + {off}, fun k hk => ?_⟩')
            lines.append(f"    obtain ⟨k', rfl⟩ := exists_add (k := k) (c := {off}) (by omega)")
        else:
            lines.append(f'    refine ⟨{off}, fun k hk => ?_⟩')
            lines.append("    obtain ⟨k', rfl⟩ := exists_add hk")
        ihs=[f"ih{i+1} k' (by omega)" for i,k in enumerate(kinds) if k[0]=='der']
        allf=facts+ihs
        lines.append('    interp_simp'+(f' [{", ".join(allf)}]' if allf else ''))
        out.append(head+'\n'+'\n'.join(lines))
    out.append('')
header=open(SP+'complete_header.lean').read()
open('Solidity/Theory/Complete.lean','w').write(header+'\nmutual\n\n'+'\n'.join(out)+'\nend\n\nend Solidity\n')
print('generated')
