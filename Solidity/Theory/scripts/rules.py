import re, json, os
SP=os.path.dirname(os.path.abspath(__file__))+'/'
src=open('Solidity/Semantics/Exec.lean').read()
start=src.index('inductive EvalExpr'); end_=src.index('\nend\n', start)
block=src[start:end_]
# split into families
fams=re.split(r'\n(?=(?:/--[^\n]*-/\n)?inductive )', block)
families={}
for f in fams:
    m=re.search(r'inductive (\w+)', f)
    if not m: continue
    name=m.group(1)
    body=f[f.index('where')+5:]
    # rules: lines starting with "  | name :"
    rules=[]
    cur=None
    for line in body.split('\n'):
        mm=re.match(r'  \| ([A-Za-z0-9_\']+) :(.*)$', line)
        if mm:
            if cur: rules.append(cur)
            cur=[mm.group(1), mm.group(2).strip()]
        elif cur is not None and line.startswith('      '):
            cur[1]+=' '+line.strip()
        elif cur is not None and line.strip()=='' :
            pass
    if cur: rules.append(cur)
    families[name]=rules
def split_arrows(t):
    parts=[]; depth=0; cur=''
    i=0
    while i < len(t):
        ch=t[i]
        if ch in '([{⟨': depth+=1
        if ch in ')]}⟩': depth-=1
        if t.startswith('→', i) and depth==0:
            parts.append(cur.strip()); cur=''; i+=1; continue
        cur+=ch; i+=1
    parts.append(cur.strip())
    return parts
FAMS=list(families.keys())
out={}
for fam, rules in families.items():
    lst=[]
    for name, text in rules:
        parts=split_arrows(text)
        prem=parts[:-1]; concl=parts[-1]
        kinds=[]
        for p in prem:
            head=p.split(' ')[0].strip('(')
            if head in FAMS: kinds.append(('der', head))
            elif head in ('callViaEVM','delegateCallViaEVM','newViaEVM'): kinds.append(('bridge', head))
            else: kinds.append(('eq', None))
        lst.append({'name':name,'prem':prem,'kinds':kinds,'concl':concl})
    out[fam]=lst
json.dump(out, open(SP+'rules.json','w'), indent=1)
for fam in out: print(fam, len(out[fam]))
