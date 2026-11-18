#!/usr/bin/env python3
"""Index explicitly named declarations; compiled Lean is authoritative for names."""
from pathlib import Path
import json, re

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / 'blueprint'
declaration = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected)\s+)*(theorem|lemma|def|abbrev|structure|inductive)\s+([\w.\u0080-\uffff]+)')
def uncomment(s):
    result=[]; i=0; depth=0; line=False; string=False
    while i<len(s):
        if line:
            if s[i]=='\n': line=False; result.append('\n')
            else: result.append(' ')
            i+=1; continue
        if depth:
            if s[i:i+2]=='/-': depth+=1; result.append('  '); i+=2
            elif s[i:i+2]=='-/': depth-=1; result.append('  '); i+=2
            else: result.append('\n' if s[i]=='\n' else ' '); i+=1
            continue
        if string:
            result.append(s[i])
            if s[i]=='\\' and i+1<len(s): result.append(s[i+1]); i+=2; continue
            if s[i]=='"':string=False
            i+=1; continue
        if s[i:i+2]=='/-':depth=1;result.append('  ');i+=2
        elif s[i:i+2]=='--':line=True;result.append('  ');i+=2
        else:
            if s[i]=='"':string=True
            result.append(s[i]);i+=1
    return ''.join(result)

records = {}
for file in sorted((ROOT/'APC').glob('*.lean')):
    lines = file.read_text().splitlines()
    stack, starts = [], []
    for i, line in enumerate(uncomment(file.read_text()).splitlines()):
        match = re.match(r'^\s*namespace\s+([\w.]+)', line)
        if match:
            stack.append(match.group(1))
            continue
        if re.match(r'^\s*(?:noncomputable\s+)?section(?:\s|$)', line):
            stack.append('')
            continue
        if re.match(r'^\s*end(?:\s|$)', line):
            if stack: stack.pop()
            continue
        match = declaration.match(line)
        if match:
            kind, name = match.groups()
            namespace = '.'.join(n for n in stack if n)
            qualified = name if name.startswith('APC.') else namespace+'.'+name
            starts.append((i, qualified, kind))
    for j, (i, name, kind) in enumerate(starts):
        stop = starts[j+1][0] if j+1<len(starts) else len(lines)
        before = '\n'.join(lines[:i])
        doc = ''
        match = re.search(r'/--((?:(?!/-|-/)[\s\S])*)-/\s*$', before)
        if match: doc = re.sub(r'\s+', ' ', match.group(1)).strip()
        records[name] = {'file':str(file.relative_to(ROOT)), 'line':i+1,
                         'kind':kind, 'doc':doc, 'source':'\n'.join(lines[i:stop]).strip()}
(HERE/'source_index.json').write_text(json.dumps(records,ensure_ascii=False,indent=2))
(HERE/'source_names.txt').write_text('\n'.join(sorted(records))+'\n')
print(f'Indexed {len(records)} source declarations.')
