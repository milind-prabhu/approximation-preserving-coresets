#!/usr/bin/env python3
"""Rebuild the offline PFR-inspired FILE IMPORT graph from audited Lean sources.
Requires Python 3 and Graphviz. No third-party Python packages are required.
"""
from pathlib import Path
import re, json, hashlib, subprocess, textwrap, xml.etree.ElementTree as ET

OUT = Path(__file__).resolve().parent
ROOT = OUT.parent
VERIFY = json.loads((ROOT/'verification-summary.json').read_text())
AUDIT = (ROOT/'final-audit.log').read_text()
AUDITED = set(re.findall(r"^'([^'\n]+)' (?:depends on axioms:|does not depend on any axioms)", AUDIT, re.M))
NS = '{http://www.w3.org/2000/svg}'

# Strip Lean comments while preserving lines, for namespace/import/declaration extraction.
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

def declarations(source):
    stack=[]; prefix=[]; results=[]
    for line_no,line in enumerate(uncomment(source).splitlines(),1):
        m=re.match(r'^namespace\s+([\w.]+)',line)
        if m:
            name=m.group(1);stack.append(('namespace',name,prefix.copy()));prefix+=name.split('.');continue
        m=re.match(r'^section(?:\s+(\w+))?\s*$',line)
        if m:stack.append(('section',m.group(1) or '',prefix.copy()));continue
        m=re.match(r'^end(?:\s+([\w.]+))?\s*$',line)
        if m and stack:
            wanted=m.group(1)
            while stack:
                kind,name,previous=stack.pop();prefix=previous
                if not wanted or name==wanted or name.split('.')[-1]==wanted:break
            continue
        m=re.match(r'^(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure)\s+([\w.]+)',line)
        if m:
            kind,name=m.groups()
            results.append({'kind':kind,'name':'.'.join(prefix+[name]),'short':name,'line':line_no,
                            'checked':kind in ('theorem','lemma') and '.'.join(prefix+[name]) in AUDITED})
    return results

GOALS = {
 'APC.EuclideanCubicSize': 'Euclidean approximation + size',
 'APC.MetricSubsetEnumeration': 'Metric APC + subset search',
}
CONDITIONAL = {'APC.TwoStage','APC.EuclideanCompression','APC.SampleCounts',
 'APC.RandomizedCompression','APC.RandomizedCounts','APC.RandomStrongInput'}
modules={}
for path in sorted((ROOT/'APC').glob('*.lean')):
    source=path.read_text(); rel=path.relative_to(ROOT).as_posix(); name='APC.'+path.stem
    digest=hashlib.sha256(path.read_bytes()).hexdigest()
    assert VERIFY['sources'][rel]==digest, f'Source no longer matches audited snapshot: {rel}'
    imports=re.findall(r'^import\s+([\w.]+)',uncomment(source),re.M)
    ds=declarations(source); ts=[d for d in ds if d['kind'] in ('theorem','lemma')]
    assert all(d['checked'] for d in ts), f'Unmapped audit names in {name}: {[d for d in ts if not d["checked"]]}'
    modules[name]={'id':name,'name':path.stem,'path':rel,'source':source,'hash':digest,
      'imports':[i for i in imports if i.startswith('APC.')],
      'externalImports':[i for i in imports if not i.startswith('APC.')],
      'declarations':ds,'theorems':len(ts),'checked':True,'goal':GOALS.get(name),
      'conditional':name in CONDITIONAL}
for row in (ROOT/'FORMALIZATION.md').read_text().splitlines():
    if row.startswith('|') and row.count('|')>=3:
        fields=row.split('|')
        for stem in re.findall(r'`(\w+)`',fields[2]):
            if 'APC.'+stem in modules: modules['APC.'+stem]['description']=fields[1].strip()

assert len(modules)==VERIFY['source_module_count']==72
assert sum(m['theorems'] for m in modules.values())==VERIFY['theorem_count']==367
all_imports={(imp,name) for name,m in modules.items() for imp in m['imports']}
assert all(a in modules and b in modules for a,b in all_imports)

cache={}
def ancestors(n,trail=()):
    assert n not in trail, f'Import cycle: {trail+(n,)}'
    if n not in cache:
        cache[n]=set().union(*({a}|ancestors(a,trail+(n,)) for a in modules[n]['imports'])) if modules[n]['imports'] else set()
    return cache[n]
for n in modules:ancestors(n)
reduced={(a,b) for a,b in all_imports if not any(a in ancestors(c) for c in modules[b]['imports'] if c!=a)}

def label(name):
    stem=modules[name]['name']; words=re.findall(r'[A-Z]+(?=[A-Z][a-z]|$)|[A-Z]?[a-z]+|\d+',stem)
    lines=[];line=''
    for w in words:
        if len(line+w)>23 and line:lines.append(line);line=w
        else:line+=w
    if line:lines.append(line)
    return '\\n'.join(lines)+f"\\n{modules[name]['theorems']} checked theorem"+('s' if modules[name]['theorems']!=1 else '')

def dot_for(selected,edges,caption=False):
    title='Approximation Preserving Coresets — file dependencies'
    lines=['digraph APC {','graph [rankdir=TB, bgcolor="transparent", pad="0.28", nodesep="0.23", ranksep="0.42", splines=true, outputorder=edgesfirst];',
      'node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=12, margin="0.12,0.08", fillcolor="#b9e8c7", color="#24844d", fontcolor="#132c1d", penwidth=1.3];',
      'edge [color="#6d8878", arrowsize=0.55, penwidth=0.9];']
    if caption:
        lines+=['graph [bgcolor="white", fontname="Helvetica", fontsize=15, labelloc="t", label='+json.dumps(title+'\n72 checked proof files · 367 theorems\nArrow: imported prerequisite → dependent file · transitive reduction\nImports are an over-approximation of theorem-proof dependencies.\nGreen: checked file | Dark green: main-result file.',ensure_ascii=False)+'];']
    for n in sorted(selected):
        goal=modules[n]['goal']
        attrs=f'label="{label(n)}", id="{n}"'
        if goal:attrs+=', fillcolor="#277b4b", color="#165a32", fontcolor="white", penwidth=2.5, peripheries=2'
        lines.append(f'{json.dumps(n)} [{attrs}];')
    for a,b in sorted(edges):
        if a in selected and b in selected:lines.append(f'{json.dumps(a)} -> {json.dumps(b)};')
    lines.append('}')
    return '\n'.join(lines)+'\n'

views={'all':{'label':'All proof files','nodes':set(modules),'target':'APC.EuclideanCubicSize'},
 'euclidean':{'label':'Euclidean main results','nodes':ancestors('APC.EuclideanCubicSize')|{'APC.EuclideanCubicSize'},'target':'APC.EuclideanCubicSize'},
 'metric':{'label':'Metric main result','nodes':ancestors('APC.MetricSubsetEnumeration')|{'APC.MetricSubsetEnumeration'},'target':'APC.MetricSubsetEnumeration'},
 'original':{'label':'Original two-stage route','nodes':ancestors('APC.RandomizedCounts')|{'APC.RandomizedCounts'},'target':'APC.RandomizedCounts'}}
svgs={}; dots={}
for key,v in views.items():
    svgs[key]={}; dots[key]={}
    for mode,edges in [('reduced',reduced),('direct',all_imports)]:
        dot=dot_for(v['nodes'],edges);dots[key][mode]=dot
        svg=subprocess.run(['dot','-Tsvg'],input=dot,text=True,capture_output=True,check=True).stdout
        root=ET.fromstring(svg)
        for group in root.findall('.//'+NS+'g'):
            if group.attrib.get('class')=='node':
                name=group.find(NS+'title').text
                group.set('data-module',name);group.set('tabindex','0');group.set('role','button')
                group.set('aria-label',modules[name]['path']+'; '+str(modules[name]['theorems'])+' checked theorems')
            if group.attrib.get('class')=='edge':
                edge=group.find(NS+'title').text
                a,b=edge.split('->');group.set('data-from',a);group.set('data-to',b)
        ET.register_namespace('', 'http://www.w3.org/2000/svg')
        svgs[key][mode]=ET.tostring(root,encoding='unicode')

full_dot=dot_for(set(modules),reduced,caption=True)
(OUT/'apc-file-dependencies.dot').write_text(full_dot)
for fmt in ['svg','pdf','png']:
    args=['dot',f'-T{fmt}','-o',str(OUT/f'apc-file-dependencies.{fmt}')]
    if fmt=='png':args+=['-Gdpi=110']
    subprocess.run(args,input=full_dot,text=True,check=True)

data={'title':'Approximation Preserving Coresets','kind':'file_import_graph','modules':modules,
 'edges':[list(e) for e in sorted(all_imports)],'reducedEdges':[list(e) for e in sorted(reduced)],
 'viewInfo':{k:{'label':v['label'],'nodes':sorted(v['nodes']),'target':v['target']} for k,v in views.items()},
 'verification':{'files':len(modules),'theorems':367,'allSourceHashesMatch':True,
  'allowedAxioms':VERIFY['audit_allowed_axioms'],'sourceHashAlgorithm':'sha256'},
 'excludedFiles':['APC.lean (aggregate entry point)','Audit.lean (audit driver)','Check.lean (scratch checker)'],
 'scope':'Arrows show direct file imports, not kernel-level theorem dependencies. A checked conditional theorem is not an unconditional mathematical claim.',
 'references':[{'title':'PFR blueprint dependency graph','url':'https://teorth.github.io/pfr/blueprint/dep_graph_document.html'},
 {'title':'Terence Tao: Formalizing PFR using Blueprint','url':'https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/'}]}
(OUT/'dependency-data.json').write_text(json.dumps(data,indent=2)+'\n')
payload={'data':data,'svgs':svgs,'dots':dots}
template=(OUT/'template.html').read_text()
html=template.replace('/*__PAYLOAD__*/',json.dumps(payload,ensure_ascii=False).replace('<','\\u003c'))
(OUT/'apc-dependency-graph.html').write_text(html)
print(json.dumps({'files':len(modules),'theorems':367,'imports':len(all_imports),'reducedImports':len(reduced),
 'htmlBytes':len(html.encode()),'views':{k:len(v['nodes']) for k,v in views.items()}}))
