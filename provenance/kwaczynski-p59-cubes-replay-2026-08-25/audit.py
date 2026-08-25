import json,glob,os,collections
S=os.path.dirname(os.path.abspath(__file__)); BASE='fa985c9d2c2cf1aaa72b0418e83f22e8c1ef10f6376bd6e29b6fdeb93af093ac'
def rows(f):
    out=[]
    for l in open(f):
        l=l.strip()
        if l: out.append(json.loads(l))
    return out
master=[r['cube_id'] if 'cube_id' in r else r.get('id') for r in rows(f'{S}/master.jsonl')]
M=set(master); print('master',len(master),'unique',len(M))
cert={}  # cube_id -> set of chains
bad=collections.Counter(); foreign=set(); rowsn={}
for f in sorted(glob.glob(f'{S}/*.jsonl')):
    name=os.path.basename(f)
    if name=='master.jsonl': continue
    R=rows(f); rowsn[name]=len(R)
    for r in R:
        if 'parent_certified' in r:
            cid=r.get('parent_id') or r.get('parent_cube_id') or r.get('cube_id')
            ok = r.get('parent_certified') is True and r.get('children_all_certified') is True and r.get('cover_certified') is True
            chain='split-cover'
        elif '.split-' in str(r.get('cube_id','')):
            continue  # child row; counted through its parent row
        else:
            cid=r.get('cube_id')
            if r.get('base_cnf_sha256')!=BASE: bad[(name,'basehash')]+=1; continue
            if r.get('solver_returncode')!=20: bad[(name,'solver')]+=1; continue
            if r.get('lrat_source')=='native':
                ok = r.get('cake_lpr_verified') is True; chain='cadical-nativeLRAT-cake_lpr'
            else:
                ok = r.get('drat_trim_verified') is True and r.get('cake_lpr_verified') is True; chain='kissat-drat_trim-cake_lpr'
        if not ok: bad[(name,chain)]+=1; continue
        if cid not in M: foreign.add((name,cid)); continue
        cert.setdefault(cid,set()).add(chain)
print('rows per ledger',rowsn)
print('uncertified rows by (ledger,chain):',dict(bad))
print('foreign ids:',len(foreign))
by=collections.Counter()
for cid,ch in cert.items(): by[tuple(sorted(ch))]+=1
print('certified unique:',len(cert),'/',len(M)); print('by chain combination:',dict(by))
short=sorted(M-set(cert)); print('shortfall',len(short),short[:40])
