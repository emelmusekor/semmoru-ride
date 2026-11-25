# OSM(osm.json) -> mapdata.js  (x=동쪽 m, z=남쪽 m, 원점=샘모루초)
import json, math, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
d = json.load(open(os.path.join(HERE, 'osm.json'), encoding='utf-8'))
LAT0, LON0 = 37.3999, 126.9409
R = 640  # 이 밖은 버림
KX = 111320 * math.cos(math.radians(LAT0)); KZ = 110540
N = {e['id']: e for e in d['elements'] if e['type'] == 'node'}
W = {e['id']: e for e in d['elements'] if e['type'] == 'way'}

def xy(nid):
    n = N[nid]; return ((n['lon'] - LON0) * KX, -(n['lat'] - LAT0) * KZ)

def pts(way):
    return [xy(n) for n in way['nodes'] if n in N]

def flat(p):
    out = []
    for x, z in p: out += [round(x, 1), round(z, 1)]
    return out

def inside(p, r=R):
    return any(abs(x) < r and abs(z) < r for x, z in p)

def area(p):
    s = 0
    for i in range(len(p)):
        x1, z1 = p[i]; x2, z2 = p[(i + 1) % len(p)]; s += x1 * z2 - x2 * z1
    return s / 2

def ring(p):
    if len(p) > 1 and p[0] == p[-1]: p = p[:-1]
    return p

def stitch(ways):
    segs = [list(w['nodes']) for w in ways]; rings = []
    while segs:
        cur = segs.pop(0)
        changed = True
        while cur[0] != cur[-1] and changed:
            changed = False
            for i, s in enumerate(segs):
                if s[0] == cur[-1]: cur += s[1:]
                elif s[-1] == cur[-1]: cur += s[::-1][1:]
                elif s[-1] == cur[0]: cur = s[:-1] + cur
                elif s[0] == cur[0]: cur = s[::-1][:-1] + cur
                else: continue
                segs.pop(i); changed = True; break
        if cur[0] == cur[-1]: rings.append([xy(n) for n in cur if n in N])
    return rings

def num(v, dflt=None):
    try: return float(str(v).split(';')[0].replace('m', '').strip())
    except: return dflt

B, RD, AR, WT, ND = [], [], [], [], []
DEF_LV = {'apartments': 15, 'school': 4, 'commercial': 4, 'retail': 2, 'church': 3, 'hospital': 6,
          'residential': 4, 'house': 2, 'yes': 3}

def add_building(t, p, nm=None):
    p = ring(p)
    if len(p) < 3 or not inside(p, 560): return
    if area(p) > 0: p = p[::-1]  # 화면 기준 반시계로 통일
    bt = t.get('building', 'yes')
    lv = num(t.get('building:levels'))
    h = num(t.get('height'))
    if h is None: h = (lv if lv else DEF_LV.get(bt, 3)) * (2.9 if bt == 'apartments' else 3.4) + 1
    if lv is None: lv = max(1, round(h / 2.9))
    nm = t.get('name', nm or '')
    B.append([nm, bt, round(h, 1), int(lv), flat(p)])

ROADW = {'primary': 24, 'primary_link': 8, 'secondary': 16, 'tertiary': 12, 'tertiary_link': 7,
         'residential': 7, 'service': 5, 'unclassified': 6, 'living_street': 5,
         'footway': 3, 'pedestrian': 5, 'cycleway': 3, 'path': 2.2, 'steps': 2.5, 'track': 3}
for w in W.values():
    t = w.get('tags', {}); p = pts(w)
    if len(p) < 2: continue
    if 'building' in t:
        add_building(t, p); continue
    hw = t.get('highway')
    if hw in ROADW and inside(p):
        wd = num(t.get('width')) or ROADW[hw]
        ln = num(t.get('lanes'))
        if hw == 'primary' and t.get('name') == '관악대로': wd = 34 if not t.get('oneway') == 'yes' else 17
        elif ln and hw not in ('footway', 'path', 'steps', 'cycleway'): wd = max(wd, ln * 3.3)
        if t.get('oneway') == 'yes' and hw == 'primary' and wd > 18: wd = 15
        RD.append([hw, t.get('name', ''), round(wd, 1), 1 if t.get('tunnel') or t.get('layer', '0').startswith('-') else 0,
                   1 if t.get('bridge') else 0, flat(p), 1 if t.get('oneway') == 'yes' else 0])
        continue
    if 'waterway' in t and inside(p):
        WT.append(['line', t.get('name', ''), 22 if t.get('name') == '학의천' else 12, flat(p)]); continue
    kind = None
    if t.get('leisure') in ('park', 'garden'): kind = 'park'
    elif t.get('leisure') == 'pitch': kind = 'pitch'
    elif t.get('leisure') == 'playground': kind = 'playground'
    elif t.get('leisure') == 'sports_centre': kind = 'sports'
    elif t.get('natural') in ('wood', 'scrub') or t.get('landuse') in ('forest',): kind = 'wood'
    elif t.get('natural') == 'water': kind = 'water'
    elif t.get('landuse') in ('residential',): kind = 'res'
    elif t.get('landuse') in ('construction',): kind = 'constr'
    elif t.get('landuse') in ('cemetery', 'grass', 'meadow'): kind = 'grass'
    elif t.get('amenity') in ('school', 'kindergarten'): kind = 'school'
    elif t.get('amenity') == 'parking': kind = 'parking'
    elif t.get('landuse') in ('commercial', 'retail'): kind = 'comm'
    if kind and len(p) >= 4 and p[0] == p[-1] or (kind and w['nodes'][0] == w['nodes'][-1]):
        p = ring(p)
        if inside(p): AR.append([kind, t.get('name', ''), flat(p)])

for e in d['elements']:
    if e['type'] != 'relation': continue
    t = e.get('tags', {})
    outers = [W[m['ref']] for m in e.get('members', []) if m['type'] == 'way' and m.get('role') in ('outer', '') and m['ref'] in W]
    for rg in stitch(outers):
        if 'building' in t: add_building(t, rg)
        elif t.get('natural') == 'water' and inside(rg): AR.append(['water', t.get('name', ''), flat(ring(rg))])

for n in N.values():
    t = n.get('tags')
    if not t: continue
    x, z = xy(n['id'])
    if abs(x) > R or abs(z) > R: continue
    k = None
    if t.get('highway') == 'bus_stop' or t.get('public_transport') == 'platform': k = 'bus'
    elif t.get('highway') == 'crossing': k = 'cross'
    elif t.get('highway') == 'traffic_signals': k = 'signal'
    elif t.get('shop'): k = 'shop'
    elif t.get('amenity') in ('restaurant', 'cafe', 'fast_food', 'clinic', 'dentist', 'pharmacy', 'veterinary', 'fuel', 'bank', 'kindergarten', 'place_of_worship', 'library', 'police'): k = 'poi'
    elif t.get('amenity') == 'bench': k = 'bench'
    if k: ND.append([k, t.get('name', ''), round(x, 1), round(z, 1)])

# 버스 정류장 같은 이름 중복 정리
seen = set(); ND2 = []
for k, nm, x, z in ND:
    key = (k, nm, round(x / 8), round(z / 8))
    if key in seen: continue
    seen.add(key); ND2.append([k, nm, x, z])

out = {'origin': [LAT0, LON0], 'buildings': B, 'roads': RD, 'areas': AR, 'water': WT, 'nodes': ND2}
js = '/* 지도 자료 © OpenStreetMap contributors (ODbL) — tools/build_map.py 로 생성 */\nwindow.MAP=' + json.dumps(out, ensure_ascii=False, separators=(',', ':')) + ';\n'
open(os.path.join(HERE, '..', 'mapdata.js'), 'w', encoding='utf-8').write(js)
print('buildings', len(B), 'roads', len(RD), 'areas', len(AR), 'water', len(WT), 'nodes', len(ND2), 'bytes', len(js.encode()))
from collections import Counter
print(Counter(a[0] for a in AR)); print(Counter(r[0] for r in RD)); print(Counter(n[0] for n in ND2))
print([ (r[1],r[2]) for r in RD if r[0] in('primary','tertiary') and r[1]])
print([w[:3] for w in WT])

# ---- 교차로(차도끼리 만나는 점) : 횡단보도·신호등 놓을 자리
CAR = ('primary', 'primary_link', 'secondary', 'tertiary', 'tertiary_link', 'residential', 'unclassified')
use = {}
for w in W.values():
    t = w.get('tags', {}); hw = t.get('highway')
    if hw not in CAR or t.get('tunnel'): continue
    ns = [n for n in w['nodes'] if n in N]
    for i, n in enumerate(ns):
        for j in (i - 1, i + 1):
            if 0 <= j < len(ns):
                a = xy(n); b = xy(ns[j]); L = math.hypot(b[0] - a[0], b[1] - a[1]) or 1
                wd = [r for r in RD if r[0] == hw]
                use.setdefault(n, []).append([round((b[0] - a[0]) / L, 3), round((b[1] - a[1]) / L, 3), hw, w['id']])
JN = []
for n, arms in use.items():
    if len(set(a[3] for a in arms)) < 2 and len(arms) < 3: continue
    x, z = xy(n)
    if abs(x) > 560 or abs(z) > 560: continue
    JN.append([round(x, 1), round(z, 1), [[a[0], a[1], a[2]] for a in arms]])
out['junctions'] = JN
js = '/* 지도 자료 © OpenStreetMap contributors (ODbL) — tools/build_map.py 로 생성 */\nwindow.MAP=' + json.dumps(out, ensure_ascii=False, separators=(',', ':')) + ';\n'
open(os.path.join(HERE, '..', 'mapdata.js'), 'w', encoding='utf-8').write(js)
print('junctions', len(JN))
for wt in WT: print(wt[1], wt[3][:2], wt[3][-2:], len(wt[3]))
for a in AR:
    if a[0] in ('water','wood','park','school','pitch','playground','sports'): 
        xs=a[2][0::2]; zs=a[2][1::2]; print(a[0], a[1], round(min(xs)),round(max(xs)),round(min(zs)),round(max(zs)))
