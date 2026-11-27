"""Generate compact binary constants and independent local arithmetic certificates."""
from fractions import Fraction
from pathlib import Path
from hashlib import sha256
from math import comb
import json
from flint import fmpz,fmpz_poly
N=16384
S=256
B=fmpz(1)<<50000

def pack(v,x):
    while len(v)>1:
        v=[v[i]+x*v[i+1] if i+1<len(v) and v[i+1] else v[i] for i in range(0,len(v),2)]
        if len(v)>1:x*=x
    return v[0]

def write(destination,i,name,values):
    with (destination/f'{i:02}-{name}.bin').open('wb') as f:
        for v in values:
            v=int(v); blob=v.to_bytes((v.bit_length()+8)//8,'little',signed=True)
            f.write(len(blob).to_bytes(4,'little'))
            f.write(blob)

def build(candidate: Path, destination: Path):
    raw = candidate.read_bytes()
    if sha256(raw).hexdigest() != 'ae71adf610b66f2742021b8abcb7fb0156d79936db44b727eee18fe4891213a8':
        raise ValueError("candidate bytes do not match the certificate input")
    destination.mkdir(parents=True)
    scaled=[Fraction(t)*2**90 for t in json.loads(raw)['coefficients']]
    assert len(scaled)==8193 and all(x.denominator==1 for x in scaled)
    w=[x.numerator for x in scaled]
    f=[];c=fmpz(1)
    for j in range(N+1):
        f.append((w[j//2]*c)<<(2*(N-j)) if j%2==0 else fmpz(0))
        c=c*(4*j+2)//(j+1)
    gpoly=fmpz_poly(f)(fmpz_poly([1,1]))
    f.append(fmpz(0))
    den=fmpz(1)<<(2*N+90)
    for i in range(65):
        j=i*S
        g=[gpoly[h] for h in range(j,min(j+S,N+2))]
        q=[]
        seed=den
        for h,y in enumerate(g,j):
            q.append(((-y if h%2 else y)<<(100+17*h))//den)
            den*=2*h+1
        src=f[j:j+len(g)]
        # Global bound via the actual contributions to the domain and codomain norms.
        for name,values in [('g',g),('q',q),('s',[pack(src,1+B)]),('v',[pack(g,B)]),
            ('u',[pack(list(map(abs,src)),2)]),('w',[sum(map(abs,g))]),('den',[seed]),('end',[den])]:
            write(destination,i,name,values)
        print('emitted',i,flush=True)

        write(destination, i, 'seed', [comb(512*i, 256*i)])
