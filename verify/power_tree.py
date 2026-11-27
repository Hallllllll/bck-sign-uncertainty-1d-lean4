"""Exact compact-interval proof using localized, outward-rounded lower polynomials."""
from flint import fmpz

from descartes import shift_one

# Adapted from the BCK production power-tree verifier.
# Original source SHA-256: 0fa0a3f8786e0394c359d3a5db23b7c849b9b4f9919b88f2dea9a4bd4efe9d76


def reduce_degree(v,precision=110):
    # Uniformly rescale so an absolute rounding loss of O(degree) is tiny at
    # the left endpoint. The lower-polynomial implication is unconditional.
    shift=max(0,v[0].bit_length()-precision) if v[0]>0 else 0
    if shift:
        v=[y>>shift for y in v]
    stop=len(v)
    err=fmpz(0)
    lost=fmpz(0)
    tol=max(128,(v[0]>>48) if v[0]>0 else 0)
    while stop>1:
        low=min(0,v[stop-1])
        lost+=abs(v[stop-1])
        if lost>tol:break
        err+=low
        stop-=1
    v=v[:stop]
    v[0]+=err
    return v


def right_half(v):
    n=len(v)-1
    exact=[y<<(n-j) for j,y in enumerate(v)]
    return [y>>n for y in shift_one(exact)]


def low(v):
    a=fmpz(0)
    for x in reversed(v):
        a=x+min(0,a)
    return a


def visit(v, a, b, path, args, report):
    # Normalize at each node. Parent receives no information from children.
    v=reduce_degree(v)
    l=low(v)
    if l>=0:
        report('proved',left=str(a),right=str(b),path=path,degree=len(v)-1)
        return
    if b<=args.omit_below:
        report('covered_by_prefix',right=str(b),path=path);return
    if len(path)>=args.max_depth:
        raise ValueError(f'unclosed leaf [{a}, {b}]')
    report('split',path=path,degree=len(v)-1,left=str(a),right=str(b),negative=sum(y<0 for y in v))
    h=[y>>j for j,y in enumerate(v)]
    # WARNING: reduction for a right child must occur AFTER shift_one, since
    # the input h then gets evaluated on [1,2], outside the unit interval.
    m=(a+b)/2
    for side in ([1,0] if args.right else [0,1]):
        if side:
            if b>args.omit_below:visit(right_half(v),m,b,path+'1',args,report)
        elif m>args.omit_below:
            visit(h,a,m,path+'0',args,report)
