"""Evaluate the sign of the rational even-Laguerre witness using integers."""
import math

from flint import fmpz

# Adapted from the BCK forward integer sign checker.
# Original source SHA-256: 9aa5edc4ca9d5395824889bd37b68e96907faa366693f1972443fcbab5dfe882


def sign_at(coeff,x):
    D=math.lcm(*(u.denominator for u in coeff))
    w=[fmpz(int(u*D)) for u in coeff]
    y,q=x.numerator,x.denominator
    prev=fmpz(0);cur=fmpz(1);v=w[0]
    for n in range(len(w)*2-2):
        prev,cur=cur,((4*n+1)*q-2*y)*cur-(2*n)*(2*n-1)*q*q*prev
        v*=2*(n+1)*q
        if n%2==1: v+=w[(n+1)//2]*cur
    return int(v>0)-int(v<0),int(int(v).bit_length())
