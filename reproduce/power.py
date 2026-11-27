"""Exact binomial reconstruction of the compact lower power coefficients."""
from math import lcm
from flint import fmpz, fmpz_poly


def shift_one(a):
    p = fmpz_poly(a)(fmpz_poly([1,1]))
    return [p[j] for j in range(len(a))]

def prepare(modes,radius,bits):
    n=2*(len(modes)-1)
    common=lcm(*(a.denominator for a in modes))
    f=[fmpz(0)]*(n+1)
    choose=fmpz(1)
    for j in range(n+1):
        if j%2==0:
            a=modes[j//2]
            f[j]=choose*(a.numerator*(common//a.denominator)) << (2*(n-j))
        choose=choose*(4*j+2)//(j+1)
    # F(z) = 4^N D sum a_n binom(2n,n) 4^-n z^n.
    v=shift_one(f)
    del f
    # [t^j]P = (-4)^j j!/(2j)! * [z^j]F(1+z)/(4^N D).
    # q(z)/2^bits <= P(Rz) on [0,1], by coefficientwise flooring.
    base=(fmpz(1) << (2*n))*common
    den=base
    powr=fmpz(1)<<bits
    for j in range(n+1):
        v[j]=(powr*v[j])//den
        powr*= -2*radius
        den*=2*j+1
    return v

