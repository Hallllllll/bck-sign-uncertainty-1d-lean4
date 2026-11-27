"""Independent conversion from rational Laguerre modes to a lower power polynomial."""
from math import lcm

from flint import fmpz, fmpz_poly

# Adapted from the BCK integer power-vector preparation code.
# Original source SHA-256: 7dc5a6c6cb04a3e758b913b4dba3862cf59cd2db87aa4e9e382b8d284117e187


def shift_one(a):
    p = fmpz_poly(a)(fmpz_poly([1,1]))
    return [p[j] for j in range(len(a))]


def prepare(modes, radius, bits, report):
    n=2*(len(modes)-1)
    common=lcm(*(a.denominator for a in modes))
    f=[fmpz(0)]*(n+1)
    choose=fmpz(1)
    for j in range(n+1):
        if j%2==0:
            a=modes[j//2]
            f[j]=choose*(a.numerator*(common//a.denominator)) << (2*(n-j))
        choose=choose*(4*j+2)//(j+1)
    report('assembled_shift',degree=n)
    # F(z) = 4^N D sum a_n binom(2n,n) 4^-n z^n.
    v=shift_one(f)
    del f
    report('shifted_modes')
    # [t^j]P = (-4)^j j!/(2j)! * [z^j]F(1+z)/(4^N D).
    # q(z)/2^bits <= P(Rz) on [0,1], by coefficientwise flooring.
    base=(fmpz(1) << (2*n))*common
    den=base
    powr=fmpz(1)<<bits
    for j in range(n+1):
        v[j]=(powr*v[j])//den
        powr*= -2*radius
        den*=2*j+1
    report('power_lower',maxbits=max(vv.bit_length() for vv in v))
    return v
