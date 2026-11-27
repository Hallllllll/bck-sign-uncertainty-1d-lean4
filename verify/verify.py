"""Monic Laguerre recurrence bound for the exterior ray."""
import math

# Adapted from the BCK production whole-ray verifier.
# Original source SHA-256: e48e7c47e22ce80440b81c5f986a8693b75b67e69aa637323953dc7bd05d7e2f


def exterior(w,degree):
    # The monic functions M_n=(-1)^n n! L_n obey
    # M_(n+1)=(t-2n-1/2) M_n-n(n-1/2) M_(n-1).
    # For t>=4D and n<D, all ratios M_(n+1)/M_n >= D by induction.
    last=max(j for j,v in enumerate(w) if v<0)*2
    # For j<=last, L_j/L_D <= prod_(k=j+1..D) k/D <= bound_at_last for even j.
    den=degree**(degree-last)
    num=math.prod(range(last+1,degree+1))
    total=sum(-v for v in w if v<0)
    if not w[-1]*den>total*num:raise ArithmeticError('exterior dominance fails')
    return last
