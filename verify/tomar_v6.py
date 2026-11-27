"""Attributed numerical input for comparison with the Tomar v6 witness.

The radius interval is an independently computed Arb enclosure of the final
root of Tejasvi Singh Tomar's publicly released Gaussian witness. The public
certificate gives the published radius 5509/10000. The tighter enclosure is
supplied as input here. Recomputing it requires the separate Tomar witness
and its rigorous tail and root checks.
"""

SOURCE_URL = (
    "https://github.com/tejasvi/sign-uncertainty-constant/blob/v6/"
    "certs/pcert_r05509_NR2.json"
)
CERTIFICATE_FILENAME = "pcert_r05509_NR2.json"
CERTIFICATE_SHA256 = "ccf9e2d5a709072f411c0e48f16f4fe93793dfe627260a02ce88545f2b6649c4"
RADIUS_BRACKET = (
    "101623087556280535787126849/184467440737095516160000000",
    "2032461751125610715742537/3689348814741910323200000",
)
SCORE_BRACKET = (
    "10327251924471459878851645007538640968737106416668801/34028236692093846346337460743176821145600000000000000",
    "4130900769788583951540658084313926432519271196369/13611294676837538538534984297270728458240000000000",
)
PUBLISHED_RADIUS = "5509/10000"
PUBLISHED_SCORE = "30349081/100000000"
