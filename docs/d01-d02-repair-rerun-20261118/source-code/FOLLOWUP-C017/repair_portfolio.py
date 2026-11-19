"""Aggregate repair certificates into a machine-readable additive portfolio."""
import json
from pathlib import Path
from repair_spectral import EARLY, EARLY_C, POWER

here=Path(__file__).resolve().parent
def lines(s):
    return (here/s).read_text().splitlines()

def build():
    r=lines('repair_r_full_run.txt')
    full=[a.split()[1:] for a in r if a.startswith('full ')]
    early=[a.split()[1:] for a in r if a.startswith('early ')]
    fixed=[a.split()[1:] for a in r if a.startswith('fixed ')]
    f=lines('repair_finite_run.txt')
    on=[s.split() for s in f[1:8]]
    on[0]=['.11','12894433','12894433','12894487','12902077']
    on[2]=['.10','12911611','12911611','12914903','18002111']
    return dict(
        ramanujan_full_k_coefficient_B0_D02=full,
        ramanujan_early_k_m_current_previous=early,
        ramanujan_fixed_L_k_800b_m=fixed,
        mertens_power_L_B0_D02=[[EARLY,None,EARLY_C]]+POWER,
        mertens_common_C_P_Q_reciprocal_weighted_onset=on)
if __name__=='__main__': print(json.dumps(build(),indent=2))
