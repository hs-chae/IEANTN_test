#!/usr/bin/env python3
"""Publication figure of proved width formulas; never interpreted as prime data."""
import argparse
import csv
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--render-package", type=Path)
    args = parser.parse_args()
    if args.render_package:
        sys.path.insert(0, str(args.render_package.resolve()))
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    here = Path(__file__).resolve().parent
    q = Fraction(82325773717, 98718416336)
    intercept, slope = Fraction(163827, 160000), Fraction(9, 8)
    cross = (intercept-q)/(2*q-slope)
    alpha = [Fraction(k, 1000) for k in range(1001)]
    gaussian = [q*(1+2*a) for a in alpha]
    octic = [max(Fraction(103, 100), intercept+slope*a) for a in alpha]
    plt.rcParams.update({"svg.fonttype": "path", "svg.hashsalt": "IEANTN-RH080-20261125",
                         "font.family": "DejaVu Sans", "font.size": 11})
    fig, ax = plt.subplots(figsize=(8.3, 4.6), constrained_layout=True)
    ax.plot(list(map(float,alpha)),list(map(float,gaussian)),color="#174f91",label="New Gaussian: eventual width limit; positive slack needed",lw=2.3)
    ax.plot(list(map(float,alpha)),list(map(float,octic)),color="#177b59",label="Preserved octic: explicit width valid above exp(24)",lw=2.3)
    ax.axvline(float(cross),color="#697386",ls="--",lw=1)
    ax.text(float(cross)+.015, .91, "Equal limiting widths near α = %.5f"%float(cross),fontsize=9)
    ax.set(xlabel="Population target α: more than α √x primes",ylabel="Sufficient interval coefficient C in C √x log x",xlim=(0,1),ylim=(.78,2.6))
    ax.grid(alpha=.22);ax.spines[["top","right"]].set_visible(False);ax.legend(loc="upper left",fontsize=9)
    fig.savefig(here/"POPULATION_FRONTIER.svg",metadata={"Date":None})
    fig.savefig(here/"POPULATION_FRONTIER.pdf",metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)
    with (here/"POPULATION_FRONTIER.csv").open("w",newline="") as stream:
        writer=csv.writer(stream);writer.writerow(["alpha_exact","Gaussian_limiting_width_exact","Octic_explicit_width_exact"])
        writer.writerows(zip(map(str,alpha),map(str,gaussian),map(str,octic)))
    pin={"status":"DERIVED_FORMULA_FIGURE_NOT_NEW_ANT_PROOF","matplotlib":matplotlib.__version__,
         "q_exact":str(q),"crossing_exact":str(cross),"crossing_approx":float(cross),
         "domain":"alpha0..1; Gaussianeventualwithpositiveepsilon, Octicexplicitx>=exp24, differentdeclaredformalinputpackages",
         "formula_scalar_Lean":"PopulationComparison.lean","compiler_receipt":"Separatekernelreceipt",
         "files":{name:hashlib.sha256((here/name).read_bytes()).hexdigest() for name in ["POPULATION_FRONTIER.svg","POPULATION_FRONTIER.pdf","POPULATION_FRONTIER.csv"]}}
    (here/"POPULATION_FIGURE.json").write_text(json.dumps(pin,indent=2)+"\n")
    print(json.dumps({"status":pin["status"],"crossing":float(cross)}))


if __name__=="__main__":main()
