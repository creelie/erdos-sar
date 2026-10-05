"""Draw the two raster figures of the paper.

  paper/figures/boxes.png      the cover of the parameter region by the boxes of Section 8
  paper/figures/densities.png  certified bounds beta(theta) against empirical proportions

The boxes come from verification/open_case/boxes.json, the certified values from
ErdosSar/Certs.lean (through code/tables.py), and the empirical proportions from
code/data/rho_density.csv, written by code/rho_density.c.

Run from the repository root:  python3 code/figures.py
"""
import csv
import json
import os
from fractions import Fraction as Fr

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FIG = os.path.join(ROOT, 'paper', 'figures')
plt.rcParams.update({'font.family': 'serif', 'mathtext.fontset': 'cm', 'font.size': 10,
                     'axes.linewidth': 0.6})

B = json.load(open(os.path.join(ROOT, 'verification', 'open_case', 'boxes.json')))

# ---- the boxes
fig, (ax, bx) = plt.subplots(1, 2, figsize=(7.2, 3.1), gridspec_kw={'width_ratios': [3.2, 1]})
for b in B['GP']:
    d0, d1, a0, a1 = (float(Fr(b[k])) for k in ('d0', 'd1', 'a0', 'a1'))
    mode_one = b['mode'] == 'Q1'
    ax.add_patch(Rectangle((d0, a0), d1 - d0, a1 - a0, facecolor='#d9e6f2' if mode_one else '#7fa7cc',
                           edgecolor='#1f3b57', linewidth=0.5))
xs = [3 / 70, 27 / 50]
ax.plot(xs, [9 / 50 - x / 3 for x in xs], color='#8c2d04', linewidth=1.0)
ax.annotate(r'$a = \frac{9}{50} - \frac{\delta}{3}$', xy=(0.33, 9 / 50 - 0.33 / 3), xytext=(0.36, 0.125), color='#8c2d04', arrowprops=dict(arrowstyle='-', color='#8c2d04', lw=0.6))
ax.set_xlim(0, 0.56)
ax.set_ylim(0, 0.2)
ax.set_xlabel(r'$\delta = 3d/n$')
ax.set_ylabel(r'$a = \mu_6/n$')
ax.axvline(3 / 70, color='0.4', linewidth=0.6, linestyle='--')
ax.text(0.048, 0.19, r'$\delta = 3/70$', fontsize=8, color='0.3')
ax.add_patch(Rectangle((0.40, 0.165), 0.02, 0.012, facecolor='#d9e6f2', edgecolor='#1f3b57', lw=0.5))
ax.text(0.425, 0.166, 'mode I', fontsize=8)
ax.add_patch(Rectangle((0.40, 0.145), 0.02, 0.012, facecolor='#7fa7cc', edgecolor='#1f3b57', lw=0.5))
ax.text(0.425, 0.146, 'mode II', fontsize=8)
ax.set_title('giant-path construction', fontsize=10)

for b in B['T']:
    l0, l1 = float(Fr(b['l0'])), float(Fr(b['l1']))
    bx.add_patch(Rectangle((0.2, l0), 0.6, l1 - l0, facecolor='#c7e9c0', edgecolor='#00441b', lw=0.5))
bx.set_xlim(0, 1)
bx.set_ylim(0.17, 0.34)
bx.set_xticks([])
bx.set_ylabel(r'$\lambda = \mu_T/n$')
bx.set_title('unit construction', fontsize=10)
fig.tight_layout()
fig.savefig(os.path.join(FIG, 'boxes.png'), dpi=300)
plt.close(fig)

# ---- certified bounds against empirical proportions
rows = list(csv.DictReader(open(os.path.join(ROOT, 'code', 'data', 'rho_density.csv'))))
th = [float(r['theta']) for r in rows]
odd = [float(r['odd']) for r in rows]
unit = [float(r['unit']) for r in rows]
cert = sorted((float(Fr(k)), float(Fr(v))) for k, v in B['beta'].items())
fig, ax = plt.subplots(figsize=(5.6, 3.4))
keep = [i for i, t in enumerate(th) if 0.5 <= t <= 0.99 and odd[i] > 0]
ax.semilogy([th[i] for i in keep], [odd[i] for i in keep], color='#1f3b57', lw=1.0,
            label=r'odd $z \leq 10^8$')
ax.semilogy([th[i] for i in keep], [unit[i] for i in keep], color='#41ab5d', lw=1.0, ls='--',
            label=r'units $z \leq 10^8$')
ax.semilogy([c[0] for c in cert], [c[1] for c in cert], 'o', ms=4, mfc='white', mec='#8c2d04',
            label=r'certified $\beta(\theta)$')
ax.set_xlabel(r'$\theta$')
ax.set_ylabel(r'proportion with $\rho^\prime(z) < \theta$')
ax.set_xlim(0.5, 1.0)
ax.legend(frameon=False, fontsize=9, loc='lower right')
fig.tight_layout()
fig.savefig(os.path.join(FIG, 'densities.png'), dpi=300)
plt.close(fig)
print('figures written to', FIG)
