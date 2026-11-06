from matplotlib import pyplot as plt
import numpy as np
import matplotlib
import os

SERIF_FONT = "Linux Libertine"
SANS_SERIF_FONT = "Linux Biolinum"

plt.rcParams.update(
    {
        "pdf.fonttype": 42,
        "font.family": [SANS_SERIF_FONT],
        "mathtext.fontset": "custom",
        "mathtext.rm": SANS_SERIF_FONT,
        "mathtext.it": SANS_SERIF_FONT + ":italic",
        "mathtext.bf": SANS_SERIF_FONT + ":bold",
    }
)

def save(self, filename, exts=None, *args, **kwargs):
    self.savefig(filename, *args, **kwargs)
    plt.close(self)
matplotlib.figure.Figure.save = save

fig, ax = plt.subplots()

np.set_printoptions(suppress=True)
data = np.genfromtxt("log", delimiter=",", dtype=int)[1:, :]
max_num_rule_fires = max(data[:, 6])
bucket = 1
while bucket <= max_num_rule_fires:
    old_bucket = bucket if bucket > 1 else 0
    bucket *= 10
    mask = (data[:, 6] >= old_bucket) & (data[:, 6] < bucket)
    ax.scatter(data[mask, 3], data[mask, 8], s=1)

ax.set_xlim(left=0)
ax.set_ylim(bottom=0)
ax.set_xlabel("Number of Reachable Locations")
ax.set_ylabel("Analysis Time (micros)")
ax.spines[["top", "right"]].set_visible(False)
fig.tight_layout()
fig.save("time_vs_locations.pdf")

fig, ax = plt.subplots()
ax.scatter(data[:, 6], data[:, 8], s=1)
ax.set_xlim(left=0)
ax.set_ylim(bottom=0)
ax.set_xlabel("Number of Rule Fires")
ax.set_ylabel("Analysis Time (micros)")
ax.spines[["top", "right"]].set_visible(False)
fig.tight_layout()
fig.save("time_vs_rules.pdf")
