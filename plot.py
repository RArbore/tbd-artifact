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
ax.scatter(data[:, 3], data[:, 8], s=1, c=np.cbrt(data[:, 6]), cmap="gist_rainbow")

ax.set_xlabel("Number of Reachable Locations")
ax.set_ylabel("Analysis Time (micros)")
ax.set_xscale("log")
ax.set_yscale("log")
ax.spines[["top", "right"]].set_visible(False)
fig.tight_layout()
fig.save("time_vs_locations.pdf")

fig, ax = plt.subplots()
ax.scatter(data[:, 6], data[:, 8], s=1, c=np.log(data[:, 3]), cmap="gist_rainbow")
ax.set_xscale("log")
ax.set_yscale("log")
ax.set_xlabel("Number of Rule Fires")
ax.set_ylabel("Analysis Time (micros)")
ax.spines[["top", "right"]].set_visible(False)
fig.tight_layout()
fig.save("time_vs_rules.pdf")
