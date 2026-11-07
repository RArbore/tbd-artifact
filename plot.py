from matplotlib import colorizer as colorizer
from matplotlib import colors as colors
from matplotlib import pyplot as plt
import numpy as np
import matplotlib
import os

np.set_printoptions(suppress=True)
data = np.genfromtxt("log", delimiter=",", dtype=int)[1:, :]

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

cmap = "gnuplot2"
s = 10
alpha = 0.5
w = 4
c = np.maximum(data[:, 6], 1)

fig, ax = plt.subplots()
norm = colors.LogNorm(vmin=c.min(), vmax=c.max())
ax.scatter(data[:, 5], data[:, 8], s=s, c=c, cmap=cmap, alpha=alpha, norm=norm)
ax.set_xlabel("Number of Reachable Locations")
ax.set_ylabel("Analysis Time (microseconds)")
ax.set_xscale("log")
ax.set_yscale("log")
ax.spines[["top", "right"]].set_visible(False)
cax = fig.add_axes([0.22, 0.5, 0.03, 0.43])
fig.colorbar(colorizer.ColorizingArtist(colorizer.Colorizer(norm=norm, cmap=cmap)), cax=cax, label="Number of Applied Rules")
fig.set_figwidth(w)
fig.set_figheight(w)
fig.tight_layout()
plt.savefig("plot.pdf", bbox_inches="tight")
