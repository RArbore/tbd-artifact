from matplotlib import colorizer as colorizer
from matplotlib import colors as colors
from matplotlib import pyplot as plt
import numpy as np
import matplotlib
import sys
import os

np.set_printoptions(suppress=True)
data = np.genfromtxt(sys.argv[1], delimiter=",", dtype=int)
data = data.reshape((100, -1, 10))
print(data.shape)
print(data[0, 0, :])
print(data[1, 0, :])
print(data[0, 1, :])
print(data[1, 1, :])

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
s = 1
w = 4
c = np.maximum(data[:, :, 7], 1)

fig, ax = plt.subplots()
norm = colors.LogNorm(vmin=c.min(), vmax=c.max())
colors = colorizer.Colorizer(norm=norm, cmap=cmap)
for i in range(data.shape[0]):
    ax.plot(data[i, :, 1], data[i, :, 9] / data[i, 0, 9], color=colors.to_rgba(c[i, 0]), linewidth=s)
ax.set_xlabel("Number of Preceding If-Elses")
ax.set_ylabel("Analysis Time, Relative to 0 Preceding If-Elses")
ax.spines[["top", "right"]].set_visible(False)
ax.set_xlim(xmin=0)
ax.set_ylim(ymin=0)
cax = fig.add_axes([0.19, 0.56, 0.03, 0.4])
fig.colorbar(colorizer.ColorizingArtist(colors), cax=cax, label="Number of Applied Rules")
fig.set_figwidth(w)
fig.set_figheight(w)
fig.tight_layout()
plt.savefig("plot.pdf", bbox_inches="tight")
