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
print("Number of rules applied does not vary across preceding if-elses:", np.all(np.min(data[:, :, 7], axis=1) == np.max(data[:, :, 7], axis=1)))

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
norm = colors.Normalize(vmin=0, vmax=12500)
colors = colorizer.Colorizer(norm=norm, cmap=cmap)
for i in range(data.shape[0]):
    ax.plot(data[i, :, 1], data[i, :, 9], color=colors.to_rgba(c[i, 0]), linewidth=s)
ax.set_xlabel("Preceding If-Elses")
ax.set_ylabel("Analysis Time (microseconds)")
#ax.spines[["top", "right"]].set_visible(False)
ax.set_xlim(xmin=0,xmax=1000)
ax.set_ylim(ymin=0)
cax = fig.add_axes([0.22, 0.932, 0.5, 0.03])
cbar = fig.colorbar(colorizer.ColorizingArtist(colors), orientation="horizontal", cax=cax, label="Applied Rules")
cbar.set_ticks(ticks=[0, 2500, 5000, 7500, 10000, 12500])
fig.set_figwidth(w)
fig.set_figheight(w)
fig.tight_layout()
plt.savefig("plot-preceding-ifs.pdf", bbox_inches="tight")
