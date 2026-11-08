from matplotlib import colorizer as colorizer
from matplotlib import colors as colors
from matplotlib import pyplot as plt
import numpy as np
import matplotlib
import os

np.set_printoptions(suppress=True)
data = np.genfromtxt("log", delimiter=",", dtype=int)[1:, :]
print("Max number of applied rules:", np.max(data[:, 6]))
print("Mean of max number of repetitions of a component:", np.mean(data[:, 4]))
print("Median of max number of repetitions of a component:", np.median(data[:, 4]))
print("Max of max number of repetitions of a component:", np.max(data[:, 4]))
fit = np.polyfit(np.log(data[:, 3]), np.log(data[:, 8]), 1)
print("Line fit vs. number of reachable blocks:", fit)
print("Line fit vs. number of visited locations:", np.polyfit(np.log(data[:, 5]), np.log(data[:, 8]), 1))
print("Line fit vs. number of applied rules", np.polyfit(np.log(np.maximum(data[:, 6], 1)), np.log(data[:, 8]), 1))

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
ax.scatter(data[:, 3], data[:, 8], s=s, c=c, cmap=cmap, alpha=alpha, norm=norm)
#x = np.arange(np.min(data[:, 3]), np.max(data[:, 3]), 100)
#ax.plot(x, np.exp(np.poly1d(fit)(np.log(x))), c="red", linewidth=1, linestyle="--")
ax.set_xlabel("Number of Reachable Locations")
ax.set_ylabel("Analysis Time (microseconds)")
ax.set_xscale("log")
ax.set_yscale("log")
ax.spines[["top", "right"]].set_visible(False)
cax = fig.add_axes([0.19, 0.56, 0.03, 0.4])
fig.colorbar(colorizer.ColorizingArtist(colorizer.Colorizer(norm=norm, cmap=cmap)), cax=cax, label="Number of Applied Rules")
fig.set_figwidth(w)
fig.set_figheight(w)
fig.tight_layout()
plt.savefig("plot.pdf", bbox_inches="tight")
