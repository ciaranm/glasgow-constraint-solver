import sys

import matplotlib.pyplot as plt
import pandas as pd

# Read the CSV file
data = pd.read_csv(sys.argv[1], index_col=False)

data = data.loc[data['noproofsolve'] < 80]
data = data.iloc[1:]
print(data)
# Plot noproofsolve against bcproofsolve
plt.figure(figsize=(10, 5))

# plt.subplot(1, 2, 1)
plt.scatter(data['noproofsolve'], data['gacproofsolve'] / 1000000, color='orange', s=8, label='GAC Proof Logging')
plt.scatter(data['noproofsolve'], data['bcproofsolve'] / 1000000, color='b', s=10, label='BC Proof Logging')
plt.yscale('log')
# plt.title('Overhead of BC vs GAC proof logging')
plt.xlabel('Time without proof logging (µs)')
plt.ylabel('Time with proof logging (s)')
plt.legend()
# plt.gca().xaxis.set_minor_locator(AutoMinorLocator(5))
plt.grid(True, which='major')
plt.gca().set_aspect('auto')
plt.gcf().set_size_inches(6, 4)
plt.tight_layout()
plt.savefig("/Users/matthewmcilree/PhD_Code/AAAI25 Paper/experiments1.png", dpi=500)
plt.clf()
# plt.subplot(1, 2, 2)

plt.scatter(data['noproofsolve'], data['gacverify'] / 1000000, color='orange', s=8, label='GAC Proof Logging')
plt.scatter(data['noproofsolve'], data['bcverify'] / 1000000, color='b', s=10, label='BC Proof Logging')
plt.yscale('log')
# plt.title('Verification for BC vs GAC proof logging')
plt.xlabel('Time without proof logging (µs)')
plt.ylabel('Verification Time (s)')
plt.legend()
# plt.gca().xaxis.set_minor_locator(AutoMinorLocator(5))
plt.grid(True, which='major')
plt.gca().set_aspect('auto')
plt.gcf().set_size_inches(6, 4)
plt.tight_layout()
# Show the plots
plt.savefig("/Users/matthewmcilree/PhD_Code/AAAI25 Paper/experiments2.png", dpi=500)
