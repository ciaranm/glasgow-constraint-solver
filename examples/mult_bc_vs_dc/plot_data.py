import sys

import matplotlib.pyplot as plt
import pandas as pd

# Read the CSV file
data = pd.read_csv(sys.argv[1], index_col=False)

print(data)
# data = data.loc[data['noproofsolve'] > 100]
# Plot noproofsolve against bcproofsolve
plt.figure(figsize=(10, 5))

plt.subplot(1, 2, 1)
plt.scatter(data['noproofsolve'], data['gacproofsolve'] / 1000000, color='r', s=10, label='GAC Proof Logging')
plt.scatter(data['noproofsolve'], data['bcproofsolve'] / 1000000, color='b', s=10, label='BC Proof Logging')
plt.yscale('log')
plt.title('Overhead of BC vs GAC proof logging')
plt.xlabel('Time without proof logging (µs)')
plt.ylabel('Time with proof logging (s)')
plt.legend()
# plt.gca().xaxis.set_minor_locator(AutoMinorLocator(5))
plt.grid(True, which='major')
plt.subplot(1, 2, 2)

plt.scatter(data['noproofsolve'], data['gacverify'] / 1000000, color='r', s=10, label='GAC Proof Logging')
plt.scatter(data['noproofsolve'], data['bcverify'] / 1000000, color='b', s=10, label='BC Proof Logging')
plt.yscale('log')
plt.title('Verification for BC vs GAC proof logging')
plt.xlabel('Time without proof logging (µs)')
plt.ylabel('Verification Time (s)')
plt.legend()
# plt.gca().xaxis.set_minor_locator(AutoMinorLocator(5))
plt.grid(True, which='major')
# Show the plots
plt.tight_layout()
plt.show()
