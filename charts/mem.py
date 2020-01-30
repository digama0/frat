# libraries
import numpy as np
import matplotlib.pyplot as plt
import data as dt
 
# set width of bar
barWidth = 0.35

def get_drat_peak_mem(x):
  return x[1][5]

length = len(dt.raw_data) + 1

mem_data = sorted(dt.raw_data, key=get_drat_peak_mem) + [dt.avg]
mem_prob_names = [x[0] for x in mem_data]
frat_peak_mems = [x[1][2] / (1024 * 1024) for x in mem_data]
drat_peak_mems = [x[1][5] / (1024 * 1024) for x in mem_data]

r = np.arange(length)
r0 = np.concatenate([r[:-1], [r[-1] + 1]])
r1 = [x - (barWidth / 2) for x in r0] # np.arange(len(prob_names))]
r2 = [x + barWidth for x in r1]
  
plt.bar(r1, drat_peak_mems, color='#60AFFE', width=barWidth, edgecolor='white', label='DRAT')
plt.bar(r2, frat_peak_mems, color='#7BCC70', width=barWidth, edgecolor='white', label='FRAT')
 
plt.tick_params(axis="x", labelsize=8)

# Add xticks on the middle of the group bars
plt.xlabel('Problems', fontweight='bold')

# plt.ylabel('Time (seconds)', fontweight='bold')
plt.ylabel('Peak memory usage (MB)', fontweight='bold')

plt.xticks(r0, mem_prob_names)

# Create legend & Show graphic
plt.legend()
plt.savefig('mem.eps', format='eps')
