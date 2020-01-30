# libraries
import numpy as np
import matplotlib.pyplot as plt
import data as dt 
 
# set width of bar
barWidth = 0.35
 
length = len(dt.raw_data) + 1
time_data = dt.raw_data + [dt.avg]

time_prob_names = [x[0] for x in time_data]
dimacs_frats = [x[1][0] / 60 for x in time_data]
frat_lrats = [x[1][1] / 60 for x in time_data]
dimacs_drats = [x[1][3] / 60 for x in time_data]
drat_lrats = [x[1][4] / 60 for x in time_data]

r = np.arange(length)
r0 = np.concatenate([r[:-1], [r[-1] + 1]])
r1 = [x - (barWidth / 2) for x in r0] # np.arange(len(prob_names))]
r2 = [x + barWidth for x in r1]
  
plt.bar(r1, dimacs_drats, color='#1464F4', width=barWidth, edgecolor='white', label='DIMACS to DRAT (unmodified CaDiCaL)')
plt.bar(r1, drat_lrats, bottom=dimacs_drats, color='#60AFFE', edgecolor='white', width=barWidth, label='DRAT to LRAT (DRAT-trim)')
plt.bar(r2, dimacs_frats, color='#1DA237', width=barWidth, edgecolor='white', label='DIMACS to FRAT (modified CaDiCaL)')
plt.bar(r2, frat_lrats, bottom=dimacs_frats, color='#7BCC70', edgecolor='white', width=barWidth, label='FRAT to LRAT (our elaborator)')
 
plt.tick_params(axis="x", labelsize=8)

# Add xticks on the middle of the group bars
plt.xlabel('Problems', fontweight='bold')
plt.ylabel('Time (minutes)', fontweight='bold')
plt.xticks(r0, time_prob_names)

# Create legend & Show graphic
plt.legend()
plt.savefig('time.eps', format='eps')
