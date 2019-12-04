# libraries
import numpy as np
import matplotlib.pyplot as plt
 
# set width of bar
barWidth = 0.3
 
data = [
  ('si', [153.06,211.09,164.38,36.86]),
  ('eq', [380.11,765.8,404.75,137.66]),
  ('cr', [301.88,689.48,294.28,64.16]),
  ('gt', [350.55,813.78,338.41,98.19]),
  ('mo', [1078.57,3466.24,1121.46,211.01]),
  ('6s', [12.16,2.63,11.98,1.26]),
  ('ab', [93.43,174.1,106.72,72.92]),
  ('sq', [938.84,1445.67,1110.18,100.11]),
  ('hw', [1644.95,4187.74,1735.62,169.34]),
  ('ma', [28.24,10.29,30.8,5.71]),
  ('dp', [125.94,213.41,144.64,26.21]),
  ('av', [464.3390909,1089.111818,496.6563636,83.94818182])
]

prob_names = [x[0] for x in data]
dimacs_drats = [x[1][0] for x in data]
drat_lrats = [x[1][1] for x in data]
dimacs_frats = [x[1][2] for x in data]
frat_lrats = [x[1][3] for x in data]

r1 = [x - (barWidth / 2) for x in np.arange(len(prob_names))]
r2 = [x + barWidth for x in r1]
  
plt.bar(r1, dimacs_drats, color='#1464F4', width=barWidth, edgecolor='white', label='DIMACS to DRAT')
plt.bar(r1, drat_lrats, bottom=dimacs_drats, color='#60AFFE', edgecolor='white', width=barWidth, label='DRAT to LRAT')

plt.bar(r2, dimacs_frats, color='#1DA237', width=barWidth, edgecolor='white', label='DIMACS to FRAT')
plt.bar(r2, frat_lrats, bottom=dimacs_frats, color='#7BCC70', edgecolor='white', width=barWidth, label='FRAT to LRAT')


# Add xticks on the middle of the group bars
plt.xlabel('Problems', fontweight='bold')
plt.ylabel('Time (seconds)', fontweight='bold')
plt.xticks(range(len(prob_names)), prob_names)
  
# Create legend & Show graphic
plt.legend()
plt.show()
