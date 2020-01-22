# libraries
import numpy as np
import matplotlib.pyplot as plt
 
# set width of bar
barWidth = 0.35
 
old_data = [
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

raw_data = [
  ("f6", [10.95, 3.85, 137744, 9.44, 4.93, 130848]),
  ("61", [11.71, 1.21, 17908, 11.97, 4.46, 109160]),
  ("ma", [29.01, 5.41, 31640, 26.76, 14.67, 182236]),
  ("ab", [106.52, 73.17, 40784, 91.56, 258.29, 1529552]),
  ("dp", [123.68, 24.49, 47320, 115.65, 255.04, 520328]),
  ("s1", [157.89, 33.94, 53396, 150.53, 304.2, 664784]),
  ("ha", [221.07, 40.29, 78608, 210.62, 557.95, 1962748]),
  ("as", [475.31, 72.23, 22364, 429.71, 497.58, 1416316]),
  ("mi", [228.4, 109.03, 150100, 419.61, 551.35, 2462572]),
  ("e1", [304.79, 74.89, 55724, 281.98, 758.72, 1219436]),
  ("e2", [295.34, 78.74, 44992, 272.06, 781.93, 1396644]),
  ("62", [466.47, 126.3, 106088, 423.09, 676.07, 1147424]),
  ("e3", [327.79, 84.33, 45840, 300.99, 849.42, 1587964]),
  ("cr", [261.51, 45.4, 38936, 249.11, 928.59, 1105608]),
  ("s2", [398.59, 70.68, 51116, 376.37, 999.79, 1374396]),
  ("gt", [288.23, 63.79, 57188, 273.24, 1103.76, 1826008]),
  ("e4", [390.42, 105.53, 56188, 348.53, 1048.24, 1799388]),
  ("sq", [920.53, 97.71, 75528, 785.91, 1764.54, 1631540]),
  ("e5", [1443.48, 154.6, 98400, 1350.81, 1689.15, 2168476]),
  ("la", [2136.73,299.21, 170988, 1949.63, 2666.81, 1627136])
]

avg = ("avg", [429.921, 78.24, 69042.6, 403.8785, 785.7745, 1293128.2])

def get_drat_peak_mem(x):
  return x[1][5]

length = len(raw_data) + 1

time_data = raw_data + [avg]
mem_data = sorted(raw_data, key=get_drat_peak_mem) + [avg]

time_prob_names = [x[0] for x in time_data]
dimacs_frats = [x[1][0] for x in time_data]
frat_lrats = [x[1][1] for x in time_data]
dimacs_drats = [x[1][3] for x in time_data]
drat_lrats = [x[1][4] for x in time_data]

mem_prob_names = [x[0] for x in mem_data]
frat_peak_mems = [x[1][2] / (1024)  for x in mem_data]
drat_peak_mems = [x[1][5] / (1024) for x in mem_data]

r = np.arange(length)
r0 = np.concatenate([r[:-1], [r[-1] + 1]])
r1 = [x - (barWidth / 2) for x in r0] # np.arange(len(prob_names))]
r2 = [x + barWidth for x in r1]
  
# plt.bar(r1, dimacs_drats, color='#1464F4', width=barWidth, edgecolor='white', label='DIMACS to DRAT')
# plt.bar(r1, drat_lrats, bottom=dimacs_drats, color='#60AFFE', edgecolor='white', width=barWidth, label='DRAT to LRAT')
# plt.bar(r2, dimacs_frats, color='#1DA237', width=barWidth, edgecolor='white', label='DIMACS to FRAT')
# plt.bar(r2, frat_lrats, bottom=dimacs_frats, color='#7BCC70', edgecolor='white', width=barWidth, label='FRAT to LRAT')
plt.bar(r1, drat_peak_mems, color='#60AFFE', width=barWidth, edgecolor='white', label='DRAT peak memory usage')
plt.bar(r2, frat_peak_mems, color='#7BCC70', width=barWidth, edgecolor='white', label='FRAT peak memory usage')
 
plt.tick_params(axis="x", labelsize=8)

# Add xticks on the middle of the group bars
plt.xlabel('Problems', fontweight='bold')

# plt.ylabel('Time (seconds)', fontweight='bold')
plt.ylabel('Peak memory usage (KB)', fontweight='bold')

plt.xticks(r0, mem_prob_names)

# Create legend & Show graphic
plt.savefig('mem.eps', format='eps')
