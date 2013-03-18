import os
import time
import sys
import io
import codecs
import re
import math
import xml.dom.minidom
from collections import defaultdict


# configs
dataDir = '/mal2/wammar/data/privacy/{0}'.format(sys.argv[1])
dataUrl = 'http://lausanne.ark.cs.cmu.edu:8050/{0}'.format(sys.argv[1])
sitePoliciesFilename = 'site-policies.txt'
stopwordsFilename = '/cab0/wammar/exp/privacy/stopwords.txt'
significantTermsFilename = os.path.join(dataDir, 'significant-terms')
minDf = documentFrequencyThreshold = 0.7
maxAvgTf = averageTermFrequencyThreshold = 15
minTokensInLine = 20

# compute document frequencies and aggregate term frequencies for all policy tokens
df = defaultdict(int)
aggregateTf = defaultdict(int)
policiesCounter = 0
for filename in os.listdir(dataDir):
  if not filename.endswith('.normalized'):
    continue
  policiesCounter += 1
  policyFile = codecs.open(os.path.join(dataDir, filename), mode='r', encoding='utf8')
  policyTokens = []
  for line in policyFile.readlines():
    policyTokens.extend(line.split(' '))
  for policyToken in set(policyTokens):
    df[policyToken] += 1
  for policyToken in policyTokens:
    aggregateTf[policyToken] += 1

# find and persist terms with high document frequency and low average term frequency
significantTerms = []
for term in df.keys():
  if len(term) > 1 and \
        1.0 * df[term] / policiesCounter > minDf and \
        1.0 * aggregateTf[term] / df[term] < maxAvgTf:
    significantTerms.append(term)
termsFile = codecs.open(significantTermsFilename, mode='w', encoding='utf8')
for term in significantTerms:
  termsFile.write(u'{0}\n'.format(term))
termsFile.close()

