# coding: utf-8

import os
import shutil
import time
import sys
import io
import codecs
import re
import math
import json
import urllib2
import HTMLParser
import xml.dom.minidom
import socket
import csv
from urlparse import urljoin
from httplib import IncompleteRead
from httplib import BadStatusLine
from collections import defaultdict
from boilerpipe.extract import Extractor

# CONFIGS

# general
startTime = time.time()
collectPolicies = True
verbose = False
azureSleepSeconds = 1
minLinesPerPolicy = 1

# paths
dataDir = '/usr0/home/wammar/privacy-policy-reader/data/{0}'.format(startTime)
dataUrl = 'http://lausanne.ark.cs.cmu.edu:8050/{0}'.format(startTime)
manualSitePolicyPairsFile = '/usr0/home/wammar/privacy-policy-reader/manualSitePolicyPairs.txt'
stopwordsFilename = '/usr0/home/wammar/privacy-policy-reader/stopwords.txt'
skeletonFilename = '/usr0/home/wammar/privacy-policy-reader/index-skeleton.html'
tosDrRulesDir = '/usr0/home/wammar/privacy/tos-dr/tosback2/rules'
sitePoliciesFilename = 'site-policies.txt'

# boilerpipe settings
boilerpipeExtractorType = 'KeepEverythingExtractor' # 'ArticleExtractor'

# what files to save?
persistHtml = True
persistFullText = True
persistNormalized = True
persistHtmlChunks = True

# policy url filter behavior
allowPolicyUrlNotIncludeSiteName = True
allowPolicyUrlNotIncludePrivacyToken = True
allowPolicyUrlToHaveForeignExtensions = True

# which sites to include?
useAlexaSites = True
useTosDrSites = False
useStopwords = False
useManualSitePolicyPairsFile = True

# alexa crawling details
alexaPages = 1
alexaSleepSeconds = 3

# chunk specification for crowdsourcing annotations
chunkCharLength = 5000

# builds a list of entries. each entry is either a string or a coherent html fragment which readers wouldn't split in two pages.
class AtomicTextExtractor(HTMLParser.HTMLParser):
  def __init__(self, url):
    HTMLParser.HTMLParser.__init__(self)
    self.url = url
    # the list of entries described above
    self.atoms = ['']
    # we ignore the header and start extracting when we encounter the body tag
    self.insideBody = False
    # this means we are inside a tag that people usually perceive as an atomic piece of discourse which shouldn't be split further for it to be intelligible
    self.insideAtom = False
    # if we are inside an atom, we keep track of open tags which haven't been matched with end tags. this is important in order to recognize when we "leave" the atom 
    self.atomStack = []
  def handle_starttag(self, tag, attrs):
    tag = tag.lower()
    if tag == 'body':
      self.insideBody = True
    if not self.insideBody:
      return
    attrsList = []
    for attr in attrs:
      # we want links to appear as links, but not to function as links
      if tag == 'a' and attr[0] == 'href':
        if attr[1].startswith('javascript') or attr[1].startswith('mailto'):
          attr = (attr[0], "javascript:alert('Disabled.')")
        elif not attr[1].startswith('http'):
          attr = (attr[0], "javascript:alert('Disabled.')")
      # sometimes the attribute name/value contains words which should be highlighted. this makes replacing the words complicated later. so lets just get rid of them! 
      attr = (keywordsRegex.sub(r"placeholder", attr[0]), keywordsRegex.sub(r"placeholder", attr[1]))
      attrsList.append(u'{0}={1}'.format(attr[0], attr[1]))
    attrsString = '' if len(attrsList) == 0 else u' ' + ' '.join(attrsList)
    if self.insideBody and tag in set(['p', 'span', 'a', 'b', 'i', 'ul', 'ol', 'h1', 'h2', 'h3', 'strong']):
      self.insideAtom = True
    if self.insideAtom:
      self.atomStack.append('{0}'.format(tag))
      self.atoms.append(u' <{0}{1}>'.format(tag, attrsString))
  def handle_endtag(self, tag):
    endTag = tag.lower()
    if self.insideAtom:
      self.atoms.append('</{0}> '.format(endTag))
      while len(self.atomStack) > 0:
        startTag = self.atomStack.pop()
        if endTag == startTag:
          break
      if len(self.atomStack) == 0:
        self.insideAtom = False
        self.atoms.append('\n')
  def handle_startendtag(self, tag, attrs):
    self.atoms.append('<{0} />'.format(tag))
  def handle_data(self, data):
    if self.insideBody:
      self.atoms.append(data.replace('\n', ' ')+'\n')

# an HTML parser for alexa web pages
class AlexaParser(HTMLParser.HTMLParser):
  def __init__(self):
    HTMLParser.HTMLParser.__init__(self)
    self.sites = []
    self.read = False
  def handle_starttag(self, tag, attrs):
    if tag == 'span' \
          and len(attrs) == 1 \
          and attrs[0][0] == 'class' \
          and attrs[0][1] == 'small topsites-label':
      self.read = True
  def handle_endtag(self, tag):
    self.read = False
  def handle_data(self, data):
    if self.read == True:
      self.sites.append(data)

# an HTML parser which extracts all page text in a list
class PolicyParser(HTMLParser.HTMLParser):

  def __init__(self):
    HTMLParser.HTMLParser.__init__(self)
    self.texts = []
    self.indexes = []
    self.currentIndex = []
    self.lastIndex = []
    self.oneline = False

  def handle_data(self, data):
    if len(data) != 0:
      if self.oneline:
        self.oneline = False
        self.texts[-1] += data
      else:
        self.texts.append(data)
        self.indexes.append(tuple(self.currentIndex))

  def handle_starttag(self, tag, attr):
    #update current/last index
    tempIndex = list(self.currentIndex)
    if len(self.lastIndex) > len(self.currentIndex):
      self.currentIndex.append(self.lastIndex[-1]+1)
    else:
      self.currentIndex.append(0)
    self.lastIndex = tempIndex
      
#    if tag.lower() == 'a':
#      self.oneline = True
#      self.texts[-1] += '<a'
#      for t in attr:
#        self.texts[-1] += ' {0}=\'{1}\''.format(t[0], t[1])
#      self.texts[-1] += '>'

  def handle_endtag(self, tag):
    #update current/last index
    self.lastIndex = list(self.currentIndex)
    self.currentIndex.pop()

    if tag.lower() == 'a':
      self.oneline = True
      self.texts[-1] += '</a>'

# returns the tuple (sites, policies) where sites and policies are two lists of equal length which contain domains and corresponding privacy policy urls
def UseCachedPolicyUrls(dataDir, sitePoliciesFilename):
  sites = []
  policies = []
  if not os.path.exists(dataDir):
    os.makedirs(dataDir)
  shutil.copyfile('{0}/../{1}'.format(dataDir, sitePoliciesFilename), 
           '{0}/{1}'.format(dataDir, sitePoliciesFilename))
  sitePoliciesFile = open('{0}/site-policies.txt'.format(dataDir))
  for site in sitePoliciesFile:
    splits = site.strip().split()
    sites.append(splits[0])
    policies.append(splits[1])
  sitePoliciesFile.close()
  return (sites, policies)

def GetStopwords(filename):
  stopwordsFile = io.open(filename, mode='r', encoding='utf8')
  stopwordsList = stopwordsFile.readlines()
  for i in range(0, len(stopwordsList)):
    stopwordsList[i] = stopwordsList[i].strip()
  return set(stopwordsList)

# returns sites listed in the first n alexa pages. each page has 25 domains
def CrawlAlexa(alexaPages, alexaSleepSeconds):
  sites = []
  parser = AlexaParser()
  for i in range(0,alexaPages):
    if i == alexaPages:
      break;
    print 'reading alexa page #' + str(i)
    alexaUrl = 'http://www.alexa.com/topsites/countries;{0}/US'.format(i)
    alexaText = urllib2.urlopen(alexaUrl).read().replace('<br clear="all">','')
    parser.feed(alexaText)
    time.sleep(alexaSleepSeconds)
  for site in parser.sites:
    sites.append(site)
  return sites

# returns urls of the privacy policies which correspond to each site in sites. 
def FindPolicyUrls(sites, azureSleepSeconds):
  print 'searching {0} sites for privacy policies..'.format(len(sites))
  policies = []
  counter = 0
  for site in sites:
    
    # reporting
    counter += 1
    if counter % 50 == 0:
      print '{0} sites processed'.format(counter)

    # blacklisted sites are those we don't want to collect a privacy policy from for whatever reason (e.g. blogspot.com's privacy policy is the same as google's)
    if IsBlacklisted(site):
      policies.append('-')
      print '{0} is blacklisted'.format(site)
      continue

    # search for a privacy policy for this site
    passMan = urllib2.HTTPPasswordMgrWithDefaultRealm()
    passMan.add_password(realm=None,
                         uri='https://api.datamarket.azure.com',
                         user='waleed.ammar@gmail.com',
                         passwd='NlxoxW7OFF/FdzWA16Fxd91TIFNxMoxUSMJvuB+xab8=')
    authHandler = urllib2.HTTPBasicAuthHandler(passMan)
    opener = urllib2.build_opener(authHandler)
    # to experiment with different queries, use this https://datamarket.azure.com/dataset/explore/8818f55e-2fe5-4ce3-a617-0b8ba8419f65
    url='https://api.datamarket.azure.com/Data.ashx/Bing/SearchWeb/Web?Query=%27{0}%20privacy%20policy%20or%20notice%27&Market=%27en-US%27&$top=5&$format=json'.format(site)
    try:
      bingResultInJson = opener.open(url).read()
    except ssl.SSLError as e:
      print 'most probably, you need to go to {0} in your browser, authenticate using one of your <key description, key value> pairs which can be found at {1}. detailed error: {2}'.format(url, 'https://datamarket.azure.com/account/keys', e)
      exit
    bingResult = json.loads(bingResultInJson)
    candidates = []
    if u'd' in bingResult.keys() and u'results' in bingResult[u'd'].keys():
      for i in range(0, len(bingResult[u'd'][u'results'])):
        if(u'Url' in bingResult[u'd'][u'results'][i].keys()):
          candidates.append(bingResult[u'd'][u'results'][i][u'Url'])
    if len(candidates) > 0:
      # got some candidate pages, compute a heuristic score of how likely is it to be a privacy policy
      scores = []
      candidateTexts = []
      best = 0
      for i in range(0, len(candidates)):
        (policyText, policyHtml) = ExtractPolicyTextWithBoilerpipe(candidates[i], 'KeepEverythingExtractor', False)
        candidateTexts.append(policyText)
        if candidateTexts[i] == None or site not in candidates[i]:
          scores.append(-1)
        else:
          scores.append(ComputePercentageOfPrivacyTermsInText(candidateTexts[i]))
        if scores[best] < scores[i]:
          best = i                
      # favor shorter URLs
      if len(candidates[0]) < len(candidates[best]) and \
            scores[0] + 0.3 > scores[best]:
        best = 0
      # now, append the best policy (if any) to the list of policies
      if scores[best] <= 0.3:
        policies.append('-')
        print '{0} couldn\'t read the results'.format(site)
      elif candidates[best] in policies:
        policies.append('-')
        print '{0}\'s privacy policy is covered by an earlier site'.format(site)
      else:
        policies.append(candidates[best])
        print '{0}%\t{1} chars\t{2}'.format(scores[best]*100, len(candidateTexts[best]), candidates[best])
    else:
      # for some sites, we won't have any candidate policy pages (for various reasons), so append a dash to the "policies" list.
      policies.append('-')
      print 'no privacy policy found for {0}'.format(site)

    # enforce some delay so that azure doesn't block us 
    time.sleep(azureSleepSeconds)

  # return the list of policies that correspond to sites
  return policies

# persist the top alexa sites and the corresponding privacy policy urls
def PersistUrls(dataDir, sitePoliciesFilename, sites, policies):
  if not os.path.exists(dataDir):
    os.makedirs(dataDir)
  out = open('{0}/{1}'.format(dataDir, sitePoliciesFilename),mode='w')
  for i in range(0,len(policies)):
    out.write('{0}\t{1}\n'.format(sites[i], policies[i]))
  out.close()
  shutil.copyfile('{0}/{1}'.format(dataDir, sitePoliciesFilename), 
           '{0}/../{1}'.format(dataDir, sitePoliciesFilename))

# downloads the page, and uses boilerpipe to extract the actual policy text and return it. In case of error, the method returns None.
def ExtractPolicyTextWithBoilerpipe(policyUrl, extractorType = 'ArticleExtractor', verbose = False, minLinesPerPolicy = 30):
  if verbose:
    if policyUrl == '-':
      print 'ExtractPolicyTextWithBoilerpipe called with policyUrl = {0}. do nothing.'.format(policyUrl)
    else:
      print 'extracting policy text from {0} using {1}'.format(policyUrl, extractorType)

  # trivial return
  if policyUrl == '-':
    return (None, None)
  
  try:
    if policyUrl.startswith('http'):
      extractor = Extractor(extractor=extractorType, url=policyUrl)
    # the policyUrl may also be a local file path
    else:
      contentFile = open(policyUrl, 'r')
      extractor = Extractor(extractor=extractorType, html=contextFile.read().decode('utf8'))
    html = extractor.getHTML()
    text = extractor.getText()
    
    if len(text.split(u'\n')) > minLinesPerPolicy:
      if verbose:
        print 'OK'
      return (text, html)
    elif len(text) > 0 and len(html) > 0:
      print 'Policy {1} ignored. Number of paragraphs in extracted policy is less than {0}.'.format(minLinesPerPolicy, policyUrl)
      return (None, None)
    else:
      print 'boilerpipe extracted nothing from {0}'.format(policyUrl)
      return (None, None)
  except socket.error as e:
    print 'socket.error thrown while using boilerpipe to extract {0}: {1}'.format(policyUrl, e)
    return (None, None)
  except BadStatusLine as e:
    print 'httplib.BadStatusLine thrown while using boilerpipe to extract {0}: {1}'.format(policyUrl, e)
    return (None, None)
  except IncompleteRead as e:
    print 'httplib.IncompleteRead thrown while using boilerpipe to extract {0}: {1}'.format(policyUrl, e)
    return (None, None)
  except LookupError as e:
    print 'LookupError using boilerpipe to extract {0}: {1}'.format(policyUrl, e)
    return (None, None)
  except UnicodeDecodeError as e:
    print 'UnicodeDecodeError using boilerpipe to extract {0}: {1}'.format(policyUrl, e)
    return (None, None)
  except ValueError as e:
    print 'ValueError using boilerpipe to extract {0}: {1}'.format(policyUrl, e)
    return (None, None)
  except urllib2.HTTPError as e:
    print 'HTTPError using boilerpipe to extract {0}: {1}'.format(policyUrl, e)
    return (None, None)
  except urllib2.URLError as e:
    print 'URLError using boilerpipe to extract {0}: {1}'.format(policyUrl, e)
    return (None, None)
  except socket.timeout as e:
    print 'socket.timeout thrown while using boilerpipe to extract {0}: {1}'.format(policyUrl, e)
    return (None, None)

def PersistPolicyHtml(index, site, policyUrl, policyHtml):
  if policyHtml == None:
    return
  policyFile = io.open('{0}/{1}-{2}.html'.format(dataDir, str(i).zfill(3), site), mode='w', encoding='utf8')
#  policyFile.write(u'<html><body>')
#  policyFile.write(u'<h2>{0}</h2>\n'.format(site))
#  policyFile.write(u'<p>{0}</p><br />\n\n'.format(policyUrl))
#  policyFile.write(u'<p>{0}</p>\n'.format(policyText.replace(u'\n', u'</p>\n<p>')))
#  policyFile.write(u'</body></html>')
  policyFile.write(policyHtml)
  policyFile.close()

keywordsRegex = re.compile('(personal information|personally identifiable|personal data|personal|data|information|name|address|email|e-mail|credit card|debit card|share|sharing|purpose|transfer|access|collect|gather|receive|deletion|deleting|storage|government|request|Third-Party|service providers|restriction|consent|terms of service)', re.IGNORECASE)
def HighlightKeywords(piece):
  return keywordsRegex.sub(r"<span  style='background-color:rgb(255,251,196);'>\1</span>", piece)

closingTagRegex = re.compile('\s*</', re.UNICODE)
someTagRegex = re.compile('\s*<(p|li|a) ', re.UNICODE)
freeTextRegex = re.compile('\s*[^<\s]', re.UNICODE)
endsWithClosingHRegex = re.compile('</h\d>', re.UNICODE)
def SplitHtmlIntoChunks(policyUrl, policyHtml, avgChunkLength):
  if policyHtml == None:
    return None
  # first get a list of all text nodes in the html
  parser = AtomicTextExtractor(policyUrl)
  parser.feed(policyHtml)
  # then split greedily to maintain an average chunk length
  chunks = ['']
  for atom in parser.atoms:
    encodedAtom = atom.encode('utf8')
    encodedCurrent = chunks[-1].encode('utf8')
    currentLengthOfLastChunk = len(chunks[-1])
    # if the current chunk is too small
    if currentLengthOfLastChunk < avgChunkLength:
      chunks[-1] += atom
#      print 'same chunk => currentLength = {0} < {1}'.format(currentLengthOfLastChunk, avgChunkLength)
    # the current chunk may not end with a :
    elif chunks[-1][-1] == ':':
      chunks[-1] += atom
#      print 'same chunk => current chunk ends with a colon:{0}'.format(encodedCurrent)
    # the current chunk may not end with a </h4> nor an </h3> nor an </h2> nor an </h1>
    elif endsWithClosingHRegex.match(chunks[-1]):
      chunks[-1] += atom
#      print 'same chunk => current chunk ends with </h\d>:{0}'.format(encodedCurrent)
    # the new chunk may not start with a blank atom 
    elif len(atom.strip()) == 0:
      chunks[-1] += atom
#      print 'same chunk => blank atom:{0}'.format(encodedAtom)
    # the new chunk cannot start with a closing tag
    elif closingTagRegex.match(atom):
      chunks[-1] += atom
#      print 'same chunk => cannot start a new chunk with a closing tag:{0}'.format(encodedAtom)
    # the new chunk cannot start with certain tags (p, li, a)
    elif someTagRegex.match(atom):
      chunks[-1] += atom
#      print 'same chunk => cannot start a new chunk with some tags:{0}'.format(encodedAtom)
    # the new chunk cannot start with plain text
    elif freeTextRegex.match(atom):
      chunks[-1] += atom
#      print 'same chunk => cannot start a new chunk with free text:{0}'.format(encodedAtom)
    # if all these criteria not met, go ahead and create a new chunk for this item
    else:
      chunks.append(atom)
#      print 'new chunk for:{0}'.format(encodedAtom)
  for i in range(0, len(chunks)):
    chunks[i] = HighlightKeywords(chunks[i])
  return chunks

def WriteHeaderLineInCssChunksFile():
  assert(persistHtmlChunks)
  globalChunksFile = open('{0}/chunks.csv'.format(dataDir), mode='w')
  globalChunksCsv = csv.writer(globalChunksFile, dialect='excel')
  globalChunksCsv.writerow( ['policy_fragment'] )
  globalChunksFile.close()

def PersistChunks(i, site, policyUrl, chunks):
  if chunks == None:
    return
  globalChunksFile = open('{0}/chunks.csv'.format(dataDir), mode='a')
  globalChunksCsv = csv.writer(globalChunksFile, dialect='excel')
  chunksFile = open('{0}/{1}-{2}.chunks'.format(dataDir, str(i).zfill(3), site), mode='w')
  chunksCsv = csv.writer(chunksFile, dialect='excel')
  for j in range(0, len(chunks)):
    field = "<chunk id='{0}-{1}-{2}' /> {3}".format(str(i).zfill(3), 
                                                       site, 
                                                       str(j).zfill(4),
                                                       chunks[j].encode('utf8'))
    globalChunksCsv.writerow( [field] )
    chunksCsv.writerow([field])
  chunksFile.close()
  globalChunksFile.close()

def PersistPolicyFullText(index, site, policyUrl, policyText):
  if policyText == None:
    return
  policyText = re.sub("[ \t]+", " ", policyText)
  policyFile = io.open('{0}/{1}-{2}.fulltext'.format(dataDir, str(i).zfill(3), site), mode='w', encoding='utf8')
  policyFile.write(u'{0}\n'.format(site))
  policyFile.write(u'{0}\n\n'.format(policyUrl))
  policyFile.write(u'{0}\n'.format(policyText))
  policyFile.close()

def PersistPolicyNormalized(index, site, policyUrl, policyText, stopwords):
  if policyText == None:
    return
  policyText = re.sub("[ \t]+", " ", policyText)
  policyFile = io.open('{0}/{1}-{2}.normalized'.format(dataDir, str(i).zfill(3), site), mode='w', encoding='utf8')
#  policyFile.write(u'{0}\n'.format(site))
#  policyFile.write(u'{0}\n\n'.format(policyUrl))

  # lowercase
  policyText = policyText.lower()

  # remove punctuations
  policyText = re.sub(u'[,\-\\.\\(\\)/:\'’;"–\\?]+', u' ', policyText)

  # remove stopwords
  temp = policyText
  policyText = ''
  for line in temp.split(u'\n'):
    for token in line.split():
      if len(token) > 0 and token not in stopwords:
        policyText += u'{0} '.format(token)
    policyText += u'\n'
  policyFile.write(u'{0}\n'.format(policyText))
  policyFile.close()

def CreateIndexHtml(skeletonFilename, dataDir, sites, policies):
  skeletonFile = io.open(skeletonFilename, mode='r', encoding='utf8')
  skeleton = ''.join(skeletonFile.readlines())
  skeletonFile.close()
  indexFile = io.open('{0}/index.html'.format(dataDir), mode='w', encoding='utf8')
  radioButtons = []
  for i in range(0, len(sites)):
    if policies[i] != '-':
      radioButtons.append('<input type="radio" name="site" value="{0}|||{1}-{2}.html" onClick="UpdatePolicy()" />{2}<br />'.format(policies[i], str(i).zfill(3), sites[i]))

  indexFile.write(skeleton.replace(u'{0}', u'\n'.join(radioButtons)))
  indexFile.close()

def IsBlacklisted(site):
  if site in 'youtube.com blogspot.com t.co msn.com live.com bing.com'.split():
    return True

# returns a number between 0 (no privacy terms found) and 1 (all privacy terms found)
def ComputePercentageOfPrivacyTermsInText(text):
  privacyTerms = 'privacy collect information service contact financial name address phone email account bank credit card ssn authorize access cookies store protect transaction transactions marketing third party parties share law providers partner partners policy'.split()
  termsFound = 0
  textTokens = text.lower().split()
  for term in privacyTerms:
    if term in textTokens:
      termsFound += 1
  return 1.0 * termsFound / len(privacyTerms)

def FindTosDrPolicies(tosDrRulesDir, alreadyFoundSites):
  policies = []
  sites = []
  for filename in os.listdir(tosDrRulesDir):    
    if filename[0:-4] in alreadyFoundSites:
      continue
    dom = xml.dom.minidom.parse(os.path.join(tosDrRulesDir, filename))
    for node in dom.getElementsByTagName('docname'):
      if node.getAttributeNode('name').nodeValue == 'Privacy Policy':
        policies.append(node.getElementsByTagName('url')[0].getAttributeNode('name').nodeValue)
        sites.append(filename[0:-4])

  return (sites, policies)

def PolicyUrlLooksFine(site, url):
  if url == '-':
    return True
  somethingFishy = False

  if url[0:4] != 'http' or url[-4:-1].lower() == u'pdf':
    somethingFishy = True
    print 'policy url doesn\'t start with (http) or ends with (pdf): {0}'.format(policyUrl)

  if 'privacy' not in url.lower() and 'pp' not in url.lower() and not allowPolicyUrlNotIncludePrivacyToken:
    somethingFishy = True
    print '(privacy|pp) didn\'t match the url {0}'.format(url)

  if '.com' not in url.lower() and \
  '.info' not in url.lower() and \
  '.org' not in url.lower() and \
  '.net' not in url.lower() and \
  '.gov' not in url.lower() and \
  not allowPolicyUrlToHaveForeignExtensions:
    somethingFishy = True
    print 'none of the popular domain extensions matches {0}'.format(url)

  if site not in url.lower() and not allowPolicyUrlNotIncludeSiteName:
    somethingFishy = True
    print 'site {0} not in url {1}'.format(site, url)

  if somethingFishy:
    return False
  else:
    return True
  
def FindManualPolicies(filename):
  manualPoliciesFile = open(filename)
  sites = []
  policyUrls = []
  for pair in manualPoliciesFile:
    # skip empty lines
    if len(pair.strip()) == 0:
      continue
    # skip comments
    elif pair[0] == '#':
      continue
    (site, policyUrl) = pair.strip().split('\t')
    sites.append(site)
    policyUrls.append(policyUrl)
  return (sites, policyUrls)


# find pairs of site-privacyPolicyUrl
print 'lets get started!'
sites = policies = None
if collectPolicies:
  sites, policies = [], []
  # collect sites from Alexa then search for their respective privacy policies
  if useAlexaSites:
    sites.extend(CrawlAlexa(alexaPages, alexaSleepSeconds))
    policies.extend(FindPolicyUrls(sites, azureSleepSeconds))
  # add manual site-policy pairs
  if useManualSitePolicyPairsFile:
    (manualSites, manualPolicies) = FindManualPolicies(manualSitePolicyPairsFile)
    sites.extend(manualSites)
    policies.extend(manualPolicies)
  # collect pairs of site-policyUrl from the awesome terms-of-service-didn't-read project
  if useTosDrSites:
    (tosDrSites, tosDrPolicies) = FindTosDrPolicies(tosDrRulesDir, sites) 
    sites.extend(tosDrSites)
    policies.extend(tosDrPolicies)
  # save this collection of site-policyUrl pairs in a text file
  PersistUrls(dataDir, sitePoliciesFilename, sites, policies)
  print 'done collecting policies!'
else:
  # load the collection of site-policyUrl pairs from a text file
  (sites, policies) = UseCachedPolicyUrls(dataDir, sitePoliciesFilename)
  print 'policies fetched!'
  
# extract policy text from policy webpage and save it
print 'policy texts can be found at', dataDir, 'or', dataUrl
stopwords = set()
if persistNormalized and useStopwords:
  stopwords = GetStopwords(stopwordsFilename)
if persistHtmlChunks:
  WriteHeaderLineInCssChunksFile()
for i in range(0,len(policies)):

  # check policy url for common problems
  if not PolicyUrlLooksFine(sites[i], policies[i]):
    policies[i] = '-'

  # use boilerpipe to get the policy's main content
  (policyText, policyHtml) = ExtractPolicyTextWithBoilerpipe(policies[i], boilerpipeExtractorType, verbose, minLinesPerPolicy)

  if policyText == None:
    policies[i] = '-'

  # save the policy's html
  if persistHtml:
    PersistPolicyHtml(i, sites[i], policies[i], policyHtml)

  # save the policy html chunks
  if persistHtmlChunks:
    chunks = SplitHtmlIntoChunks(policies[i], policyHtml, chunkCharLength)
    PersistChunks(i, sites[i], policies[i], chunks)

  # save the policy's text
  if persistFullText:
    PersistPolicyFullText(i, sites[i], policies[i], policyText)

  # save the policy's normalized text
  if persistNormalized:
    PersistPolicyNormalized(i, sites[i], policies[i], policyText, stopwords)

if persistHtml:
  CreateIndexHtml(skeletonFilename, dataDir, sites, policies)
