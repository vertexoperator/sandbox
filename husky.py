#-*- coding:utf-8 -*-
"""
-- Haskellで作る超コンパクト音声認識システム：HuskyをPythonに移植してみたもの
http://www.furui.cs.titech.ac.jp/~shinot/husky/

-- 実行用サンプルデータは上記HPのものを使用
pypy husky.py dcd.config csj-3gram-v30k-mpe-mix32.hloop.hclg.lmw10.asciiid.wfst hmm.spdfs decode.scp

sample output:[1, 29302, 26898, 3292, 23846, 4555, 1591, 2614, 248, 3896, 2]
"""

import sys,traceback
import struct
#-- numpy.arrayを使ったほうがよい
import array
from itertools import takewhile,islice
from math import log,exp

#-- Feature vectors --------------------------------------
#-- read from HTK(HMM Toolkit) MFCC(Mel Frequency Cepstral Coefficient) file

def htkParmFromFile(fp):
   assert(fp is not None)
   (nSamples,sampPeriod,sampSize,parmKind)= struct.unpack('>LLHH' , fp.read(12))
   feavecs = []
   for _ in xrange(nSamples):
      v = array.array('f' , fp.read(sampSize) )
      v.byteswap()
      feavecs.append(v)
   return (nSamples,sampPeriod,sampSize,parmKind,feavecs)

def readScpFile(fp):
  for line in fp:yield line[:-1]

#-- state-conditional probability density functions of the HMM's --------------
#-- 標準的な混合Gauss分布(対角共分散)を使用
#-- 各係数はHTKのascii形式のHMM定義ファイル/MMF(Master Macro File)から取得
class GMixture:
   def __init__(self,_name,_nmix,_weights,_means,_vars,_gconsts):
       self.name = _name
       self.nmix = _nmix
       self.weights = _weights
       self.means = _means
       self.vars = _vars
       self.gconsts = _gconsts
   #-- 音響尤度計算(gmixLProb in husky.hs)
   def __call__(self , fvec):
       mxdiff = [array.array('d' , [a-b for (a,b) in zip(fvec,meanseq)]) for meanseq in self.means]
       mxdiffsqvsum = []
       for (mseq , vseq) in zip(mxdiff , self.vars):
          mxdiffsqvsum.append( sum([(a*a)/b for (a,b) in zip(mseq , vseq)]) )
       lcompPs = [-(a+b)/2 for (a,b) in zip(mxdiffsqvsum , self.gconsts)]
       return log(sum([exp(a)*b for (a,b) in zip(lcompPs,self.weights)]))


def spdfsFromFile(fp):
   assert(fp is not None)
   mixtures = []
   while True:
     line = fp.readline()
     if line=='':
        break
     else:
        ls = line[:-1].split()
        assert( ls[0]=="~s" )
        name = eval(ls[1])
        ls = fp.readline()[:-1].split()  # "<NUMMIXES> %d"
        assert( ls[0]=="<NUMMIXES>" )
        nmix = int(ls[1])
        weights = []
        means = []
        vars = []
        gconsts = []
        for n in xrange(1 , nmix + 1):
          ls = fp.readline()[:-1].split()  # "<MIXTURE> %d %f"
          assert( n==int(ls[1]) and ls[0]=="<MIXTURE>")
          weights.append( float(ls[2]) )
          #--- read MEAN
          ls = fp.readline()[:-1].split() # "<MEAN> %d"
          assert( ls[0]=="<MEAN>" )
          len_means = int(ls[1])
          ls = array.array('d' , [float(c) for c  in fp.readline().split()])
          assert( len_means==len(ls) )
          means.append( ls )
          #--- read VARIANCE
          ls = fp.readline()[:-1].split() # "<VARIANCE> %d"
          assert( ls[0]=="<VARIANCE>" )
          len_vars = int(ls[1])
          ls = array.array('d' , [float(c) for c  in fp.readline().split()])
          assert( len_vars==len(ls) )
          vars.append( ls )
          #--- read GCONST
          ls = fp.readline().split() # "<GCONST> %f"
          assert( ls[0]=="<GCONST>" )
          gconsts.append( float(ls[1]) )
        mixture = GMixture(name,nmix,array.array('d',weights),means,vars,array.array('d',gconsts))
        mixtures.append( mixture )
   return mixtures



"""
-- WFST definitions --------------------------------------
-- Assumptions are 
1) the initial state is the first state in the file,
2) there is only one final state, 
3) Final state does not have associated cost, 
4) arcs are sorted by its start and end node IDs

ファイルフォーマットは、AT&T FSM formatとかいうもの？
"""

class WFST:
   def __init__(self , arcs , Narcs):
      self.band = 10000
      self.beam = 20.0
      self.insPenalty = 0.0
      self.ImWeight = 10.0
      self.arcStart = array.array('I' , xrange(Narcs) )
      self.arcEnd = array.array('I' , xrange(Narcs) )
      self.arcInput = array.array('I' , xrange(Narcs) )
      self.arcOutput = array.array('I' , xrange(Narcs) )
      self.arcWeight = array.array('f' , xrange(Narcs) )
      idx = 0
      for arc in arcs:
         if idx==0:self.initState = arc[0]
         if arc[1]==-1:self.finalState = arc[0]
         if arc[1]>=0:
            self.arcStart[idx] = arc[0]
            self.arcEnd[idx] = arc[1]
            self.arcInput[idx] = arc[2]
            self.arcOutput[idx] = arc[3]
            self.arcWeight[idx] = arc[4]
            idx += 1
      #-- Index of arc start position and its numbers [(pos, num)] in arcs
      #-- Ex. when arc start = [0,1,1,1,2,3,5,5] in arcArray,
      #-- we want [(0,1), (1,3), (4,1), (5,1), (6,0), (6,2)]
      self.startArray = []
      start_pos = 0
      cur_start = 0
      cur_num = 0
      for s in self.arcStart:
        if cur_start==s:
           cur_num += 1
        else:
           self.startArray.append( (start_pos , cur_num) )
           start_pos += cur_num
           cur_num = 1
           for n in xrange(cur_start+1 , s):
              self.startArray.append( (start_pos , 0) )
           cur_start = s
      self.startArray.append( (start_pos , cur_num) )
   def readConfig(self , fp):
      assert(fp is not None)
      for line in fp:
         (key , val) = line[:-1].split('=')
         if key=="beam":
            self.beam = float(val)
         elif key=="band":
            self.band = int(val)
         elif key=="insPenalty":
            self.insPenalty = float(val)
         elif key=="ImWeight":
            self.ImWeight = float(val)
   def findNextEpsArcs(self , state):
      (start , num) = self.startArray[state]
      for idx in xrange(start , start+num):
         if self.arcInput[idx]==0:
            yield (self.arcStart[idx],self.arcEnd[idx],0,
                   self.arcOutput[idx] , self.arcWeight[idx])
   def findNextHmmArcs(self , state , hmmObsProb):
      (start , num) = self.startArray[state]
      for idx in xrange(start , start+num):
         if self.arcInput[idx]>0:
            i = self.arcInput[idx]
            wt = self.arcWeight[idx] + hmmObsProb(i)
            yield (self.arcStart[idx],self.arcEnd[idx],i,
                   self.arcOutput[idx] , wt)      


def wfstFromFile(fp):
   assert(fp is not None)
   lineCount = len([1 for line in fp if len(line)>1])
   fp.seek(0)
   def arcProducer(fp):
      for line in fp:
         ls = line[:-1].split()
         if len(ls)==5:
            arc = ( int(ls[0]) , int(ls[1]) , int(ls[2]) , int(ls[3]) , float(ls[4]) )
         elif len(ls)==4:
            arc = ( int(ls[0]) , int(ls[1]) , int(ls[2]) , int(ls[3]) , 0.0 )
         elif len(ls)==1:
            arc = ( int(ls[0]) , -1 , 0 , 0 , 0.0)
         else:
            assert(False),'invalid line:%s' % line
         yield arc
   return WFST(arcProducer(fp) , lineCount)


#-- Decoding ----------------------------------------------

#-- expandEps in husky.hs
#-- Depth first search of epsilon reachable nodes from the end of path.
#-- Push path and paths derived from the path by epsilon transitions to hpm
#-- とあるけどhusky.hsのコードは、epsilon遷移で循環しないと仮定しないと
#-- 停止しない気がするので、とりあえずDijkstra
def expandEps(wfst , rootState):
    cost = dict()
    symbols = dict()
    curState = rootState
    fixed = set([])
    for epsarc in wfst.findNextEpsArcs(curState):
        cost[epsarc[1]] = epsarc[4]
        symbols[epsarc[1]] = [epsarc[3]]
    while True:
        temp = [(s,c) for (s,c) in cost.items() if not(s in fixed)]
        if len(temp)==0:break
        (curState , curCost) = min(temp , key=lambda x:x[1])
        fixed.add(curState)
        for epsarc in wfst.findNextEpsArcs(curState):
            if cost.has_key(epsarc[1]) and cost[epsarc[1]] < curCost+epsarc[4]:
               continue
            else:
               cost[epsarc[1]] = curCost+epsarc[4]
               symbols[epsarc[1]] = symbols[curState] + [epsarc[3]]
        yield (rootState , curState , symbols[curState] , curCost)


def expandStates(wfst , previousPathSet , hmmObsProb):
    cost = dict()
    firstState = dict()
    symbols = dict()
    for (_,prevEnd,_,prevScore) in previousPathSet:
        rootState = prevEnd
        baseScore = prevScore 
        for hmmarc in wfst.findNextHmmArcs(rootState , hmmObsProb):
           if cost.has_key(hmmarc[1]) and cost[hmmarc[1]]<hmmarc[4]+baseScore:
              continue
           else:
              cost[hmmarc[1]] = hmmarc[4]+baseScore
              firstState[hmmarc[1]] = rootState
              symbols[hmmarc[1]] = [hmmarc[3]]
           currentScore = cost[hmmarc[1]]
           for (_,exEnd,exOutput,exScore) in expandEps(wfst,hmmarc[1]):
              reachedState = exEnd
              if cost.has_key(reachedState) and cost[reachedState]<exScore+currentScore:
                 continue
              else:
                 cost[reachedState] = currentScore+exScore
                 firstState[reachedState] = rootState
                 symbols[reachedState] = [hmmarc[3]]+exOutput
    for (st , score) in sorted(cost.items() , key=lambda x:x[1]):
        yield (firstState[st] , st , symbols[st] , score)

#-- memoization
def memoize(f):
    cache = {}
    def memf(*x):
        if x not in cache:
            cache[x] = f(*x)
        return cache[x]
    return memf

#-- decodeWfst and backTrack in husky.hs
def decode(wfst , feaSeq , spdfs):
   Nband = wfst.band
   hypsPathSet = list( expandEps(wfst , wfst.initState) )
   hypsPathSet.sort(key = lambda x:x[3])
   activePathSet = hypsPathSet[:wfst.band]
   lattice = [ activePathSet ]
   for fvec in feaSeq:
      assert(len(activePathSet) > 0)
      bestHypScore = activePathSet[0][3]
      #-- Gaussian pruningとかいう技らしい
      prunedPathSet = takewhile(lambda x:x[3]-bestHypScore<wfst.beam , activePathSet)
      hmmObsProb = memoize(lambda st:-spdfs[st-1](fvec))
      activePathSet = list(islice(expandStates(wfst , prunedPathSet , hmmObsProb),Nband))
      lattice.append( activePathSet )
   #-- Backtrack viterbi lattice and find the best hypothesis
   symbols = []   #--output symbols
   endSt = wfst.finalState
   for slice in lattice[::-1]:
       validPath = [path for path in slice if path[1]==endSt]
       assert( len(validPath)>0 )
       (bestPartPathStart,_,pathOutput,_) = min(validPath,key=lambda x:x[3])
       symbols.append(pathOutput)
       endSt = bestPartPathStart
   return [s for s in sum(symbols[::-1] , []) if s!=0]


def main(configf , wfstf , spdff , scpf):
    try:
        wfst = wfstFromFile( open(wfstf) )
        wfst.readConfig( open(configf) )
        spdfs = spdfsFromFile( open(spdff) )
        for feaf in readScpFile( open(scpf) ):
           (_,_,_,_,feas) = htkParmFromFile( open(feaf) )
           out = decode(wfst , feas , spdfs)
           print out
    except:
        traceback.print_exc(file=sys.stdout)

if __name__=="__main__":
     main(sys.argv[1] , sys.argv[2] , sys.argv[3] , sys.argv[4])

"""
#-- 以下はhuskyに含まれないMFCC計算用のコード
import numpy as np
#import struct


#標準のwave moduleを使えばいいけど何となく
def wavread(fp):
  assert('RIFF'==fp.read(4))
  filesz = struct.unpack('>I' , fp.read(4))[0]
  assert('WAVE'==fp.read(4))
  assert('fmt '==fp.read(4))
  chunkSize = struct.unpack('<I' , fp.read(4))[0]
  assert(chunkSize>=16)
  fmtId = struct.unpack('H' , fp.read(2))[0]
  nChannel = struct.unpack('H' , fp.read(2))[0]  #1:monoral,2:stereo
  #assert(nChannel==1 or nChannel==2)
  fs = struct.unpack('<I' , fp.read(4))[0]  #sampling rate
  nbps = struct.unpack('<I' , fp.read(4))[0]
  Bs,nbits = struct.unpack('HH' , fp.read(4))
  #assert(nbits==8 or nbits==16)
  fp.read(chunkSize-16)
  assert('data'==fp.read(4))
  sz = struct.unpack('<I' , fp.read(4))[0]
  if nbits==16:
     dat = 1.0*np.fromstring(fp.read(sz) , dtype=np.int16)
  elif nbits==8:
     assert(False),'めんどい'
  if nChannel==2:
     return dat.reshape(len(dat)/2 , 2).T , fs
  elif nChannel==1:
     return dat,fs

#-- HTKの出力に近い値を出すように
#-- MFCC39(MFCC+ΔMFCC+ΔΔMFCC、それぞれ12次元+log-energy)で出力する
#-- メンバー変数の名前・意味はHTKに合わせているのでHTK Bookなど参照
#-- デフォルトのパラメータの値は、HTKのでなくhuskyのサンプルデータ作成時に
#-- 使用されたらしき値に合わせてある
#-- signal:振幅値,fs:サンプリング周波数
class MFCC39:
  def __init__(self):
     self.WINDOWSIZE = 25.0    #-- フレーム幅[msec];HTKと単位が違うので注意
     self.TARGETRATE = 10.0    #-- フレームシフト長[msec]
     self.PREEMCOEF = 0.97     #-- プリエンファシス係数
     self.NUMCHANS = 24        #-- メルフィルタバンクのチャンネル数
     self.CEPLIFTER = 22       #-- ケプストラムのリフタリングの値
     self.STEREOMODE = 'L'     #-- Select Channel:'L' or 'R'
     self.RAWENERGY = False    #-- エネルギー計算で生データを使うかどうか
     self.ZMEANSOURCE = True   #-- Zero mean source waveform before analysis
     #self.NUMCEPS = 12        #-- 12に固定
     #self.USEHAMMING = True   #-- Hamming窓を使うか(常にTrue)
  def __call__(self,signal , fs):
     def delta(dat):
         #-- 線形回帰はscipy.stats.linregressを使えば一発
         def regress(xs , ys):
             assert(len(xs)==len(ys) and len(xs)>0)
             N = len(xs)
             xm , ym = sum(xs)/N , sum(ys)/N
             a = sum([(x-xm)*(y-ym) for (x,y) in zip(xs,ys)])/sum([(x-xm)*(x-xm) for x in xs])
             b = ym- a*xm
             return a,b
         ret = np.zeros( dat.shape )
         for n in xrange(len(dat)):
             pprev = dat[max(0,n-2)]
             prev = dat[max(0,n-1)]
             cur = dat[n]
             next = dat[min(n+1,len(dat)-1)]
             nnext = dat[min(n+2,len(dat)-1)]
             ret[n] = np.array([regress([1,2,3,4,5],ys)[0] for ys in zip(pprev , prev , cur , next, nnext)])
         return ret
     #-- 初期化と前準備
     log,exp,cos,sin,sqrt,pi = np.log, np.exp, np.cos, np.sin, np.sqrt, np.pi
     alpha = self.PREEMCOEF
     L = self.CEPLIFTER
     ncep = 12   #-- self.NUMCEPS
     nfilt = self.NUMCHANS
     melfloor = 1.0
     Nw = int( round(fs*(self.WINDOWSIZE)/1000.0) )
     Ns = int( round(fs*(self.TARGETRATE)/1000.0) )
     nfft = 2**(int(log(Nw)/log(2))+1)
     def mel(hz):
       return 1127.01048*log(1.0 + hz/700.0)
     def mel2h(mel):
       return 700.0*exp(mel/1127.01048)-700.0
     #-- triangular filterbank with uniformly spaced filters on mel scal
     fbank = np.zeros( (nfft/2+1,nfilt) )
     klo,khi=2,nfft/2
     LOFREQ , HIFREQ = 0.0 , float(0.5*fs)
     mfreqs = np.linspace(mel(LOFREQ),mel(HIFREQ),nfilt+2)
     loChan = np.zeros(nfft/2+1)
     for chan in xrange(0 , nfilt+1):
        for k in xrange(int(mel2h(mfreqs[chan])*nfft/fs)+1 , int(mel2h(mfreqs[chan+1])*nfft/fs)+1):
          loChan[k+1] = chan
     loWt = np.zeros(nfft/2+1)
     for k in xrange(klo,khi+1):
        chan = loChan[k]
        wt = ( mfreqs[chan+1]-mel((k-1)*fs/float(nfft)) )/(mfreqs[chan+1]-mfreqs[chan])
        loWt[k] = wt
        if chan>0:fbank[k-1][chan-1] = wt
        if chan<nfilt:fbank[k-1][chan] = 1.0-wt
     #-- DCT matrix
     DCTmat = np.zeros( (ncep , nfilt) )
     for i in xrange(ncep):
        DCTmat[i] = cos(pi*float(i+1)/nfilt * np.arange(0.5 , float(nfilt)+0.5 , 1.0 , 'd'))
     DCTmat *= sqrt(2.0/nfilt)
     lifter = 1.0 + 0.5*L*sin(pi*np.arange(1,ncep+1)/L)
     hamWin = np.hamming(Nw)
     #-- メイン処理
     if dat.ndim==1:
        speech = dat
     elif dat.ndim==2:  #-- stereo
        if self.STEREOMODE=='R':
           speech = dat[1]
        elif self.STEREOMODE=='L':
           speech = dat[0]
        else:  #-- errorにはしない
           speech = dat[0]
     else:
        assert(False),'invalid ndim of input signal:ndim=%d' % dat.ndim
     nframe = (len(speech)-Nw)/Ns + 1
     mfcc = np.zeros( (nframe , 39) )
     logEs = np.zeros(nframe)
     for i in xrange(nframe):
        #-- 末尾のframeはpaddingしない
        frame = speech[i*Ns:i*Ns+Nw]
        if self.ZMEANSOURCE:frame = frame - sum(frame)/len(frame)
        #-- 高域強調
        frame[1:] = frame[1:] - alpha*frame[0:-1]
        frame[0] = frame[0]*(1.0-alpha)
        #-- windowing
        frame = frame*hamWin
        if self.RAWENERGY:
           mfcc[i][12] = log(sum([x*x for x in dat[i*Ns:i*Ns+Nw]]))
        else:
           mfcc[i][12] = log(sum([x*x for x in frame]))
        MAG = np.abs( np.fft.rfft(frame , nfft) )
        #-- log filterbank amplitude
        FBE = log( np.dot(MAG , fbank).clip(melfloor , np.inf) )
        mfcc[i][:12] = lifter*np.dot(FBE , DCTmat.T)
     #-- ZeroMean Shift
     mfcc = mfcc.T
     for j in xrange(ncep):
         mfcc[j] -= sum(mfcc[j])/float(nframe)
     mfcc = mfcc.T
     mfcc[:,13:26] = delta(mfcc[:,0:13])
     mfcc[:,26:39] = delta(mfcc[:,13:26])
     return mfcc


#test
if __name__=="__main__":
    wfst = wfstFromFile( open("csj-3gram-v30k-mpe-mix32.hloop.hclg.lmw10.asciiid.wfst") )
    wfst.readConfig( open("dcd.config") )
    spdfs = spdfsFromFile( open("hmm.spdfs") )
    mfcc39 = MFCC39()
    feas = mfcc39(open('onseininsikinokenkyuwoshiteimasu.wav','rb'))
    out = decode(wfst , feas , spdfs)
    print out

"""

