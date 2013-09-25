#-*- coding:utf-8 -*-
import numpy as np
from numpy import exp,sqrt
from numpy.linalg import eigh,cholesky,inv
import ctypes
from ctypes import c_double,c_long
from copy import deepcopy
import time
M_PI = np.pi


libhf = ctypes.cdll.LoadLibrary("libhf.so")
__computeERI__ = libhf.computeERI
__computeERI__.restype = c_double

Fgamma = libhf.Fgamma
Fgamma.restype = c_double


"""
原始Gauss基底
each primitive gauss-type basis:
norm*(x-x0)^nx*(y-y0)^ny*(z-z0)^nz*exp( alpha*( (x-x0)**2 + (y-y0)**2 + (z-z0)**2 ) )

長さの単位は、a.u./bohr
1 bohr = 0.52917721092(17) nm

"""
class PrimitiveBasis:
   def __init__(self):
      self.nx = 0
      self.ny = 0
      self.nz = 0
      self.x0 = 0.0
      self.y0 = 0.0
      self.z0 = 0.0
      self.alpha = 0,0
      self.norm = 0.0    #-- normalized coefficient
   def __repr__(self):
      return str(self.__dict__)


class Atoms:
   def __init__(self):
      self.nucleus = []  #-- list of (atom no,x,y,z) of atomic nucleus
      self.basis = []    #-- list of 縮約Gauss基底 , 縮約Gauss基底=list of 原始Gauss基底


def rysint(degree , X , fn):
   roots = (c_double * degree)()
   weights = (c_double * degree)()
   computeRysParams(ctypes.c_ulong(degree) , c_double(X) , ctypes.cast(roots,ctypes.POINTER(c_double)) , ctypes.cast(weights,ctypes.POINTER(c_double)))
   s = 0.0
   for i in xrange(0 , degree):
       t = roots[i]/(1+roots[i])
       s += fn(t)*weights[i]
   return s


#-- 二項係数
def binomial(n , k):
   dn = reduce(lambda x,y:x*y , range(k+1,n+1),1)
   nm = reduce(lambda x,y:x*y , range(1,n-k+1),1)
   return dn/nm


#-- 一般化固有値問題
def geneig(H , S):
    R = inv(cholesky(S))
    val,vec = eigh(R*H*R.T)
    vec = (R.T)*vec
    return val,vec

"""
overlap integral using Obara-Saika scheme
"""
def overlap(p , q):
  def overlap1D(a , b , x1 , x2 , n , m):
      if n<0 or m <0:
          return 0.0
      elif n==0 and m==0:
          return 1.0
      elif n>0:
          t1 = -b*(x1-x2)*overlap1D(a,b,x1,x2,n-1,m)
          t2 = (n-1)*overlap1D(a,b,x1,x2,n-2,m)+m*overlap1D(a,b,x1,x2,n-1,m-1)
          return (t1+0.5*t2)/(a+b)
      else:
          assert(n==0 and m>0)
          t1 = a*(x1-x2)*overlap1D(a,b,x1,x2,n,m-1)
          t2 = (m-1)*overlap1D(a,b,x1,x2,n,m-2)
          return (t1+0.5*t2)/(a+b)
  Sx = overlap1D(p.alpha , q.alpha , p.x0 , q.x0 , p.nx , q.nx)
  Sy = overlap1D(p.alpha , q.alpha , p.y0 , q.y0 , p.ny , q.ny)
  Sz = overlap1D(p.alpha , q.alpha , p.z0 , q.z0 , p.nz , q.nz)
  eta = p.alpha + q.alpha
  K = pow(M_PI/eta,1.5)*exp(-(p.alpha)*(q.alpha)*((p.x0-q.x0)**2+(p.y0-q.y0)**2+(p.z0-q.z0)**2)/eta)
  return (p.norm)*(q.norm)*K*(Sx*Sy*Sz)


#-- kinetic integral
def kinetic(p , q):
    def shift(p , key , val):
       ret = deepcopy(p)
       ret.__dict__[key] += val
       return ret
    t1 = q.alpha*(2*(q.nx+q.ny+q.nz)+3)*overlap(p , q)
    t2 = -2*pow(q.alpha , 2)*(overlap(p , shift(q, "nx" , +2)) + overlap(p , shift(q, "ny" , +2)) + overlap(p , shift(q, "nz" , +2)))
    tx = (q.nx-1)*q.nx*overlap(p , shift(q, "nx" , -2))
    ty = (q.ny-1)*q.ny*overlap(p , shift(q, "ny" , -2))
    tz = (q.nz-1)*q.nz*overlap(p , shift(q, "nz" , -2))
    #normはoverlap内で織り込み済
    return ( t1+t2-0.5*(tx+ty+tz) )



"""
Nuclear Attraction Integral by McMurchie–Davidson Scheme

atno:原子番号
Cx/Cy/Cz:原子のx/y/z座標
"""
def computeNAI(p , q , atno , Cx, Cy, Cz):
    gamma = p.alpha + q.alpha
    r2 = (p.x0-q.x0)**2+(p.y0-q.y0)**2+(p.z0-q.z0)**2
    Px = (p.alpha*p.x0 + q.alpha*q.x0)/gamma
    Py = (p.alpha*p.y0 + q.alpha*q.y0)/gamma
    Pz = (p.alpha*p.z0 + q.alpha*q.z0)/gamma
    X = (p.alpha + q.alpha)*((Cx-Px)**2+(Cy-Py)**2+(Cz-Pz)**2)
    K = exp(-p.alpha*q.alpha*r2/gamma)
    def E(i,j,t,Pxyz,Axyz,Bxyz):
       if  t<0 or (t>i+j):
          return 0.0
       elif i>0:
          return 0.5*E(i-1,j,t-1,Pxyz,Axyz,Bxyz)/gamma + (Pxyz-Axyz)*E(i-1,j,t,Pxyz,Axyz,Bxyz) + (t+1)*E(i-1,j,t+1,Pxyz,Axyz,Bxyz)
       elif j>0:
          return 0.5*E(i,j-1,t-1,Pxyz,Axyz,Bxyz)/gamma + (Pxyz-Bxyz)*E(i,j-1,t,Pxyz,Axyz,Bxyz) + (t+1)*E(i,j-1,t+1,Pxyz,Axyz,Bxyz)
       else:
          assert(i==0 and j==0 and t==0)
          return 1.0
    def R(t,u,v,N):
       if t<0 or u<0 or v<0:
          return 0.0
       elif t>0:
          return (t-1)*R(t-2,u,v,N+1)+(Px-Cx)*R(t-1,u,v,N+1)
       elif u>0:
          return (u-1)*R(t,u-2,v,N+1)+(Py-Cy)*R(t,u-1,v,N+1)
       elif v>0:
          return (v-1)*R(t,u,v-2,N+1)+(Pz-Cz)*R(t,u,v-1,N+1)
       else:
          assert(t==0 and u==0 and v==0)
          return pow(-2*gamma,N) * Fgamma(N,c_double(X))
    s = 0.0
    ex = [E(p.nx , q.nx , t , Px , p.x0 , q.x0) for t in xrange(0 , p.nx+q.nx+1)]
    ey = [E(p.ny , q.ny , u , Py , p.y0 , q.y0) for u in xrange(0 , p.ny+q.ny+1)]
    ez = [E(p.nz , q.nz , v , Pz , p.z0 , q.z0) for v in xrange(0 , p.nz+q.nz+1)]
    for t in xrange(0 , p.nx+q.nx+1):
       for u in xrange(0 , p.ny+q.ny+1):
          for v in xrange(0 , p.nz+q.nz+1):
             s += (ex[t] * ey[u] * ez[v] * R(t,u,v,0))
    return -atno*(p.norm)*(q.norm)*(2*M_PI/gamma)*K*s


"""
Electron Repulsion Integral

現在最速のアルゴリズムは
The prism algorithm for two-electron integrals
http://rscweb.anu.edu.au/~pgill/papers/026PRISM.pdf

"""
def computeERI(a , b ,  c ,  d):
   t = __computeERI__(
         c_double(a.x0),
         c_double(a.y0),
         c_double(a.z0),a.nx,a.ny,a.nz,
         c_double(a.alpha) , 
         c_double(b.x0),
         c_double(b.y0),
         c_double(b.z0),b.nx,b.ny,b.nz,
         c_double(b.alpha) , 
         c_double(c.x0),
         c_double(c.y0),
         c_double(c.z0),c.nx,c.ny,c.nz,
         c_double(c.alpha) , 
         c_double(d.x0),
         c_double(d.y0),
         c_double(d.z0),d.nx,d.ny,d.nz,
         c_double(d.alpha))
   return (a.norm)*(b.norm)*(c.norm)*(d.norm)*t




#-- Huckel法
def guessHuckel(atoms):
   Nbasis = len(atoms.basis)
   S , H =  np.matrix(np.zeros((Nbasis,Nbasis))) , np.matrix(np.zeros((Nbasis,Nbasis)))
   for i,v in enumerate(atoms.basis):
      for j,w in enumerate(atoms.basis):
          sval = 0.0
          kinval = 0.0
          naival = 0.0
          for pf in v:
              for qf in w:
                  sval += overlap(pf , qf)
                  kinval += kinetic(pf , qf)
                  for (AN,Ax,Ay,Az) in atoms.nucleus:
                      naival += computeNAI(pf , qf , AN  , Ax , Ay , Az)
          S[i,j] = sval
          H[i,j] = kinval + naival
   #-- solve H x = E S x
   return geneig(H , S)



#-- RHF calculation
def runRHF(atoms , init=None , N_occ=-1, maxiter=50 , opttol=1.0e-5):
   Nbasis = len(atoms.basis)
   S , P , H = np.matrix(np.zeros((Nbasis,Nbasis))) , np.matrix(np.zeros((Nbasis,Nbasis))) , np.matrix(np.zeros((Nbasis,Nbasis))) 
   energy , old_energy = 0.0 , 0.0
   mix = 0.0   #-- 今は意味がない
   #-- initialization
   if N_occ==-1:N_occ = sum([n for (n,_,_,_) in atoms.nucleus])/2
   for i,v in enumerate(atoms.basis):
      for j,w in enumerate(atoms.basis):
          sval = 0.0
          kinval = 0.0
          naival = 0.0
          for pf in v:
              for qf in w:
                  sval += overlap(pf , qf)
                  kinval += kinetic(pf , qf)
                  for (AN,Ax,Ay,Az) in atoms.nucleus:
                      naival += computeNAI(pf , qf , AN  , Ax , Ay , Az)
          S[i,j] = sval
          H[i,j] = kinval + naival
   En = 0.0
   for c1,(n1,x1,y1,z1) in enumerate(atoms.nucleus):
       for c2,(n2,x2,y2,z2) in enumerate(atoms.nucleus):
           if c1<=c2:continue
           En += n1*n2/sqrt((x1-x2)**2+(y1-y2)**2+(z1-z2)**2)
   if init is None:
      #-- Huckel近似による初期状態
      _,C = geneig(H,S)
      for p in xrange(Nbasis):
         for q in xrange(Nbasis):
            for k in xrange(N_occ):
               P[p,q] += C[p,k]*C[q,k]
   else:
      for p in xrange(Nbasis):
         for q in xrange(Nbasis):
            for k in xrange(N_occ):
               P[p,q] += init[p,k]*init[q,k]
   #-- main loop
   F = np.matrix(np.zeros((Nbasis,Nbasis)))
   start_time = time.clock()
   for iter in xrange(maxiter):
        #-- copy matrix
        for i in xrange(Nbasis):
           for j in xrange(Nbasis):
               F[i,j] = H[i,j]
        #-- compute ERI
        for i,ei in enumerate(atoms.basis):
           for j,ej in enumerate(atoms.basis):
              for k,ek in enumerate(atoms.basis):
                  for l,el in enumerate(atoms.basis):
                        ijkl = 0.0
                        for pf in ei:
                           for qf in ej:
                              for rf in ek:
                                 for sf in el:
                                      ijkl += computeERI(pf , qf , rf , sf)
                        F[i,j] += 2.0*P[k,l]*ijkl
                        F[i,l] += -P[k,j]*ijkl
        Es,C = geneig(F , S)
        for p in xrange(Nbasis):
           for q in xrange(Nbasis):
               P[p,q] *= mix
               for k in xrange(N_occ):
                   P[p,q] += (1.0-mix)*C[p,k]*C[q,k]
        old_energy = energy
        energy = En + Es[:N_occ].sum() + np.trace(P*H.T)
        if iter>0 and abs(old_energy - energy)<opttol:
            end_time = time.clock()
            return (energy,C,True,end_time-start_time)
   end_time = time.clock()
   return (energy,C,False,end_time-start_time)


"""
g94フォーマットの基底関数データを読み込む


基底関数セットは、例えば
EMSL Basis Set Exchange
https://bse.pnl.gov/bse/portal
で、様々なフォーマットで配布されている
"""
def readBasis_g94(fp):
    ret = {}
    atoms = [None , "H","He","Li","Be","B","C","N","O","F","Ne","Na","Mg","Al","Si","P","S","Cl","Ar","K","Ca","Sc","Ti"]
    lines = [line for line in fp if line[0]!='!' and len(line.strip())>0][1:]
    idx = 0
    while True:
        if idx==len(lines):break
        atomname = lines[idx].split()[0]
        assert(atomname in atoms),"未知の原子"
        atno = atoms.index(atomname)
        idx += 1
        ret[atno] = []
        while True:
            ls = lines[idx].split()
            if len(ls)<2:
               idx+=1
               break
            orbtype = list(ls[0])
            contnum = int(ls[1])
            for c,orb in enumerate( orbtype ):
               ndata = []
               for i in xrange(contnum):
                  ls = lines[idx+i+1].split()
                  ndata.append( (float(ls[0]) , float(ls[c+1])) )
               ret[atno].append( (orb , ndata) )
            idx+=(contnum+1)
    return ret


"""
各原子核の原子番号と座標情報と基底関数セットから、Atomsクラスを構築する
"""
def Molecule(nucleus , basisSet):
   def fact2(n):
       return reduce(lambda x,y:x*y , range(1,n+1,2) , 1)
   atoms = Atoms()
   atoms.nucleus = deepcopy(nucleus)
   Lname = ["S" , "P" , "D" , "F"]
   for (atno , ax , ay , az) in nucleus:
       assert(basisSet.has_key(atno)) , ("基底関数セットに必要な情報が含まれていない(%d)" % atno)
       for (orbtype , params) in basisSet[atno]:
           assert(orbtype in Lname) , ("未知の軌道(%s)" % orbtype)
           Lidx = Lname.index(orbtype)  #-- 主量子数-1
           for nx in xrange(Lidx+1):
               for ny in xrange(Lidx+1):
                   for nz in xrange(Lidx+1):
                        if nx+ny+nz!=Lidx:continue
                        MO = []
                        for (exponent,coeff) in params:
                            pb = PrimitiveBasis()
                            pb.nx , pb.ny , pb.nz = nx,ny,nz
                            pb.x0 , pb.y0 , pb.z0 = ax,ay,az
                            pb.alpha = exponent
                            norm2 = pow(2*exponent/M_PI,1.5)*pow(2,2*(nx+ny+nz))*pow(exponent,nx+ny+nz)/(fact2(2*nx-1)*fact2(2*ny-1)*fact2(2*nz-1))
                            pb.norm = sqrt(norm2)*coeff
                            MO.append(pb)
                        atoms.basis.append( MO )
   return atoms



if __name__=="__main__":
   def angstrom2bohr(r):
      return (r)*1.8897261249935898
   basisSet = readBasis_g94(open('631g.g94'))
   H2 = Molecule([(1 , 0.0 , 0.0 , 0.0) , (1 , angstrom2bohr(0.74114) , 0.0 , 0.0)] , basisSet)
   E,C,check,t = runRHF(H2)
   assert(check),"SCF計算が収束していない"
   print("水素分子のエネルギー: %2.5f(hartree) SCF計算時間:%2.2f(s)" % (E,t))
   basisSet = readBasis_g94(open('sto3g.g94'))
   H2O_nm = [ (8 , -0.332 , 0.440 , -0.016) , (1 , 0.596 , 0.456 , 0.228) , (1,-0.596 , -0.456 , -0.228) ]
   H2O = Molecule([ (n,angstrom2bohr(x),angstrom2bohr(y),angstrom2bohr(z)) for (n,x,y,z) in H2O_nm ] , basisSet)
   E,C,check,t = runRHF(H2O)
   assert(check),"SCF計算が収束していない"
   print("H2O分子のエネルギー: %2.5f(hartree) SCF計算時間:%2.2f(s)" % (E,t))


