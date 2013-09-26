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
   __slots__ = ['nx','ny','nz','x0','y0','z0','alpha','norm']
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


"""
縮約Gauss基底のC/C++コード側でのデータ型
"""
class CGaussBasis(ctypes.Structure):
   __fields__ = [("nx" , c_long),
                 ("ny" , c_long),
                 ("nz" , c_long),
                 ("x" , c_double),
                 ("y" , c_double),
                 ("z" , c_double),
                 ("norms" , ctypes.POINTER(c_double)),
                 ("exponents" , ctypes.POINTER(c_double)),
                 ("length" , c_long)]


"""
Contracted Gauss-type Basis
each contracted gauss-type basis:
\sum_{I=0}^{L-1} norms[I]*(x-x0)^nx*(y-y0)^ny*(z-z0)^nz*exp( exponents[I]*( (x-x0)**2 + (y-y0)**2 + (z-z0)**2 ) )

長さの単位は、a.u./bohr
1 bohr = 0.52917721092(17) nm
"""
class GaussBasis:
   __slots__ = ['nx','ny','nz','x','y','z']
   def __init__(self , _nx,_ny,_nz,_x,_y,_z):
      self.nx = _nx
      self.ny = _ny
      self.nz = _nz
      self.x = _x
      self.y = _y
      self.z = _z
      self.exponents = []
      self.norms = []
   def __repr__(self):
      return str(self.__dict__)
   def __len__(self):
      assert(len(self.exponents)==len(self.norms))
      return len(self.exponents)
   def __iter__(self):
      for (norm,alpha) in zip(self.norms,self.exponents):
         pb = PrimitiveBasis()
         pb.nx , pb.ny , pb.nz = self.nx , self.ny , self.nz
         pb.x0 , pb.y0 , pb.z0 = self.x , self.y , self.z
         pb.norm , pb.alpha = norm , alpha 
         yield pb
   def ctype(self):
      _norms = (c_double * len(self.norms))()
      _exponents = (c_double * len(self.exponents))()
      for i,norm in enumerate(self.norms):
         _norms[i] = norm
      for i,exponent in enumerate(self.exponents):
         _exponents[i] = exponent
      rawdata = CGaussBasis(nx=self.nx , 
                            ny=self.ny , 
                            nz=self.nz ,
                            x=c_double(self.x) , 
                            y=c_double(self.y) , 
                            z=c_double(self.z) , 
                            norms=ctypes.cast(_norms , ctypes.POINTER(c_double)),
                            exponents=ctypes.cast(_exponents , ctypes.POINTER(c_double)),
                            length=len(self.norms) )
      return rawdata


class Atoms:
   def __init__(self):
      self.nucleus = []  #-- list of (atom no,x,y,z) of atomic nucleus
      self.basis = []    #-- list of 縮約Gauss基底


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

よりよいアルゴリズムの候補
Two-Electron Repulsion Integrals Over Gaussian s Functions
http://rsc.anu.edu.au/~pgill/papers/025ssss.pdf

The prism algorithm for two-electron integrals
http://rscweb.anu.edu.au/~pgill/papers/026PRISM.pdf

A Tensor Approach to Two-Electron Matrix Elements
http://rsc.anu.edu.au/~pgill/papers/061COLD.pdf


"""
def computeERI(a , b ,  c ,  d):
   t = __computeERI__(
       a.x,a.y,a.z,
       a.nx,a.ny,a.nz,
       a.exponents,
       a.norms,
       a.length,
       b.x,b.y,b.z,
       b.nx,b.ny,b.nz,
       b.exponents,
       b.norms,
       b.length,
       c.x,c.y,c.z,
       c.nx,c.ny,c.nz,
       c.exponents,
       c.norms,
       c.length,
       d.x,d.y,d.z,
       d.nx,d.ny,d.nz,
       d.exponents,
       d.norms,
       d.length)
   return t



#-- RHF calculation
def runRHF(atoms , init=None , N_occ=-1, maxiter=50 , opttol=1.0e-5):
   Nbasis = len(atoms.basis)
   S , P , H = np.matrix(np.zeros((Nbasis,Nbasis))) , np.matrix(np.zeros((Nbasis,Nbasis))) , np.matrix(np.zeros((Nbasis,Nbasis))) 
   energy , old_energy = 0.0 , 0.0
   mix = 0.0   #-- 今は意味がない
   cbasis = [b.ctype() for b in atoms.basis]
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
        for i,ei in enumerate(cbasis):
           for j,ej in enumerate(cbasis):
              for k,ek in enumerate(cbasis):
                  for l,el in enumerate(cbasis):
                        if i<j or k<l:continue
                        ijkl = computeERI(ei,ej,ek,el)
                        F[i,j] += 2.0*P[k,l]*ijkl
                        F[i,l] += -P[k,j]*ijkl
                        """
                          (ij|kl) = (ji|kl) = (ij|lk) = (ji|kl) = 
                          (kl|ij) = (lk|ij) = (lk|ji) = (kl|ji)
                        """
                        if i!=j and k!=l:
                           F[j,i] += 2.0*P[k,l]*ijkl
                           F[j,l] += -P[k,i]*ijkl
                           F[i,j] += 2.0*P[l,k]*ijkl
                           F[i,k] += -P[l,j]*ijkl
                           F[j,i] += 2.0*P[l,k]*ijkl
                           F[j,k] += -P[l,i]*ijkl
                        elif i!=j:
                           F[j,i] += 2.0*P[k,l]*ijkl
                           F[j,l] += -P[k,i]*ijkl
                        elif k!=l:
                           F[i,j] += 2.0*P[l,k]*ijkl
                           F[i,k] += -P[l,j]*ijkl
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
各原子核の原子番号と座標情報と基底関数セットから、Atomsクラスを構築する
"""
def Molecule(nucleus , basisSet):
   def fact2(n):
       return reduce(lambda x,y:x*y , range(1,n+1,2) , 1)
   atoms = Atoms()
   atoms.nucleus = deepcopy(nucleus)
   Lname = ["S" , "P" , "D" , "F"]
   for (atno , ax , ay , az) in nucleus:
       assert(basisSet.has_key(str(atno))) , ("基底関数セットに必要な情報が含まれていない(%d)" % atno)
       for (orbtype , params) in basisSet[str(atno)]:
           assert(orbtype in Lname) , ("未知の軌道(%s)" % orbtype)
           Lidx = Lname.index(orbtype)  #-- 主量子数-1
           for nx in xrange(Lidx+1):
               for ny in xrange(Lidx+1):
                   for nz in xrange(Lidx+1):
                        if nx+ny+nz!=Lidx:continue
                        MO = GaussBasis(nx,ny,nz,ax,ay,az)
                        for (exponent,coeff) in params:
                            MO.exponents.append( exponent )
                            norm2 = pow(2*exponent/M_PI,1.5)*pow(2,2*(nx+ny+nz))*pow(exponent,nx+ny+nz)/(fact2(2*nx-1)*fact2(2*ny-1)*fact2(2*nz-1))
                            MO.norms.append( sqrt(norm2)*coeff )
                        atoms.basis.append( MO )
   return atoms


import json
from util import *
if __name__=="__main__":
   def angstrom2bohr(r):
      return (r)*1.8897261249935898
   basisSet = json.load(open('basis/631g.js'))
   H2 = Molecule([(1 , 0.0 , 0.0 , 0.0) , (1 , angstrom2bohr(0.74114) , 0.0 , 0.0)] , basisSet)
   E,C,check,t = runRHF(H2)
   assert(check),"SCF計算が収束していない"
   print("水素分子のHFエネルギー: %2.5f(hartree) SCF計算時間:%2.2f(s)" % (E,t))
   #--
   basisSet = json.load(open('basis/631g.js'))
   H2O_nm = [ (8 , -0.332 , 0.440 , -0.016) , (1 , 0.596 , 0.456 , 0.228) , (1,-0.596 , -0.456 , -0.228) ]
   H2O = Molecule([ (n,angstrom2bohr(x),angstrom2bohr(y),angstrom2bohr(z)) for (n,x,y,z) in H2O_nm ] , basisSet)
   E,C,check,t = runRHF(H2O)
   assert(check),"SCF計算が収束していない"
   print("H2O分子のHFエネルギー: %2.5f(hartree) SCF計算時間:%2.2f(s)" % (E,t))
   #--
   basisSet = json.load(open('basis/sto3g.js'))
   CH4 = Molecule(readpdb('pdb/methane.pdb') , basisSet)
   E,C,check,t = runRHF(CH4)
   assert(check),"SCF計算が収束していない"
   print("メタンのHFエネルギー: %2.5f(hartree) SCF計算時間:%2.2f(s)" % (E,t))
