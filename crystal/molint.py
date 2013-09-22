#-*- coding:utf-8 -*-
import numpy as np
from numpy import exp,sqrt
from numpy.linalg import eigh,cholesky,inv
import ctypes
from copy import deepcopy
M_PI = np.pi


librys = ctypes.cdll.LoadLibrary("libhf.so")
computeRysParams = librys.computeRysParams


"""
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
   roots = (ctypes.c_double * degree)()
   weights = (ctypes.c_double * degree)()
   computeRysParams(ctypes.c_ulong(degree) , ctypes.c_double(X) , ctypes.cast(roots,ctypes.POINTER(ctypes.c_double)) , ctypes.cast(weights,ctypes.POINTER(ctypes.c_double)))
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


#-- overlap integral
def overlap(p , q):
  def overlap1D(a , b , x1 , x2 , n , m):
      if n<0 or m <0:
          return 0.0
      elif n==0 and m==0:
          return sqrt(M_PI/(a+b))*exp(-a*b*(x1-x2)*(x1-x2)/(a+b))
      elif n==1 and m==0:
          return -b*(x1-x2)*overlap1D(a,b,x1,x2,0,0)/(a+b)
      elif n==0 and m==1:
          return a*(x1-x2)*overlap1D(a,b,x1,x2,0,0)/(a+b)
      elif n==1 and m==1:
          t1 = 0.5*pow(M_PI/((a+b)*(a+b)*(a+b)) , 0.5)*exp(-a*b*(x1-x2)*(x1-x2)/(a+b))
          t2 = a*b*(x1-x2)*(x1-x2)*overlap1D(a,b,x1,x2,0,0)/((a+b)*(a+b))
          return t1-t2
      elif n>=2:
          t1= -b*(x1-x2)*overlap1D(a,b,x1,x2,n-1,m)
          t2 = 0.5*(n-1)*overlap1D(a,b,x1,x2,n-2,m)
          return (t1+t2)/(a+b)
      else:
          assert(m>=2)
          t1 = a*(x1-x2)*overlap1D(a,b,x1,x2,n,m-1)
          t2 = 0.5*(m-1)*overlap1D(a,b,x1,x2,n,m-2)
          return (t1+t2)/(a+b)
  Sx = overlap1D(p.alpha , q.alpha , p.x0 , q.x0 , p.nx , q.nx)
  Sy = overlap1D(p.alpha , q.alpha , p.y0 , q.y0 , p.ny , q.ny)
  Sz = overlap1D(p.alpha , q.alpha , p.z0 , q.z0 , p.nz , q.nz)
  return (p.norm)*(q.norm)*(Sx*Sy*Sz)


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
    #normはoverlap内で計算済
    return ( t1+t2-0.5*(tx+ty+tz) )



"""
 Nuclear Attraction Integral by Gauss-Rys integrator
atno:原子番号
Ax/Ay/Az:原子のx/y/z座標

"""
def computeNAI(p , q , atno , Ax, Ay, Az):
    def computeNAI1D(t , a , b , xa , xb , xC , xp , p):
       if a < 0 or b < 0:
          return 0.0
       elif a==0 and b==0:
          return 1.0
       elif b>0:
          t1 = computeNAI1D(t , a+1 , b-1 , xa , xb , xC, xp , p)
          t2 = (xa-xb)*computeNAI1D(t , a , b-1 , xa , xb , xC , xp , p)
          return t1+t2
       else:
          assert(a> 0 and b==0)
          t1 = (xp-xa-(xp-xC)*t)*computeNAI1D(t , a-1 , 0 , xa , xb , xC , xp , p)
          t2 = (a-1)*(1-t)*computeNAI1D(t , a-2 , 0 , xa , xb , xC , xp , p)
          return t1+t2
    def fn(t,xp,yp,zp,gamma):
       Ix = computeNAI1D(t, p.nx, q.nx, p.x0, q.x0, Ax, xp, gamma)
       Iy = computeNAI1D(t, p.ny, q.ny, p.y0, q.y0, Ay, yp, gamma)
       Iz = computeNAI1D(t, p.nz, q.nz, p.z0, q.z0, Az, zp, gamma)
       return Ix*Iy*Iz
    deg = (p.nx+p.ny+p.nz+q.nx+q.ny+q.nz)/2+1
    gamma = p.alpha + q.alpha
    r2 = (p.x0-q.x0)**2+(p.y0-q.y0)**2+(p.z0-q.z0)**2
    Ex = (p.alpha*p.x0 + q.alpha*q.x0)/(p.alpha+q.alpha)
    Ey = (p.alpha*p.y0 + q.alpha*q.y0)/(p.alpha+q.alpha)
    Ez = (p.alpha*p.z0 + q.alpha*q.z0)/(p.alpha+q.alpha)
    X = (p.alpha + q.alpha)*((Ax-Ex)**2+(Ay-Ey)**2+(Az-Ez)**2)
    return atno*(p.norm)*(q.norm)*(-2*M_PI/gamma)*exp(-p.alpha*q.alpha*r2/gamma)*rysint(deg , X ,lambda t:fn(t,Ex,Ey,Ez,gamma))


"""
Electron Repulsion Integral by Gauss-Rys integrator
"""
def computeERI(a , b ,  c ,  d):
   def computeERI1D(t , i , j , k , l , xi , xj , xk , xl , ai , aj , ak , al):
       n , m = i+j , k+l
       if n==0 and m==0:return 1.0
       A,B = ai+aj , ak+al
       Px ,Qx = (ai*xi+aj*xj)/A , (ak*xk+al*xl)/B
       fff = t/(A+B)
       C10 = (Px-xi) + B*(Qx-Px)*fff
       C01 = (Qx-xk) - A*(Qx-Px)*fff
       if n==1 and j==0 and m==0:return C10
       if m==1 and l==0 and n==0:return C01
       B00 = 0.5*fff
       B10 = (1-B*fff)/(2*A)
       B01 = (1-A*fff)/(2*B)
       G = np.zeros((n+2,m+2))
       G[0,0],G[1,0],G[0,1] = 1.0 , C10 , C01
       for a in xrange(2,n+1):G[a,0] = B10*(a-1)*G[a-2,0] + C10*G[a-1,0]
       for b in xrange(2,m+1):G[0,b] = B01*(b-1)*G[0,b-2] + C01*G[0,b-1]
       for a in xrange(1,n+1):
           G[a,1] = a*B00*G[a-1,0] + C01*G[a,0]
           for b in xrange(1,m+1):
               G[a,b] = B01*(b-1)*G[a,b-2] + a*B00*G[a-1,b-1] + C01*G[a,b-1]
       #-- compute I(i,j,k,l) from I(n,0,m,0)=G[n][m]
       ret = G[n,m]
       if j==0 and l==0:
          return ret
       else:
          for m in xrange(0,l+1):
             ijm0 = 0.0
             for n in xrange(0,j+1):
                ijm0 += binomial(j,n)*pow(xi-xj,j-n)*G[n+1,m+k]
             ret += binomial(l,m)*pow(xk-xl,l-m)*ijm0
          return ret
   def fn(t):
      Ix = computeERI1D(t , a.nx,b.nx,c.nx,d.nx , a.x0,b.x0,c.x0,d.x0 , a.alpha,b.alpha,c.alpha,d.alpha)
      Iy = computeERI1D(t , a.ny,b.ny,c.ny,d.ny , a.y0,b.y0,c.y0,d.y0 , a.alpha,b.alpha,c.alpha,d.alpha)
      Iz = computeERI1D(t , a.nz,b.nz,c.nz,d.nz , a.z0,b.z0,c.z0,d.z0 , a.alpha,b.alpha,c.alpha,d.alpha)
      return Ix*Iy*Iz
   A,B = a.alpha + b.alpha , c.alpha + d.alpha
   invA,invB,rho = 1.0/A , 1.0/B , A*B/(A+B)
   rab2 = (a.x0-b.x0)**2 + (a.y0-b.y0)**2 + (a.z0-b.z0)**2
   rcd2 = (c.x0-d.x0)**2 + (c.y0-d.y0)**2 + (c.z0-d.z0)**2
   #-- 34.98683665524972 = 2*pow(np.pi , 2.5)
   K = 34.98683665524972*exp(-a.alpha*b.alpha*rab2*invA - c.alpha*d.alpha*rcd2*invB)
   K /= A*B*sqrt(A+B)
   if K<1.0e-10:return 0.0
   degree = (a.nx+b.nx+c.nx+d.nx+a.ny+b.ny+c.ny+d.ny+a.nz+b.nz+c.nz+d.nz)/2 + 1
   xp = (a.alpha*a.x0 + b.alpha*b.x0)*invA
   yp = (a.alpha*a.y0 + b.alpha*b.y0)*invA
   zp = (a.alpha*a.z0 + b.alpha*b.z0)*invA
   xq = (c.alpha*c.x0+d.alpha*d.x0)*invB
   yq = (c.alpha*c.y0+d.alpha*d.y0)*invB
   zq = (c.alpha*c.z0+d.alpha*d.z0)*invB
   rpq2 = (xp-xq)*(xp-xq)+(yp-yq)*(yp-yq)+(zp-zq)*(zp-zq)
   X = rpq2*rho
   return K*(a.norm)*(b.norm)*(c.norm)*(d.norm)*rysint(degree , X, fn)


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
          S[(i,j)] = sval
          H[(i,j)] = kinval + naival
   #-- solve H x = E S x
   return geneig(H , S)



#-- RHF calculation
def runRHF(atoms , initC , N_occ=-1, maxiter=50 , opttol=1.0e-5):
   Nbasis = len(atoms.basis)
   S , P , H = np.matrix(np.zeros((Nbasis,Nbasis))) , np.matrix(np.zeros((Nbasis,Nbasis))) , np.matrix(np.zeros((Nbasis,Nbasis))) 
   energy , old_energy = 0.0 , 0.0
   mix = 0.0   #-- 今は意味がない
   #-- initialization
   if N_occ==-1:N_occ = sum([n for (n,_,_,_) in atoms.nucleus])/2
   for p in xrange(Nbasis):
      for q in xrange(Nbasis):
         for k in xrange(N_occ):
            P[(p,q)] += initC[(p,k)]*initC[(q,k)]
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
          S[(i,j)] = sval
          H[(i,j)] = kinval + naival
   En = 0.0
   for c1,(n1,x1,y1,z1) in enumerate(atoms.nucleus):
       for c2,(n2,x2,y2,z2) in enumerate(atoms.nucleus):
           if c1<=c2:continue
           En+= n1*n2/sqrt((x1-x2)**2+(y1-y2)**2+(z1-z2)**2)
   #-- main loop
   F = np.matrix(np.zeros((Nbasis,Nbasis)))
   for iter in xrange(maxiter):
        #-- copy matrix
        for i in xrange(Nbasis):
           for j in xrange(Nbasis):
               F[(i,j)] = H[(i,j)]
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
                        F[i,j] += 2.0*P[(k,l)]*ijkl
                        F[i,l] += -P[(k,j)]*ijkl
        Es,C = geneig(F , S)
        for p in xrange(Nbasis):
           for q in xrange(Nbasis):
               P[(p,q)] *= mix
               for k in xrange(N_occ):
                   P[(p,q)] += (1.0-mix)*C[(p,k)]*C[(q,k)]
        old_energy = energy
        energy = Es[:N_occ].sum()
        for p in xrange(Nbasis):
            for q in xrange(Nbasis):
                energy += P[p,q]*H[p,q]
        if iter>0 and abs(old_energy - energy)<opttol:
            return (En+energy,C,True)
   return (En+energy,C,False)


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
            ndata = []
            for c,orb in enumerate( orbtype ):
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
                            norm = sqrt(pow(2,2*(nx+ny+nz)+1.5)*pow(exponent,nx+ny+nz+1.5)/(fact2(2*nx-1)*fact2(2*ny-1)*fact2(2*nz-1)*pow(M_PI,1.5)))
                            pb.norm = norm*coeff
                            MO.append(pb)
                        atoms.basis.append( MO )
   return atoms



if __name__=="__main__":
   def angstrom2bohr(r):
      return (r)*1.8897261249935898
   basisSet = readBasis_g94(open('631g.g94'))
   H2 = Molecule([(1 , 0.0 , 0.0 , 0.0) , (1 , angstrom2bohr(0.74114) , 0.0 , 0.0)] , basisSet)
   _,C = guessHuckel(H2)
   E,C,check = runRHF(H2 , C)
   assert(check),"SCF計算が収束していない"
   print("水素分子の結合エネルギー: %2.5f(hartree)" % E)


