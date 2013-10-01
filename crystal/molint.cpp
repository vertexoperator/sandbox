#include "rysquad.h"
#include <math.h>
#include <omp.h>
#include "gammainc.hpp"

#ifndef M_PI
#define M_PI 3.1415926535897932384626433
#endif

#define MAXROOTS 13

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    long nx;
    long ny;
    long nz;
    double x;
    double y;
    double z;
    long length;
    double *norms;
    double *exponents;
} GaussBasis;

double Fm(int m, double X);

double computeERI(
    double xa,double ya,double za,int la,int ma,int na,double *alphaa , double *anorm , int La ,
    double xb,double yb,double zb,int lb,int mb,int nb,double *alphab , double *bnorm , int Lb ,
    double xc,double yc,double zc,int lc,int mc,int nc,double *alphac , double *cnorm , int Lc ,
    double xd,double yd,double zd,int ld,int md,int nd,double *alphad , double *dnorm , int Ld);

double computeeri_(
    double *xa,double *ya,double *za,long *la,long *ma,long *na,double *alphaa , double *anorm , long *La ,
    double *xb,double *yb,double *zb,long *lb,long *mb,long *nb,double *alphab , double *bnorm , long *Lb ,
    double *xc,double *yc,double *zc,long *lc,long *mc,long *nc,double *alphac , double *cnorm , long *Lc ,
    double *xd,double *yd,double *zd,long *ld,long *md,long *nd,double *alphad , double *dnorm , long *Ld);


void computeFockMatrix(GaussBasis *basis , int Nbasis , double *P , double *F);

#ifdef __cplusplus
}
#endif


static inline int binomial(int n , int k){
        int p=1;
        for(int i = n ; i > k ; i--)p *= i;
        for(int i = n-k ; i > 1 ; i--)p /= i;
        return p;
}


//molecular incomplete gamma function or boys function
//F_m(x) = \int_{0}^{1} t^{2*m} exp^{-x*t^2}dt
double Fm(int m, double X){

  double x = fmax(fabs(X),1.0e-10);
  return 0.5*tgamma(m+0.5)*pow(x,-m-0.5)*gammap(m+0.5 , x);
#if 0
  double roots[MAXROOTS],weights[MAXROOTS];

  computeRysParams(m+1 , X , roots, weights);

  double ret = 0.0;
  for(int i = 0; i < m+1 ; i++){
	double t = roots[i]/(1+roots[i]);
	ret += weights[i] * pow(t,m);
  }
  double x = fmax(fabs(X),1.0e-10);
  printf("%d , %lf,%lf\n",m , ret , 0.5*tgamma(m+0.5)*pow(x,-m-0.5)*gammap(m+0.5 , x));
  return ret;
#endif
}

double computeERI1D(double t,int i,int j,int k, int l,double xi,double xj,double xk,double xl,double ai,double aj,double ak,double al){
	int n,m,a,b;
	double A,B,Px,Qx,fff;
	double B00,B10,B01,C10,C01;
	double xij=xi-xj,xkl=xk-xl;
        double G[MAXROOTS][MAXROOTS];

	n = i+j;
	m = k+l;
	if(n==0 && m==0)return 1.0;

	A = ai+aj;
	B = ak+al;
	Px = (ai*xi+aj*xj)/A;
	Qx = (ak*xk+al*xl)/B;

	fff = t/(A+B);
	C10 = (Px-xi) + B*(Qx-Px)*fff;
	C01 = (Qx-xk) - A*(Qx-Px)*fff;
	if(n==1 && j==0 && m==0)return C10;
	if(m==1 && l==0 && n==0)return C01;
	B00 = 0.5*fff;
	B10 = (1-B*fff)/(2*A);
	B01 = (1-A*fff)/(2*B);

	G[0][0] = 1.0;
	G[1][0] = C10; 
	G[0][1] = C01;

	for (a=2; a<n+1; a++) G[a][0] = B10*(a-1)*G[a-2][0] + C10*G[a-1][0];
	for (b=2; b<m+1; b++) G[0][b] = B01*(b-1)*G[0][b-2] + C01*G[0][b-1];
	if ((m==0) || (n==0)) goto HRR;

	for (a=1; a<n+1; a++){
		G[a][1] = a*B00*G[a-1][0] + C01*G[a][0];
		for (b=2; b<m+1; b++){
			G[a][b] = B01*(b-1)*G[a][b-2] + a*B00*G[a-1][b-1] + C01*G[a][b-1];
		}
	}

	//compute I(i,j,k,l) from I(n,0,m,0)=G[n][m]
HRR:
	if(j==0 && l==0){
		return G[n][m];
	}else{
		double ijkl = 0;
		for (int m=0; m<l+1; m++){
			double ijm0 = 0;
			for (int n=0; n<j+1; n++) 
				ijm0 += binomial(j,n)*pow(xij,j-n)*G[n+i][m+k];
			ijkl += binomial(l,m)*pow(xkl,l-m)*ijm0;
		}
		return ijkl;
	}
}
   

           
inline double computeERIprim(
           double xa,double ya,double za,int la,int ma,int na,double alphaa,
	   double xb,double yb,double zb,int lb,int mb,int nb,double alphab,
	   double xc,double yc,double zc,int lc,int mc,int nc,double alphac,
           double xd,double yd,double zd,int ld,int md,int nd,double alphad){

  int norder,i;
  double A,B,xp,yp,zp,xq,yq,zq,rpq2,X,rho,sum,t,Ix,Iy,Iz,invA,invB;
  double rab2,rcd2,K;
  double roots[MAXROOTS],weights[MAXROOTS];

  A = alphaa+alphab; 
  B = alphac+alphad;
  invA = 1/A;
  invB = 1/B;
  rho = A*B/(A+B);
  rab2 = (xa-xb)*(xa-xb)+(ya-yb)*(ya-yb)+(za-zb)*(za-zb);
  rcd2 = (xc-xd)*(xc-xd)+(yc-yd)*(yc-yd)+(zc-zd)*(zc-zd);
  //34.98683665524972 == 2*pow(M_PI , 2.5);
  K = 34.98683665524972*exp( -alphaa*alphab*rab2*invA - alphac*alphad*rcd2*invB );
  K /= A*B*sqrt(A+B);

  //if(K < 1.0e-10)return 0.0;

  norder = (la+ma+na+lb+nb+mb+lc+mc+nc+ld+md+nd)/2 + 1;
  xp = (alphaa*xa+alphab*xb)*invA;
  yp = (alphaa*ya+alphab*yb)*invA;
  zp = (alphaa*za+alphab*zb)*invA;
  xq = (alphac*xc+alphad*xd)*invB;
  yq = (alphac*yc+alphad*yd)*invB;
  zq = (alphac*zc+alphad*zd)*invB;
  rpq2 = (xp-xq)*(xp-xq)+(yp-yq)*(yp-yq)+(zp-zq)*(zp-zq);

  X = rpq2*rho;

  computeRysParams(norder,X,roots,weights); 

  sum = 0.;
  for (i=0; i<norder; i++){
    t = roots[i]/(1+roots[i]);
    Ix = computeERI1D(t,la,lb,lc,ld,xa,xb,xc,xd,alphaa,alphab,alphac,alphad);
    Iy = computeERI1D(t,ma,mb,mc,md,ya,yb,yc,yd,alphaa,alphab,alphac,alphad);
    Iz = computeERI1D(t,na,nb,nc,nd,za,zb,zc,zd,alphaa,alphab,alphac,alphad);
    sum = sum + Ix*Iy*Iz*weights[i]; 
  }
  return K*sum;
}



double computeERI(
   double xa,double ya,double za,int la,int ma,int na,double *alphaa , double *anorm , int La ,
   double xb,double yb,double zb,int lb,int mb,int nb,double *alphab , double *bnorm , int Lb ,
   double xc,double yc,double zc,int lc,int mc,int nc,double *alphac , double *cnorm , int Lc ,
   double xd,double yd,double zd,int ld,int md,int nd,double *alphad , double *dnorm , int Ld){

   int p,q,r,s;
   double ret=0.0,tmp;
   for(p = 0 ; p < La ; p++){
       for(q = 0 ; q < Lb ; q++){
           for(r = 0 ; r < Lc ; r++){
               for(s = 0 ; s < Ld ; s++){
                     tmp = computeERIprim(xa,ya,za,la,ma,na,alphaa[p]  ,
                                          xb,yb,zb,lb,mb,nb,alphab[q]  ,
                                          xc,yc,zc,lc,mc,nc,alphac[r]  ,
                                          xd,yd,zd,ld,md,nd,alphad[s]  );
                     ret += anorm[p]*bnorm[q]*cnorm[r]*dnorm[s]*tmp;
               }
           }
       }
   }
   return ret;
}


double computeeri_(double *xa,double *ya,double *za,long *la,long *ma,long *na,double *alphaa , double *anorm , long *La ,
    double *xb,double *yb,double *zb,long *lb,long *mb,long *nb,double *alphab , double *bnorm , long *Lb ,
    double *xc,double *yc,double *zc,long *lc,long *mc,long *nc,double *alphac , double *cnorm , long *Lc ,
    double *xd,double *yd,double *zd,long *ld,long *md,long *nd,double *alphad , double *dnorm , long *Ld)
{
     return computeERI(*xa,*ya,*za,*la,*ma,*na,alphaa,anorm,*La,
                       *xb,*yb,*zb,*lb,*mb,*nb,alphab,bnorm,*Lb,
                       *xc,*yc,*zc,*lc,*mc,*nc,alphac,cnorm,*Lc,
                       *xd,*yd,*zd,*ld,*md,*nd,alphad,dnorm,*Ld);
}


/*
basis:縮約Gauss基底の配列
Nbasis:基底の個数
P:密度行列
F:Fock行列(返り値)
*/
void computeFockMatrix(GaussBasis *basis , int Nbasis , double *P , double *F){
  int i,j,k,l=0;
  double ijkl;
  GaussBasis a,b,c,d;

  for(i = 0 ; i < Nbasis ; i++){
     for(j = i ; j < Nbasis ; j++){
        for(k = 0 ; k < Nbasis ; k++){
           for(l = k ; l < Nbasis ; l++){
                a = basis[i];
                b = basis[j];
                c = basis[k];
                d = basis[l];
                ijkl = computeERI(a.x , a.y , a.z , a.nx , a.ny , a.nz , a.exponents , a.norms , a.length ,
                                  b.x , b.y , b.z , b.nx , b.ny , b.nz , b.exponents , b.norms , b.length ,
                                  c.x , c.y , c.z , c.nx , c.ny , c.nz , c.exponents , c.norms , c.length ,
                                  d.x , d.y , d.z , d.nx , d.ny , d.nz , d.exponents , d.norms , d.length );

            /*
                F[i,j] += 2.0*P[k,l]*(ij|kl)
                F[i,l] += -P[k,j]*(ij|kl)
            */
                F[i+j*Nbasis] += 2.0*P[k+l*Nbasis]*ijkl;
                F[i+l*Nbasis] -= P[k+j*Nbasis]*ijkl; 
             /*
                 (ij|kl) = (ji|kl) = (ij|lk) = (ji|kl) =
                 (kl|ij) = (lk|ij) = (lk|ji) = (kl|ji)
              */
                if(i!=j && k!=l){
                   F[j+i*Nbasis] += 2.0*P[k+l*Nbasis]*ijkl;
                   F[j+l*Nbasis] += -P[k+i*Nbasis]*ijkl;
                   F[i+j*Nbasis] += 2.0*P[l+k*Nbasis]*ijkl;
                   F[i+k*Nbasis] += -P[l+j*Nbasis]*ijkl;
                   F[j+i*Nbasis] += 2.0*P[l+k*Nbasis]*ijkl;
                   F[j+k*Nbasis] += -P[l+i*Nbasis]*ijkl;
                }else if(i!=j){
                   F[j+i*Nbasis] += 2.0*P[k+l*Nbasis]*ijkl;
                   F[j+l*Nbasis] += -P[k+i*Nbasis]*ijkl;
                }else if(k!=l){
                   F[i+j*Nbasis] += 2.0*P[l+k*Nbasis]*ijkl;
                   F[i+k*Nbasis] += -P[l+j*Nbasis]*ijkl;
                }

           }
        }
     }
  }
  return ;
}


