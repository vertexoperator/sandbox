#include "crys.h"
#include <math.h>
#ifndef M_PI
#define M_PI 3.1415926535897932384626433
#endif

#define MAXROOTS 13

//Rys多項式のRootsとWeightsを一時的に格納

static double roots[MAXROOTS];
static double weights[MAXROOTS];
static double G[MAXROOTS][MAXROOTS];


static inline int binomial(int n , int k){
        int p=1;
        for(int i = n ; i > k ; i--)p *= i;
        for(int i = n-k ; i > 1 ; i--)p /= i;
        return p;
}

#ifdef __cplusplus
extern "C" {
#endif


double computeERI(
            double xa,double ya,double za,int la,int ma,int na,double alphaa,
            double xb,double yb,double zb,int lb,int mb,int nb,double alphab,
	    double xc,double yc,double zc,int lc,int mc,int nc,double alphac,
	    double xd,double yd,double zd,int ld,int md,int nd,double alphad);


#ifdef __cplusplus
}
#endif




#if 0
static inline int binomial(int n , int k){
	int p=1;
	for(int i = n ; i > k ; i--)p *= i;
	for(int i = n-k ; i > 1 ; i--)p /= i;
	return p;
}
#endif

double computeERI1D(double t,int i,int j,int k, int l,double xi,double xj,double xk,double xl,double ai,double aj,double ak,double al){
	int n,m,a,b;
	double A,B,Px,Qx,fff;
	double B00,B10,B01,C10,C01;
	double xij=xi-xj,xkl=xk-xl;

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


double computeERI(double xa,double ya,double za,int la,int ma,int na,double alphaa,
	          double xb,double yb,double zb,int lb,int mb,int nb,double alphab,
	          double xc,double yc,double zc,int lc,int mc,int nc,double alphac,
		  double xd,double yd,double zd,int ld,int md,int nd,double alphad){

  int norder,i;
  double A,B,xp,yp,zp,xq,yq,zq,rpq2,X,rho,sum,t,Ix,Iy,Iz,invA,invB;
  double rab2,rcd2,K;

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


