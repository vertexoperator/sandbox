/*
 * Rys polynomial computation was first discussed by [1].
 * Other reference about the computation of Rys polynomials is [2].
 * [1]"Numerical Integration Using Rys Polynomials"
 * Harry F. King, Michel Dupuis
 * Journal of Computational Physics, Vol. 21, 144-165(1976)
 *
 * [2]"General formula evaluation of the electron-repulsion integral (ERI) and its derivatives over Gaussian-type orbitals. II. ERI evaluation improved"
 * K.Ishida 
 * J.Chem.Phys ,Vol.98, 2176-2181(1993) 
 *
 * for the general theory of Orthogonal Polynomials, see [3][4]:
 * [3]"Calculation of Gauss Quadrature Rules"
 * Gene H. Golub, John H. Welsch
 * Mathematics of Computation, 23, 221-230(1969)
 *
 * [4] "Algorithm 726: ORTHPOL - A Package of Routines for Generating Orthogonal Polynomials and Gauss-Type Quadrature Rules" 
 * Walter Gautschi
 * ACM Transactions on Mathematical Software  20, 21-62(1994)
 *
 * Most of this codes taken from ryspol.src in  GAMESS
 *
 */

#include "crys.h"
#include <math.h>
#include <assert.h>

static void A_Root1(double , double[] , double[]);
static void A_Root2(double , double[] , double[]);
static void A_Root3(double , double[] , double[]);
static void A_Root4(double , double[] , double[]);
static void A_Root5(double , double[] , double[]);

#if 0
static void Root1(double , double[] , double[]);
static void Root23(unsigned int ,double , double[] , double[]);
static void Root4(double , double[] , double[]);
static void Root5(double , double[] , double[]);
#endif

#if 0
static void __Root1(double , double[] , double[]);
static void __Root2(double , double[] , double[]);
static void __Root3(double , double[] , double[]);
static void __Root4(double , double[] , double[]);
static void __Root5(double , double[] , double[]);
#endif

static void RootN(unsigned int , double);

#define MAXROOTS 13
#define MAXAUX 55
#include "rys_table.h"
#include "quadrature_rule.h"
static double roots[MAXROOTS];
static double weights[MAXROOTS];

//以下の変数と関数は、全部RootN専用
static double LargeX[] = {0.0, 29.0 , 37.0 , 43.0 , 49.0 , 55.0 , 60.0 , 65.0 , 71.0 , 76.0 , 81.0 , 86.0 , 91.0 , 96.0};
static unsigned int NAUXS[] =  {0 , 20 , 25 , 30 , 30 , 35 , 40 , 40 , 40 , 45 , 50 , 50 , 55 , 55};
static unsigned int MAPRYS[] = {0 ,  1 ,  2 ,  3 ,  3 ,  4 ,  5 ,  5 ,  5 ,  6 ,  7 ,  7 ,  8 ,  8};
static double ALPHA[MAXROOTS];
static double BETA[MAXROOTS];
static double RGRID[MAXAUX];
static double WGRID[MAXAUX];
static double P0[MAXAUX];	//補助
static double P1[MAXAUX];	//補助
static double P2[MAXAUX];	//補助
static double WRK[MAXROOTS];
static void RYSDS(unsigned int , unsigned int);	//Stieltjes Procedure
static void RYSGW(unsigned int , double);	//Golub-Welsch

//Rys多項式のRootとWeightを計算
void computeRysParams(unsigned int n , double X , double rts[] ,double wts[]){
	assert(n <= 13);	//not implemented

	switch(n){
		case 1:
			A_Root1(X , rts, wts);
			return;
		case 2:
			A_Root2(X , rts , wts);
			//Root23(2 , X, rts , wts);
			return;
		case 3:
			A_Root3(X, rts , wts);
			//Root23(3 , X, rts , wts);
			return;
		case 4:
			A_Root4(X, rts , wts);
			return;
		case 5:
			A_Root5(X, rts , wts);
			return;
		default:
			RootN(n , X);
			break;
	}

	for(unsigned int i = 0 ; i < n ; i++){
		rts[i] = roots[i];
		wts[i] = weights[i];
	}
	return;
}

#undef MAXROOTS
#undef MAXAUX
void A_Root1(double X , double rts[] , double wts[]){
	if(X < 40.0){
		int n = int(X);
		double x = X - double(n) - 0.5;
		double *r0,*w0;
		r0 = r1_0[n];
		w0 = w1_0[n];
		rts[0] = ((((((((((r0[11]*x+r0[10])*x+r0[9])*x+r0[8])*x+r0[7])*x+r0[6])*x+r0[5])*x+r0[4])*x+r0[3])*x+r0[2])*x+r0[1])*x+r0[0];
		wts[0] = ((((((((((w0[11]*x+w0[10])*x+w0[9])*x+w0[8])*x+w0[7])*x+w0[6])*x+w0[5])*x+w0[4])*x+w0[3])*x+w0[2])*x+w0[1])*x+w0[0];
	}else{
		double fr = 1/X;
		double fw = sqrt(fr);
		for(unsigned int i = 0 ; i < 1 ; i++){
			double DUM = fr*hermite_roots[1][i]*hermite_roots[1][i];
			rts[i] = DUM/(1.0-DUM);
			wts[i] = fw*hermite_weights[1][i];
		}
	}
}

void A_Root2(double X , double rts[] , double wts[]){
	if(X < 45.0){
		int n = int(X);
		double x = X - double(n) - 0.5;
		double *r0,*r1,*w0,*w1;
		r0 = r2_0[n];r1 = r2_1[n];
		w0 = w2_0[n];w1 = w2_1[n];
		rts[0] = ((((((((((r0[11]*x+r0[10])*x+r0[9])*x+r0[8])*x+r0[7])*x+r0[6])*x+r0[5])*x+r0[4])*x+r0[3])*x+r0[2])*x+r0[1])*x+r0[0];
		rts[1] = ((((((((((r1[11]*x+r1[10])*x+r1[9])*x+r1[8])*x+r1[7])*x+r1[6])*x+r1[5])*x+r1[4])*x+r1[3])*x+r1[2])*x+r1[1])*x+r1[0];
		wts[0] = ((((((((((w0[11]*x+w0[10])*x+w0[9])*x+w0[8])*x+w0[7])*x+w0[6])*x+w0[5])*x+w0[4])*x+w0[3])*x+w0[2])*x+w0[1])*x+w0[0];
		wts[1] = ((((((((((w1[11]*x+w1[10])*x+w1[9])*x+w1[8])*x+w1[7])*x+w1[6])*x+w1[5])*x+w1[4])*x+w1[3])*x+w1[2])*x+w1[1])*x+w1[0];
	}else{
		double fr = 1/X;
		double fw = sqrt(fr);
		double DUM0 = fr*hermite_roots[2][0]*hermite_roots[2][0];
		double DUM1 = fr*hermite_roots[2][1]*hermite_roots[2][1];
		rts[0] = DUM0/(1.0 - DUM0);
		rts[1] = DUM1/(1.0 - DUM1);
		wts[0] = fw*hermite_weights[2][0];
		wts[1] = fw*hermite_weights[2][1];
	}
}

void A_Root3(double X , double rts[] , double wts[]){
	if(X < 60.0){
		int n = int(X);
		double x = X - double(n) - 0.5;
		double *r0,*r1,*r2,*w0,*w1,*w2;
		r0 = r3_0[n];r1 = r3_1[n];r2 = r3_2[n];
		w0 = w3_0[n];w1 = w3_1[n];w2 = w3_2[n];
		rts[0] = ((((((((((r0[11]*x+r0[10])*x+r0[9])*x+r0[8])*x+r0[7])*x+r0[6])*x+r0[5])*x+r0[4])*x+r0[3])*x+r0[2])*x+r0[1])*x+r0[0];
		rts[1] = ((((((((((r1[11]*x+r1[10])*x+r1[9])*x+r1[8])*x+r1[7])*x+r1[6])*x+r1[5])*x+r1[4])*x+r1[3])*x+r1[2])*x+r1[1])*x+r1[0];
		rts[2] = ((((((((((r2[11]*x+r2[10])*x+r2[9])*x+r2[8])*x+r2[7])*x+r2[6])*x+r2[5])*x+r2[4])*x+r2[3])*x+r2[2])*x+r2[1])*x+r2[0];
		wts[0] = ((((((((((w0[11]*x+w0[10])*x+w0[9])*x+w0[8])*x+w0[7])*x+w0[6])*x+w0[5])*x+w0[4])*x+w0[3])*x+w0[2])*x+w0[1])*x+w0[0];
		wts[1] = ((((((((((w1[11]*x+w1[10])*x+w1[9])*x+w1[8])*x+w1[7])*x+w1[6])*x+w1[5])*x+w1[4])*x+w1[3])*x+w1[2])*x+w1[1])*x+w1[0];
		wts[2] = ((((((((((w2[11]*x+w2[10])*x+w2[9])*x+w2[8])*x+w2[7])*x+w2[6])*x+w2[5])*x+w2[4])*x+w2[3])*x+w2[2])*x+w2[1])*x+w2[0];
	}else{
		double fr = 1/X;
		double fw = sqrt(fr);
		for(unsigned int i = 0 ; i < 3 ; i++){
			double DUM = fr*hermite_roots[3][i]*hermite_roots[3][i];
			rts[i] = DUM/(1.0-DUM);
			wts[i] = fw*hermite_weights[3][i];
		}
	}
}

void A_Root4(double X , double rts[] , double wts[]){
	if(X < 70.0){
		int n = int(X);
		double x = X - double(n) - 0.5;
		double *r0,*r1,*r2,*r3,*w0,*w1,*w2,*w3;
		r0 = r4_0[n];r1 = r4_1[n];r2 = r4_2[n];r3 = r4_3[n];
		w0 = w4_0[n];w1 = w4_1[n];w2 = w4_2[n];w3 = w4_3[n];
		rts[0] = ((((((((((r0[11]*x+r0[10])*x+r0[9])*x+r0[8])*x+r0[7])*x+r0[6])*x+r0[5])*x+r0[4])*x+r0[3])*x+r0[2])*x+r0[1])*x+r0[0];
		rts[1] = ((((((((((r1[11]*x+r1[10])*x+r1[9])*x+r1[8])*x+r1[7])*x+r1[6])*x+r1[5])*x+r1[4])*x+r1[3])*x+r1[2])*x+r1[1])*x+r1[0];
		rts[2] = ((((((((((r2[11]*x+r2[10])*x+r2[9])*x+r2[8])*x+r2[7])*x+r2[6])*x+r2[5])*x+r2[4])*x+r2[3])*x+r2[2])*x+r2[1])*x+r2[0];
		rts[3] = ((((((((((r3[11]*x+r3[10])*x+r3[9])*x+r3[8])*x+r3[7])*x+r3[6])*x+r3[5])*x+r3[4])*x+r3[3])*x+r3[2])*x+r3[1])*x+r3[0];
				
		wts[0] = ((((((((((w0[11]*x+w0[10])*x+w0[9])*x+w0[8])*x+w0[7])*x+w0[6])*x+w0[5])*x+w0[4])*x+w0[3])*x+w0[2])*x+w0[1])*x+w0[0];
		wts[1] = ((((((((((w1[11]*x+w1[10])*x+w1[9])*x+w1[8])*x+w1[7])*x+w1[6])*x+w1[5])*x+w1[4])*x+w1[3])*x+w1[2])*x+w1[1])*x+w1[0];
		wts[2] = ((((((((((w2[11]*x+w2[10])*x+w2[9])*x+w2[8])*x+w2[7])*x+w2[6])*x+w2[5])*x+w2[4])*x+w2[3])*x+w2[2])*x+w2[1])*x+w2[0];
		wts[3] = ((((((((((w3[11]*x+w3[10])*x+w3[9])*x+w3[8])*x+w3[7])*x+w3[6])*x+w3[5])*x+w3[4])*x+w3[3])*x+w3[2])*x+w3[1])*x+w3[0];
	
	}else{
		double fr = 1/X;
		double fw = sqrt(fr);
		for(unsigned int i = 0 ; i < 4 ; i++){
			double DUM = fr*hermite_roots[4][i]*hermite_roots[4][i];
			rts[i] = DUM/(1.0-DUM);
			wts[i] = fw*hermite_weights[4][i];
		}
	}
}

void A_Root5(double X , double rts[] , double wts[]){
  if(X < 70.0){
		int n = int(X);
		double x = X - double(n) - 0.5;
		double *r0,*r1,*r2,*r3,*r4,*w0,*w1,*w2,*w3,*w4;
		r0 = r5_0[n];r1 = r5_1[n];r2 = r5_2[n];r3 = r5_3[n];r4 = r5_4[n];
		w0 = w5_0[n];w1 = w5_1[n];w2 = w5_2[n];w3 = w5_3[n];w4 = w5_4[n];
		rts[0] = ((((((((((r0[11]*x+r0[10])*x+r0[9])*x+r0[8])*x+r0[7])*x+r0[6])*x+r0[5])*x+r0[4])*x+r0[3])*x+r0[2])*x+r0[1])*x+r0[0];
		rts[1] = ((((((((((r1[11]*x+r1[10])*x+r1[9])*x+r1[8])*x+r1[7])*x+r1[6])*x+r1[5])*x+r1[4])*x+r1[3])*x+r1[2])*x+r1[1])*x+r1[0];
		rts[2] = ((((((((((r2[11]*x+r2[10])*x+r2[9])*x+r2[8])*x+r2[7])*x+r2[6])*x+r2[5])*x+r2[4])*x+r2[3])*x+r2[2])*x+r2[1])*x+r2[0];
		rts[3] = ((((((((((r3[11]*x+r3[10])*x+r3[9])*x+r3[8])*x+r3[7])*x+r3[6])*x+r3[5])*x+r3[4])*x+r3[3])*x+r3[2])*x+r3[1])*x+r3[0];
		rts[4] = ((((((((((r4[11]*x+r4[10])*x+r4[9])*x+r4[8])*x+r4[7])*x+r4[6])*x+r4[5])*x+r4[4])*x+r4[3])*x+r4[2])*x+r4[1])*x+r4[0];
				
		wts[0] = ((((((((((w0[11]*x+w0[10])*x+w0[9])*x+w0[8])*x+w0[7])*x+w0[6])*x+w0[5])*x+w0[4])*x+w0[3])*x+w0[2])*x+w0[1])*x+w0[0];
		wts[1] = ((((((((((w1[11]*x+w1[10])*x+w1[9])*x+w1[8])*x+w1[7])*x+w1[6])*x+w1[5])*x+w1[4])*x+w1[3])*x+w1[2])*x+w1[1])*x+w1[0];
		wts[2] = ((((((((((w2[11]*x+w2[10])*x+w2[9])*x+w2[8])*x+w2[7])*x+w2[6])*x+w2[5])*x+w2[4])*x+w2[3])*x+w2[2])*x+w2[1])*x+w2[0];
		wts[3] = ((((((((((w3[11]*x+w3[10])*x+w3[9])*x+w3[8])*x+w3[7])*x+w3[6])*x+w3[5])*x+w3[4])*x+w3[3])*x+w3[2])*x+w3[1])*x+w3[0];
		wts[4] = ((((((((((w4[11]*x+w4[10])*x+w4[9])*x+w4[8])*x+w4[7])*x+w4[6])*x+w4[5])*x+w4[4])*x+w4[3])*x+w4[2])*x+w4[1])*x+w4[0];
	
	}else{
		double fr = 1/X;
		double fw = sqrt(fr);
		for(unsigned int i = 0 ; i < 5 ; i++){
			double DUM = fr*hermite_roots[5][i]*hermite_roots[5][i];
			rts[i] = DUM/(1.0-DUM);
			wts[i] = fw*hermite_weights[5][i];
		}
	}
}




//Rys Roots/Weights for general case
void RootN(unsigned int n,double X){
	/*
	 * The roots and weights for X = BIG are given by:
	 *    T*T = S*S/X    W = V/SQRT(X)
	 * where S and V are the roots and weights of the Hermite polynomials of order 2*n
	 * SEE ISHIDA-SAN'S SECOND PAPER FOR DETAILS
	 *
	 */
	if(X > LargeX[n]){
		double fr = 1/X;
		double fw = sqrt(fr);
		for(unsigned int i = 0 ; i < n ; i++){
			roots[i] = fr*hermite_roots[n][i]*hermite_roots[n][i];
			weights[i] = fw*hermite_weights[n][i];
		}
	}else{
         unsigned int NAUX=NAUXS[n];
         unsigned int MAP=MAPRYS[n];
		 for(unsigned int i = 0 ;i < NAUX ; i++){
            double T2 = RTSAUX[MAP][i]*RTSAUX[MAP][i];
            RGRID[i] = T2;
            WGRID[i] = WTSAUX[MAP][i]*exp(-X*T2);
		 }
         RYSDS(n , NAUX);
         RYSGW(n , 1.0e-14);
	}
    
	for(unsigned int k = 0 ; k < n ; k++){
		double DUM = roots[k];
		roots[k] = DUM/(1.0-DUM);
		//weights[k] = weights[k];
	}
}

/*
 * THIS ROUTINE APPLIES STIELTJES'S PROCEDURE (CF. SECTION 2.1 OF
 * W. GAUTSCHI, 'ON GENERATING ORTHOGONAL POLYNOMIALS', SIAM J. SCI.
 * STATIST. COMPUT. 3, 1982, 289-317) TO GENERATE THE RECURSION
 * COEFFICIENTS  ALPHA(K), BETA(K) , K=0,1,...,N-1
 *
 */
void RYSDS(unsigned int N , unsigned int NCAP){
	double sum0 = 0.0 , sum1 = 0.0 , sum2;

	for(unsigned int i = 0 ; i < NCAP ; i++){
		sum0 += WGRID[i];
		sum1 += WGRID[i]*RGRID[i];
	}
	ALPHA[0] = sum1/sum0;
	BETA[0] = sum0;
	if(N==1)return;

	//compute the remaining ALPHA and BETA Coefficients
	for(unsigned int i = 0 ; i < NCAP ; i++){
		P1[i] = 0.0;
		P2[i] = 1.0;
	}

	for(unsigned int k = 1 ; k < N ; k++){
		double alpha,beta;
		sum1 = 0.0;
		sum2 = 0.0;
		alpha = ALPHA[k-1];
		beta = BETA[k-1];

		for(unsigned int i = 0 ; i < NCAP ; i++){
			double T;
			//if(WGRID[i] == 0.0)continue;
			P0[i] = P1[i];
			P1[i] = P2[i];
			P2[i] = (RGRID[i] - alpha)*P1[i] - beta*P0[i];

			assert( fabs(P2[i]) < 1.0e40 && fabs(sum2) < 1.0e40 );	//check overflow
			
			T = WGRID[i]*P2[i]*P2[i];
			sum1 += T;
			sum2 += T*RGRID[i];
		}

		assert( fabs(sum1) > 1.0e-40 );	//check underflow

		ALPHA[k] = sum2/sum1;
		BETA[k] = sum1/sum0;
		sum0 = sum1;
	}

}


#define MAX_ITER 30
inline double SIGN(const double a ,const double b){
	return (b > 0.0)?fabs(a):-fabs(a);
}

//Golub-Welsch procedure to compute roots and weights from ALPHA,BETA 
static void RYSGW(unsigned int n , double eps)
{
	unsigned int M,iter = 0;
	roots[0] = ALPHA[0];
	weights[0] = BETA[0];
	if(n == 1)return;
	
	weights[0] = 1.0;
	WRK[n-1] = 0.0;
	for(unsigned int k = 1; k < n ; k++){
		roots[k] = ALPHA[k];
		WRK[k-1] = sqrt(BETA[k]);
		weights[k] = 0.0;
	}

	for(unsigned int L = 0;;){
top:
		assert(iter < MAX_ITER);
		if(L == n-1)break;
		for(M = L ; M < n-1 ; M++){
			if(fabs(WRK[M]) < eps*fabs(roots[M])*fabs(roots[M+1]))break;
		}
		double DP = roots[L];
		if(M == L){
			iter = 0;
			L++;
			goto top;
		}
		iter++;
		double DG = (roots[L+1] - DP)/(2.0*WRK[L]);
		double DR = sqrt(DG*DG + 1.0);
		double DS = 1.0;
		double DC = 1.0;
		DG = roots[M] - DP + WRK[L]/(DG + SIGN(DR,DG));

		DP = 0.0;
		unsigned int MML = M-L;
		for(unsigned int j = 0 ; j < MML ; j++){
			unsigned int i = M -j-1;
			double DF = DS*WRK[i];
			double DB = DC*WRK[i];
			if(fabs(DF) < fabs(DG)){
				DS = DF/DG;
				DR = sqrt(DS*DS + 1.0);
				WRK[i+1] = DG*DR;
				DC = 1.0/DR;
				DS *= DC;
			}else{
				DC = DG/DF;
				DR = sqrt(DC*DC + 1.0);
				WRK[i+1] = DF*DR;
				DS = 1.0/DR;
				DC *= DS;
			}
			DG = roots[i+1] - DP;
			DR = (roots[i] - DG)*DS + 2.0*DC*DB;
			DP = DS*DR;
			roots[i+1] = DG+DP;
			DG = DC*DR-DB;
			DF = weights[i+1];
			weights[i+1] = DS*weights[i]+DC*DF;
			weights[i] = DC*weights[i] - DS*DF;
		}
		roots[L] = roots[L] - DP;
		WRK[L] = DG;
		WRK[M] = 0.0;
	}

	//ORDER EIGENVALUES AND EIGENVECTORS
	for(unsigned int t = 1 ; t < n ; t++){
		unsigned int i = t-1;
		unsigned int k = i;
		double tmp = roots[i];
		for(unsigned int j = t ; j < n ; j++){
			if(roots[j] < tmp){
				k = j;
				tmp = roots[j];
			}
		}
		if(k != i){
			roots[k] = roots[i];
			roots[i] = tmp;
			tmp = weights[i];
			weights[i] = weights[k];
			weights[k] = tmp;
		}
	}
	for(unsigned int s = 0 ; s < n ; s++)weights[s] = BETA[0]*weights[s]*weights[s];

}


//Rys Polynomial Interpolation generator(based on ref[2])

int binomial(int n , int k){
	int p=1;
	for(int i = n ; i > k ; i--)p *= i;
	for(int i = n-k ; i > 1 ; i--)p /= i;
	return p;
}

//Chebyshev polynomial
double T(int n , double x){
	if(n==0){
		return 1.0;
	}else if(n==1){
		return x;
	}else{
		return 2*T(n-1,x)*x - T(n-2,x);
	}
}


#include <string>
#include <sstream>
#include<iomanip>
#include <assert.h>
#ifndef M_PI
#define M_PI 3.1415926535897932384626433
#endif
//n : degree of Rys Polynomial
//N : degree of interpolation polynomial
//minX,maxX : interpolation interval
void RysExpr(int n , int N , double minX , double maxX , double rts_coeff[] ,double wts_coeff[] , int d0){
	//std::string ret;
	double X0 = (minX+maxX)/2.0;
	double *a;
	a = new double[N];

	assert(maxX-minX==1.0);	//この時のみ対応
	
	//roots
	for(int d = 0 ; d < n ;d++)
	{
		for(int k = 0 ; k < N ; k++)a[k] = 0.0;
		for(int k = 0 ; k < N ; k++){
			double r = cos((2*k+1)*M_PI/(double)(2*N));
			RootN(n , X0 + 0.5*r*(maxX-minX));
			for(int n = 0 ; n < N ; n++){
				a[n] += roots[d]*cos((2*k+1)*n*M_PI/(double)(2*N));
				//a[n] += roots[d] * T(n , r);
			}
		}
		a[0] *= 1.0/(double)N;
		for(int n = 1 ; n < N ; n++)a[n] *= (double)2.0/(double)N;
		for(int k = 0 ; k < N ; k++){
			//rts[0] += a[k]*T(k , 2*(X-X0));
			double g = 0.0;
			if(k == 0){
				for(int r = 0 ; 2*r < N ; r++)g+= pow(-1.0,r)*a[2*r];	
			}else if(k % 2 == 0){
				int _k = k/2;
				for(int r = _k ; 2*r < N ; r++){
					g+=pow(-1.0 , r-_k)*((double)r/(double)(r+_k))*(double)binomial(r+_k,r-_k)*a[2*r];
				}
				g *= pow(4.0 , k);
			}else{
				int _k = k/2;
				for(int r = _k ; r < N/2 ; r++){
					g+=pow(-1.0 , r-_k)*((double)(2*r+1)/(double)(2*r+2*_k+2))*(double)binomial(r+_k+1,r-_k)*a[2*r+1];
				}
				g *= pow(4.0 , k);
			}
			//rts[0] += g*pow(X-X0 , k);
			if(d==d0)rts_coeff[k] = g;
		}
/*
		{
			std::ostringstream oss;
			oss << "\t\trts[" << d << "] = ";
			for(int k = 0 ; k < N ; k++)oss << "(";
			for(int k = 0 ; k < N ; k++){
				if(k<N-1){
					oss << "(" <<std::setprecision(18)<< gs[N-k-1] << "))*x+";
				}else{
					oss << "(" << std::setprecision(18)<< gs[N-k-1] << "));\n";
				}
			}
			ret.append(oss.str());
		}
		*/
	}

	//weights
	for(int d = 0 ; d < n ;d++)
	{
		for(int k = 0 ; k < N ; k++)a[k] = 0.0;
		for(int k = 0 ; k < N ; k++){
			double r = cos((2*k+1)*M_PI/(double)(2*N));
			RootN(n , X0 + 0.5*r*(maxX-minX));
			for(int n = 0 ; n < N ; n++){
				a[n] += weights[d]*cos((2*k+1)*n*M_PI/(double)(2*N));
				//a[n] += weights[d] * T(n , r);
			}
		}
		a[0] *= 1.0/(double)N;
		for(int n = 1 ; n < N ; n++)a[n] *= (double)2.0/(double)N;
		for(int k = 0 ; k < N ; k++){
			//rts[0] += a[k]*T(k , 2*(X-X0));
			double g = 0.0;
			if(k == 0){
				for(int r = 0 ; 2*r < N ; r++)g+= pow(-1.0,r)*a[2*r];	
			}else if(k % 2 == 0){
				int _k = k/2;
				for(int r = _k ; 2*r < N ; r++){
					g+=pow(-1.0 , r-_k)*((double)r/(double)(r+_k))*(double)binomial(r+_k,r-_k)*a[2*r];
				}
				g *= pow(4.0 , k);
			}else{
				int _k = k/2;
				for(int r = _k ; r < N/2 ; r++){
					g+=pow(-1.0 , r-_k)*((double)(2*r+1)/(double)(2*r+2*_k+2))*(double)binomial(r+_k+1,r-_k)*a[2*r+1];
				}
				g *= pow(4.0 , k);
			}
			//rts[0] += g*pow(X-X0 , k);
			if(d==d0)wts_coeff[k] = g;
		}
/*
		{
			std::ostringstream oss;
			oss << "\t\twts[" << d << "] = ";
			for(int k = 0 ; k < N ; k++)oss << "(";
			for(int k = 0 ; k < N ; k++){
				if(k<N-1){
					oss << "(" <<std::setprecision(18)<< gs[N-k-1] << "))*x+";
				}else{
					oss << "(" << std::setprecision(18)<< gs[N-k-1] << "));\n";
				}
			}
			ret.append(oss.str());
		}
		*/
	}
	delete [] a;
	//delete [] gs;
	//return ret;
}


//Gamess code
#if 0
void Root1(double X , double *rts , double *wts){
	double RT1=0,WW1=0;
	double F1,Y,E,PIE4;
	PIE4 = 7.85398163397448E-01;
	if (X < 3.e-7){
      RT1 = 0.5E+00 -X/5.0E+00;
      WW1 = 1.0E+00 -X/3.0E+00;
	}else if (X < 1.) {
      F1 = ((((((((-8.36313918003957E-08*X+1.21222603512827E-06 )*X-
		  1.15662609053481E-05 )*X+9.25197374512647E-05 )*X-
		6.40994113129432E-04 )*X+3.78787044215009E-03 )*X-
	      1.85185172458485E-02 )*X+7.14285713298222E-02 )*X-
	    1.99999999997023E-01 )*X+3.33333333333318E-01;
      WW1 = (X+X)*F1+exp(-X);
      RT1 = F1/(WW1-F1);
	}else if (X < 3.) {
      Y = X-2.0E+00;
      F1 = ((((((((((-1.61702782425558E-10*Y+1.96215250865776E-09 )*Y-
		    2.14234468198419E-08 )*Y+2.17216556336318E-07 )*Y-
		  1.98850171329371E-06 )*Y+1.62429321438911E-05 )*Y-
		1.16740298039895E-04 )*Y+7.24888732052332E-04 )*Y-
	      3.79490003707156E-03 )*Y+1.61723488664661E-02 )*Y-
	    5.29428148329736E-02 )*Y+1.15702180856167E-01;
      WW1 = (X+X)*F1+exp(-X);
      RT1 = F1/(WW1-F1);
	}else if (X < 5.0){
      Y = X-4.0E+00;
      F1 = ((((((((((-2.62453564772299E-11*Y+3.24031041623823E-10 )*Y-
		    3.614965656163E-09)*Y+3.760256799971E-08)*Y-
		  3.553558319675E-07)*Y+3.022556449731E-06)*Y-
		2.290098979647E-05)*Y+1.526537461148E-04)*Y-
	      8.81947375894379E-04 )*Y+4.33207949514611E-03 )*Y-
	    1.75257821619926E-02 )*Y+5.28406320615584E-02;
      WW1 = (X+X)*F1+exp(-X);
      RT1 = F1/(WW1-F1);
	}else if (X < 10.0) {
	  E = exp(-X);
	  WW1 = (((((( 4.6897511375022E-01/X-6.9955602298985E-01)/X +
	       5.3689283271887E-01)/X-3.2883030418398E-01)/X +
	     2.4645596956002E-01)/X-4.9984072848436E-01)/X -
	   3.1501078774085E-06)*E + sqrt(PIE4/X);
	  F1 = (WW1-E)/(X+X);
	  RT1 = F1/(WW1-F1);
	}else if (X < 15) {
	  E = exp(-X);
	  WW1 = (((-1.8784686463512E-01/X+2.2991849164985E-01)/X -
	    4.9893752514047E-01)/X-2.1916512131607E-05)*E \
      + sqrt(PIE4/X);
	  F1 = (WW1-E)/(X+X);
      RT1 = F1/(WW1-F1);
	}else if (X < 33) {
	  E = exp(-X);
	  WW1 = (( 1.9623264149430E-01/X-4.9695241464490E-01)/X -
	   6.0156581186481E-05)*E + sqrt(PIE4/X);
	  F1 = (WW1-E)/(X+X);
      RT1 = F1/(WW1-F1);
	}else{
	  WW1 = sqrt(PIE4/X);
      RT1 = 0.5E+00/(X-0.5E+00);
	}
	rts[0] = RT1;
	wts[0] = WW1;
	return;
}

void Root23(unsigned int n, double X , double *rts , double *wts){

  double R12, PIE4, R22, W22, R13, R23, W23, R33, W33;
  double RT1=0,RT2=0,RT3=0,WW1=0,WW2=0,WW3=0;
  double F1,F2,E,T1,T2,T3,A1,A2,Y;

  R12 = 2.75255128608411E-01;
  PIE4 = 7.85398163397448E-01;
  R22 =  2.72474487139158E+00;
  W22 = 9.17517095361369E-02;
  R13 = 1.90163509193487E-01;
  R23 = 1.78449274854325E+00;
  W23 = 1.77231492083829E-01;
  R33 = 5.52534374226326E+00;
  W33 = 5.11156880411248E-03;
    
  if (X < 3.e-7){
	if (n == 2) {
      RT1 = 1.30693606237085E-01 -2.90430236082028E-02 *X;
      RT2 = 2.86930639376291E+00 -6.37623643058102E-01 *X;
      WW1 = 6.52145154862545E-01 -1.22713621927067E-01 *X;
      WW2 = 3.47854845137453E-01 -2.10619711404725E-01 *X;
    } else if (n == 3) {
      RT1 = 6.03769246832797E-02 -9.28875764357368E-03 *X;
      RT2 = 7.76823355931043E-01 -1.19511285527878E-01 *X;
      RT3 = 6.66279971938567E+00 -1.02504611068957E+00 *X;
      WW1 = 4.67913934572691E-01 -5.64876917232519E-02 *X;
      WW2 = 3.60761573048137E-01 -1.49077186455208E-01 *X;
      WW3 = 1.71324492379169E-01 -1.27768455150979E-01 *X;
    }
  } else if (X < 1.) {
    if (n == 2) {
      F1 = ((((((((-8.36313918003957E-08*X+1.21222603512827E-06 )*X-
		  1.15662609053481E-05 )*X+9.25197374512647E-05 )*X-
		6.40994113129432E-04 )*X+3.78787044215009E-03 )*X-
	      1.85185172458485E-02 )*X+7.14285713298222E-02 )*X-
	    1.99999999997023E-01 )*X+3.33333333333318E-01;
      WW1 = (X+X)*F1+exp(-X);
      RT1 = (((((((-2.35234358048491E-09*X+2.49173650389842E-08)*X-
		  4.558315364581E-08)*X-2.447252174587E-06)*X+
		4.743292959463E-05)*X-5.33184749432408E-04 )*X+
	      4.44654947116579E-03 )*X-2.90430236084697E-02 )*X+\
	1.30693606237085E-01;
      RT2 = (((((((-2.47404902329170E-08*X+2.36809910635906E-07)*X+
		  1.835367736310E-06)*X-2.066168802076E-05)*X-
		1.345693393936E-04)*X-5.88154362858038E-05 )*X+
	      5.32735082098139E-02 )*X-6.37623643056745E-01 )*X+\
	2.86930639376289E+00;
      WW2 = ((F1-WW1)*RT1+F1)*(1.0E+00+RT2)/(RT2-RT1);
      WW1 = WW1-WW2;
    } else if (n==3){
      RT1 = ((((((-5.10186691538870E-10*X+2.40134415703450E-08)*X-
                 5.01081057744427E-07 )*X+7.58291285499256E-06 )*X-
               9.55085533670919E-05 )*X+1.02893039315878E-03 )*X-
             9.28875764374337E-03 )*X+6.03769246832810E-02;
      RT2 = ((((((-1.29646524960555E-08*X+7.74602292865683E-08)*X+
		 1.56022811158727E-06 )*X-1.58051990661661E-05 )*X-
	       3.30447806384059E-04 )*X+9.74266885190267E-03 )*X-
	     1.19511285526388E-01 )*X+7.76823355931033E-01;
      RT3 = ((((((-9.28536484109606E-09*X-3.02786290067014E-07)*X-
		 2.50734477064200E-06 )*X-7.32728109752881E-06 )*X+
	       2.44217481700129E-04 )*X+4.94758452357327E-02 )*X-
	     1.02504611065774E+00 )*X+6.66279971938553E+00;
      F2 = ((((((((-7.60911486098850E-08*X+1.09552870123182E-06 )*X-
		  1.03463270693454E-05 )*X+8.16324851790106E-05 )*X-
		5.55526624875562E-04 )*X+3.20512054753924E-03 )*X-
	      1.51515139838540E-02 )*X+5.55555554649585E-02 )*X-
	    1.42857142854412E-01 )*X+1.99999999999986E-01;
      E = exp(-X);
      F1 = ((X+X)*F2+E)/3.0E+00;
      WW1 = (X+X)*F1+E;
      T1 = RT1/(RT1+1.0E+00);
      T2 = RT2/(RT2+1.0E+00);
      T3 = RT3/(RT3+1.0E+00);
      A2 = F2-T1*F1;
      A1 = F1-T1*WW1;
      WW3 = (A2-T2*A1)/((T3-T2)*(T3-T1));
      WW2 = (T3*A1-A2)/((T3-T2)*(T2-T1));
      WW1 = WW1-WW2-WW3;
    }
  } else if (X < 3.) {
    Y = X-2.0E+00;
    if (n == 2) {
      F1 = ((((((((((-1.61702782425558E-10*Y+1.96215250865776E-09 )*Y-
		    2.14234468198419E-08 )*Y+2.17216556336318E-07 )*Y-
		  1.98850171329371E-06 )*Y+1.62429321438911E-05 )*Y-
		1.16740298039895E-04 )*Y+7.24888732052332E-04 )*Y-
	      3.79490003707156E-03 )*Y+1.61723488664661E-02 )*Y-
	    5.29428148329736E-02 )*Y+1.15702180856167E-01;
      WW1 = (X+X)*F1+exp(-X);
      RT1 = (((((((((-6.36859636616415E-12*Y+8.47417064776270E-11)*Y-
		    5.152207846962E-10)*Y-3.846389873308E-10)*Y+
		  8.472253388380E-08)*Y-1.85306035634293E-06 )*Y+
		2.47191693238413E-05 )*Y-2.49018321709815E-04 )*Y+
	      2.19173220020161E-03 )*Y-1.63329339286794E-02 )*Y+\
	8.68085688285261E-02;
      RT2 = ((((((((( 1.45331350488343E-10*Y+2.07111465297976E-09)*Y-
		    1.878920917404E-08)*Y-1.725838516261E-07)*Y+
		  2.247389642339E-06)*Y+9.76783813082564E-06 )*Y-
		1.93160765581969E-04 )*Y-1.58064140671893E-03 )*Y+
	      4.85928174507904E-02 )*Y-4.30761584997596E-01 )*Y+\
	1.80400974537950E+00;
      WW2 = ((F1-WW1)*RT1+F1)*(1.0E+00+RT2)/(RT2-RT1);
      WW1 = WW1-WW2;
    } else if (n == 3) {
      RT1 = (((((((( 1.44687969563318E-12*Y+4.85300143926755E-12)*Y-
		   6.55098264095516E-10 )*Y+1.56592951656828E-08 )*Y-
		 2.60122498274734E-07 )*Y+3.86118485517386E-06 )*Y-
	       5.13430986707889E-05 )*Y+6.03194524398109E-04 )*Y-
	     6.11219349825090E-03 )*Y+4.52578254679079E-02;
      RT2 = ((((((( 6.95964248788138E-10*Y-5.35281831445517E-09)*Y-
		  6.745205954533E-08)*Y+1.502366784525E-06)*Y+
		9.923326947376E-07)*Y-3.89147469249594E-04 )*Y+
	      7.51549330892401E-03 )*Y-8.48778120363400E-02 )*Y+\
	5.73928229597613E-01;
      RT3 = ((((((((-2.81496588401439E-10*Y+3.61058041895031E-09)*Y+
		   4.53631789436255E-08 )*Y-1.40971837780847E-07 )*Y-
		 6.05865557561067E-06 )*Y-5.15964042227127E-05 )*Y+
	       3.34761560498171E-05 )*Y+5.04871005319119E-02 )*Y-
	     8.24708946991557E-01 )*Y+4.81234667357205E+00;
      F2 = ((((((((((-1.48044231072140E-10*Y+1.78157031325097E-09 )*Y-
		    1.92514145088973E-08 )*Y+1.92804632038796E-07 )*Y-
		  1.73806555021045E-06 )*Y+1.39195169625425E-05 )*Y-
		9.74574633246452E-05 )*Y+5.83701488646511E-04 )*Y-
	      2.89955494844975E-03 )*Y+1.13847001113810E-02 )*Y-
	    3.23446977320647E-02 )*Y+5.29428148329709E-02;
      E = exp(-X);
      F1 = ((X+X)*F2+E)/3.0E+00;
      WW1 = (X+X)*F1+E;
      T1 = RT1/(RT1+1.0E+00);
      T2 = RT2/(RT2+1.0E+00);
      T3 = RT3/(RT3+1.0E+00);
      A2 = F2-T1*F1;
      A1 = F1-T1*WW1;
      WW3 = (A2-T2*A1)/((T3-T2)*(T3-T1));
      WW2 = (T3*A1-A2)/((T3-T2)*(T2-T1));
      WW1 = WW1-WW2-WW3;
    }
  } else if (X < 5.){
    Y = X-4.0E+00;
    if (n == 2) {
      F1 = ((((((((((-2.62453564772299E-11*Y+3.24031041623823E-10 )*Y-
		    3.614965656163E-09)*Y+3.760256799971E-08)*Y-
		  3.553558319675E-07)*Y+3.022556449731E-06)*Y-
		2.290098979647E-05)*Y+1.526537461148E-04)*Y-
	      8.81947375894379E-04 )*Y+4.33207949514611E-03 )*Y-
	    1.75257821619926E-02 )*Y+5.28406320615584E-02;
      WW1 = (X+X)*F1+exp(-X);
      RT1 = ((((((((-4.11560117487296E-12*Y+7.10910223886747E-11)*Y-
		   1.73508862390291E-09 )*Y+5.93066856324744E-08 )*Y-
		 9.76085576741771E-07 )*Y+1.08484384385679E-05 )*Y-
	       1.12608004981982E-04 )*Y+1.16210907653515E-03 )*Y-
	     9.89572595720351E-03 )*Y+6.12589701086408E-02;
      RT2 = (((((((((-1.80555625241001E-10*Y+5.44072475994123E-10)*Y+
		    1.603498045240E-08)*Y-1.497986283037E-07)*Y-
		  7.017002532106E-07)*Y+1.85882653064034E-05 )*Y-
		2.04685420150802E-05 )*Y-2.49327728643089E-03 )*Y+
	      3.56550690684281E-02 )*Y-2.60417417692375E-01 )*Y+\
	1.12155283108289E+00;
      WW2 = ((F1-WW1)*RT1+F1)*(1.0E+00+RT2)/(RT2-RT1);
      WW1 = WW1-WW2;
    } else if (n == 3) {
      RT1 = ((((((( 1.44265709189601E-11*Y-4.66622033006074E-10)*Y+
		  7.649155832025E-09)*Y-1.229940017368E-07)*Y+
		2.026002142457E-06)*Y-2.87048671521677E-05 )*Y+
	      3.70326938096287E-04 )*Y-4.21006346373634E-03 )*Y+\
	3.50898470729044E-02;
      RT2 = ((((((((-2.65526039155651E-11*Y+1.97549041402552E-10)*Y+
		   2.15971131403034E-09 )*Y-7.95045680685193E-08 )*Y+
		 5.15021914287057E-07 )*Y+1.11788717230514E-05 )*Y-
	       3.33739312603632E-04 )*Y+5.30601428208358E-03 )*Y-
	     5.93483267268959E-02 )*Y+4.31180523260239E-01;
      RT3 = ((((((((-3.92833750584041E-10*Y-4.16423229782280E-09)*Y+
		   4.42413039572867E-08 )*Y+6.40574545989551E-07 )*Y-
		 3.05512456576552E-06 )*Y-1.05296443527943E-04 )*Y-
	       6.14120969315617E-04 )*Y+4.89665802767005E-02 )*Y-
	     6.24498381002855E-01 )*Y+3.36412312243724E+00;
      F2 = ((((((((((-2.36788772599074E-11*Y+2.89147476459092E-10 )*Y-
		    3.18111322308846E-09 )*Y+3.25336816562485E-08 )*Y-
		  3.00873821471489E-07 )*Y+2.48749160874431E-06 )*Y-
		1.81353179793672E-05 )*Y+1.14504948737066E-04 )*Y-
	      6.10614987696677E-04 )*Y+2.64584212770942E-03 )*Y-
	    8.66415899015349E-03 )*Y+1.75257821619922E-02;
      E = exp(-X);
      F1 = ((X+X)*F2+E)/3.0E+00;
      WW1 = (X+X)*F1+E;
      T1 = RT1/(RT1+1.0E+00);
      T2 = RT2/(RT2+1.0E+00);
      T3 = RT3/(RT3+1.0E+00);
      A2 = F2-T1*F1;
      A1 = F1-T1*WW1;
      WW3 = (A2-T2*A1)/((T3-T2)*(T3-T1));
      WW2 = (T3*A1-A2)/((T3-T2)*(T2-T1));
      WW1 = WW1-WW2-WW3;
    }
  } else if (X < 10) {
    E = exp(-X);
    WW1 = (((((( 4.6897511375022E-01/X-6.9955602298985E-01)/X +
	       5.3689283271887E-01)/X-3.2883030418398E-01)/X +
	     2.4645596956002E-01)/X-4.9984072848436E-01)/X -
	   3.1501078774085E-06)*E + sqrt(PIE4/X);
    F1 = (WW1-E)/(X+X);
    if (n == 2){
      Y = X-7.5E+00;
      RT1 = (((((((((((((-1.43632730148572E-16*Y+2.38198922570405E-16)*
			Y+1.358319618800E-14)*Y-7.064522786879E-14)*Y-
		      7.719300212748E-13)*Y+7.802544789997E-12)*Y+
		    6.628721099436E-11)*Y-1.775564159743E-09)*Y+
		  1.713828823990E-08)*Y-1.497500187053E-07)*Y+
		2.283485114279E-06)*Y-3.76953869614706E-05 )*Y+
	      4.74791204651451E-04 )*Y-4.60448960876139E-03 )*Y+\
	3.72458587837249E-02;
      RT2 = (((((((((((( 2.48791622798900E-14*Y-1.36113510175724E-13)*Y-
		       2.224334349799E-12)*Y+4.190559455515E-11)*Y-
		     2.222722579924E-10)*Y-2.624183464275E-09)*Y+
		   6.128153450169E-08)*Y-4.383376014528E-07)*Y-
		 2.49952200232910E-06 )*Y+1.03236647888320E-04 )*Y-
	       1.44614664924989E-03 )*Y+1.35094294917224E-02 )*Y-
	     9.53478510453887E-02 )*Y+5.44765245686790E-01;
      WW2 = ((F1-WW1)*RT1+F1)*(1.0E+00+RT2)/(RT2-RT1);
      WW1 = WW1-WW2;
    } else if (n == 3) {
      F2 = (F1+F1+F1-E)/(X+X);
      Y = X-7.5E+00;
      RT1 = ((((((((((( 5.74429401360115E-16*Y+7.11884203790984E-16)*Y-
		      6.736701449826E-14)*Y-6.264613873998E-13)*Y+
		    1.315418927040E-11)*Y-4.23879635610964E-11 )*Y+
		  1.39032379769474E-09 )*Y-4.65449552856856E-08 )*Y+
		7.34609900170759E-07 )*Y-1.08656008854077E-05 )*Y+
	      1.77930381549953E-04 )*Y-2.39864911618015E-03 )*Y+\
	2.39112249488821E-02;
      RT2 = ((((((((((( 1.13464096209120E-14*Y+6.99375313934242E-15)*Y-
		      8.595618132088E-13)*Y-5.293620408757E-12)*Y-
		    2.492175211635E-11)*Y+2.73681574882729E-09 )*Y-
		  1.06656985608482E-08 )*Y-4.40252529648056E-07 )*Y+
		9.68100917793911E-06 )*Y-1.68211091755327E-04 )*Y+
	      2.69443611274173E-03 )*Y-3.23845035189063E-02 )*Y+\
	2.75969447451882E-01;
      RT3 = (((((((((((( 6.66339416996191E-15*Y+1.84955640200794E-13)*Y-
		       1.985141104444E-12)*Y-2.309293727603E-11)*Y+
		     3.917984522103E-10)*Y+1.663165279876E-09)*Y-
		   6.205591993923E-08)*Y+8.769581622041E-09)*Y+
		 8.97224398620038E-06 )*Y-3.14232666170796E-05 )*Y-
	       1.83917335649633E-03 )*Y+3.51246831672571E-02 )*Y-
	     3.22335051270860E-01 )*Y+1.73582831755430E+00;
      T1 = RT1/(RT1+1.0E+00);
      T2 = RT2/(RT2+1.0E+00);
      T3 = RT3/(RT3+1.0E+00);
      A2 = F2-T1*F1;
      A1 = F1-T1*WW1;
      WW3 = (A2-T2*A1)/((T3-T2)*(T3-T1));
      WW2 = (T3*A1-A2)/((T3-T2)*(T2-T1));
      WW1 = WW1-WW2-WW3;
    }
  } else if (X < 15) {
    E = exp(-X);
    WW1 = (((-1.8784686463512E-01/X+2.2991849164985E-01)/X -
	    4.9893752514047E-01)/X-2.1916512131607E-05)*E \
      + sqrt(PIE4/X);
    F1 = (WW1-E)/(X+X);
    if (n == 2) {
      RT1 = ((((-1.01041157064226E-05*X+1.19483054115173E-03)*X -
	       6.73760231824074E-02)*X+1.25705571069895E+00)*X +
	     (((-8.57609422987199E+03/X+5.91005939591842E+03)/X -
	       1.70807677109425E+03)/X+2.64536689959503E+02)/X -
	     2.38570496490846E+01)*E + R12/(X-R12);
      RT2 = ((( 3.39024225137123E-04*X-9.34976436343509E-02)*X -
	      4.22216483306320E+00)*X +
	     (((-2.08457050986847E+03/X -
		1.04999071905664E+03)/X+3.39891508992661E+02)/X -
	      1.56184800325063E+02)/X+8.00839033297501E+00)*E + R22/(X-R22);
      WW2 = ((F1-WW1)*RT1+F1)*(1.0E+00+RT2)/(RT2-RT1);
      WW1 = WW1-WW2;
    } else if (n == 3) {
      F2 = (F1+F1+F1-E)/(X+X);
      Y = X-12.5E+00;
      RT1 = ((((((((((( 4.42133001283090E-16*Y-2.77189767070441E-15)*Y-
		      4.084026087887E-14)*Y+5.379885121517E-13)*Y+
		    1.882093066702E-12)*Y-8.67286219861085E-11 )*Y+
		  7.11372337079797E-10 )*Y-3.55578027040563E-09 )*Y+
		1.29454702851936E-07 )*Y-4.14222202791434E-06 )*Y+
	      8.04427643593792E-05 )*Y-1.18587782909876E-03 )*Y+\
	1.53435577063174E-02;
      RT2 = ((((((((((( 6.85146742119357E-15*Y-1.08257654410279E-14)*Y-
		      8.579165965128E-13)*Y+6.642452485783E-12)*Y+
		    4.798806828724E-11)*Y-1.13413908163831E-09 )*Y+
		  7.08558457182751E-09 )*Y-5.59678576054633E-08 )*Y+
		2.51020389884249E-06 )*Y-6.63678914608681E-05 )*Y+
	      1.11888323089714E-03 )*Y-1.45361636398178E-02 )*Y+\
	1.65077877454402E-01;
      RT3 = (((((((((((( 3.20622388697743E-15*Y-2.73458804864628E-14)*Y-
		       3.157134329361E-13)*Y+8.654129268056E-12)*Y-
		     5.625235879301E-11)*Y-7.718080513708E-10)*Y+
		   2.064664199164E-08)*Y-1.567725007761E-07)*Y-
		 1.57938204115055E-06 )*Y+6.27436306915967E-05 )*Y-
	       1.01308723606946E-03 )*Y+1.13901881430697E-02 )*Y-
	     1.01449652899450E-01 )*Y+7.77203937334739E-01;
      T1 = RT1/(RT1+1.0E+00);
      T2 = RT2/(RT2+1.0E+00);
      T3 = RT3/(RT3+1.0E+00);
      A2 = F2-T1*F1;
      A1 = F1-T1*WW1;
      WW3 = (A2-T2*A1)/((T3-T2)*(T3-T1));
      WW2 = (T3*A1-A2)/((T3-T2)*(T2-T1));
      WW1 = WW1-WW2-WW3;
    }
  } else if (X < 33) {
    E = exp(-X);
    WW1 = (( 1.9623264149430E-01/X-4.9695241464490E-01)/X -
	   6.0156581186481E-05)*E + sqrt(PIE4/X);
    F1 = (WW1-E)/(X+X);
    if (n == 2){
      RT1 = ((((-1.14906395546354E-06*X+1.76003409708332E-04)*X -
	       1.71984023644904E-02)*X-1.37292644149838E-01)*X +
	     (-4.75742064274859E+01/X+9.21005186542857E+00)/X -
	     2.31080873898939E-02)*E + R12/(X-R12);
      RT2 = ((( 3.64921633404158E-04*X-9.71850973831558E-02)*X -
	      4.02886174850252E+00)*X +
	     (-1.35831002139173E+02/X -
	      8.66891724287962E+01)/X+2.98011277766958E+00)*E + R22/(X-R22);
      WW2 = ((F1-WW1)*RT1+F1)*(1.0E+00+RT2)/(RT2-RT1);
      WW1 = WW1-WW2;
    } else if (n == 3) {
      F2 = (F1+F1+F1-E)/(X+X);
      if (X < 20) {
	RT1 = ((((((-2.43270989903742E-06*X+3.57901398988359E-04)*X -
		   2.34112415981143E-02)*X+7.81425144913975E-01)*X -
		 1.73209218219175E+01)*X+2.43517435690398E+02)*X +
	       (-1.97611541576986E+04/X+9.82441363463929E+03)/X -
	       2.07970687843258E+03)*E + R13/(X-R13);
	RT2 = (((((-2.62627010965435E-04*X+3.49187925428138E-02)*X -
		  3.09337618731880E+00)*X+1.07037141010778E+02)*X -
		2.36659637247087E+03)*X +
	       ((-2.91669113681020E+06/X +
		 1.41129505262758E+06)/X-2.91532335433779E+05)/X +
	       3.35202872835409E+04)*E + R23/(X-R23);
	RT3 = ((((( 9.31856404738601E-05*X-2.87029400759565E-02)*X -
		  7.83503697918455E-01)*X-1.84338896480695E+01)*X +
		4.04996712650414E+02)*X +
	       (-1.89829509315154E+05/X +
		5.11498390849158E+04)/X-6.88145821789955E+03)*E \
	  + R33/(X-R33);
      } else {
	RT1 = ((((-4.97561537069643E-04*X-5.00929599665316E-02)*X +
		 1.31099142238996E+00)*X-1.88336409225481E+01)*X -
	       6.60344754467191E+02 /X+1.64931462413877E+02)*E \
	  + R13/(X-R13);
	RT2 = ((((-4.48218898474906E-03*X-5.17373211334924E-01)*X +
		 1.13691058739678E+01)*X-1.65426392885291E+02)*X -
	       6.30909125686731E+03 /X+1.52231757709236E+03)*E \
	  + R23/(X-R23);
	RT3 = ((((-1.38368602394293E-02*X-1.77293428863008E+00)*X +
		 1.73639054044562E+01)*X-3.57615122086961E+02)*X -
	       1.45734701095912E+04 /X+2.69831813951849E+03)*E \
	  + R33/(X-R33);
      }
      T1 = RT1/(RT1+1.0E+00);
      T2 = RT2/(RT2+1.0E+00);
      T3 = RT3/(RT3+1.0E+00);
      A2 = F2-T1*F1;
      A1 = F1-T1*WW1;
      WW3 = (A2-T2*A1)/((T3-T2)*(T3-T1));
      WW2 = (T3*A1-A2)/((T3-T2)*(T2-T1));
      WW1 = WW1-WW2-WW3; 
    }
  } else {
    WW1 = sqrt(PIE4/X);
    if (n == 2) {
      if (X < 40) {
	E = exp(-X);
	RT1 = (-8.78947307498880E-01*X+1.09243702330261E+01)*E \
	  + R12/(X-R12);
	RT2 = (-9.28903924275977E+00*X+8.10642367843811E+01)*E \
	  + R22/(X-R22);
	WW2 = ( 4.46857389308400E+00*X-7.79250653461045E+01)*E + W22*WW1;
	WW1 = WW1-WW2;
      } else {
	RT1 = R12/(X-R12);
	RT2 = R22/(X-R22);
	WW2 = W22*WW1;
	WW1 = WW1-WW2;
      }
    } else if (n == 3) {
      if (X < 47) {
	E = exp(-X);
	RT1 = ((-7.39058467995275E+00*X+3.21318352526305E+02)*X -
	       3.99433696473658E+03)*E + R13/(X-R13);
	RT2 = ((-7.38726243906513E+01*X+3.13569966333873E+03)*X -
	       3.86862867311321E+04)*E + R23/(X-R23);
	RT3 = ((-2.63750565461336E+02*X+1.04412168692352E+04)*X -
	       1.28094577915394E+05)*E + R33/(X-R33);
	WW3 = ((( 1.52258947224714E-01*X-8.30661900042651E+00)*X +
		1.92977367967984E+02)*X-1.67787926005344E+03)*E \
	  + W33*WW1;
	WW2 = (( 6.15072615497811E+01*X-2.91980647450269E+03)*X +
	       3.80794303087338E+04)*E + W23*WW1;
	WW1 = WW1-WW2-WW3;
      } else {
	RT1 = R13/(X-R13);
	RT2 = R23/(X-R23);
	RT3 = R33/(X-R33);
	WW2 = W23*WW1;
	WW3 = W33*WW1;
	WW1 = WW1-WW2-WW3;
      }
    }
  }
  rts[0] = RT1;
  wts[0] = WW1;
  rts[1] = RT2;
  wts[1] = WW2;
  if (n > 2) {
    rts[2] = RT3;
    wts[2] = WW3;
  }
  return;
}

void Root4(double X , double *rts, double *wts){
  double R14,PIE4,R24,W24,R34,W34,R44,W44;
  double RT1=0,RT2=0,RT3=0,RT4=0,WW1=0,WW2=0,WW3=0,WW4=0;
  double Y,E;
  
  R14 = 1.45303521503316E-01;
  PIE4 = 7.85398163397448E-01;
  R24 = 1.33909728812636E+00;
  W24 = 2.34479815323517E-01;
  R34 = 3.92696350135829E+00;
  W34 = 1.92704402415764E-02;
  R44 = 8.58863568901199E+00;
  W44 = 2.25229076750736E-04;

  if (X <= 3.0E-7) {
    RT1 = 3.48198973061471E-02 -4.09645850660395E-03 *X;
    RT2 = 3.81567185080042E-01 -4.48902570656719E-02 *X;
    RT3 = 1.73730726945891E+00 -2.04389090547327E-01 *X;
    RT4 = 1.18463056481549E+01 -1.39368301742312E+00 *X;
    WW1 = 3.62683783378362E-01 -3.13844305713928E-02 *X;
    WW2 = 3.13706645877886E-01 -8.98046242557724E-02 *X;
    WW3 = 2.22381034453372E-01 -1.29314370958973E-01 *X;
    WW4 = 1.01228536290376E-01 -8.28299075414321E-02 *X;
  } else if (X <= 1.0) {
    RT1 = ((((((-1.95309614628539E-10*X+5.19765728707592E-09)*X-
	       1.01756452250573E-07 )*X+1.72365935872131E-06 )*X-
	     2.61203523522184E-05 )*X+3.52921308769880E-04 )*X-
	   4.09645850658433E-03 )*X+3.48198973061469E-02;
    RT2 = (((((-1.89554881382342E-08*X+3.07583114342365E-07)*X+
	      1.270981734393E-06)*X-1.417298563884E-04)*X+
	    3.226979163176E-03)*X-4.48902570678178E-02 )*X+\
      3.81567185080039E-01;
    RT3 = (((((( 1.77280535300416E-09*X+3.36524958870615E-08)*X-
	       2.58341529013893E-07 )*X-1.13644895662320E-05 )*X-
	     7.91549618884063E-05 )*X+1.03825827346828E-02 )*X-
	   2.04389090525137E-01 )*X+1.73730726945889E+00;
    RT4 = (((((-5.61188882415248E-08*X-2.49480733072460E-07)*X+
	      3.428685057114E-06)*X+1.679007454539E-04)*X+
	    4.722855585715E-02)*X-1.39368301737828E+00 )*X+\
      1.18463056481543E+01;
    WW1 = ((((((-1.14649303201279E-08*X+1.88015570196787E-07)*X-
	       2.33305875372323E-06 )*X+2.68880044371597E-05 )*X-
	     2.94268428977387E-04 )*X+3.06548909776613E-03 )*X-
	   3.13844305680096E-02 )*X+3.62683783378335E-01;
    WW2 = ((((((((-4.11720483772634E-09*X+6.54963481852134E-08)*X-
		 7.20045285129626E-07 )*X+6.93779646721723E-06 )*X-
	       6.05367572016373E-05 )*X+4.74241566251899E-04 )*X-
	     3.26956188125316E-03 )*X+1.91883866626681E-02 )*X-
	   8.98046242565811E-02 )*X+3.13706645877886E-01;
    WW3 = ((((((((-3.41688436990215E-08*X+5.07238960340773E-07)*X-
		 5.01675628408220E-06 )*X+4.20363420922845E-05 )*X-
	       3.08040221166823E-04 )*X+1.94431864731239E-03 )*X-
	     1.02477820460278E-02 )*X+4.28670143840073E-02 )*X-
	   1.29314370962569E-01 )*X+2.22381034453369E-01;
    WW4 = ((((((((( 4.99660550769508E-09*X-7.94585963310120E-08)*X+
		  8.359072409485E-07)*X-7.422369210610E-06)*X+
		5.763374308160E-05)*X-3.86645606718233E-04 )*X+
	      2.18417516259781E-03 )*X-9.99791027771119E-03 )*X+
	    3.48791097377370E-02 )*X-8.28299075413889E-02 )*X+\
      1.01228536290376E-01;
  } else if (X <= 5) {
    Y = X-3.0E+00;
    RT1 = (((((((((-1.48570633747284E-15*Y-1.33273068108777E-13)*Y+
		  4.068543696670E-12)*Y-9.163164161821E-11)*Y+
		2.046819017845E-09)*Y-4.03076426299031E-08 )*Y+
	      7.29407420660149E-07 )*Y-1.23118059980833E-05 )*Y+
	    1.88796581246938E-04 )*Y-2.53262912046853E-03 )*Y+\
      2.51198234505021E-02;
    RT2 = ((((((((( 1.35830583483312E-13*Y-2.29772605964836E-12)*Y-
		  3.821500128045E-12)*Y+6.844424214735E-10)*Y-
		1.048063352259E-08)*Y+1.50083186233363E-08 )*Y+
	      3.48848942324454E-06 )*Y-1.08694174399193E-04 )*Y+
	    2.08048885251999E-03 )*Y-2.91205805373793E-02 )*Y+\
      2.72276489515713E-01;
    RT3 = ((((((((( 5.02799392850289E-13*Y+1.07461812944084E-11)*Y-
		  1.482277886411E-10)*Y-2.153585661215E-09)*Y+
		3.654087802817E-08)*Y+5.15929575830120E-07 )*Y-
	      9.52388379435709E-06 )*Y-2.16552440036426E-04 )*Y+
	    9.03551469568320E-03 )*Y-1.45505469175613E-01 )*Y+\
      1.21449092319186E+00;
    RT4 = (((((((((-1.08510370291979E-12*Y+6.41492397277798E-11)*Y+
		  7.542387436125E-10)*Y-2.213111836647E-09)*Y-
		1.448228963549E-07)*Y-1.95670833237101E-06 )*Y-
	      1.07481314670844E-05 )*Y+1.49335941252765E-04 )*Y+
	    4.87791531990593E-02 )*Y-1.10559909038653E+00 )*Y+\
      8.09502028611780E+00;
    WW1 = ((((((((((-4.65801912689961E-14*Y+7.58669507106800E-13)*Y-
		   1.186387548048E-11)*Y+1.862334710665E-10)*Y-
		 2.799399389539E-09)*Y+4.148972684255E-08)*Y-
	       5.933568079600E-07)*Y+8.168349266115E-06)*Y-
	     1.08989176177409E-04 )*Y+1.41357961729531E-03 )*Y-
	   1.87588361833659E-02 )*Y+2.89898651436026E-01;
    WW2 = ((((((((((((-1.46345073267549E-14*Y+2.25644205432182E-13)*Y-
		     3.116258693847E-12)*Y+4.321908756610E-11)*Y-
		   5.673270062669E-10)*Y+7.006295962960E-09)*Y-
		 8.120186517000E-08)*Y+8.775294645770E-07)*Y-
	       8.77829235749024E-06 )*Y+8.04372147732379E-05 )*Y-
	     6.64149238804153E-04 )*Y+4.81181506827225E-03 )*Y-
	   2.88982669486183E-02 )*Y+1.56247249979288E-01;
    WW3 = ((((((((((((( 9.06812118895365E-15*Y-1.40541322766087E-13)*
		      Y+1.919270015269E-12)*Y-2.605135739010E-11)*Y+
		    3.299685839012E-10)*Y-3.86354139348735E-09 )*Y+
		  4.16265847927498E-08 )*Y-4.09462835471470E-07 )*Y+
		3.64018881086111E-06 )*Y-2.88665153269386E-05 )*Y+
	      2.00515819789028E-04 )*Y-1.18791896897934E-03 )*Y+
	    5.75223633388589E-03 )*Y-2.09400418772687E-02 )*Y+\
      4.85368861938873E-02;
    WW4 = ((((((((((((((-9.74835552342257E-16*Y+1.57857099317175E-14)*
		       Y-2.249993780112E-13)*Y+3.173422008953E-12)*Y-
		     4.161159459680E-11)*Y+5.021343560166E-10)*Y-
		   5.545047534808E-09)*Y+5.554146993491E-08)*Y-
		 4.99048696190133E-07 )*Y+3.96650392371311E-06 )*Y-
	       2.73816413291214E-05 )*Y+1.60106988333186E-04 )*Y-
	     7.64560567879592E-04 )*Y+2.81330044426892E-03 )*Y-
	   7.16227030134947E-03 )*Y+9.66077262223353E-03;
  } else if (X <= 10.0) {
    Y = X-7.5E+00;
    RT1 = ((((((((( 4.64217329776215E-15*Y-6.27892383644164E-15)*Y+
		  3.462236347446E-13)*Y-2.927229355350E-11)*Y+
		5.090355371676E-10)*Y-9.97272656345253E-09 )*Y+
	      2.37835295639281E-07 )*Y-4.60301761310921E-06 )*Y+
	    8.42824204233222E-05 )*Y-1.37983082233081E-03 )*Y+\
      1.66630865869375E-02;
    RT2 = ((((((((( 2.93981127919047E-14*Y+8.47635639065744E-13)*Y-
		  1.446314544774E-11)*Y-6.149155555753E-12)*Y+
		8.484275604612E-10)*Y-6.10898827887652E-08 )*Y+
	      2.39156093611106E-06 )*Y-5.35837089462592E-05 )*Y+
	    1.00967602595557E-03 )*Y-1.57769317127372E-02 )*Y+\
      1.74853819464285E-01;
    RT3 = (((((((((( 2.93523563363000E-14*Y-6.40041776667020E-14)*Y-
		   2.695740446312E-12)*Y+1.027082960169E-10)*Y-
		 5.822038656780E-10)*Y-3.159991002539E-08)*Y+
	       4.327249251331E-07)*Y+4.856768455119E-06)*Y-
	     2.54617989427762E-04 )*Y+5.54843378106589E-03 )*Y-
	   7.95013029486684E-02 )*Y+7.20206142703162E-01;
    RT4 = (((((((((((-1.62212382394553E-14*Y+7.68943641360593E-13)*Y+
		    5.764015756615E-12)*Y-1.380635298784E-10)*Y-
		  1.476849808675E-09)*Y+1.84347052385605E-08 )*Y+
		3.34382940759405E-07 )*Y-1.39428366421645E-06 )*Y-
	      7.50249313713996E-05 )*Y-6.26495899187507E-04 )*Y+
	    4.69716410901162E-02 )*Y-6.66871297428209E-01 )*Y+\
      4.11207530217806E+00;
    WW1 = ((((((((((-1.65995045235997E-15*Y+6.91838935879598E-14)*Y-
		   9.131223418888E-13)*Y+1.403341829454E-11)*Y-
		 3.672235069444E-10)*Y+6.366962546990E-09)*Y-
	       1.039220021671E-07)*Y+1.959098751715E-06)*Y-
	     3.33474893152939E-05 )*Y+5.72164211151013E-04 )*Y-
	   1.05583210553392E-02 )*Y+2.26696066029591E-01;
    WW2 = ((((((((((((-3.57248951192047E-16*Y+6.25708409149331E-15)*Y-
		     9.657033089714E-14)*Y+1.507864898748E-12)*Y-
		   2.332522256110E-11)*Y+3.428545616603E-10)*Y-
		 4.698730937661E-09)*Y+6.219977635130E-08)*Y-
	       7.83008889613661E-07 )*Y+9.08621687041567E-06 )*Y-
	     9.86368311253873E-05 )*Y+9.69632496710088E-04 )*Y-
	   8.14594214284187E-03 )*Y+8.50218447733457E-02;
    WW3 = ((((((((((((( 1.64742458534277E-16*Y-2.68512265928410E-15)*
		      Y+3.788890667676E-14)*Y-5.508918529823E-13)*Y+
		    7.555896810069E-12)*Y-9.69039768312637E-11 )*Y+
		  1.16034263529672E-09 )*Y-1.28771698573873E-08 )*Y+
		1.31949431805798E-07 )*Y-1.23673915616005E-06 )*Y+
	      1.04189803544936E-05 )*Y-7.79566003744742E-05 )*Y+
	    5.03162624754434E-04 )*Y-2.55138844587555E-03 )*Y+\
      1.13250730954014E-02;
    WW4 = ((((((((((((((-1.55714130075679E-17*Y+2.57193722698891E-16)*
		       Y-3.626606654097E-15)*Y+5.234734676175E-14)*Y-
		     7.067105402134E-13)*Y+8.793512664890E-12)*Y-
		   1.006088923498E-10)*Y+1.050565098393E-09)*Y-
		 9.91517881772662E-09 )*Y+8.35835975882941E-08 )*Y-
	       6.19785782240693E-07 )*Y+3.95841149373135E-06 )*Y-
	     2.11366761402403E-05 )*Y+9.00474771229507E-05 )*Y-
	   2.78777909813289E-04 )*Y+5.26543779837487E-04;
  } else if (X <= 15) {
    Y = X-12.5E+00;
    RT1 = ((((((((((( 4.94869622744119E-17*Y+8.03568805739160E-16)*Y-
		    5.599125915431E-15)*Y-1.378685560217E-13)*Y+
		  7.006511663249E-13)*Y+1.30391406991118E-11 )*Y+
		8.06987313467541E-11 )*Y-5.20644072732933E-09 )*Y+
	      7.72794187755457E-08 )*Y-1.61512612564194E-06 )*Y+
	    4.15083811185831E-05 )*Y-7.87855975560199E-04 )*Y+\
      1.14189319050009E-02;
    RT2 = ((((((((((( 4.89224285522336E-16*Y+1.06390248099712E-14)*Y-
		    5.446260182933E-14)*Y-1.613630106295E-12)*Y+
		  3.910179118937E-12)*Y+1.90712434258806E-10 )*Y+
		8.78470199094761E-10 )*Y-5.97332993206797E-08 )*Y+
	      9.25750831481589E-07 )*Y-2.02362185197088E-05 )*Y+
	    4.92341968336776E-04 )*Y-8.68438439874703E-03 )*Y+\
      1.15825965127958E-01;
    RT3 = (((((((((( 6.12419396208408E-14*Y+1.12328861406073E-13)*Y-
		   9.051094103059E-12)*Y-4.781797525341E-11)*Y+
		 1.660828868694E-09)*Y+4.499058798868E-10)*Y-
	       2.519549641933E-07)*Y+4.977444040180E-06)*Y-
	     1.25858350034589E-04 )*Y+2.70279176970044E-03 )*Y-
	   3.99327850801083E-02 )*Y+4.33467200855434E-01;
    RT4 = ((((((((((( 4.63414725924048E-14*Y-4.72757262693062E-14)*Y-
		    1.001926833832E-11)*Y+6.074107718414E-11)*Y+
		  1.576976911942E-09)*Y-2.01186401974027E-08 )*Y-
		1.84530195217118E-07 )*Y+5.02333087806827E-06 )*Y+
	      9.66961790843006E-06 )*Y-1.58522208889528E-03 )*Y+
	    2.80539673938339E-02 )*Y-2.78953904330072E-01 )*Y+\
      1.82835655238235E+00;
    WW4 = ((((((((((((( 2.90401781000996E-18*Y-4.63389683098251E-17)*
		      Y+6.274018198326E-16)*Y-8.936002188168E-15)*Y+
		    1.194719074934E-13)*Y-1.45501321259466E-12 )*Y+
		  1.64090830181013E-11 )*Y-1.71987745310181E-10 )*Y+
		1.63738403295718E-09 )*Y-1.39237504892842E-08 )*Y+
	      1.06527318142151E-07 )*Y-7.27634957230524E-07 )*Y+
	    4.12159381310339E-06 )*Y-1.74648169719173E-05 )*Y+\
      8.50290130067818E-05;
    WW3 = ((((((((((((-4.19569145459480E-17*Y+5.94344180261644E-16)*Y-
		     1.148797566469E-14)*Y+1.881303962576E-13)*Y-
		   2.413554618391E-12)*Y+3.372127423047E-11)*Y-
		 4.933988617784E-10)*Y+6.116545396281E-09)*Y-
	       6.69965691739299E-08 )*Y+7.52380085447161E-07 )*Y-
	     8.08708393262321E-06 )*Y+6.88603417296672E-05 )*Y-
	   4.67067112993427E-04 )*Y+5.42313365864597E-03;
    WW2 = ((((((((((-6.22272689880615E-15*Y+1.04126809657554E-13)*Y-
		   6.842418230913E-13)*Y+1.576841731919E-11)*Y-
		 4.203948834175E-10)*Y+6.287255934781E-09)*Y-
	       8.307159819228E-08)*Y+1.356478091922E-06)*Y-
	     2.08065576105639E-05 )*Y+2.52396730332340E-04 )*Y-
	   2.94484050194539E-03 )*Y+6.01396183129168E-02;
    WW1 = (((-1.8784686463512E-01/X+2.2991849164985E-01)/X -
	    4.9893752514047E-01)/X-2.1916512131607E-05)*exp(-X) +\
      sqrt(PIE4/X)-WW4-WW3-WW2;
  } else if (X <= 20) {
    WW1 = sqrt(PIE4/X);
    Y = X-17.5E+00;
    RT1 = ((((((((((( 4.36701759531398E-17*Y-1.12860600219889E-16)*Y-
		    6.149849164164E-15)*Y+5.820231579541E-14)*Y+
		  4.396602872143E-13)*Y-1.24330365320172E-11 )*Y+
		6.71083474044549E-11 )*Y+2.43865205376067E-10 )*Y+
	      1.67559587099969E-08 )*Y-9.32738632357572E-07 )*Y+
	    2.39030487004977E-05 )*Y-4.68648206591515E-04 )*Y+\
      8.34977776583956E-03;
    RT2 = ((((((((((( 4.98913142288158E-16*Y-2.60732537093612E-16)*Y-
		    7.775156445127E-14)*Y+5.766105220086E-13)*Y+
		  6.432696729600E-12)*Y-1.39571683725792E-10 )*Y+
		5.95451479522191E-10 )*Y+2.42471442836205E-09 )*Y+
	      2.47485710143120E-07 )*Y-1.14710398652091E-05 )*Y+
	    2.71252453754519E-04 )*Y-4.96812745851408E-03 )*Y+\
      8.26020602026780E-02;
    RT3 = ((((((((((( 1.91498302509009E-15*Y+1.48840394311115E-14)*Y-
		    4.316925145767E-13)*Y+1.186495793471E-12)*Y+
		  4.615806713055E-11)*Y-5.54336148667141E-10 )*Y+
		3.48789978951367E-10 )*Y-2.79188977451042E-09 )*Y+
	      2.09563208958551E-06 )*Y-6.76512715080324E-05 )*Y+
	    1.32129867629062E-03 )*Y-2.05062147771513E-02 )*Y+\
      2.88068671894324E-01;
    RT4 = (((((((((((-5.43697691672942E-15*Y-1.12483395714468E-13)*Y+
		    2.826607936174E-12)*Y-1.266734493280E-11)*Y-
		  4.258722866437E-10)*Y+9.45486578503261E-09 )*Y-
		5.86635622821309E-08 )*Y-1.28835028104639E-06 )*Y+
	      4.41413815691885E-05 )*Y-7.61738385590776E-04 )*Y+
	    9.66090902985550E-03 )*Y-1.01410568057649E-01 )*Y+\
      9.54714798156712E-01;
    WW4 = ((((((((((((-7.56882223582704E-19*Y+7.53541779268175E-18)*Y-
		     1.157318032236E-16)*Y+2.411195002314E-15)*Y-
		   3.601794386996E-14)*Y+4.082150659615E-13)*Y-
		 4.289542980767E-12)*Y+5.086829642731E-11)*Y-
	       6.35435561050807E-10 )*Y+6.82309323251123E-09 )*Y-
	     5.63374555753167E-08 )*Y+3.57005361100431E-07 )*Y-
	   2.40050045173721E-06 )*Y+4.94171300536397E-05;
    WW3 = (((((((((((-5.54451040921657E-17*Y+2.68748367250999E-16)*Y+
		    1.349020069254E-14)*Y-2.507452792892E-13)*Y+
		  1.944339743818E-12)*Y-1.29816917658823E-11 )*Y+
		3.49977768819641E-10 )*Y-8.67270669346398E-09 )*Y+
	      1.31381116840118E-07 )*Y-1.36790720600822E-06 )*Y+
	    1.19210697673160E-05 )*Y-1.42181943986587E-04 )*Y+\
      4.12615396191829E-03;
    WW2 = (((((((((((-1.86506057729700E-16*Y+1.16661114435809E-15)*Y+
		    2.563712856363E-14)*Y-4.498350984631E-13)*Y+
		  1.765194089338E-12)*Y+9.04483676345625E-12 )*Y+
		4.98930345609785E-10 )*Y-2.11964170928181E-08 )*Y+
	      3.98295476005614E-07 )*Y-5.49390160829409E-06 )*Y+
	    7.74065155353262E-05 )*Y-1.48201933009105E-03 )*Y+\
      4.97836392625268E-02;
    WW1 = (( 1.9623264149430E-01/X-4.9695241464490E-01)/X -
	   6.0156581186481E-05)*exp(-X)+WW1-WW2-WW3-WW4;
  } else if (X <= 35) {
    WW1 = sqrt(PIE4/X);
    E = exp(-X);
    RT1 = ((((((-4.45711399441838E-05*X+1.27267770241379E-03)*X -
	       2.36954961381262E-01)*X+1.54330657903756E+01)*X -
	     5.22799159267808E+02)*X+1.05951216669313E+04)*X +
	   (-2.51177235556236E+06/X+8.72975373557709E+05)/X -
	   1.29194382386499E+05)*E + R14/(X-R14);
    RT2 = (((((-7.85617372254488E-02*X+6.35653573484868E+00)*X -
	      3.38296938763990E+02)*X+1.25120495802096E+04)*X -
	    3.16847570511637E+05)*X +
	   ((-1.02427466127427E+09/X +
	     3.70104713293016E+08)/X-5.87119005093822E+07)/X +
	   5.38614211391604E+06)*E + R24/(X-R24);
    RT3 = (((((-2.37900485051067E-01*X+1.84122184400896E+01)*X -
	      1.00200731304146E+03)*X+3.75151841595736E+04)*X -
	    9.50626663390130E+05)*X +
	   ((-2.88139014651985E+09/X +
	     1.06625915044526E+09)/X-1.72465289687396E+08)/X +
	   1.60419390230055E+07)*E + R34/(X-R34);
    RT4 = ((((((-6.00691586407385E-04*X-3.64479545338439E-01)*X +
	       1.57496131755179E+01)*X-6.54944248734901E+02)*X +
	     1.70830039597097E+04)*X-2.90517939780207E+05)*X +
	   (3.49059698304732E+07/X-1.64944522586065E+07)/X +
	   2.96817940164703E+06)*E + R44/(X-R44);
    if (X <= 25) 
      WW4 = ((((((( 2.33766206773151E-07*X-
		    3.81542906607063E-05)*X +3.51416601267000E-03)*X-
		 1.66538571864728E-01)*X +4.80006136831847E+00)*X-
	       8.73165934223603E+01)*X +9.77683627474638E+02)*X +
	     1.66000945117640E+04/X -6.14479071209961E+03)*E + W44*WW1;
    else
      WW4 = (((((( 5.74245945342286E-06*X-
		   7.58735928102351E-05)*X +2.35072857922892E-04)*X-
		3.78812134013125E-03)*X +3.09871652785805E-01)*X-
	      7.11108633061306E+00)*X +5.55297573149528E+01)*E + W44*WW1;
    WW3 = (((((( 2.36392855180768E-04*X-9.16785337967013E-03)*X +
	       4.62186525041313E-01)*X-1.96943786006540E+01)*X +
	     4.99169195295559E+02)*X-6.21419845845090E+03)*X +
	   ((+5.21445053212414E+07/X-1.34113464389309E+07)/X +
	    1.13673298305631E+06)/X-2.81501182042707E+03)*E + W34*WW1;
    WW2 = (((((( 7.29841848989391E-04*X-3.53899555749875E-02)*X +
	       2.07797425718513E+00)*X-1.00464709786287E+02)*X +
	     3.15206108877819E+03)*X-6.27054715090012E+04)*X +
	   (+1.54721246264919E+07/X-5.26074391316381E+06)/X +
	   7.67135400969617E+05)*E + W24*WW1;
    WW1 = (( 1.9623264149430E-01/X-4.9695241464490E-01)/X -
	   6.0156581186481E-05)*E + WW1-WW2-WW3-WW4;
  } else if (X <= 53) {
    WW1 = sqrt(PIE4/X);
    E = exp(-X)*pow(X,4);
    RT4 = ((-2.19135070169653E-03*X-1.19108256987623E-01)*X -
	   7.50238795695573E-01)*E + R44/(X-R44);
    RT3 = ((-9.65842534508637E-04*X-4.49822013469279E-02)*X +
	   6.08784033347757E-01)*E + R34/(X-R34);
    RT2 = ((-3.62569791162153E-04*X-9.09231717268466E-03)*X +
	   1.84336760556262E-01)*E + R24/(X-R24);
    RT1 = ((-4.07557525914600E-05*X-6.88846864931685E-04)*X +
	   1.74725309199384E-02)*E + R14/(X-R14);
    WW4 = (( 5.76631982000990E-06*X-7.89187283804890E-05)*X +
	   3.28297971853126E-04)*E + W44*WW1;
    WW3 = (( 2.08294969857230E-04*X-3.77489954837361E-03)*X +
	   2.09857151617436E-02)*E + W34*WW1;
    WW2 = (( 6.16374517326469E-04*X-1.26711744680092E-02)*X +
	   8.14504890732155E-02)*E + W24*WW1;
    WW1 = WW1-WW2-WW3-WW4;
  } else {
    WW1 = sqrt(PIE4/X);
    RT1 = R14/(X-R14);
    RT2 = R24/(X-R24);
    RT3 = R34/(X-R34);
    RT4 = R44/(X-R44);
    WW4 = W44*WW1;
    WW3 = W34*WW1;
    WW2 = W24*WW1;
    WW1 = WW1-WW2-WW3-WW4;
  }
  rts[0] = RT1;
  wts[0] = WW1;
  rts[1] = RT2;
  wts[1] = WW2;
  rts[2] = RT3;
  wts[2] = WW3;
  rts[3] = RT4;
  wts[3] = WW4;
  return;
}

void Root5(double X , double *rts, double *wts){
  double R15,PIE4,R25,W25,R35,W35,R45,W45,R55,W55;
  double RT1=0,RT2=0,RT3=0,RT4=0,RT5=0,
    WW1=0,WW2=0,WW3=0,WW4=0,WW5=0;
  double Y,E=0,XXX;

  R15 = 1.17581320211778E-01;
  PIE4 = 7.85398163397448E-01;
  R25 = 1.07456201243690E+00;
  W25 = 2.70967405960535E-01;
  R35 = 3.08593744371754E+00;
  W35 = 3.82231610015404E-02;
  R45 = 6.41472973366203E+00;
  W45 = 1.51614186862443E-03;
  R55 = 1.18071894899717E+01;
  W55 = 8.62130526143657E-06;

  if (X < 3.e-7){
    RT1 = 2.26659266316985E-02 -2.15865967920897E-03 *X;
    RT2 = 2.31271692140903E-01 -2.20258754389745E-02 *X;
    RT3 = 8.57346024118836E-01 -8.16520023025515E-02 *X;
    RT4 = 2.97353038120346E+00 -2.83193369647137E-01 *X;
    RT5 = 1.84151859759051E+01 -1.75382723579439E+00 *X;
    WW1 = 2.95524224714752E-01 -1.96867576909777E-02 *X;
    WW2 = 2.69266719309995E-01 -5.61737590184721E-02 *X;
    WW3 = 2.19086362515981E-01 -9.71152726793658E-02 *X;
    WW4 = 1.49451349150580E-01 -1.02979262193565E-01 *X;
    WW5 = 6.66713443086877E-02 -5.73782817488315E-02 *X;
  } else if (X < 1.0){
    RT1 = ((((((-4.46679165328413E-11*X+1.21879111988031E-09)*X-
	       2.62975022612104E-08 )*X+5.15106194905897E-07 )*X-
	     9.27933625824749E-06 )*X+1.51794097682482E-04 )*X-
	   2.15865967920301E-03 )*X+2.26659266316985E-02;
    RT2 = (((((( 1.93117331714174E-10*X-4.57267589660699E-09)*X+
	       2.48339908218932E-08 )*X+1.50716729438474E-06 )*X-
	     6.07268757707381E-05 )*X+1.37506939145643E-03 )*X-
	   2.20258754419939E-02 )*X+2.31271692140905E-01;
    RT3 = ((((( 4.84989776180094E-09*X+1.31538893944284E-07)*X-
	      2.766753852879E-06)*X-7.651163510626E-05)*X+
	    4.033058545972E-03)*X-8.16520022916145E-02 )*X+\
      8.57346024118779E-01;
    RT4 = ((((-2.48581772214623E-07*X-4.34482635782585E-06)*X-
	     7.46018257987630E-07 )*X+1.01210776517279E-02 )*X-
	   2.83193369640005E-01 )*X+2.97353038120345E+00;
    RT5 = (((((-8.92432153868554E-09*X+1.77288899268988E-08)*X+
	      3.040754680666E-06)*X+1.058229325071E-04)*X+
	    4.596379534985E-02)*X-1.75382723579114E+00 )*X+\
      1.84151859759049E+01;
    WW1 = ((((((-2.03822632771791E-09*X+3.89110229133810E-08)*X-
	       5.84914787904823E-07 )*X+8.30316168666696E-06 )*X-
	     1.13218402310546E-04 )*X+1.49128888586790E-03 )*X-
	   1.96867576904816E-02 )*X+2.95524224714749E-01;
    WW2 = ((((((( 8.62848118397570E-09*X-1.38975551148989E-07)*X+
		1.602894068228E-06)*X-1.646364300836E-05)*X+
	      1.538445806778E-04)*X-1.28848868034502E-03 )*X+
	    9.38866933338584E-03 )*X-5.61737590178812E-02 )*X+\
      2.69266719309991E-01;
    WW3 = ((((((((-9.41953204205665E-09*X+1.47452251067755E-07)*X-
		 1.57456991199322E-06 )*X+1.45098401798393E-05 )*X-
	       1.18858834181513E-04 )*X+8.53697675984210E-04 )*X-
	     5.22877807397165E-03 )*X+2.60854524809786E-02 )*X-
	   9.71152726809059E-02 )*X+2.19086362515979E-01;
    WW4 = ((((((((-3.84961617022042E-08*X+5.66595396544470E-07)*X-
		 5.52351805403748E-06 )*X+4.53160377546073E-05 )*X-
	       3.22542784865557E-04 )*X+1.95682017370967E-03 )*X-
	     9.77232537679229E-03 )*X+3.79455945268632E-02 )*X-
	   1.02979262192227E-01 )*X+1.49451349150573E-01;
    WW5 = ((((((((( 4.09594812521430E-09*X-6.47097874264417E-08)*X+
		  6.743541482689E-07)*X-5.917993920224E-06)*X+
		4.531969237381E-05)*X-2.99102856679638E-04 )*X+
	      1.65695765202643E-03 )*X-7.40671222520653E-03 )*X+
	    2.50889946832192E-02 )*X-5.73782817487958E-02 )*X+\
      6.66713443086877E-02;
  } else if (X < 5.0) {
    Y = X-3.0E+00;
    RT1 = ((((((((-2.58163897135138E-14*Y+8.14127461488273E-13)*Y-
		 2.11414838976129E-11 )*Y+5.09822003260014E-10 )*Y-
	       1.16002134438663E-08 )*Y+2.46810694414540E-07 )*Y-
	     4.92556826124502E-06 )*Y+9.02580687971053E-05 )*Y-
	   1.45190025120726E-03 )*Y+1.73416786387475E-02;
    RT2 = ((((((((( 1.04525287289788E-14*Y+5.44611782010773E-14)*Y-
		  4.831059411392E-12)*Y+1.136643908832E-10)*Y-
		1.104373076913E-09)*Y-2.35346740649916E-08 )*Y+
	      1.43772622028764E-06 )*Y-4.23405023015273E-05 )*Y+
	    9.12034574793379E-04 )*Y-1.52479441718739E-02 )*Y+\
      1.76055265928744E-01;
    RT3 = (((((((((-6.89693150857911E-14*Y+5.92064260918861E-13)*Y+
		  1.847170956043E-11)*Y-3.390752744265E-10)*Y-
		2.995532064116E-09)*Y+1.57456141058535E-07 )*Y-
	      3.95859409711346E-07 )*Y-9.58924580919747E-05 )*Y+
	    3.23551502557785E-03 )*Y-5.97587007636479E-02 )*Y+\
      6.46432853383057E-01;
    RT4 = ((((((((-3.61293809667763E-12*Y-2.70803518291085E-11)*Y+
		 8.83758848468769E-10 )*Y+1.59166632851267E-08 )*Y-
	       1.32581997983422E-07 )*Y-7.60223407443995E-06 )*Y-
	     7.41019244900952E-05 )*Y+9.81432631743423E-03 )*Y-
	   2.23055570487771E-01 )*Y+2.21460798080643E+00;
    RT5 = ((((((((( 7.12332088345321E-13*Y+3.16578501501894E-12)*Y-
		  8.776668218053E-11)*Y-2.342817613343E-09)*Y-
		3.496962018025E-08)*Y-3.03172870136802E-07 )*Y+
	      1.50511293969805E-06 )*Y+1.37704919387696E-04 )*Y+
	    4.70723869619745E-02 )*Y-1.47486623003693E+00 )*Y+\
      1.35704792175847E+01;
    WW1 = ((((((((( 1.04348658616398E-13*Y-1.94147461891055E-12)*Y+
		  3.485512360993E-11)*Y-6.277497362235E-10)*Y+
		1.100758247388E-08)*Y-1.88329804969573E-07 )*Y+
	      3.12338120839468E-06 )*Y-5.04404167403568E-05 )*Y+
	    8.00338056610995E-04 )*Y-1.30892406559521E-02 )*Y+\
      2.47383140241103E-01;
    WW2 = ((((((((((( 3.23496149760478E-14*Y-5.24314473469311E-13)*Y+
		    7.743219385056E-12)*Y-1.146022750992E-10)*Y+
		  1.615238462197E-09)*Y-2.15479017572233E-08 )*Y+
		2.70933462557631E-07 )*Y-3.18750295288531E-06 )*Y+
	      3.47425221210099E-05 )*Y-3.45558237388223E-04 )*Y+
	    3.05779768191621E-03 )*Y-2.29118251223003E-02 )*Y+\
      1.59834227924213E-01;
    WW3 = ((((((((((((-3.42790561802876E-14*Y+5.26475736681542E-13)*Y-
		     7.184330797139E-12)*Y+9.763932908544E-11)*Y-
		   1.244014559219E-09)*Y+1.472744068942E-08)*Y-
		 1.611749975234E-07)*Y+1.616487851917E-06)*Y-
	       1.46852359124154E-05 )*Y+1.18900349101069E-04 )*Y-
	     8.37562373221756E-04 )*Y+4.93752683045845E-03 )*Y-
	   2.25514728915673E-02 )*Y+6.95211812453929E-02;
    WW4 = ((((((((((((( 1.04072340345039E-14*Y-1.60808044529211E-13)*
		      Y+2.183534866798E-12)*Y-2.939403008391E-11)*Y+
		    3.679254029085E-10)*Y-4.23775673047899E-09 )*Y+
		  4.46559231067006E-08 )*Y-4.26488836563267E-07 )*Y+
		3.64721335274973E-06 )*Y-2.74868382777722E-05 )*Y+
	      1.78586118867488E-04 )*Y-9.68428981886534E-04 )*Y+
	    4.16002324339929E-03 )*Y-1.28290192663141E-02 )*Y+\
      2.22353727685016E-02;
    WW5 = ((((((((((((((-8.16770412525963E-16*Y+1.31376515047977E-14)*
		       Y-1.856950818865E-13)*Y+2.596836515749E-12)*Y-
		     3.372639523006E-11)*Y+4.025371849467E-10)*Y-
		   4.389453269417E-09)*Y+4.332753856271E-08)*Y-
		 3.82673275931962E-07 )*Y+2.98006900751543E-06 )*Y-
	       2.00718990300052E-05 )*Y+1.13876001386361E-04 )*Y-
	     5.23627942443563E-04 )*Y+1.83524565118203E-03 )*Y-
	   4.37785737450783E-03 )*Y+5.36963805223095E-03;
  } else if (X < 10.0) {
    Y = X-7.5E+00;
    RT1 = ((((((((-1.13825201010775E-14*Y+1.89737681670375E-13)*Y-
		 4.81561201185876E-12 )*Y+1.56666512163407E-10 )*Y-
	       3.73782213255083E-09 )*Y+9.15858355075147E-08 )*Y-
	     2.13775073585629E-06 )*Y+4.56547356365536E-05 )*Y-
	   8.68003909323740E-04 )*Y+1.22703754069176E-02;
    RT2 = (((((((((-3.67160504428358E-15*Y+1.27876280158297E-14)*Y-
		  1.296476623788E-12)*Y+1.477175434354E-11)*Y+
		5.464102147892E-10)*Y-2.42538340602723E-08 )*Y+
	      8.20460740637617E-07 )*Y-2.20379304598661E-05 )*Y+
	    4.90295372978785E-04 )*Y-9.14294111576119E-03 )*Y+\
      1.22590403403690E-01;
    RT3 = ((((((((( 1.39017367502123E-14*Y-6.96391385426890E-13)*Y+
		  1.176946020731E-12)*Y+1.725627235645E-10)*Y-
		3.686383856300E-09)*Y+2.87495324207095E-08 )*Y+
	      1.71307311000282E-06 )*Y-7.94273603184629E-05 )*Y+
	    2.00938064965897E-03 )*Y-3.63329491677178E-02 )*Y+\
      4.34393683888443E-01;
    RT4 = ((((((((((-1.27815158195209E-14*Y+1.99910415869821E-14)*Y+
		   3.753542914426E-12)*Y-2.708018219579E-11)*Y-
		 1.190574776587E-09)*Y+1.106696436509E-08)*Y+
	       3.954955671326E-07)*Y-4.398596059588E-06)*Y-
	     2.01087998907735E-04 )*Y+7.89092425542937E-03 )*Y-
	   1.42056749162695E-01 )*Y+1.39964149420683E+00;
    RT5 = ((((((((((-1.19442341030461E-13*Y-2.34074833275956E-12)*Y+
		   6.861649627426E-12)*Y+6.082671496226E-10)*Y+
		 5.381160105420E-09)*Y-6.253297138700E-08)*Y-
	       2.135966835050E-06)*Y-2.373394341886E-05)*Y+
	     2.88711171412814E-06 )*Y+4.85221195290753E-02 )*Y-
	   1.04346091985269E+00 )*Y+7.89901551676692E+00;
    WW1 = ((((((((( 7.95526040108997E-15*Y-2.48593096128045E-13)*Y+
		  4.761246208720E-12)*Y-9.535763686605E-11)*Y+
		2.225273630974E-09)*Y-4.49796778054865E-08 )*Y+
	      9.17812870287386E-07 )*Y-1.86764236490502E-05 )*Y+
	    3.76807779068053E-04 )*Y-8.10456360143408E-03 )*Y+\
      2.01097936411496E-01;
    WW2 = ((((((((((( 1.25678686624734E-15*Y-2.34266248891173E-14)*Y+
		    3.973252415832E-13)*Y-6.830539401049E-12)*Y+
		  1.140771033372E-10)*Y-1.82546185762009E-09 )*Y+
		2.77209637550134E-08 )*Y-4.01726946190383E-07 )*Y+
	      5.48227244014763E-06 )*Y-6.95676245982121E-05 )*Y+
	    8.05193921815776E-04 )*Y-8.15528438784469E-03 )*Y+\
      9.71769901268114E-02;
    WW3 = ((((((((((((-8.20929494859896E-16*Y+1.37356038393016E-14)*Y-
		     2.022863065220E-13)*Y+3.058055403795E-12)*Y-
		   4.387890955243E-11)*Y+5.923946274445E-10)*Y-
		 7.503659964159E-09)*Y+8.851599803902E-08)*Y-
	       9.65561998415038E-07 )*Y+9.60884622778092E-06 )*Y-
	     8.56551787594404E-05 )*Y+6.66057194311179E-04 )*Y-
	   4.17753183902198E-03 )*Y+2.25443826852447E-02;
    WW4 = ((((((((((((((-1.08764612488790E-17*Y+1.85299909689937E-16)*
		       Y-2.730195628655E-15)*Y+4.127368817265E-14)*Y-
		     5.881379088074E-13)*Y+7.805245193391E-12)*Y-
		   9.632707991704E-11)*Y+1.099047050624E-09)*Y-
		 1.15042731790748E-08 )*Y+1.09415155268932E-07 )*Y-
	       9.33687124875935E-07 )*Y+7.02338477986218E-06 )*Y-
	     4.53759748787756E-05 )*Y+2.41722511389146E-04 )*Y-
	   9.75935943447037E-04 )*Y+2.57520532789644E-03;
    WW5 = ((((((((((((((( 7.28996979748849E-19*Y-1.26518146195173E-17)
			*Y+1.886145834486E-16)*Y-2.876728287383E-15)*Y+
		      4.114588668138E-14)*Y-5.44436631413933E-13 )*Y+
		    6.64976446790959E-12 )*Y-7.44560069974940E-11 )*Y+
		  7.57553198166848E-10 )*Y-6.92956101109829E-09 )*Y+
		5.62222859033624E-08 )*Y-3.97500114084351E-07 )*Y+
	      2.39039126138140E-06 )*Y-1.18023950002105E-05 )*Y+
	    4.52254031046244E-05 )*Y-1.21113782150370E-04 )*Y+\
      1.75013126731224E-04;
  } else if (X < 15.0) {
    Y = X-12.5E+00;
    RT1 = ((((((((((-4.16387977337393E-17*Y+7.20872997373860E-16)*Y+
		   1.395993802064E-14)*Y+3.660484641252E-14)*Y-
		 4.154857548139E-12)*Y+2.301379846544E-11)*Y-
	       1.033307012866E-09)*Y+3.997777641049E-08)*Y-
	     9.35118186333939E-07 )*Y+2.38589932752937E-05 )*Y-
	   5.35185183652937E-04 )*Y+8.85218988709735E-03;
    RT2 = ((((((((((-4.56279214732217E-16*Y+6.24941647247927E-15)*Y+
		   1.737896339191E-13)*Y+8.964205979517E-14)*Y-
		 3.538906780633E-11)*Y+9.561341254948E-11)*Y-
	       9.772831891310E-09)*Y+4.240340194620E-07)*Y-
	     1.02384302866534E-05 )*Y+2.57987709704822E-04 )*Y-
	   5.54735977651677E-03 )*Y+8.68245143991948E-02;
    RT3 = ((((((((((-2.52879337929239E-15*Y+2.13925810087833E-14)*Y+
		   7.884307667104E-13)*Y-9.023398159510E-13)*Y-
		 5.814101544957E-11)*Y-1.333480437968E-09)*Y-
	       2.217064940373E-08)*Y+1.643290788086E-06)*Y-
	     4.39602147345028E-05 )*Y+1.08648982748911E-03 )*Y-
	   2.13014521653498E-02 )*Y+2.94150684465425E-01;
    RT4 = ((((((((((-6.42391438038888E-15*Y+5.37848223438815E-15)*Y+
		   8.960828117859E-13)*Y+5.214153461337E-11)*Y-
		 1.106601744067E-10)*Y-2.007890743962E-08)*Y+
	       1.543764346501E-07)*Y+4.520749076914E-06)*Y-
	     1.88893338587047E-04 )*Y+4.73264487389288E-03 )*Y-
	   7.91197893350253E-02 )*Y+8.60057928514554E-01;
    RT5 = (((((((((((-2.24366166957225E-14*Y+4.87224967526081E-14)*Y+
		    5.587369053655E-12)*Y-3.045253104617E-12)*Y-
		  1.223983883080E-09)*Y-2.05603889396319E-09 )*Y+
		2.58604071603561E-07 )*Y+1.34240904266268E-06 )*Y-
	      5.72877569731162E-05 )*Y-9.56275105032191E-04 )*Y+
	    4.23367010370921E-02 )*Y-5.76800927133412E-01 )*Y+\
      3.87328263873381E+00;
    WW1 = ((((((((( 8.98007931950169E-15*Y+7.25673623859497E-14)*Y+
		  5.851494250405E-14)*Y-4.234204823846E-11)*Y+
		3.911507312679E-10)*Y-9.65094802088511E-09 )*Y+
	      3.42197444235714E-07 )*Y-7.51821178144509E-06 )*Y+
	    1.94218051498662E-04 )*Y-5.38533819142287E-03 )*Y+\
      1.68122596736809E-01;
    WW2 = ((((((((((-1.05490525395105E-15*Y+1.96855386549388E-14)*Y-
		   5.500330153548E-13)*Y+1.003849567976E-11)*Y-
		 1.720997242621E-10)*Y+3.533277061402E-09)*Y-
	       6.389171736029E-08)*Y+1.046236652393E-06)*Y-
	     1.73148206795827E-05 )*Y+2.57820531617185E-04 )*Y-
	   3.46188265338350E-03 )*Y+7.03302497508176E-02;
    WW3 = ((((((((((( 3.60020423754545E-16*Y-6.24245825017148E-15)*Y+
		    9.945311467434E-14)*Y-1.749051512721E-12)*Y+
		  2.768503957853E-11)*Y-4.08688551136506E-10 )*Y+
		6.04189063303610E-09 )*Y-8.23540111024147E-08 )*Y+
	      1.01503783870262E-06 )*Y-1.20490761741576E-05 )*Y+
	    1.26928442448148E-04 )*Y-1.05539461930597E-03 )*Y+\
      1.15543698537013E-02;
    WW4 = ((((((((((((( 2.51163533058925E-18*Y-4.31723745510697E-17)*
		      Y+6.557620865832E-16)*Y-1.016528519495E-14)*Y+
		    1.491302084832E-13)*Y-2.06638666222265E-12 )*Y+
		  2.67958697789258E-11 )*Y-3.23322654638336E-10 )*Y+
		3.63722952167779E-09 )*Y-3.75484943783021E-08 )*Y+
	      3.49164261987184E-07 )*Y-2.92658670674908E-06 )*Y+
	    2.12937256719543E-05 )*Y-1.19434130620929E-04 )*Y+\
      6.45524336158384E-04;
    WW5 = ((((((((((((((-1.29043630202811E-19*Y+2.16234952241296E-18)*
		       Y-3.107631557965E-17)*Y+4.570804313173E-16)*Y-
		     6.301348858104E-15)*Y+8.031304476153E-14)*Y-
		   9.446196472547E-13)*Y+1.018245804339E-11)*Y-
		 9.96995451348129E-11 )*Y+8.77489010276305E-10 )*Y-
	       6.84655877575364E-09 )*Y+4.64460857084983E-08 )*Y-
	     2.66924538268397E-07 )*Y+1.24621276265907E-06 )*Y-
	   4.30868944351523E-06 )*Y+9.94307982432868E-06;
  } else if (X < 20.0){
    Y = X-17.5E+00;
    RT1 = (((((((((( 1.91875764545740E-16*Y+7.8357401095707E-16)*Y-
		   3.260875931644E-14)*Y-1.186752035569E-13)*Y+
		 4.275180095653E-12)*Y+3.357056136731E-11)*Y-
	       1.123776903884E-09)*Y+1.231203269887E-08)*Y-
	     3.99851421361031E-07 )*Y+1.45418822817771E-05 )*Y-
	   3.49912254976317E-04 )*Y+6.67768703938812E-03;
    RT2 = (((((((((( 2.02778478673555E-15*Y+1.01640716785099E-14)*Y-
		   3.385363492036E-13)*Y-1.615655871159E-12)*Y+
		 4.527419140333E-11)*Y+3.853670706486E-10)*Y-
	       1.184607130107E-08)*Y+1.347873288827E-07)*Y-
	     4.47788241748377E-06 )*Y+1.54942754358273E-04 )*Y-
	   3.55524254280266E-03 )*Y+6.44912219301603E-02;
    RT3 = (((((((((( 7.79850771456444E-15*Y+6.00464406395001E-14)*Y-
		   1.249779730869E-12)*Y-1.020720636353E-11)*Y+
		 1.814709816693E-10)*Y+1.766397336977E-09)*Y-
	       4.603559449010E-08)*Y+5.863956443581E-07)*Y-
	     2.03797212506691E-05 )*Y+6.31405161185185E-04 )*Y-
	   1.30102750145071E-02 )*Y+2.10244289044705E-01;
    RT4 = (((((((((((-2.92397030777912E-15*Y+1.94152129078465E-14)*Y+
		    4.859447665850E-13)*Y-3.217227223463E-12)*Y-
		  7.484522135512E-11)*Y+7.19101516047753E-10 )*Y+
		6.88409355245582E-09 )*Y-1.44374545515769E-07 )*Y+
	      2.74941013315834E-06 )*Y-1.02790452049013E-04 )*Y+
	    2.59924221372643E-03 )*Y-4.35712368303551E-02 )*Y+\
      5.62170709585029E-01;
    RT5 = ((((((((((( 1.17976126840060E-14*Y+1.24156229350669E-13)*Y-
		    3.892741622280E-12)*Y-7.755793199043E-12)*Y+
		  9.492190032313E-10)*Y-4.98680128123353E-09 )*Y-
		1.81502268782664E-07 )*Y+2.69463269394888E-06 )*Y+
	      2.50032154421640E-05 )*Y-1.33684303917681E-03 )*Y+
	    2.29121951862538E-02 )*Y-2.45653725061323E-01 )*Y+\
      1.89999883453047E+00;
    WW1 = (((((((((( 1.74841995087592E-15*Y-6.95671892641256E-16)*Y-
		   3.000659497257E-13)*Y+2.021279817961E-13)*Y+
		 3.853596935400E-11)*Y+1.461418533652E-10)*Y-
	       1.014517563435E-08)*Y+1.132736008979E-07)*Y-
	     2.86605475073259E-06 )*Y+1.21958354908768E-04 )*Y-
	   3.86293751153466E-03 )*Y+1.45298342081522E-01;
    WW2 = ((((((((((-1.11199320525573E-15*Y+1.85007587796671E-15)*Y+
		   1.220613939709E-13)*Y+1.275068098526E-12)*Y-
		 5.341838883262E-11)*Y+6.161037256669E-10)*Y-
	       1.009147879750E-08)*Y+2.907862965346E-07)*Y-
	     6.12300038720919E-06 )*Y+1.00104454489518E-04 )*Y-
	   1.80677298502757E-03 )*Y+5.78009914536630E-02;
    WW3 = ((((((((((-9.49816486853687E-16*Y+6.67922080354234E-15)*Y+
		   2.606163540537E-15)*Y+1.983799950150E-12)*Y-
		 5.400548574357E-11)*Y+6.638043374114E-10)*Y-
	       8.799518866802E-09)*Y+1.791418482685E-07)*Y-
	     2.96075397351101E-06 )*Y+3.38028206156144E-05 )*Y-
	   3.58426847857878E-04 )*Y+8.39213709428516E-03;
    WW4 = ((((((((((( 1.33829971060180E-17*Y-3.44841877844140E-16)*Y+
		    4.745009557656E-15)*Y-6.033814209875E-14)*Y+
		  1.049256040808E-12)*Y-1.70859789556117E-11 )*Y+
		2.15219425727959E-10 )*Y-2.52746574206884E-09 )*Y+
	      3.27761714422960E-08 )*Y-3.90387662925193E-07 )*Y+
	    3.46340204593870E-06 )*Y-2.43236345136782E-05 )*Y+\
      3.54846978585226E-04;
    WW5 = ((((((((((((( 2.69412277020887E-20*Y-4.24837886165685E-19)*
		      Y+6.030500065438E-18)*Y-9.069722758289E-17)*Y+
		    1.246599177672E-15)*Y-1.56872999797549E-14 )*Y+
		  1.87305099552692E-13 )*Y-2.09498886675861E-12 )*Y+
		2.11630022068394E-11 )*Y-1.92566242323525E-10 )*Y+
	      1.62012436344069E-09 )*Y-1.23621614171556E-08 )*Y+
	    7.72165684563049E-08 )*Y-3.59858901591047E-07 )*Y+\
      2.43682618601000E-06;
  } else if (X < 25.0) {
    Y = X-22.5E+00;
    RT1 = (((((((((-1.13927848238726E-15*Y+7.39404133595713E-15)*Y+
		  1.445982921243E-13)*Y-2.676703245252E-12)*Y+
		5.823521627177E-12)*Y+2.17264723874381E-10 )*Y+
	      3.56242145897468E-09 )*Y-3.03763737404491E-07 )*Y+
	    9.46859114120901E-06 )*Y-2.30896753853196E-04 )*Y+\
      5.24663913001114E-03;
    RT2 = (((((((((( 2.89872355524581E-16*Y-1.22296292045864E-14)*Y+
		   6.184065097200E-14)*Y+1.649846591230E-12)*Y-
		 2.729713905266E-11)*Y+3.709913790650E-11)*Y+
	       2.216486288382E-09)*Y+4.616160236414E-08)*Y-
	     3.32380270861364E-06 )*Y+9.84635072633776E-05 )*Y-
	   2.30092118015697E-03 )*Y+5.00845183695073E-02;
    RT3 = (((((((((( 1.97068646590923E-15*Y-4.89419270626800E-14)*Y+
		   1.136466605916E-13)*Y+7.546203883874E-12)*Y-
		 9.635646767455E-11)*Y-8.295965491209E-11)*Y+
	       7.534109114453E-09)*Y+2.699970652707E-07)*Y-
	     1.42982334217081E-05 )*Y+3.78290946669264E-04 )*Y-
	   8.03133015084373E-03 )*Y+1.58689469640791E-01;
    RT4 = (((((((((( 1.33642069941389E-14*Y-1.55850612605745E-13)*Y-
		   7.522712577474E-13)*Y+3.209520801187E-11)*Y-
		 2.075594313618E-10)*Y-2.070575894402E-09)*Y+
	       7.323046997451E-09)*Y+1.851491550417E-06)*Y-
	     6.37524802411383E-05 )*Y+1.36795464918785E-03 )*Y-
	   2.42051126993146E-02 )*Y+3.97847167557815E-01;
    RT5 = ((((((((((-6.07053986130526E-14*Y+1.04447493138843E-12)*Y-
		   4.286617818951E-13)*Y-2.632066100073E-10)*Y+
		 4.804518986559E-09)*Y-1.835675889421E-08)*Y-
	       1.068175391334E-06)*Y+3.292234974141E-05)*Y-
	     5.94805357558251E-04 )*Y+8.29382168612791E-03 )*Y-
	   9.93122509049447E-02 )*Y+1.09857804755042E+00;
    WW1 = (((((((((-9.10338640266542E-15*Y+1.00438927627833E-13)*Y+
		  7.817349237071E-13)*Y-2.547619474232E-11)*Y+
		1.479321506529E-10)*Y+1.52314028857627E-09 )*Y+
	      9.20072040917242E-09 )*Y-2.19427111221848E-06 )*Y+
	    8.65797782880311E-05 )*Y-2.82718629312875E-03 )*Y+\
      1.28718310443295E-01;
    WW2 = ((((((((( 5.52380927618760E-15*Y-6.43424400204124E-14)*Y-
		  2.358734508092E-13)*Y+8.261326648131E-12)*Y+
		9.229645304956E-11)*Y-5.68108973828949E-09 )*Y+
	      1.22477891136278E-07 )*Y-2.11919643127927E-06 )*Y+
	    4.23605032368922E-05 )*Y-1.14423444576221E-03 )*Y+\
      5.06607252890186E-02;
    WW3 = ((((((((( 3.99457454087556E-15*Y-5.11826702824182E-14)*Y-
		  4.157593182747E-14)*Y+4.214670817758E-12)*Y+
		6.705582751532E-11)*Y-3.36086411698418E-09 )*Y+
	      6.07453633298986E-08 )*Y-7.40736211041247E-07 )*Y+
	    8.84176371665149E-06 )*Y-1.72559275066834E-04 )*Y+\
      7.16639814253567E-03;
    WW4 = (((((((((((-2.14649508112234E-18*Y-2.45525846412281E-18)*Y+
		    6.126212599772E-16)*Y-8.526651626939E-15)*Y+
		  4.826636065733E-14)*Y-3.39554163649740E-13 )*Y+
		1.67070784862985E-11 )*Y-4.42671979311163E-10 )*Y+
	      6.77368055908400E-09 )*Y-7.03520999708859E-08 )*Y+
	    6.04993294708874E-07 )*Y-7.80555094280483E-06 )*Y+\
      2.85954806605017E-04;
    WW5 = ((((((((((((-5.63938733073804E-21*Y+6.92182516324628E-20)*Y-
		     1.586937691507E-18)*Y+3.357639744582E-17)*Y-
		   4.810285046442E-16)*Y+5.386312669975E-15)*Y-
		 6.117895297439E-14)*Y+8.441808227634E-13)*Y-
	       1.18527596836592E-11 )*Y+1.36296870441445E-10 )*Y-
	     1.17842611094141E-09 )*Y+7.80430641995926E-09 )*Y-
	   5.97767417400540E-08 )*Y+1.65186146094969E-06;
  } else if (X < 40) {
    WW1 = sqrt(PIE4/X);
    E = exp(-X);
    RT1 = ((((((((-1.73363958895356E-06*X+1.19921331441483E-04)*X -
		 1.59437614121125E-02)*X+1.13467897349442E+00)*X -
	       4.47216460864586E+01)*X+1.06251216612604E+03)*X -
	     1.52073917378512E+04)*X+1.20662887111273E+05)*X -
	   4.07186366852475E+05)*E + R15/(X-R15);
    RT2 = ((((((((-1.60102542621710E-05*X+1.10331262112395E-03)*X -
		 1.50043662589017E-01)*X+1.05563640866077E+01)*X -
	       4.10468817024806E+02)*X+9.62604416506819E+03)*X -
	     1.35888069838270E+05)*X+1.06107577038340E+06)*X -
	   3.51190792816119E+06)*E + R25/(X-R25);
    RT3 = ((((((((-4.48880032128422E-05*X+2.69025112122177E-03)*X -
		 4.01048115525954E-01)*X+2.78360021977405E+01)*X -
	       1.04891729356965E+03)*X+2.36985942687423E+04)*X -
	     3.19504627257548E+05)*X+2.34879693563358E+06)*X -
	   7.16341568174085E+06)*E + R35/(X-R35);
    RT4 = ((((((((-6.38526371092582E-05*X-2.29263585792626E-03)*X -
		 7.65735935499627E-02)*X+9.12692349152792E+00)*X -
	       2.32077034386717E+02)*X+2.81839578728845E+02)*X +
	     9.59529683876419E+04)*X-1.77638956809518E+06)*X +
	   1.02489759645410E+07)*E + R45/(X-R45);
    RT5 = ((((((((-3.59049364231569E-05*X-2.25963977930044E-02)*X +
		 1.12594870794668E+00)*X-4.56752462103909E+01)*X +
	       1.05804526830637E+03)*X-1.16003199605875E+04)*X -
	     4.07297627297272E+04)*X+2.22215528319857E+06)*X -
	   1.61196455032613E+07)*E + R55/(X-R55);
    WW5 = (((((((((-4.61100906133970E-10*X+1.43069932644286E-07)*X -
		  1.63960915431080E-05)*X+1.15791154612838E-03)*X -
		5.30573476742071E-02)*X+1.61156533367153E+00)*X -
	      3.23248143316007E+01)*X+4.12007318109157E+02)*X -
	    3.02260070158372E+03)*X+9.71575094154768E+03)*E + W55*WW1;
    WW4 = (((((((((-2.40799435809950E-08*X+8.12621667601546E-06)*X -
		  9.04491430884113E-04)*X+6.37686375770059E-02)*X -
		2.96135703135647E+00)*X+9.15142356996330E+01)*X -
	      1.86971865249111E+03)*X+2.42945528916947E+04)*X -
	    1.81852473229081E+05)*X+5.96854758661427E+05)*E + W45*WW1;
    WW3 = (((((((( 1.83574464457207E-05*X-1.54837969489927E-03)*X +
		 1.18520453711586E-01)*X-6.69649981309161E+00)*X +
	       2.44789386487321E+02)*X-5.68832664556359E+03)*X +
	     8.14507604229357E+04)*X-6.55181056671474E+05)*X +
	   2.26410896607237E+06)*E + W35*WW1;
    WW2 = (((((((( 2.77778345870650E-05*X-2.22835017655890E-03)*X +
		 1.61077633475573E-01)*X-8.96743743396132E+00)*X +
	       3.28062687293374E+02)*X-7.65722701219557E+03)*X +
	     1.10255055017664E+05)*X-8.92528122219324E+05)*X +
	   3.10638627744347E+06)*E + W25*WW1;
    WW1 = WW1-0.01962E+00*E-WW2-WW3-WW4-WW5;
  } else if (X < 59.0) {
    WW1 = sqrt(PIE4/X);
    XXX = pow(X,3);
    E = XXX*exp(-X);
    RT1 = (((-2.43758528330205E-02*X+2.07301567989771E+00)*X -
	    6.45964225381113E+01)*X+7.14160088655470E+02)*E + R15/(X-R15);
    RT2 = (((-2.28861955413636E-01*X+1.93190784733691E+01)*X -
	    5.99774730340912E+02)*X+6.61844165304871E+03)*E + R25/(X-R25);
    RT3 = (((-6.95053039285586E-01*X+5.76874090316016E+01)*X -
	    1.77704143225520E+03)*X+1.95366082947811E+04)*E + R35/(X-R35);
    RT4 = (((-1.58072809087018E+00*X+1.27050801091948E+02)*X -
	    3.86687350914280E+03)*X+4.23024828121420E+04)*E + R45/(X-R45);
    RT5 = (((-3.33963830405396E+00*X+2.51830424600204E+02)*X -
	    7.57728527654961E+03)*X+8.21966816595690E+04)*E + R55/(X-R55);
    E = XXX*E;
    WW5 = (( 1.35482430510942E-08*X-3.27722199212781E-07)*X +
	   2.41522703684296E-06)*E + W55*WW1;
    WW4 = (( 1.23464092261605E-06*X-3.55224564275590E-05)*X +
	   3.03274662192286E-04)*E + W45*WW1;
    WW3 = (( 1.34547929260279E-05*X-4.19389884772726E-04)*X +
	   3.87706687610809E-03)*E + W35*WW1;
    WW2 = (( 2.09539509123135E-05*X-6.87646614786982E-04)*X +
	   6.68743788585688E-03)*E + W25*WW1;
    WW1 = WW1-WW2-WW3-WW4-WW5;
  } else {
    WW1 = sqrt(PIE4/X);
    RT1 = R15/(X-R15);
    RT2 = R25/(X-R25);
    RT3 = R35/(X-R35);
    RT4 = R45/(X-R45);
    RT5 = R55/(X-R55);
    WW2 = W25*WW1;
    WW3 = W35*WW1;
    WW4 = W45*WW1;
    WW5 = W55*WW1;
    WW1 = WW1-WW2-WW3-WW4-WW5;
  }
  rts[0] = RT1;
  wts[0] = WW1;
  rts[1] = RT2;
  wts[1] = WW2;
  rts[2] = RT3;
  wts[2] = WW3;
  rts[3] = RT4;
  wts[3] = WW4;
  rts[4] = RT5;
  wts[4] = WW5;
  return;
}
#endif


//switch~case code
#if 1
void __Root1(double X , double rts[] , double wts[]){
	int n = int(X);
	double x = X - double(n) - 0.5;

	switch(n){
	case 0:
		rts[0] = (((((((((((((6.0147916277249647e-010))*x+(2.5829649530351162e-009))*x+(-2.1987943910062313e-008))*x+(2.5136008237799008e-008))*x+(1.0333117946477917e-006))*x+(-1.0002320237845195e-005))*x+(2.4365177163569264e-005))*x+(0.00038771065517669473))*x+(-0.0054079209582592238))*x+(0.037061332476980881))*x+(-0.15869847166000434))*x+(0.41068613464244785));
		wts[0] = (((((((((((((4.8506384094556166e-010))*x+(8.3673512563109398e-009))*x+(-9.3084963737055659e-008))*x+(9.3374486217120034e-007))*x+(-8.5207417820735518e-006))*x+(6.9388468565042175e-005))*x+(-0.00049734119021138657))*x+(0.0030843129661093367))*x+(-0.016203670735739511))*x+(0.070375268412995906))*x+(-0.24909373217951761))*x+(0.85562439189214856));
		break;
	case 1:
		rts[0] = (((((((((((((1.4066851387421289e-010))*x+(1.1629405586669841e-009))*x+(-1.3566629301446178e-009))*x+(-6.5595637958419203e-008))*x+(7.4705174786989425e-007))*x+(-3.3595623042022753e-006))*x+(-1.4631234005690885e-005))*x+(0.00039523521223057873))*x+(-0.003777410800919645))*x+(0.023279189661938666))*x+(-0.099179650046123932))*x+(0.28404418735072601));
		wts[0] = (((((((((((((6.8879065414269758e-010))*x+(3.3614924177527428e-009))*x+(-3.8275781359213092e-008))*x+(3.8535987793390325e-007))*x+(-3.5678965559782228e-006))*x+(2.9602430856812134e-005))*x+(-0.0002174783533182752))*x+(0.0013954739035568762))*x+(-0.0077048638380389587))*x+(0.036181770923925091))*x+(-0.14674026189730302))*x+(0.66335094584033438));
		break;
	case 2:
		rts[0] = (((((((((((((2.255546860396862e-010))*x+(2.9103830456733704e-011))*x+(3.5150454399020719e-009))*x+(-4.562919760549751e-008))*x+(2.7430974114395212e-007))*x+(1.1359342503662143e-007))*x+(-2.2695444540588028e-005))*x+(0.00029328806697511328))*x+(-0.0023874844897344332))*x+(0.014135515387449985))*x+(-0.06246117203817126))*x+(0.20474424184257861));
		wts[0] = (((((((((((((5.6267405549685157e-010))*x+(1.3703053506712117e-009))*x+(-1.5930709196254608e-008))*x+(1.6079987593305609e-007))*x+(-1.5144970954376429e-006))*x+(1.2847507747437703e-005))*x+(-9.7224265071342103e-005))*x+(0.00065009052199253381))*x+(-0.0038118062213925441))*x+(0.019643918527310105))*x+(-0.092841394632251897))*x+(0.54629197178514766));
		break;
	case 3:
		rts[0] = (((((((((((((2.2070404763023058e-010))*x+(-1.9038755757113296e-010))*x+(2.2287167666945602e-009))*x+(-1.7046659195329994e-008))*x+(3.2108346204040572e-008))*x+(1.0512820220280141e-006))*x+(-1.8359252092518354e-005))*x+(0.00018837464347735514))*x+(-0.0014316656923366589))*x+(0.0085121530761145814))*x+(-0.040290650347758417))*x+(0.15430203922689403));
		wts[0] = (((((((((((((4.9961575617392851e-010))*x+(5.6995001311103499e-010))*x+(-6.7857399699278176e-009))*x+(6.7955321962169052e-008))*x+(-6.5308696169571101e-007))*x+(5.6881194060072922e-006))*x+(-4.4595079047600919e-005))*x+(0.00031322798587396505))*x+(-0.0019718972638185965))*x+(0.011301706850845378))*x+(-0.06280709311132901))*x+(0.46984703520162335));
		break;
	case 4:
		rts[0] = (((((((((((((1.3581787546475727e-010))*x+(-9.7619097990294293e-011))*x+(7.9611102895190322e-010))*x+(-3.0963747121859338e-009))*x+(-3.9480786047837078e-008))*x+(9.6075356026403824e-007))*x+(-1.2078935110793053e-005))*x+(0.0001125376725464496))*x+(-0.00084038875499259369))*x+(0.0051798539272196742))*x+(-0.026893223615038941))*x+(0.12126296015254383));
		wts[0] = (((((((((((((5.9177788595358527e-010))*x+(2.2312936683495838e-010))*x+(-3.0989516138409576e-009))*x+(2.9149911521623533e-008))*x+(-2.8676481633738149e-007))*x+(2.5769708713596624e-006))*x+(-2.1066497531307959e-005))*x+(0.00015676299020839224))*x+(-0.0010707095818077346))*x+(0.0068927313968136774))*x+(-0.045059387226920995))*x+(0.41664348158051567));
		break;
	case 5:
		rts[0] = (((((((((((((1.6128372711439926e-010))*x+(-3.9714601977417864e-011))*x+(8.7690447495939822e-011))*x+(1.1732481652870774e-009))*x+(-4.3069690036645625e-008))*x+(6.5227479595364457e-007))*x+(-7.2301126143869965e-006))*x+(6.5045861870801261e-005))*x+(-0.00049330590077258552))*x+(0.0032266467754512628))*x+(-0.018659455805743123))*x+(0.098810579388741354));
		wts[0] = (((((((((((((4.026029879848162e-010))*x+(8.2460852960745485e-011))*x+(-1.4100199526486297e-009))*x+(1.2720041316545879e-008))*x+(-1.2858329985950451e-007))*x+(1.1985390149978532e-006))*x+(-1.0287285162983533e-005))*x+(8.1786955059707608e-005))*x+(-0.00061139351315101886))*x+(0.0044438743313005196))*x+(-0.033950668909015075))*x+(0.37754412943762894));
		break;
	case 6:
		rts[0] = (((((((((((((1.152026622245709e-010))*x+(-8.4886172165473291e-012))*x+(-9.5269570010714233e-011))*x+(1.6851799955475142e-009))*x+(-3.0400097254338711e-008))*x+(3.928076258337872e-007))*x+(-4.1400917210054891e-006))*x+(3.7270082047828147e-005))*x+(-0.00029380884951004288))*x+(0.0020736203967141043))*x+(-0.013458424329740629))*x+(0.082942890717533496));
		wts[0] = (((((((((((((3.5167128468553222e-010))*x+(3.5167128468553223e-011))*x+(-7.231998703597733e-010))*x+(5.6547833082731805e-009))*x+(-5.9024273468821769e-008))*x+(5.7412565013237327e-007))*x+(-5.2100498333373935e-006))*x+(4.4588475078081537e-005))*x+(-0.00036702484281444142))*x+(0.0030131376941392265))*x+(-0.026615006413544497))*x+(0.34749852256904484));
		break;
	case 7:
		rts[0] = (((((((((((((9.4587448984384537e-011))*x+(2.7284841053187847e-012))*x+(-1.176279814292987e-010))*x+(1.245325620402582e-009))*x+(-1.847511536349581e-008))*x+(2.2375582275913075e-007))*x+(-2.3322802936339335e-006))*x+(2.151071976289979e-005))*x+(-0.00017924628757359784))*x+(0.0013797128330772926))*x+(-0.010062073076161174))*x+(0.071297771972864174));
		wts[0] = (((((((((((((4.2443086082736648e-010))*x+(2.3040532444914181e-011))*x+(-4.8703441279940307e-010))*x+(2.5629560695961114e-009))*x+(-2.7801092983281706e-008))*x+(2.8410127110115957e-007))*x+(-2.7434607326644782e-006))*x+(2.5422707311761883e-005))*x+(-0.00023107759682228224))*x+(0.0021350068097243935))*x+(-0.021534429553869947))*x+(0.32356952767817854));
		break;
	case 8:
		rts[0] = (((((((((((((1.0489505560447772e-010))*x+(1.2126596023639042e-012))*x+(-1.1190574393064404e-010))*x+(7.6734825900833426e-010))*x+(-1.0492883006918419e-008))*x+(1.2452172389506205e-007))*x+(-1.3153250558358327e-006))*x+(1.2638668888194834e-005))*x+(-0.00011263315240681025))*x+(0.00095071642941925905))*x+(-0.0077647822146756163))*x+(0.062455550339613058));
		wts[0] = (((((((((((((2.4253192047278083e-010))*x+(8.4886172165473291e-012))*x+(-2.5283952709287405e-010))*x+(1.1940149609775592e-009))*x+(-1.3495612923482742e-008))*x+(1.4558049106957088e-007))*x+(-1.5040687723436954e-006))*x+(1.5147049693927292e-005))*x+(-0.00015198725421535406))*x+(0.0015706168307991575))*x+(-0.017868146871994502))*x+(0.30396196519290031));
		break;
	case 9:
		rts[0] = (((((((((((((7.4578565545380116e-011))*x+(4.2443086082736646e-012))*x+(-7.6283868111204356e-011))*x+(4.3435951132172096e-010))*x+(-5.7852863240744528e-009))*x+(6.9003256442101688e-008))*x+(-7.5116889701002754e-007))*x+(7.6104651277238604e-006))*x+(-7.3069681967657951e-005))*x+(0.00067716284253345927))*x+(-0.006156591432017469))*x+(0.055540289484810712));
		wts[0] = (((((((((((((3.3226873104770977e-010))*x+(-2.3040532444914181e-011))*x+(-2.529911095431695e-010))*x+(5.8707882999442518e-010))*x+(-6.7367598906760877e-009))*x+(7.7372168523955523e-008))*x+(-8.5859818395780008e-007))*x+(9.4094770428654328e-006))*x+(-0.00010394222054018373))*x+(0.0011924264984018809))*x+(-0.015129019589749753))*x+(0.28752622403511491));
		break;
	case 10:
		rts[0] = (((((((((((((5.1234868199874953e-011))*x+(1.2126596023639042e-012))*x+(-4.7123194235609844e-011))*x+(2.3866656799024594e-010))*x+(-3.1620667565827412e-009))*x+(3.8543670181449365e-008))*x+(-4.3767489255053249e-007))*x+(4.7140505453254393e-006))*x+(-4.894009846842054e-005))*x+(0.00049702948730731555))*x+(-0.0049944120793096267))*x+(0.049994714126559696));
		wts[0] = (((((((((((((3.5652192309498787e-010))*x+(-1.4551915228366852e-011))*x+(-2.496562956366688e-010))*x+(2.9043197476615507e-010))*x+(-3.4632610853198758e-009))*x+(4.2679658918132191e-008))*x+(-5.0976284230822933e-007))*x+(6.0746621001565399e-006))*x+(-7.3551572979687244e-005))*x+(0.00092950346643690574))*x+(-0.01302222734661671))*x+(0.27349431072827191));
		break;
	case 11:
		rts[0] = (((((((((((((5.0022208597511053e-011))*x+(6.6696278130014735e-012))*x+(-4.0984104998642579e-011))*x+(1.2520710394407311e-010))*x+(-1.7314931710643577e-009))*x+(2.1879190607402659e-008))*x+(-2.6138262051074906e-007))*x+(3.0078185474143502e-006))*x+(-3.378852767287055e-005))*x+(0.00037463451994014979))*x+(-0.0041302947114381094))*x+(0.045452703411179227));
		wts[0] = (((((((((((((3.5167128468553222e-010))*x+(-1.4551915228366852e-011))*x+(-2.2843475259530047e-010))*x+(1.506729555937151e-010))*x+(-1.8381266878956619e-009))*x+(2.4423741251666797e-008))*x+(-3.1410005677893571e-007))*x+(4.0603487458194341e-006))*x+(-5.3605775932126974e-005))*x+(0.00074077271870883377))*x+(-0.011361891717972257))*x+(0.26133363960695344));
		break;
	case 12:
		rts[0] = (((((((((((((7.5791225147744016e-011))*x+(3.0316490059097606e-013))*x+(-5.475916016924505e-011))*x+(6.965213591077675e-011))*x+(-9.5446731999497071e-010))*x+(1.2686129480243833e-008))*x+(-1.6037709012669171e-007))*x+(1.9762673410343252e-006))*x+(-2.3987805926134476e-005))*x+(0.00028899701378849263))*x+(-0.0034715468317669035))*x+(0.041666021389129296));
		wts[0] = (((((((((((((2.8133702774842578e-010))*x+(-9.701276818911234e-012))*x+(-1.7644197214394808e-010))*x+(7.9126039054244757e-011))*x+(-1.0108275697954619e-009))*x+(1.4480643055018541e-008))*x+(-2.0029443466758795e-007))*x+(2.7990822536831197e-006))*x+(-4.0075619860413518e-005))*x+(0.00060150696399404369))*x+(-0.01002635828416536))*x+(0.25066268375731282));
		break;
	case 13:
		rts[0] = (((((((((((((4.4565240386873484e-011))*x+(-2.5769016550232964e-012))*x+(-3.1055454504288114e-011))*x+(3.9695654171130933e-011))*x+(-5.4038432987605723e-010))*x+(7.5371702952982868e-009))*x+(-1.0116492984065435e-007))*x+(1.3352147606079019e-006))*x+(-1.7463042792334457e-005))*x+(0.00022745923991624589))*x+(-0.0029583431602893057))*x+(0.038461311441862468));
		wts[0] = (((((((((((((2.7163575092951453e-010))*x+(1.2126596023639042e-012))*x+(-1.7068183903271952e-010))*x+(3.8577733600201704e-011))*x+(-5.6485305321984914e-010))*x+(8.8774688341194015e-009))*x+(-1.31770798124838e-007))*x+(1.9828649039747384e-006))*x+(-3.0625416647408109e-005))*x+(0.00049626884676092398))*x+(-0.008933296227906019))*x+(0.24120036911254678));
		break;
	case 14:
		rts[0] = (((((((((((((3.8198777474462986e-011))*x+(-2.4253192047278085e-012))*x+(-2.4707939398164552e-011))*x+(2.2509993868879974e-011))*x+(-3.1141903870472254e-010))*x+(4.595156847623608e-009))*x+(-6.5568191764953086e-008))*x+(9.257002870910469e-007))*x+(-1.3000273687585606e-005))*x+(0.00018217231981533522))*x+(-0.0025509370904348307))*x+(0.035714205555522849));
		wts[0] = (((((((((((((2.7891170854369796e-010))*x+(6.6696278130014735e-012))*x+(-1.7689671949483452e-010))*x+(1.7659355459424358e-011))*x+(-3.1743259872503887e-010))*x+(5.6132331375617168e-009))*x+(-8.9156131958626845e-008))*x+(1.4386840456737102e-006))*x+(-2.3853060589347955e-005))*x+(0.00041509369088357778))*x+(-0.0080253128061486805))*x+(0.2327345757259478));
		break;
	case 15:
		rts[0] = (((((((((((((5.3357022504011788e-011))*x+(-1.2126596023639042e-012))*x+(-3.5053441630831607e-011))*x+(1.2391865311656147e-011))*x+(-1.7962283512436744e-010))*x+(2.8752751290994638e-009))*x+(-4.3605272133836102e-008))*x+(6.570483878457859e-007))*x+(-9.8712325151869198e-006))*x+(0.00014813285835139448))*x+(-0.0022221927936151744))*x+(0.033333304942664559));
		wts[0] = (((((((((((((2.2676734564205009e-010))*x+(-6.0632980118195212e-013))*x+(-1.4044114019876966e-010))*x+(1.2505552149377762e-011))*x+(-1.8777276030353582e-010))*x+(3.6498709240125509e-009))*x+(-6.1852907092448575e-008))*x+(1.0660602773882033e-006))*x+(-1.8888915095660597e-005))*x+(0.00035135237604273317))*x+(-0.0072613442845029389))*x+(0.22510185835870919));
		break;
	case 16:
		rts[0] = (((((((((((((2.9406995357324675e-011))*x+(-1.3642420526593924e-012))*x+(-1.8284633066893243e-011))*x+(7.5980703210613374e-012))*x+(-1.100275426324515e-010))*x+(1.8447590122150359e-009))*x+(-2.9700820395698692e-008))*x+(4.7635001469240962e-007))*x+(-7.6275238663168583e-006))*x+(0.00012206491026153554))*x+(-0.0019531145741666031))*x+(0.031249989917875334));
		wts[0] = (((((((((((((3.0195224098861217e-010))*x+(4.2443086082736646e-012))*x+(-1.9182759084894011e-010))*x+(4.0169349328304333e-012))*x+(-9.4303231890080497e-011))*x+(2.4359418186274224e-009))*x+(-4.3882623460926119e-008))*x+(8.0476148678343396e-007))*x+(-1.5177130052890229e-005))*x+(0.0003005140029240701))*x+(-0.0066113308161619361))*x+(0.21817398518935294));
		break;
	case 17:
		rts[0] = (((((((((((((4.2746250983327627e-011))*x+(-6.0632980118195212e-013))*x+(-2.6849041508588318e-011))*x+(4.2727303177040694e-012))*x+(-6.5050187458837172e-011))*x+(1.2122936728549878e-009))*x+(-2.067931833179178e-008))*x+(3.5197647315262276e-007))*x+(-5.9858571973779116e-006))*x+(0.00010176889775351249))*x+(-0.0017301001029848993))*x+(0.029411761117234356));
		wts[0] = (((((((((((((2.6557245291769505e-010))*x+(6.0632980118195212e-013))*x+(-1.6742281635136655e-010))*x+(3.259022681352993e-012))*x+(-5.1329607231309637e-011))*x+(1.6630181676191567e-009))*x+(-3.1759486004053386e-008))*x+(6.1759796536146416e-007))*x+(-1.2352558830530658e-005))*x+(0.00025940624862657208))*x+(-0.0060528208378366208))*x+(0.21184875443424239));
		break;
	case 18:
		rts[0] = (((((((((((((2.986174270821114e-011))*x+(9.0949470177292824e-013))*x+(-1.7953046456871864e-011))*x+(1.8000415972589203e-012))*x+(-4.1493327292603986e-011))*x+(8.146929057299227e-010))*x+(-1.4688247100084576e-008))*x+(2.6455003846829561e-007))*x+(-4.7627590936058506e-006))*x+(8.5733201901555534e-005))*x+(-0.0015432085581661076))*x+(0.027777776497837421));
		wts[0] = (((((((((((((2.5708383570114768e-010))*x+(-3.637978807091713e-012))*x+(-1.6279955161735413e-010))*x+(3.7137700322394567e-012))*x+(-2.2168933355715126e-011))*x+(1.1591841560705991e-009))*x+(-2.339973903531245e-008))*x+(4.8097082997837026e-007))*x+(-1.016931901154372e-005))*x+(0.00022575980812198729))*x+(-0.0055687450126848895))*x+(0.20604357470675794));
		break;
	case 19:
		rts[0] = (((((((((((((2.1221543041368324e-011))*x+(3.0316490059097606e-013))*x+(-1.2126596023639042e-011))*x+(1.2316074086508404e-012))*x+(-2.7187733545967298e-011))*x+(5.5869027922502324e-010))*x+(-1.0623563954463101e-008))*x+(2.0190900788345326e-007))*x+(-3.8365969259416639e-006))*x+(7.2896681577371461e-005))*x+(-0.0013850410809580957))*x+(0.026315789016356651));
		wts[0] = (((((((((((((2.5223319729169208e-010))*x+(-1.5764574830730755e-011))*x+(-1.5825207810848951e-010))*x+(1.1217101321866114e-011))*x+(-4.6990559591601271e-012))*x+(8.2140161339339102e-010))*x+(-1.7518911950749803e-008))*x+(3.7952677326795009e-007))*x+(-8.4581029916227131e-006))*x+(0.00019791995195630091))*x+(-0.0051459198836627997))*x+(0.20069087886109258));
		break;
	case 20:
		rts[0] = (((((((((((((2.0160465889299907e-011))*x+(-1.5916157281026244e-012))*x+(-1.1435001094165878e-011))*x+(1.7716198878285163e-012))*x+(-1.7472245872340864e-011))*x+(3.9023984044206372e-010))*x+(-7.8110120223702958e-009))*x+(1.5624235294442457e-007))*x+(-3.1249703474090875e-006))*x+(6.2499913600493284e-005))*x+(-0.0012499998319425454))*x+(0.024999999836333796));
		wts[0] = (((((((((((((2.5829649530351162e-010))*x+(-1.2126596023639042e-012))*x+(-1.6242059549161544e-010))*x+(1.2884508275116482e-012))*x+(8.5265128291212022e-012))*x+(5.9498480216764926e-010))*x+(-1.3307322947279468e-008))*x+(3.0304591547292148e-007))*x+(-7.0999630932451945e-006))*x+(0.00017465921947277621))*x+(-0.0047740190822638095))*x+(0.19573478362293811));
		break;
	case 21:
		rts[0] = (((((((((((((3.0013325158506632e-011))*x+(1.5158245029548803e-012))*x+(-1.8549902354910348e-011))*x+(-4.6422125402993199e-013))*x+(-9.2702142258834393e-012))*x+(2.777854983075182e-010))*x+(-5.8295746748389847e-009))*x+(1.224232113461454e-007))*x+(-2.5709346426899811e-006))*x+(5.3989819030468095e-005))*x+(-0.0011337867879225401))*x+(0.023809523750867756));
		wts[0] = (((((((((((((2.0979011120895544e-010))*x+(-1.2126596023639042e-012))*x+(-1.2876929152601707e-010))*x+(9.8528592692067219e-013))*x+(8.1854523159563509e-012))*x+(4.3668535454344232e-010))*x+(-1.0240525760707442e-008))*x+(2.4458449014256683e-007))*x+(-6.0098025548109089e-006))*x+(0.00015505295326747232))*x+(-0.0044448514801835436))*x+(0.19112861410779311));
		break;
	case 22:
		rts[0] = (((((((((((((2.3950027146687109e-011))*x+(-1.5158245029548803e-013))*x+(-1.4532967422079914e-011))*x+(2.7474319116057206e-013))*x+(-6.0964566728216596e-012))*x+(2.0049917281994564e-010))*x+(-4.4099952578591228e-009))*x+(9.7017973062681507e-008))*x+(-2.1344132592054921e-006))*x+(4.695716400367432e-005))*x+(-0.0010330578296806328))*x+(0.022727272706223916));
		wts[0] = (((((((((((((2.0979011120895544e-010))*x+(9.0949470177292824e-012))*x+(-1.3271043523369977e-010))*x+(-5.9117155615240335e-012))*x+(1.5688783605583009e-011))*x+(3.2650149250912364e-010))*x+(-7.9758555315834201e-009))*x+(1.99333767566164e-007))*x+(-5.1257342239726294e-006))*x+(0.00013839484284971132))*x+(-0.0041518453416385138))*x+(0.18683304054291625));
		break;
	case 23:
		rts[0] = (((((((((((((3.152914966146151e-011))*x+(-3.1074402310575047e-012))*x+(-1.9554136088117957e-011))*x+(2.0558369821325564e-012))*x+(-2.1837346745693748e-012))*x+(1.4649052341534721e-010))*x+(-3.3778488154704669e-009))*x+(7.7683543930895369e-008))*x+(-1.7867275278378907e-006))*x+(4.1094760564300975e-005))*x+(-0.00094517957638393449))*x+(0.021739130427220355));
		wts[0] = (((((((((((((2.2676734564205009e-010))*x+(7.2759576141834259e-012))*x+(-1.425632945029065e-010))*x+(-4.5474735088646412e-012))*x+(2.1429968910524622e-011))*x+(2.4608463415158133e-010))*x+(-6.2799919338848058e-009))*x+(1.6390684720590798e-007))*x+(-4.4020747452244704e-006))*x+(0.00012413851626643285))*x+(-0.0038896735302168537))*x+(0.18281465598241869));
		break;
	case 24:
		rts[0] = (((((((((((((3.1983897012347974e-011))*x+(-1.2884508275116482e-012))*x+(-1.9828879279278528e-011))*x+(9.0002079862946007e-013))*x+(-2.818486185181728e-013))*x+(1.0888327276840452e-010))*x+(-2.6167328674257346e-009))*x+(6.2793253744845374e-008))*x+(-1.5070403985179928e-006))*x+(3.6168980059486891e-005))*x+(-0.00086805555277575308))*x+(0.020833333330613501));
		wts[0] = (((((((((((((2.0008883439004421e-010))*x+(4.850638409455617e-012))*x+(-1.2695030212247124e-010))*x+(-4.0927261579781771e-012))*x+(2.0918378140777349e-011))*x+(1.8808539910727024e-010))*x+(-4.9939753073620823e-009))*x+(1.3587983834402923e-007))*x+(-3.8046406960664156e-006))*x+(0.00011185644088451685))*x+(-0.0036539770762452845))*x+(0.17904487675889885));
		break;
	case 25:
		rts[0] = (((((((((((((2.5314269199346502e-011))*x+(-1.8947806286936002e-012))*x+(-1.5319301382987757e-011))*x+(1.2221335055073721e-012))*x+(-1.5395092608135558e-013))*x+(8.1707973720313021e-011))*x+(-2.0482245159196091e-009))*x+(5.1199970004430398e-008))*x+(-1.2799998220953495e-006))*x+(3.1999999488824024e-005))*x+(-0.00079999999900013817))*x+(0.019999999999020777));
		wts[0] = (((((((((((((2.1706606882313886e-010))*x+(7.2759576141834259e-012))*x+(-1.3559050178931403e-010))*x+(-5.4569682106375694e-012))*x+(2.412055740326953e-011))*x+(1.4550020447738157e-010))*x+(-4.0081949611211103e-009))*x+(1.134936429281197e-007))*x+(-3.3075340021467467e-006))*x+(0.0001012105434901415))*x+(-0.0034411584812312226))*x+(0.17549908255120195));
		break;
	case 26:
		rts[0] = (((((((((((((2.7588005953778822e-011))*x+(-6.8212102632969618e-013))*x+(-1.7090921270816274e-011))*x+(3.221127068779121e-013))*x+(1.2517394528307096e-012))*x+(6.2250945139415606e-011))*x+(-1.6188666703461272e-009))*x+(4.2082646959743876e-008))*x+(-1.0941492939499828e-006))*x+(2.8447883293979355e-005))*x+(-0.00073964497005432313))*x+(0.019230769230416247));
		wts[0] = (((((((((((((2.0979011120895544e-010))*x+(-1.8189894035458565e-012))*x+(-1.321041054325178e-010))*x+(1.5158245029548811e-013))*x+(2.5011104298755523e-011))*x+(1.1245759878875106e-010))*x+(-3.2444035606242019e-009))*x+(9.5454458855688998e-008))*x+(-2.8909087943692251e-006))*x+(9.1930902452917268e-005))*x+(-0.0032482252208187678))*x+(0.17215593670646431));
		break;
	case 27:
		rts[0] = (((((((((((((1.7886729134867587e-011))*x+(-2.2737367544323206e-012))*x+(-1.1160257903005306e-011))*x+(1.4021376652332644e-012))*x+(6.5369931689929217e-013))*x+(4.7535309022350696e-011))*x+(-1.2907986531492572e-009))*x+(3.4845872631805719e-008))*x+(-9.4083818247732898e-007))*x+(2.540263164626614e-005))*x+(-0.00068587105611192024))*x+(0.018518518518390998));
		wts[0] = (((((((((((((2.0736479200422764e-010))*x+(7.8822874153653775e-012))*x+(-1.2467656536803892e-010))*x+(-6.063298011819521e-012))*x+(2.2206828968288999e-011))*x+(8.979602246957559e-011))*x+(-2.6461804599383259e-009))*x+(8.0798802019425395e-008))*x+(-2.5393965717435125e-006))*x+(8.3800087830922701e-005))*x+(-0.0030726698872558115))*x+(0.16899684380024907));
		break;
	case 28:
		rts[0] = (((((((((((((2.8952248006438214e-011))*x+(3.0316490059097606e-013))*x+(-1.8521480645479944e-011))*x+(-2.4632148173016805e-013))*x+(2.81493347150293e-012))*x+(3.7149542701323903e-011))*x+(-1.0379542040676408e-009))*x+(2.9052240317165946e-008))*x+(-8.1346312066678706e-007))*x+(2.2776967906886398e-005))*x+(-0.00063775510199425391))*x+(0.017857142857096497));
		wts[0] = (((((((((((((1.673470251262188e-010))*x+(-2.4253192047278085e-012))*x+(-1.0049916454590857e-010))*x+(8.3370347662518408e-013))*x+(1.8114102810310822e-011))*x+(6.9926879101937331e-011))*x+(-2.1742424157385658e-009))*x+(6.8801982185580826e-008))*x+(-2.2409798224876094e-006))*x+(7.6641511006873359e-005))*x+(-0.0029123774183107661))*x+(0.166005512844137));
		break;
	case 29:
		rts[0] = (((((((((((((2.1524707941959299e-011))*x+(-3.0316490059097606e-013))*x+(-1.3452942463724563e-011))*x+(9.4739031434680016e-014))*x+(1.893596390800667e-012))*x+(2.9006722949513154e-011))*x+(-8.4082785178907216e-010))*x+(2.4376980360211558e-008))*x+(-7.0693259931568309e-007))*x+(2.0501045553733558e-005))*x+(-0.00059453032104637635))*x+(0.017241379310344824));
		wts[0] = (((((((((((((1.988761747876803e-010))*x+(-1.0307606620093186e-011))*x+(-1.239944443417092e-010))*x+(5.5327594357853124e-012))*x+(2.4916365267320842e-011))*x+(5.4908374143754678e-011))*x+(-1.7995702705775327e-009))*x+(5.8912074922072101e-008))*x+(-1.9861767492172313e-006))*x+(7.0310659000621945e-005))*x+(-0.0027655525873469533))*x+(0.16316760265346789));
		break;
	case 30:
		rts[0] = (((((((((((((2.1069960591072835e-011))*x+(-2.2737367544323206e-013))*x+(-1.3197147078850927e-011))*x+(4.7369515717340021e-014))*x+(2.1079434494216303e-012))*x+(2.2891614529877792e-011))*x+(-6.8612104886511815e-010))*x+(2.0576124507935372e-008))*x+(-6.1728394329154291e-007))*x+(1.8518518519018007e-005))*x+(-0.00055555555555559632))*x+(0.016666666666666659));
		wts[0] = (((((((((((((1.964508555829525e-010))*x+(1.2126596023639042e-012))*x+(-1.2353969699082276e-010))*x+(-1.5158245029548803e-012))*x+(2.5560590681076669e-011))*x+(4.5531578507507213e-011))*x+(-1.4985577223569635e-009))*x+(5.0705264579657225e-008))*x+(-1.767443373323907e-006))*x+(6.468842988223883e-005))*x+(-0.0026306628150357873))*x+(0.16047043171716635));
		break;
	case 31:
		rts[0] = (((((((((((((2.3343697345505156e-011))*x+(-4.5474735088646412e-013))*x+(-1.4570863034653787e-011))*x+(2.5579538487363607e-013))*x+(2.5555853729504934e-012))*x+(1.8136011211330089e-011))*x+(-5.6364461246497888e-010))*x+(1.7464717338988578e-008))*x+(-5.4140619815586566e-007))*x+(1.6783592360229693e-005))*x+(-0.00052029136316338476))*x+(0.016129032258064523));
		wts[0] = (((((((((((((1.5885840790967146e-010))*x+(-4.850638409455617e-012))*x+(-9.5875899811896176e-011))*x+(2.2737367544323206e-012))*x+(1.8455163323475667e-011))*x+(3.6199783911191233e-011))*x+(-1.2544309295018743e-009))*x+(4.3853618810392917e-008))*x+(-1.5787305648514343e-006))*x+(5.9676016306631212e-005))*x+(-0.0025063926847828715))*x+(0.15790273914133093));
		break;
	case 32:
		rts[0] = (((((((((((((2.0008883439004421e-011))*x+(1.5158245029548803e-013))*x+(-1.2391865311656147e-011))*x+(-1.3263464400855202e-013))*x+(2.1884716261411086e-012))*x+(1.4597508387244787e-011))*x+(-4.6588199964503474e-010))*x+(1.4901155346673058e-008))*x+(-4.7683715263350612e-007))*x+(1.5258789062786805e-005))*x+(-0.00048828125))*x+(0.015624999999999998));
		wts[0] = (((((((((((((1.964508555829525e-010))*x+(-6.0632980118195212e-013))*x+(-1.2278178473934531e-010))*x+(-4.5474735088646412e-013))*x+(2.5702699228228689e-011))*x+(3.0115169617298911e-011))*x+(-1.0573586450846051e-009))*x+(3.8100188189578902e-008))*x+(-1.4151522942743946e-006))*x+(5.5190941913724194e-005))*x+(-0.002391607482744001))*x+(0.15545448637834702));
		break;
	case 33:
		rts[0] = (((((((((((((1.8644641386345029e-011))*x+(-7.5791225147744013e-013))*x+(-1.1510792319313623e-011))*x+(4.3106259302779405e-013))*x+(2.092548356813495e-012))*x+(1.1654085104358577e-011))*x+(-3.8736040301283004e-010))*x+(1.2776164015626533e-008))*x+(-4.2161323881897045e-007))*x+(1.3913237053686521e-005))*x+(-0.00045913682277319551))*x+(0.015151515151515155));
		wts[0] = (((((((((((((1.8553691916167736e-010))*x+(-4.850638409455617e-012))*x+(-1.1603636570119609e-010))*x+(2.0463630789890885e-012))*x+(2.4423722303860508e-011))*x+(2.4267402901993286e-011))*x+(-8.9524980021830436e-010))*x+(3.3243070518551576e-008))*x+(-1.2727353809564395e-006))*x+(5.1163964724950287e-005))*x+(-0.0022853237576011668))*x+(0.1531166917592601));
		break;
	case 34:
		rts[0] = (((((((((((((1.7962520360015333e-011))*x+(-3.0316490059097606e-013))*x+(-1.1136573145146636e-011))*x+(1.3263464400855202e-013))*x+(2.099653784171096e-012))*x+(9.5064696855236743e-012))*x+(-3.2386524943343409e-010))*x+(1.1004629059859401e-008))*x+(-3.7415739232461259e-007))*x+(1.2721351516482848e-005))*x+(-0.00043252595155710748))*x+(0.014705882352941178));
		wts[0] = (((((((((((((1.8917489796876907e-010))*x+(-3.637978807091713e-012))*x+(-1.1808272878018519e-010))*x+(1.5916157281026244e-012))*x+(2.4944786976751253e-011))*x+(2.0023094293719623e-011))*x+(-7.6187175087246339e-010))*x+(2.9121716001630677e-008))*x+(-1.148227932364539e-006))*x+(4.7536638818346237e-005))*x+(-0.0021866853855756229))*x+(0.15088129160471181));
		break;
	case 35:
		rts[0] = (((((((((((((1.8341476485754051e-011))*x+(-4.5474735088646412e-013))*x+(-1.1435001094165878e-011))*x+(2.2263672387149808e-013))*x+(2.2429465692160493e-012))*x+(7.7419552250527577e-012))*x+(-2.722054063634497e-010))*x+(9.519843210033704e-009))*x+(-3.3319449668084417e-007))*x+(1.1661807580304329e-005))*x+(-0.00040816326530613179))*x+(0.014285714285714284));
		wts[0] = (((((((((((((1.7947362114985782e-010))*x+(3.0316490059097605e-012))*x+(-1.1186784831807016e-010))*x+(-2.5011104298755523e-012))*x+(2.3608966633522261e-011))*x+(1.7453298066053925e-011))*x+(-6.5124912869881269e-010))*x+(2.560790897850514e-008))*x+(-1.038952528231718e-006))*x+(4.4259379991075834e-005))*x+(-0.0020949439860796547))*x+(0.14874102301164588));
		break;
	case 36:
		rts[0] = (((((((((((((1.6370904631912708e-011))*x+(-7.5791225147744016e-014))*x+(-1.0174971976084635e-011))*x+(4.736951571733997e-015))*x+(2.0049147527364162e-012))*x+(6.3934043244747345e-012))*x+(-2.2988078107744059e-010))*x+(8.2690829369032778e-009))*x+(-2.9768708557457535e-007))*x+(1.0716735253970867e-005))*x+(-0.00038580246913581427))*x+(0.01388888888888889));
		wts[0] = (((((((((((((1.7583564234276611e-010))*x+(-9.0949470177292824e-012))*x+(-1.0785091338523974e-010))*x+(4.9264296346033616e-012))*x+(2.2282620193436742e-011))*x+(1.3123724329489049e-011))*x+(-5.5906242598287759e-010))*x+(2.2598838060143102e-008))*x+(-9.4269220698069611e-007))*x+(4.1289920555733398e-005))*x+(-0.0020094428003847109))*x+(0.1466893244280783));
		break;
	case 37:
		rts[0] = (((((((((((((1.3339255626002947e-011))*x+(3.7895612573872008e-014))*x+(-8.033869865660865e-012))*x+(-9.9475983006414026e-014))*x+(1.4850343177386092e-012))*x+(5.3105668011236649e-012))*x+(-1.9499749962884985e-010))*x+(7.2104271257404183e-009))*x+(-2.6678604260939781e-007))*x+(9.8710836479286995e-006))*x+(-0.00036523009495979109))*x+(0.013513513513513511));
		wts[0] = (((((((((((((1.6613436552385488e-010))*x+(-6.063298011819521e-012))*x+(-1.0254552762489766e-010))*x+(3.3348139065007363e-012))*x+(2.1363651588520345e-011))*x+(1.1127099242003167e-011))*x+(-4.820141323117847e-010))*x+(2.0010741508258431e-008))*x+(-8.5760144683903294e-007))*x+(3.8592066909241371e-005))*x+(-0.0019296033454826223))*x+(0.14472025091120311));
		break;
	case 38:
		rts[0] = (((((((((((((1.546140993013978e-011))*x+(-3.7895612573872007e-013))*x+(-9.6065377874765545e-012))*x+(1.8000415972589201e-013))*x+(1.9421501444109408e-012))*x+(4.34822548337858e-012))*x+(-1.6623391552172959e-010))*x+(6.3103288150401218e-009))*x+(-2.3979250789174511e-007))*x+(9.1121154689050489e-006))*x+(-0.00034626038781164291))*x+(0.013157894736842103));
		wts[0] = (((((((((((((1.673470251262188e-010))*x+(-6.0632980118195212e-013))*x+(-1.0292448375063638e-010))*x+(-5.3053857603420817e-013))*x+(2.1505760135672368e-011))*x+(1.0272079483305181e-011))*x+(-4.1733313101606956e-010))*x+(1.7775753313742367e-008))*x+(-7.821361934038743e-007))*x+(3.6134694280052601e-005))*x+(-0.0018549143061436766))*x+(0.14282840157304369));
		break;
	case 39:
		rts[0] = (((((((((((((1.5991948506173987e-011))*x+(-2.6526928801710404e-013))*x+(-9.8954918333523275e-012))*x+(1.1842378929335001e-013))*x+(2.007283228522283e-012))*x+(3.6313174689439616e-012))*x+(-1.4226899288279543e-010))*x+(5.5417497812904051e-009))*x+(-2.1612826535284216e-007))*x+(8.429002511988493e-006))*x+(-0.00032873109796186954))*x+(0.012820512820512818));
		wts[0] = (((((((((((((1.5279510989785194e-010))*x+(-7.8822874153653775e-012))*x+(-9.398111918320258e-011))*x+(4.3200998334214083e-012))*x+(1.9563609991261426e-011))*x+(7.595701845275471e-012))*x+(-3.6247153426908579e-010))*x+(1.5838621081343263e-008))*x+(-7.1499845936499418e-007))*x+(3.3890928664135712e-005))*x+(-0.0017849222429730898))*x+(0.14100885719488179));
		break;
		/*
	case 40:
		rts[0] = (((((((((((((1.6674069532503683e-011))*x+(-7.5791225147744016e-014))*x+(-1.0421293457814802e-011))*x+(-2.368475785867001e-014))*x+(2.1778134851047071e-012))*x+(3.0751697484750671e-012))*x+(-1.2226308854224044e-010))*x+(4.8828083798468924e-009))*x+(-1.9531249487632813e-007))*x+(7.8125000002419992e-006))*x+(-0.00031249999999999854))*x+(0.012499999999999999));
		wts[0] = (((((((((((((1.673470251262188e-010))*x+(-2.4253192047278085e-012))*x+(-1.0444030825359126e-010))*x+(5.3053857603420807e-013))*x+(2.233946361229755e-011))*x+(7.2759576141834251e-012))*x+(-3.1642422015920602e-010))*x+(1.4153175520448258e-008))*x+(-6.5509207847203044e-007))*x+(3.1837477454055296e-005))*x+(-0.0017192237823205128))*x+(0.13925712636795548));
		break;
	case 41:
		rts[0] = (((((((((((((1.5006662579253316e-011))*x+(-3.7895612573872007e-013))*x+(-9.312846790029047e-012))*x+(1.9895196601282803e-013))*x+(1.9350447170533398e-012))*x+(2.5351572692973905e-012))*x+(-1.0543029412464951e-010))*x+(4.3156959857644966e-009))*x+(-1.7694348074479927e-007))*x+(7.2546828979019413e-006))*x+(-0.00029744199881024487))*x+(0.012195121951219506));
		wts[0] = (((((((((((((1.673470251262188e-010))*x+(-3.637978807091713e-012))*x+(-1.0428872580329578e-010))*x+(1.5158245029548805e-012))*x+(2.2292094096580211e-011))*x+(5.9401372709544376e-012))*x+(-2.7692692583514145e-010))*x+(1.2681953265314405e-008))*x+(-6.0148747460520013e-007))*x+(2.9954078710536788e-005))*x+(-0.001657459021887131))*x+(0.13756909881662488));
		break;
	case 42:
		rts[0] = (((((((((((((1.6522487082208194e-011))*x+(-6.8212102632969618e-013))*x+(-1.0392871748384398e-011))*x+(3.5053441630831611e-013))*x+(2.2168933355715122e-012))*x+(2.1129764604665975e-012))*x+(-9.1288051192369338e-011))*x+(3.8258137028771931e-009))*x+(-1.6068407153226513e-007))*x+(6.7487312386133496e-006))*x+(-0.00028344671201815925))*x+(0.011904761904761906));
		wts[0] = (((((((((((((1.697723443309466e-010))*x+(-4.850638409455617e-012))*x+(-1.0686562745831906e-010))*x+(2.1221543041368323e-012))*x+(2.3334223442361687e-011))*x+(4.992746956607637e-012))*x+(-2.4334845249995851e-010))*x+(1.1393371283456114e-008))*x+(-5.5339299587231494e-007))*x+(2.822304598149028e-005))*x+(-0.0015993059388097128))*x+(0.1359410047987997));
		break;
	case 43:
		rts[0] = (((((((((((((1.2808717049968738e-011))*x+(-3.7895612573872007e-013))*x+(-7.8017592386459e-012))*x+(2.1789977229976401e-013))*x+(1.5738521597086219e-012))*x+(1.7950085862139529e-012))*x+(-7.9223387109787297e-011))*x+(3.4011688650655478e-009))*x+(-1.4625010095678512e-007))*x+(6.2887544492265975e-006))*x+(-0.00027041644131961491))*x+(0.011627906976744186));
		wts[0] = (((((((((((((1.5036979069312412e-010))*x+(-4.850638409455617e-012))*x+(-9.2162129779656724e-011))*x+(2.0463630789890885e-012))*x+(1.9175179962379236e-011))*x+(4.2774672692758031e-012))*x+(-2.1383783632700213e-010))*x+(1.0261265022866912e-008))*x+(-5.1013196222804414e-007))*x+(2.662889014628152e-005))*x+(-0.0015444756283920457))*x+(0.13436937967011833));
		break;
	case 44:
		rts[0] = (((((((((((((1.2505552149377763e-011))*x+(-3.4106051316484809e-013))*x+(-7.5933333694896045e-012))*x+(1.5158245029548806e-013))*x+(1.5276668818842154e-012))*x+(1.5491311936936352e-012))*x+(-6.9026062643473551e-011))*x+(3.0318418331454211e-009))*x+(-1.3340106321096018e-007))*x+(5.8696468821916905e-006))*x+(-0.00025826446280990283))*x+(0.011363636363636366));
		wts[0] = (((((((((((((1.6492170592149097e-010))*x+(-4.850638409455617e-012))*x+(-1.0398556090270479e-010))*x+(2.1979455292845764e-012))*x+(2.2680524125462398e-011))*x+(3.5906092913743728e-012))*x+(-1.8933950703588681e-010))*x+(9.2636671666923559e-009))*x+(-4.7112361360272337e-007))*x+(2.515800395027264e-005))*x+(-0.0014927082343060977))*x+(0.13285103285322949));
		break;
	case 45:
		rts[0] = (((((((((((((1.3869794202037156e-011))*x+(1.1368683772161603e-013))*x+(-8.6449366184145528e-012))*x+(-1.1368683772161603e-013))*x+(1.8308317824751916e-012))*x+(1.3750482234324104e-012))*x+(-6.0371245040139827e-011))*x+(2.7096090001362443e-009))*x+(-1.2193262807653576e-007))*x+(5.4869684502165811e-006))*x+(-0.0002469135802469208))*x+(0.011111111111111106));
		wts[0] = (((((((((((((1.697723443309466e-010))*x+(2.4253192047278085e-012))*x+(-1.062592976571371e-010))*x+(-2.3495279795800643e-012))*x+(2.3012110735483774e-011))*x+(4.0927261579781763e-012))*x+(-1.678047330718376e-010))*x+(8.3819792588239254e-009))*x+(-4.3586803003906971e-007))*x+(2.379839764658313e-005))*x+(-0.0014437694569156949))*x+(0.13138302057929618));
		break;
	case 46:
		rts[0] = (((((((((((((1.2960299500264227e-011))*x+(-3.0316490059097606e-013))*x+(-8.0954502360934076e-012))*x+(1.2316074086508402e-013))*x+(1.7266188478970435e-012))*x+(1.1389407935287937e-012))*x+(-5.2924831184242294e-011))*x+(2.4276189577084511e-009))*x+(-1.1167055161478978e-007))*x+(5.1368455661002701e-006))*x+(-0.00023629489603025993))*x+(0.010869565217391304));
		wts[0] = (((((((((((((1.4915713109076023e-010))*x+(-2.4253192047278085e-012))*x+(-9.163159120362252e-011))*x+(8.3370347662518408e-013))*x+(1.9232023381240044e-011))*x+(2.8895404587577405e-012))*x+(-1.4868669258779241e-010))*x+(7.600875780629698e-009))*x+(-4.0393323350966048e-007))*x+(2.2539476566237521e-005))*x+(-0.0013974475470053317))*x+(0.12996262187148638));
		break;
	case 47:
		rts[0] = (((((((((((((1.2505552149377763e-011))*x+(-7.5791225147744016e-014))*x+(-7.7259680134981555e-012))*x+(-9.4739031434680067e-015))*x+(1.6212216754259621e-012))*x+(1.0051219116273083e-012))*x+(-4.6521767919453318e-011))*x+(2.1801176419700137e-009))*x+(-1.0246571106066008e-007))*x+(4.8158885798804214e-006))*x+(-0.00022634676324128776))*x+(0.010638297872340425));
		wts[0] = (((((((((((((1.5036979069312412e-010))*x+(0))*x+(-9.3829536732907088e-011))*x+(-5.3053857603420807e-013))*x+(2.0283626630164992e-011))*x+(2.7900644757513265e-012))*x+(-1.3263405188960553e-010))*x+(6.9068318471939465e-009))*x+(-3.7494474273517636e-007))*x+(2.1371853297998584e-005))*x+(-0.0013535507086781552))*x+(0.12858731732439813));
		break;
	case 48:
		rts[0] = (((((((((((((1.3263464400855202e-011))*x+(-7.5791225147744016e-014))*x+(-8.3038761052497031e-012))*x+(-2.8421709430404007e-014))*x+(1.7787253151861173e-012))*x+(8.7781633813695704e-013))*x+(-4.1034120545901936e-011))*x+(1.9622881097802747e-009))*x+(-9.4190051895768706e-008))*x+(4.5211226854628694e-006))*x+(-0.00021701388888889972))*x+(0.010416666666666664));
		wts[0] = (((((((((((((1.5885840790967146e-010))*x+(-6.6696278130014735e-012))*x+(-9.9968625969874354e-011))*x+(3.4863963567962246e-012))*x+(2.1780503326832936e-011))*x+(1.6224059133188953e-012))*x+(-1.1859816832308451e-010))*x+(6.2887920056671947e-009))*x+(-3.4857706534182254e-007))*x+(2.0287188378885025e-005))*x+(-0.0013119048484818323))*x+(0.12725477030270824));
		break;
	case 49:
		rts[0] = (((((((((((((1.1065518871570626e-011))*x+(-1.1368683772161603e-013))*x+(-6.7169973287188124e-012))*x+(3.3158661002138011e-014))*x+(1.3677947663381925e-012))*x+(7.3792823703418741e-013))*x+(-3.6230685118709971e-011))*x+(1.770065779134929e-009))*x+(-8.6733260714714572e-008))*x+(4.2499298762195773e-006))*x+(-0.00020824656393168204))*x+(0.01020408163265306));
		wts[0] = (((((((((((((1.6613436552385488e-010))*x+(-2.4253192047278085e-012))*x+(-1.0390976967755705e-010))*x+(8.3370347662518408e-013))*x+(2.2472098256306101e-011))*x+(1.9184653865522701e-012))*x+(-1.0624183014821634e-010))*x+(5.7369119825049584e-009))*x+(-3.2454632435211883e-007))*x+(1.9278054828764102e-005))*x+(-0.0012723516185831143))*x+(0.12596281023971334));
		break;
	case 50:
		rts[0] = (((((((((((((1.2884508275116483e-011))*x+(-5.6843418860808015e-013))*x+(-8.033869865660865e-012))*x+(2.9369099744750809e-013))*x+(1.7189213015929754e-012))*x+(5.9226697620336678e-013))*x+(-3.2147543886177722e-011))*x+(1.6000020382674525e-009))*x+(-7.9999996005034963e-008))*x+(4.000000000089001e-006))*x+(-0.00020000000000001063))*x+(0.0099999999999999985));
		wts[0] = (((((((((((((1.5885840790967146e-010))*x+(-6.0632980118195212e-013))*x+(-1.0012020842016985e-010))*x+(-4.5474735088646412e-013))*x+(2.1903664067698021e-011))*x+(2.0392576516314875e-012))*x+(-9.5368749934247405e-011))*x+(5.2430806363190641e-009))*x+(-3.0260427339815854e-007))*x+(1.8337822437569651e-005))*x+(-0.0012347467105359687))*x+(0.12470941776409905));
		break;
	case 51:
		rts[0] = (((((((((((((1.1596057447604835e-011))*x+(-3.7895612573872007e-013))*x+(-7.1480599217466079e-012))*x+(1.8947806286936003e-013))*x+(1.4986530535073448e-012))*x+(5.278740407751077e-013))*x+(-2.853826434427257e-011))*x+(1.4491704132998011e-009))*x+(-7.3907631150532658e-008))*x+(3.7692893382380859e-006))*x+(-0.00019223375624759844))*x+(0.0098039215686274491));
		wts[0] = (((((((((((((1.4551915228366852e-010))*x+(1.2126596023639042e-012))*x+(-9.0797887726997331e-011))*x+(-1.4400332778071363e-012))*x+(1.9525714378687553e-011))*x+(1.9847827085565464e-012))*x+(-8.5545200552890791e-011))*x+(4.80025767283602e-009))*x+(-2.8253326841050824e-007))*x+(1.7460558692561357e-005))*x+(-0.0011989583633305577))*x+(0.1234927114230342));
		break;
	case 52:
		rts[0] = (((((((((((((1.038339784524093e-011))*x+(-3.0316490059097606e-013))*x+(-6.4375171859865077e-012))*x+(1.3263464400855202e-013))*x+(1.3618735768735253e-012))*x+(4.7251091928046662e-013))*x+(-2.5403475619375133e-011))*x+(1.3150825983743175e-009))*x+(-6.838433252651098e-008))*x+(3.5559854348355766e-006))*x+(-0.00018491124260354856))*x+(0.0096153846153846142));
		wts[0] = (((((((((((((1.3096723705530167e-010))*x+(-6.063298011819521e-012))*x+(-8.1096610908086106e-011))*x+(3.3348139065007363e-012))*x+(1.717618639910749e-011))*x+(7.1527968733183412e-013))*x+(-7.6871842225045839e-011))*x+(4.4024002221476613e-009))*x+(-2.6414193092053984e-007))*x+(1.6640943647043084e-005))*x+(-0.0011648660552663545))*x+(0.1223109358029818));
		break;
	case 53:
		rts[0] = (((((((((((((1.1065518871570626e-011))*x+(4.1685173831259209e-013))*x+(-6.8875275853012365e-012))*x+(-3.1737575530617807e-013))*x+(1.4708234630234072e-012))*x+(5.1085062106418866e-013))*x+(-2.2683817787102118e-011))*x+(1.1956034495774757e-009))*x+(-6.3367489711492933e-008))*x+(3.3584771325281121e-006))*x+(-0.00017799928800285391))*x+(0.009433962264150943));
		wts[0] = (((((((((((((1.5036979069312412e-010))*x+(6.0632980118195212e-013))*x+(-9.4739031434680016e-011))*x+(-8.3370347662518418e-013))*x+(2.0738373981051456e-011))*x+(1.4755604145951413e-012))*x+(-6.985404847152192e-011))*x+(4.0439527282387644e-009))*x+(-2.4726157477061861e-007))*x+(1.5874196553975855e-005))*x+(-0.0011323593539964867))*x+(0.12116245087759103));
		break;
	case 54:
		rts[0] = (((((((((((((1.2657134599673251e-011))*x+(-2.2737367544323206e-013))*x+(-8.0101851078021956e-012))*x+(8.5265128291212022e-014))*x+(1.7639223415244485e-012))*x+(3.7096251996141894e-013))*x+(-2.0324427326319967e-011))*x+(1.0889310564365928e-009))*x+(-5.8802383192992545e-008))*x+(3.1753289642932427e-006))*x+(-0.00017146776406039944))*x+(0.0092592592592592587));
		wts[0] = (((((((((((((1.4673181188603241e-010))*x+(-1.8189894035458565e-012))*x+(-9.1176843852736043e-011))*x+(4.1685173831259214e-013))*x+(1.9478344862970211e-011))*x+(1.1344999014302932e-012))*x+(-6.3066885047646792e-011))*x+(3.7206155193795589e-009))*x+(-2.3174326881555035e-007))*x+(1.5156012430285932e-005))*x+(-0.0011013369030792482))*x+(0.12004572243563211));
		break;
	case 55:
		rts[0] = (((((((((((((9.701276818911234e-012))*x+(-7.5791225147744016e-014))*x+(-5.9306633678109693e-012))*x+(4.736951571733997e-015))*x+(1.2256862191861728e-012))*x+(3.3869203737898107e-013))*x+(-1.815925187997891e-011))*x+(9.9347171230353593e-010))*x+(-5.4641074604770225e-008))*x+(3.0052592037768666e-006))*x+(-0.00016528925619833067))*x+(0.0090909090909090887));
		wts[0] = (((((((((((((1.4248750327775875e-010))*x+(-2.7284841053187847e-012))*x+(-8.8562046585138887e-011))*x+(9.0949470177292824e-013))*x+(1.8957280190079473e-011))*x+(9.4857455223973375e-013))*x+(-5.7190252533700914e-011))*x+(3.4283114125344127e-009))*x+(-2.1745502016649412e-007))*x+(1.4482507120267921e-005))*x+(-0.0010717055266838281))*x+(0.11895931346189501));
		break;
	case 56:
		rts[0] = (((((((((((((1.0231815394945443e-011))*x+(3.7895612573872008e-014))*x+(-6.3048825419779559e-012))*x+(-5.6843418860808009e-014))*x+(1.3233858453531866e-012))*x+(3.1101047663166049e-013))*x+(-1.6319260757550559e-011))*x+(9.0787971585015725e-010))*x+(-5.0841443974963811e-008))*x+(2.8471209914503423e-006))*x+(-0.00015943877551019263))*x+(0.0089285714285714263));
		wts[0] = (((((((((((((1.2854191785057384e-010))*x+(1.5158245029548803e-012))*x+(-7.85197092530628e-011))*x+(-1.7810937909719842e-012))*x+(1.6342482922482304e-011))*x+(1.4435859914859368e-012))*x+(-5.1690799788654353e-011))*x+(3.1635368398970814e-009))*x+(-2.0427975929345382e-007))*x+(1.3850169520051209e-005))*x+(-0.0010433794368221356))*x+(0.11790187636092067));
		break;
	case 57:
		rts[0] = (((((((((((((1.1368683772161603e-011))*x+(-7.5791225147744016e-014))*x+(-7.1338490670314059e-012))*x+(4.736951571733997e-015))*x+(1.547798926064085e-012))*x+(2.6674958538327093e-013))*x+(-1.4713378663581505e-011))*x+(8.3098718646941916e-010))*x+(-4.7366418354695864e-008))*x+(2.6998860650090844e-006))*x+(-0.00015389350569407746))*x+(0.0087719298245613996));
		wts[0] = (((((((((((((1.3581787546475727e-010))*x+(-3.0316490059097606e-013))*x+(-8.4279842364291341e-011))*x+(-3.0316490059097606e-013))*x+(1.8019363778876137e-011))*x+(9.1067893966586167e-013))*x+(-4.7273592448012395e-011))*x+(2.9234334952832337e-009))*x+(-1.9211329327362137e-007))*x+(1.3255819955958665e-005))*x+(-0.0010162795298075632))*x+(0.11687214592786273));
		break;
	case 58:
		rts[0] = (((((((((((((1.0307606620093186e-011))*x+(-1.8947806286936003e-013))*x+(-6.3285672998366254e-012))*x+(6.1580370432541999e-014))*x+(1.3251622021925868e-012))*x+(2.2959412149248232e-013))*x+(-1.3241259940362699e-011))*x+(7.6177815907148739e-010))*x+(-4.4183285479356314e-008))*x+(2.5626306944161875e-006))*x+(-0.00014863258026157931))*x+(0.0086206896551724085));
		wts[0] = (((((((((((((1.303609072541197e-010))*x+(-4.2443086082736646e-012))*x+(-8.0225011818887041e-011))*x+(2.08425869156296e-012))*x+(1.6891969304803446e-011))*x+(3.5290289209418302e-013))*x+(-4.2995385030053506e-011))*x+(2.7052182716147399e-009))*x+(-1.8086284217511128e-007))*x+(1.2696573854507436e-005))*x+(-0.00099033276053937173))*x+(0.11586893298309967));
		break;
	case 59:
		rts[0] = (((((((((((((1.0989727646422882e-011))*x+(-3.0316490059097606e-013))*x+(-6.750155989720951e-012))*x+(1.3737159558028603e-013))*x+(1.4169406388949329e-012))*x+(1.8444505182439269e-013))*x+(-1.1969073880161808e-011))*x+(6.9937450275503455e-010))*x+(-4.1263107325671213e-008))*x+(2.4345234908284643e-006))*x+(-0.00014363688595231235))*x+(0.0084745762711864406));
		wts[0] = (((((((((((((1.3763686486830312e-010))*x+(-9.0949470177292824e-013))*x+(-8.5227232678638146e-011))*x+(-7.5791225147743953e-014))*x+(1.8142524519741223e-011))*x+(7.6620191672797467e-013))*x+(-3.9424315663912538e-011))*x+(2.5065142554107447e-009))*x+(-1.7044547820366238e-007))*x+(1.2169809895661483e-005))*x+(-0.00096547158485534544))*x+(0.11489111859777525));
		break;
		*/
	default:
		double fr = 1/X;
		double fw = sqrt(fr);
		for(unsigned int i = 0 ; i < 1 ; i++){
			double DUM = fr*hermite_roots[1][i]*hermite_roots[1][i];
			rts[i] = DUM/(1.0-DUM);
			wts[i] = fw*hermite_weights[1][i];
		}
		break;
	}
}

void __Root2(double X , double rts[] , double wts[]){
	int n = int(X);
	double x = X - double(n) - 0.5;

	switch(n){
	case 0:
		rts[0] = (((((((((((((2.255546860396862e-010))*x+(-7.2759576141834259e-012))*x+(3.7137700322394552e-011))*x+(-2.3458142095478252e-009))*x+(1.5438539927951446e-008))*x+(2.5159276143919364e-008))*x+(-2.4696358054872763e-006))*x+(4.1242584527090287e-005))*x+(-0.00044450058965025041))*x+(0.0037148352648456173))*x+(-0.024973416969387381))*x+(0.11721997126167431));
		rts[1] = (((((((((((((3.0267983675003052e-009))*x+(3.686485191186269e-010))*x+(-3.1335124125083285e-009))*x+(-2.5013529617960252e-008))*x+(1.3895714801037684e-007))*x+(2.4910910572846961e-006))*x+(-1.4085682626803948e-005))*x+(-0.00017841313481881113))*x+(-0.00037454517987948555))*x+(0.052959469176417251))*x+(-0.58446761938527259))*x+(2.5637965715270385));
		wts[0] = (((((((((((((6.0147916277249647e-010))*x+(1.13990002622207e-009))*x+(-1.2115075757416586e-008))*x+(1.1259726306889206e-007))*x+(-1.0158919773554467e-006))*x+(8.5476507933890389e-006))*x+(-6.6788150554941694e-005))*x+(0.00048204021589034102))*x+(-0.003162211394632426))*x+(0.018674060075668814))*x+(-0.10140429062505212))*x+(0.59634686150556027));
		wts[1] = (((((((((((((-2.2312936683495838e-010))*x+(7.2056233572463189e-009))*x+(-8.0893490424690143e-008))*x+(8.2116290892978816e-007))*x+(-7.504869662019094e-006))*x+(6.0840813697874793e-005))*x+(-0.0004305530374371831))*x+(0.002602272750703349))*x+(-0.013041459341199602))*x+(0.051701208337306286))*x+(-0.14768944155446553))*x+(0.25927753038658824));
		break;
	case 1:
		rts[0] = (((((((((((((1.861432489628593e-010))*x+(4.5474735088646412e-012))*x+(-2.4632148173016634e-012))*x+(-9.7789628246876715e-010))*x+(2.5620749966037693e-009))*x+(8.1491721222922323e-008))*x+(-2.1049261484940018e-006))*x+(2.9668603506542247e-005))*x+(-0.00030330094001310148))*x+(0.0026047341916460619))*x+(-0.018724384428429365))*x+(0.095555700313959172));
		rts[1] = (((((((((((((2.3671115438143411e-009))*x+(3.7834979593753815e-010))*x+(-3.4682064627607657e-010))*x+(-2.6382622309029102e-008))*x+(-8.0638831908193723e-008))*x+(2.6999892194605004e-006))*x+(2.2662975140974591e-006))*x+(-0.00020848746243965857))*x+(-0.0011758608235528099))*x+(0.050664040022735161))*x+(-0.48044068968859399))*x+(2.0317239810105332));
		wts[0] = (((((((((((((5.0446639458338416e-010))*x+(4.6081064889828361e-010))*x+(-4.8209282491977011e-009))*x+(4.5029082684777677e-008))*x+(-4.2771349247535301e-007))*x+(3.80488146826489e-006))*x+(-3.1759798410746498e-005))*x+(0.00024737312751099694))*x+(-0.001761093077664218))*x+(0.011521443071712914))*x+(-0.071903604508454108))*x+(0.51087730526004271));
		wts[1] = (((((((((((((1.2126596023639042e-012))*x+(2.9346362377206483e-009))*x+(-3.3328660720144392e-008))*x+(3.4030911895873334e-007))*x+(-3.1402144031744683e-006))*x+(2.579755402128588e-005))*x+(-0.00018571855159669562))*x+(0.0011481007756864632))*x+(-0.0059437707605090222))*x+(0.02466032785221961))*x+(-0.074836657388847441))*x+(0.15247364058029172));
		break;
	case 2:
		rts[0] = (((((((((((((1.2247861983875433e-010))*x+(-9.0949470177292824e-012))*x+(-2.0539422015038625e-011))*x+(-2.0221098869418103e-010))*x+(-1.7624775712950698e-009))*x+(8.0574809639225961e-008))*x+(-1.6039030699133148e-006))*x+(2.0400603966722976e-005))*x+(-0.00020400246531265823))*x+(0.0018530461184320945))*x+(-0.01431616915240321))*x+(0.079160395982901172));
		rts[1] = (((((((((((((1.998463024695714e-009))*x+(-9.7012768189112337e-011))*x+(1.2987584341317415e-009))*x+(-7.9653545981273055e-009))*x+(-2.2662546446857354e-007))*x+(1.5355777425914614e-006))*x+(1.5489877895902279e-005))*x+(-0.00016114210196368123))*x+(-0.0019373324275375006))*x+(0.045946310048438001))*x+(-0.38344737512445276))*x+(1.6005678434625858));
		wts[0] = (((((((((((((3.2256745422879851e-010))*x+(1.6249638671676317e-010))*x+(-1.9631443137768656e-009))*x+(1.8805470366108541e-008))*x+(-1.8836965409718684e-007))*x+(1.7689158748150171e-006))*x+(-1.5865073417960691e-005))*x+(0.00013334090406284341))*x+(-0.0010258822551014364))*x+(0.0074540114304287126))*x+(-0.053293145396920621))*x+(0.44895308212649432));
		wts[1] = (((((((((((((3.152914966146151e-011))*x+(1.2250893632881343e-009))*x+(-1.381825616893669e-008))*x+(1.4198485587257892e-007))*x+(-1.3261670138338861e-006))*x+(1.1078593249891355e-005))*x+(-8.13591869276801e-005))*x+(0.00051674961795826013))*x+(-0.0027859239665358011))*x+(0.012189907096869573))*x+(-0.039548249235326974))*x+(0.097338889658653421));
		break;
	case 3:
		rts[0] = (((((((((((((7.3365905943016203e-011))*x+(-5.4569682106375694e-012))*x+(-3.5508188981718071e-011))*x+(6.9386866622759642e-011))*x+(-2.0369602301191963e-009))*x+(6.5926386128012382e-008))*x+(-1.1636524074691104e-006))*x+(1.3518970932047125e-005))*x+(-0.00013689728676181495))*x+(0.0013485706194582556))*x+(-0.011148031597847845))*x+(0.066512145827585883));
		rts[1] = (((((((((((((1.7753336578607559e-009))*x+(-2.0857745160659153e-010))*x+(3.2923708204180002e-010))*x+(1.1524510531065365e-008))*x+(-2.0606694306479767e-007))*x+(-7.3224650047147108e-008))*x+(1.9800352771900027e-005))*x+(-6.8847796671415523e-005))*x+(-0.002404470148700562))*x+(0.039340494145468766))*x+(-0.29792628741673077))*x+(1.2609850969574581));
		wts[0] = (((((((((((((5.1901830981175101e-010))*x+(6.0632980118195207e-011))*x+(-1.0625929765713711e-009))*x+(8.3083856831459944e-009))*x+(-8.6035091347487949e-008))*x+(8.5642416062607185e-007))*x+(-8.3427966461139639e-006))*x+(7.507846922057601e-005))*x+(-0.00062146334425894345))*x+(0.0050408060732248794))*x+(-0.040999300377580414))*x+(0.40220713943436309));
		wts[1] = (((((((((((((5.6388671509921551e-011))*x+(4.9991892107451952e-010))*x+(-5.7832873305111808e-009))*x+(5.9653643802448628e-008))*x+(-5.6703424888837617e-007))*x+(4.8316934204706286e-006))*x+(-3.6252284694911666e-005))*x+(0.00023814951687883834))*x+(-0.0013504339194357986))*x+(0.0062609007776097906))*x+(-0.02180779273375081))*x+(0.067639895767260177));
		break;
	case 4:
		rts[0] = (((((((((((((7.1546916539470346e-011))*x+(-9.0949470177292824e-013))*x+(-5.532759435785313e-011))*x+(3.6360840264630191e-011))*x+(-1.4894728413613241e-009))*x+(5.3691705896123189e-008))*x+(-8.0680415237566194e-007))*x+(8.6233290438701236e-006))*x+(-9.3206752725782924e-005))*x+(0.0010083041109277963))*x+(-0.0088129427573636759))*x+(0.056588206836661707));
		rts[1] = (((((((((((((9.9923151234785702e-010))*x+(-1.2611659864584604e-010))*x+(-8.7250858390082909e-010))*x+(1.6474587027914822e-008))*x+(-8.3373606685199775e-008))*x+(-1.1104275472462177e-006))*x+(1.5811817895894364e-005))*x+(2.278708271319374e-005))*x+(-0.002489797035154802))*x+(0.031906936644437778))*x+(-0.22663687896214987))*x+(0.99994551937158105));
		wts[0] = (((((((((((((3.5409660389026004e-010))*x+(2.4253192047278084e-011))*x+(-5.4963796477143956e-010))*x+(3.8242736385048675e-009))*x+(-3.985583892548069e-008))*x+(4.3603404265013518e-007))*x+(-4.625535040029642e-006))*x+(4.3698375273256332e-005))*x+(-0.00039005194498324219))*x+(0.0035547059684065312))*x+(-0.032518882078659293))*x+(0.36569469541670002));
		wts[1] = (((((((((((((5.184119800105691e-011))*x+(2.1206384796338776e-010))*x+(-2.4266266033616071e-009))*x+(2.5318646142598784e-008))*x+(-2.4693815703358268e-007))*x+(2.1409380395927733e-006))*x+(-1.6440959445640502e-005))*x+(0.00011306461485867854))*x+(-0.00068065763696609671))*x+(0.0033380254284088653))*x+(-0.01254050514825894))*x+(0.05094878616381554));
		break;
	case 5:
		rts[0] = (((((((((((((8.1551358258972557e-011))*x+(2.2737367544323206e-012))*x+(-5.7809756981441745e-011))*x+(-5.0476955948397517e-011))*x+(-1.586547189920869e-009))*x+(4.3268303902740016e-008))*x+(-5.1554029645295429e-007))*x+(5.3433185968435968e-006))*x+(-6.5759031203117339e-005))*x+(0.0007731302946521445))*x+(-0.007045183649315374))*x+(0.048698230180812922));
		rts[1] = (((((((((((((5.7237533231576277e-010))*x+(-7.0334256937106446e-011))*x+(-1.3030027427400151e-009))*x+(9.7373534420815612e-009))*x+(2.5575748926106218e-008))*x+(-1.2806792616023206e-006))*x+(8.2539961307285629e-006))*x+(8.33607264224175e-005))*x+(-0.0022647764452377035))*x+(0.024714422389179348))*x+(-0.1701293082417896))*x+(0.80276320108374988));
		wts[0] = (((((((((((((1.7947362114985782e-010))*x+(-1.8189894035458565e-011))*x+(-2.5981231980646647e-010))*x+(1.6843841876834631e-009))*x+(-1.8888992296221353e-008))*x+(2.4022010336466337e-007))*x+(-2.669579516852612e-006))*x+(2.5945136966853966e-005))*x+(-0.00025400066477376804))*x+(0.0026062838111850875))*x+(-0.026425595398683478))*x+(0.33637993985390702));
		wts[1] = (((((((((((((6.6999443030605705e-011))*x+(9.0191557925815375e-011))*x+(-1.0401398261213519e-009))*x+(1.1041606740036514e-008))*x+(-1.0972304664846888e-007))*x+(9.5831769956570634e-007))*x+(-7.6177022569160844e-006))*x+(5.5841818207502669e-005))*x+(-0.00035739284855009862))*x+(0.0018375905201102119))*x+(-0.0075250735103288688))*x+(0.041164189583721991));
		break;
	case 6:
		rts[0] = (((((((((((((6.6393113229423761e-011))*x+(1.0610771520684161e-012))*x+(-3.2154427268930405e-011))*x+(-2.1657342585967854e-011))*x+(-1.9566594270751616e-009))*x+(3.0650341524089221e-008))*x+(-2.9244460475474904e-007))*x+(3.3549788497714652e-006))*x+(-4.873471664539978e-005))*x+(0.00060337168274359149))*x+(-0.0056771565814704708))*x+(0.042365287190881444));
		rts[1] = (((((((((((((6.0632980118195212e-010))*x+(-3.3954468866189317e-011))*x+(-1.0862398388174672e-009))*x+(1.5749416585701206e-009))*x+(6.8740291681024233e-008))*x+(-9.1246486514743675e-007))*x+(1.5249071990316072e-006))*x+(0.00010686810555900669))*x+(-0.0018730539291291759))*x+(0.018484359091494783))*x+(-0.12712751663049363))*x+(0.6551739070660173));
		wts[0] = (((((((((((((2.1342809001604715e-010))*x+(-1.9402553637822468e-011))*x+(-1.9523819598058856e-010))*x+(6.6393113229423761e-010))*x+(-1.0211617033443568e-008))*x+(1.4295851732034254e-007))*x+(-1.5499338630320378e-006))*x+(1.5637155901989292e-005))*x+(-0.00017269225010589176))*x+(0.0019765044620962584))*x+(-0.0218832761388933))*x+(0.31233012599270832));
		wts[1] = (((((((((((((5.4872847006966666e-011))*x+(3.6834535421803594e-011))*x+(-4.7197090680128895e-010))*x+(5.0017661124002188e-009))*x+(-4.8826192274494438e-008))*x+(4.3116503611884127e-007))*x+(-3.6601145683897345e-006))*x+(2.8951319290445216e-005))*x+(-0.00019433259276643389))*x+(0.0010366332320451536))*x+(-0.004731730274650358))*x+(0.035168396576336379));
		break;
	case 7:
		rts[0] = (((((((((((((2.849750065555175e-011))*x+(-1.6674069532503684e-012))*x+(-1.0080232944649954e-011))*x+(6.6620486904866981e-011))*x+(-1.7716885736263064e-009))*x+(1.7138261772705239e-008))*x+(-1.4975036736567896e-007))*x+(2.2834851172159887e-006))*x+(-3.7695386940511659e-005))*x+(0.00047479120464986635))*x+(-0.0046044896087635264))*x+(0.037245858783725154));
		rts[1] = (((((((((((((5.8692724754412962e-010))*x+(4.850638409455617e-012))*x+(-5.8723041244472063e-010))*x+(-2.6020643417723477e-009))*x+(6.1358718994597439e-008))*x+(-4.3834406445360702e-007))*x+(-2.4995280642296316e-006))*x+(0.00010323665054556841))*x+(-0.0014461466492426596))*x+(0.013509429490813055))*x+(-0.095347851045366375))*x+(0.54476524568685059));
		wts[0] = (((((((((((((3.5167128468553222e-010))*x+(-1.4551915228366852e-011))*x+(-2.2995057709825534e-010))*x+(3.3378455555066466e-010))*x+(-6.6225804099910119e-009))*x+(8.5268311522668228e-008))*x+(-8.7751231762448845e-007))*x+(9.7120516405387499e-006))*x+(-0.00012311048208916525))*x+(0.0015386968305948212))*x+(-0.018392754238725766))*x+(0.29226488260219496));
		wts[1] = (((((((((((((4.8506384094556168e-011))*x+(1.7431981783981122e-011))*x+(-2.3855288115252432e-010))*x+(2.2421507613519984e-009))*x+(-2.118414717718527e-008))*x+(1.9883004457691791e-007))*x+(-1.8659475797081864e-006))*x+(1.5710655924576027e-005))*x+(-0.00010796711479205134))*x+(0.00059630997912412059))*x+(-0.0031416753151424356))*x+(0.031304645075983441));
		break;
	case 8:
		rts[0] = (((((((((((((5.244752780223886e-011))*x+(-4.5474735088646412e-013))*x+(-3.4579746473658205e-011))*x+(9.6539073031938941e-011))*x+(-1.0619605935365446e-009))*x+(7.038608510849068e-009))*x+(-7.9729086666091562e-008))*x+(1.7351091625705806e-006))*x+(-2.9774059414145824e-005))*x+(0.00037413034095266223))*x+(-0.003759517177013482))*x+(0.033080614163734236));
		rts[1] = (((((((((((((4.1230426480372745e-010))*x+(4.3655745685100555e-011))*x+(-1.8402109465872246e-010))*x+(-3.1624646605147668e-009))*x+(3.6561762802496858e-008))*x+(-9.3821521810847727e-008))*x+(-4.0081394191796944e-006))*x+(8.6105146749559935e-005))*x+(-0.0010649781637131668))*x+(0.0097600463360369219))*x+(-0.072269206683464732))*x+(0.4615810347468593));
		wts[0] = (((((((((((((3.0801553900043166e-010))*x+(3.637978807091713e-012))*x+(-1.9720876783442992e-010))*x+(2.6117656185912586e-010))*x+(-4.3186976957561756e-009))*x+(4.6919964802327734e-008))*x+(-4.8898465069650387e-007))*x+(6.3915878983541079e-006))*x+(-9.1548075328481027e-005))*x+(0.0012200103154034745))*x+(-0.015649763923299077))*x+(0.27529662816972428));
		wts[1] = (((((((((((((4.0320931778599814e-011))*x+(4.9264296346033608e-012))*x+(-1.2253546325761514e-010))*x+(9.3118046606832639e-010))*x+(-9.1617048762297291e-009))*x+(9.8661388096369735e-008))*x+(-1.0150856037949296e-006))*x+(8.7554616526874796e-006))*x+(-6.0439178833494395e-005))*x+(0.00035060651540374729))*x+(-0.0022183829486953962))*x+(0.028665337023175908));
		break;
	case 9:
		rts[0] = (((((((((((((4.0927261579781771e-011))*x+(-2.1221543041368323e-012))*x+(-2.9615421226480976e-011))*x+(6.6431008841997625e-011))*x+(-3.9244459533923265e-010))*x+(2.0546444545743725e-009))*x+(-5.48175082363637e-008))*x+(1.4111281293841909e-006))*x+(-2.3522311597352446e-005))*x+(0.00029450729553590538))*x+(-0.0030940013757666455))*x+(0.029667114713106638));
		rts[1] = (((((((((((((2.8376234695315361e-010))*x+(-4.3655745685100555e-011))*x+(-3.1377567211166024e-011))*x+(-2.1162425885753082e-009))*x+(1.501602279555906e-008))*x+(8.1632966460650394e-008))*x+(-3.9690855692479472e-006))*x+(6.5725848182059579e-005))*x+(-0.00076140650628401618))*x+(0.0070409356727524717))*x+(-0.055620000387258908))*x+(0.39808893286884051));
		wts[0] = (((((((((((((1.5522042910257974e-010))*x+(-2.7891170854369797e-011))*x+(-9.6709603288521365e-011))*x+(2.2616101584086815e-010))*x+(-2.4179864036947643e-009))*x+(2.3403633993742307e-008))*x+(-2.8477014168970522e-007))*x+(4.5158527530730899e-006))*x+(-7.007128855092877e-005))*x+(0.00097944528896759509))*x+(-0.013461012999841995))*x+(0.26078127191251865));
		wts[1] = (((((((((((((4.5474735088646412e-011))*x+(5.1538033100465928e-012))*x+(-6.730260793119669e-011))*x+(3.6288838600739832e-010))*x+(-4.3404379349946485e-009))*x+(5.3967409504214928e-008))*x+(-5.7382575165595051e-007))*x+(4.893624492741111e-006))*x+(-3.387093209225589e-005))*x+(0.00021298120942207324))*x+(-0.0016680065899058749))*x+(0.026744952122596255));
		break;
	case 10:
		rts[0] = (((((((((((((3.6076623170326151e-011))*x+(-2.1979455292845764e-012))*x+(-2.537111261820731e-011))*x+(2.618586828854556e-011))*x+(-4.1247005810873809e-011))*x+(6.9572347882740349e-010))*x+(-4.7790650622066736e-008))*x+(1.1579096991232161e-006))*x+(-1.8395539488712715e-005))*x+(0.0002318830856285192))*x+(-0.0025701732677719333))*x+(0.02684545635000771));
		rts[1] = (((((((((((((3.7107383832335472e-010))*x+(-5.8207660913467407e-011))*x+(-1.320283142073701e-010))*x+(-1.0237878692957261e-009))*x+(2.4438880548890056e-009))*x+(1.3735571731861759e-007))*x+(-3.2681514223753538e-006))*x+(4.7496018854786819e-005))*x+(-0.0005361456276522143))*x+(0.0051128644320009489))*x+(-0.043578711810006852))*x+(0.34881031302581461));
		wts[0] = (((((((((((((1.9160021717349687e-010))*x+(-4.6081064889828362e-011))*x+(-1.2596501619555054e-010))*x+(1.4703497678662339e-010))*x+(-1.0886462102159082e-009))*x+(1.1396072826149368e-008))*x+(-1.8496974085735474e-007))*x+(3.3713236078369846e-006))*x+(-5.4461731552657433e-005))*x+(0.00079378434267041165))*x+(-0.011695571733287481))*x+(0.24823388516899841));
		wts[1] = (((((((((((((2.986174270821114e-011))*x+(6.8970014884447055e-012))*x+(-3.1330197695448682e-011))*x+(1.5597834135405717e-010))*x+(-2.3971485537307067e-009))*x+(3.1281669106893631e-008))*x+(-3.2479078171387954e-007))*x+(2.7033385603762263e-006))*x+(-1.908984151654386e-005))*x+(0.0001357191237686487))*x+(-0.0013266556133285916))*x+(0.025260425559273349));
		break;
	case 11:
		rts[0] = (((((((((((((1.6522487082208194e-011))*x+(1.6674069532503684e-012))*x+(-1.1435001094165878e-011))*x+(1.0137076363510762e-012))*x+(4.8975342300157841e-011))*x+(8.0594197982009053e-010))*x+(-4.3599438022864e-008))*x+(9.2910909077481563e-007))*x+(-1.4228383558590371e-005))*x+(0.00018317607139583386))*x+(-0.0021571970049537167))*x+(0.024489881419306421));
		rts[1] = (((((((((((((3.686485191186269e-010))*x+(-1.0913936421275139e-011))*x+(-1.7886729134867585e-010))*x+(-3.5030704263287283e-010))*x+(-2.9141726069307574e-009))*x+(1.3209384045846187e-007))*x+(-2.4412234959451471e-006))*x+(3.3237400797858634e-005))*x+(-0.00037606316041275772))*x+(0.0037588067681102264))*x+(-0.034786943143180309))*x+(0.30985268668796717));
		wts[0] = (((((((((((((3.2499277343352634e-010))*x+(-2.7891170854369797e-011))*x+(-2.0948694630836445e-010))*x+(7.0182674486810954e-011))*x+(-3.9263644187788788e-010))*x+(6.2938691295736744e-009))*x+(-1.3422831438939889e-007))*x+(2.5859398314527957e-006))*x+(-4.2630996314333793e-005))*x+(0.00064892812887012985))*x+(-0.010258766283718333))*x+(0.23728083280253737));
		wts[1] = (((((((((((((3.6228205620621637e-011))*x+(-3.1832314562052488e-012))*x+(-2.8090122820382625e-011))*x+(9.1584221687905171e-011))*x+(-1.4425343882370119e-009))*x+(1.8127183309957218e-008))*x+(-1.7987215180278088e-007))*x+(1.4744091917003506e-006))*x+(-1.0974779591460072e-005))*x+(9.1844589827765971e-005))*x+(-0.0011031254342547549))*x+(0.02405280680441611));
		break;
	case 12:
		rts[0] = (((((((((((((1.8796223836640515e-011))*x+(5.3053857603420807e-013))*x+(-1.1179205709292242e-011))*x+(-4.5569474120081087e-012))*x+(3.2052582810138119e-011))*x+(1.1034494799370502e-009))*x+(-3.780701677650692e-008))*x+(7.248353165456578e-007))*x+(-1.0930171161854794e-005))*x+(0.00014564266598347692))*x+(-0.0018300264051489394))*x+(0.022502518465407712));
		rts[1] = (((((((((((((2.352559628585974e-010))*x+(4.850638409455617e-012))*x+(-1.1717323407841224e-010))*x+(-2.4253192047278084e-011))*x+(-4.2337167845592676e-009))*x+(1.0524025621331627e-007))*x+(-1.7248214394527393e-006))*x+(2.2890223489705854e-005))*x+(-0.00026500335810319958))*x+(0.0028075405168029866))*x+(-0.028276006153281519))*x+(0.27847941215959737));
		wts[0] = (((((((((((((2.5465851649641991e-010))*x+(-1.5158245029548802e-011))*x+(-1.5719100095642111e-010))*x+(2.5314269199346498e-011))*x+(-1.4550020447738157e-010))*x+(4.3118314844529477e-009))*x+(-1.0328900342434129e-007))*x+(1.9970398967098886e-006))*x+(-3.3516304693725907e-005))*x+(0.00053529510838256267))*x+(-0.0090790952782458263))*x+(0.22763082127437506));
		wts[1] = (((((((((((((4.759688939278324e-011))*x+(-2.8800665556142726e-012))*x+(-3.4124999122771741e-011))*x+(5.9515059547265992e-011))*x+(-8.6148806606919004e-010))*x+(1.016735081312466e-008))*x+(-9.7005874666322711e-008))*x+(8.020425166233025e-007))*x+(-6.5593151451724206e-006))*x+(6.6211855605811942e-005))*x+(-0.00094726300591958009))*x+(0.023031862482937787));
		break;
	case 13:
		rts[0] = (((((((((((((3.7137700322394565e-011))*x+(-5.3811769854898249e-012))*x+(-2.3713179568100408e-011))*x+(-3.979039320256561e-013))*x+(1.5134560271690134e-012))*x+(1.1896347610710714e-009))*x+(-3.0806224275240858e-008))*x+(5.5308885623291571e-007))*x+(-8.3860317711056936e-006))*x+(0.00011684015090151004))*x+(-0.0015688144853314384))*x+(0.020807892712425589));
		rts[1] = (((((((((((((3.3711936945716537e-010))*x+(-1.2126596023639042e-011))*x+(-2.0903219895747799e-010))*x+(1.0519822050506869e-010))*x+(-3.7826453080924693e-009))*x+(7.637039326861364e-008))*x+(-1.1815737419595962e-006))*x+(1.5696690901142084e-005))*x+(-0.00018873440982588213))*x+(0.0021341128866291985))*x+(-0.023372396759025728))*x+(0.25276720954855014));
		wts[0] = (((((((((((((3.0073958138624824e-010))*x+(1.2126596023639042e-012))*x+(-1.8887173306817809e-010))*x+(2.1221543041368323e-012))*x+(-6.2243543652584776e-011))*x+(3.3917094318288337e-009))*x+(-8.0430047214955864e-008))*x+(1.5400336916826516e-006))*x+(-2.6480174355913988e-005))*x+(0.00044575694279253003))*x+(-0.0081015574940575125))*x+(0.21905540270383064));
		wts[1] = (((((((((((((1.2732925824820995e-011))*x+(1.5158245029548803e-013))*x+(-8.6780952794166897e-012))*x+(3.6417683683490999e-011))*x+(-4.9637331282307662e-010))*x+(5.4857209145590478e-009))*x+(-5.1341388621987484e-008))*x+(4.428312319060268e-007))*x+(-4.1452422628226078e-006))*x+(5.0511903966018547e-005))*x+(-0.00083173873384893263))*x+(0.022144966408716018));
		break;
	case 14:
		rts[0] = (((((((((((((2.6375346351414919e-011))*x+(-4.0169349328304325e-012))*x+(-1.6844599789086107e-011))*x+(8.7159908919905576e-013))*x+(-2.0302574436451927e-011))*x+(1.0813101525286584e-009))*x+(-2.391897043393006e-008))*x+(4.1655429901717623e-007))*x+(-6.4582477957662397e-006))*x+(9.4710210388009239e-005))*x+(-0.0013582268648013539))*x+(0.019348055812280444));
		rts[1] = (((((((((((((2.8376234695315361e-010))*x+(-7.2759576141834259e-012))*x+(-1.8083786320251724e-010))*x+(1.2020488308432201e-010))*x+(-2.881146580572628e-009))*x+(5.2665569683085771e-008))*x+(-7.9767458712372752e-007))*x+(1.0807887383279535e-005))*x+(-0.00013636400896395914))*x+(0.0016513421993365656))*x+(-0.019613063044102957))*x+(0.23135477903297447));
		wts[0] = (((((((((((((2.1464074961841106e-010))*x+(5.4569682106375694e-012))*x+(-1.3271043523369977e-010))*x+(-2.9558577807620168e-012))*x+(-5.7298166211694479e-011))*x+(2.7442084160611557e-009))*x+(-6.2085786881974997e-008))*x+(1.1853721213483936e-006))*x+(-2.1059914776096662e-005))*x+(0.0003748011483271918))*x+(-0.0072837064783285331))*x+(0.21137458487666266));
		wts[1] = (((((((((((((1.6674069532503683e-011))*x+(1.8947806286936002e-012))*x+(-1.0629719326971099e-011))*x+(2.0132044179869506e-011))*x+(-2.6882437017169042e-010))*x+(2.8691292304946119e-009))*x+(-2.7069339436636142e-008))*x+(2.5331191910726853e-007))*x+(-2.793145863447255e-006))*x+(4.0292542555926916e-005))*x+(-0.0007416063278192944))*x+(0.021359990849285134));
		break;
	case 15:
		rts[0] = (((((((((((((1.4703497678662338e-011))*x+(-2.0463630789890885e-012))*x+(-8.7823082139948367e-012))*x+(1.2126596023639042e-012))*x+(-2.8289074786395456e-011))*x+(8.8467988490492644e-010))*x+(-1.7998398068227079e-008))*x+(3.1225752180249106e-007))*x+(-5.0104980689862537e-006))*x+(7.7611288980998269e-005))*x+(-0.0011866282526439909))*x+(0.018078474601966679));
		rts[1] = (((((((((((((2.013014939924081e-010))*x+(-7.8822874153653775e-012))*x+(-1.3384730361091593e-010))*x+(1.0156024169797699e-010))*x+(-2.0242130934396605e-009))*x+(3.5345628646155085e-008))*x+(-5.3667853272543187e-007))*x+(7.5152723431060045e-006))*x+(-0.00010015166637933337))*x+(0.0012998526548688991))*x+(-0.016679931007074839))*x+(0.21326675425598587));
		wts[0] = (((((((((((((1.964508555829525e-010))*x+(-2.2434202643732228e-011))*x+(-1.2535868639436862e-010))*x+(1.5082453804401059e-011))*x+(-4.8657966544851661e-011))*x+(2.1723209897572811e-009))*x+(-4.7362292458312062e-008))*x+(9.1318455108790886e-007))*x+(-1.6887330580324839e-005))*x+(0.00031815218394943645))*x+(-0.0065928369856901098))*x+(0.20444574557931008));
		wts[1] = (((((((((((((4.3049415883918599e-011))*x+(2.6526928801710406e-012))*x+(-2.7777484016648181e-011))*x+(9.8812809786371271e-012))*x+(-1.3501733064913424e-010))*x+(1.4747980614515652e-009))*x+(-1.4491138807433874e-008))*x+(1.5287595911406268e-007))*x+(-2.0015844909201017e-006))*x+(3.3200192087827707e-005))*x+(-0.00066850729881324188))*x+(0.020656112779398956));
		break;
	case 16:
		rts[0] = (((((((((((((7.2759576141834259e-012))*x+(-1.1368683772161603e-012))*x+(-3.3537617127876729e-012))*x+(1.2789769243681803e-012))*x+(-2.7402080604588264e-011))*x+(6.7951185419209037e-010))*x+(-1.331273424831636e-008))*x+(2.3449463744847537e-007))*x+(-3.9248001590663772e-006))*x+(6.4286001439596327e-005))*x+(-0.001045273030672478))*x+(0.0169647422543792));
		rts[1] = (((((((((((((2.013014939924081e-010))*x+(6.0632980118195212e-013))*x+(-1.2505552149377763e-010))*x+(6.9121597334742533e-011))*x+(-1.3577050594903992e-009))*x+(2.3440271945673885e-008))*x+(-3.6266762097151661e-007))*x+(5.2966240060570158e-006))*x+(-7.4817107982405595e-005))*x+(0.0010396122056317292))*x+(-0.014353104535903001))*x+(0.1977935362203736));
		wts[0] = (((((((((((((3.2014213502407074e-010))*x+(-8.4886172165473291e-012))*x+(-2.0372681319713593e-010))*x+(4.6990559591601279e-012))*x+(-1.9800457569848121e-011))*x+(1.6775108709528768e-009))*x+(-3.5845340325598343e-008))*x+(7.0642643734686306e-007))*x+(-1.3667293146705596e-005))*x+(0.00027252675688381006))*x+(-0.0060037661456946766))*x+(0.19815504137139439));
		wts[1] = (((((((((((((4.4413657936577991e-011))*x+(-2.2737367544323206e-013))*x+(-2.9738581967346058e-011))*x+(6.2906716872627531e-012))*x+(-6.4600177059522438e-011))*x+(7.5721503141797553e-010))*x+(-8.0382841494142082e-009))*x+(9.8335128891532023e-008))*x+(-1.5098368675604359e-006))*x+(2.7987246037821052e-005))*x+(-0.00060756467046759464))*x+(0.020018943817958532));
		break;
	case 17:
		rts[0] = (((((((((((((1.606773973132173e-011))*x+(-2.2737367544323206e-013))*x+(-9.2844250805986414e-012))*x+(9.0949470177292824e-013))*x+(-2.0699294130584651e-011))*x+(5.0332804590880187e-010))*x+(-9.7823755022356344e-009))*x+(1.7719807698934886e-007))*x+(-3.1072926744470561e-006))*x+(5.3795070512976245e-005))*x+(-0.00092760012493784663))*x+(0.015980052259378676));
		rts[1] = (((((((((((((1.697723443309466e-010))*x+(1.3945585427184899e-011))*x+(-9.9134922493249165e-011))*x+(3.9108272176235914e-011))*x+(-8.9318064055987623e-010))*x+(1.5517829391834916e-008))*x+(-2.4745076861639365e-007))*x+(3.7910927609037986e-006))*x+(-5.6833150501237974e-005))*x+(0.00084363840202279306))*x+(-0.012478826782924352))*x+(0.18441018286510519));
		wts[0] = (((((((((((((2.8861298536260921e-010))*x+(1.4551915228366852e-011))*x+(-1.8083786320251721e-010))*x+(-8.1854523159563541e-012))*x+(-1.3187673175707453e-011))*x+(1.2686882655543741e-009))*x+(-2.7057897848218694e-008))*x+(5.502149947507935e-007))*x+(-1.116863905148424e-005))*x+(0.00023542886386185288))*x+(-0.0054970583897468008))*x+(0.19241080688859702));
		wts[1] = (((((((((((((2.9710160257915654e-011))*x+(-5.0022208597511053e-012))*x+(-1.9762561957274251e-011))*x+(6.034876302389117e-012))*x+(-3.1198747289333064e-011))*x+(3.9548631036723236e-010))*x+(-4.7020955277569474e-009))*x+(6.7382858996249212e-008))*x+(-1.1839197752901614e-006))*x+(2.3977384770050569e-005))*x+(-0.00055576244808947677))*x+(0.019437947545645255));
		break;
	case 18:
		rts[0] = (((((((((((((3.3044974164416388e-011))*x+(-1.4400332778071363e-012))*x+(-2.2017350905419637e-011))*x+(1.2789769243681803e-012))*x+(-1.1703823095861784e-011))*x+(3.6586111917813469e-010))*x+(-7.1941449834393252e-009))*x+(1.3510184130686534e-007))*x+(-2.4870008115731217e-006))*x+(4.5445657790430201e-005))*x+(-0.00082866911203345367))*x+(0.015103307809743676));
		rts[1] = (((((((((((((2.3889394166568912e-010))*x+(-1.3945585427184899e-011))*x+(-1.5150665907034028e-010))*x+(3.9563019527122378e-011))*x+(-5.6187824763280026e-010))*x+(1.0321938267073467e-008))*x+(-1.7103967457169725e-007))*x+(2.7578188221966116e-006))*x+(-4.3862314305476158e-005))*x+(0.0006936258937832358))*x+(-0.010948035222194548))*x+(0.17272171962785274));
		wts[0] = (((((((((((((1.3824319466948509e-010))*x+(-6.0632980118195212e-013))*x+(-7.7458632100994393e-011))*x+(6.0632980118195212e-013))*x+(-2.6735354670866699e-011))*x+(9.4430419039781555e-010))*x+(-2.046714264736238e-008))*x+(4.3221803528818248e-007))*x+(-9.2147382369326767e-006))*x+(0.00020497163385849171))*x+(-0.005057633746542077))*x+(0.18713853309988535));
		wts[1] = (((((((((((((2.5769016550232964e-012))*x+(1.2884508275116482e-012))*x+(-8.0528176719478008e-013))*x+(5.4001247917767614e-013))*x+(-1.817923589442216e-011))*x+(2.1534862781891206e-010))*x+(-2.9298469946444543e-009))*x+(4.8752774225076692e-008))*x+(-9.5458091516759081e-007))*x+(2.0788174262728842e-005))*x+(-0.00051111126614085693))*x+(0.018905041606872498));
		break;
	case 19:
		rts[0] = (((((((((((((2.1979455292845764e-012))*x+(-5.3053857603420807e-013))*x+(2.3684757858670074e-014))*x+(8.0054481562304614e-013))*x+(-1.286319199304368e-011))*x+(2.6408001711312557e-010))*x+(-5.3194932347899729e-009))*x+(1.0407289922446476e-007))*x+(-2.0117692791423816e-006))*x+(3.8728480777652084e-005))*x+(-0.00074473227768564988))*x+(0.01431772561250726));
		rts[1] = (((((((((((((1.176279814292987e-010))*x+(-3.637978807091713e-012))*x+(-6.3588837898957224e-011))*x+(2.3267906120357413e-011))*x+(-3.7848243058154668e-010))*x+(6.9355176416744744e-009))*x+(-1.1997880170847944e-007))*x+(2.0387223186683436e-006))*x+(-3.4354089596640616e-005))*x+(0.00057701869810535445))*x+(-0.009682136267277831))*x+(0.16242604452612586));
		wts[0] = (((((((((((((2.3889394166568912e-010))*x+(6.6696278130014735e-012))*x+(-1.448370312573388e-010))*x+(-2.9558577807620168e-012))*x+(-1.1368683772161603e-013))*x+(7.0086277522326169e-010))*x+(-1.5572878986347405e-008))*x+(3.4273403937135072e-007))*x+(-7.6729818829964387e-006))*x+(0.00017972941593272229))*x+(-0.0046737027605945275))*x+(0.18227706890563297));
		wts[1] = (((((((((((((4.7293724492192268e-011))*x+(-1.7431981783981123e-012))*x+(-3.2135479462643467e-011))*x+(1.4495071809506042e-012))*x+(-1.4139800441625994e-012))*x+(1.2316340540034312e-010))*x+(-1.94613954581276e-009))*x+(3.679253675799761e-008))*x+(-7.8512112288338842e-007))*x+(1.8190536026297527e-005))*x+(-0.00047221712306753119))*x+(0.018413809955459586));
		break;
	case 20:
		rts[0] = (((((((((((((1.7886729134867587e-011))*x+(9.0949470177292824e-013))*x+(-1.1179205709292242e-011))*x+(-1.1842378929335006e-013))*x+(-6.4173851418066379e-012))*x+(1.9085059458726997e-010))*x+(-3.9675014384954457e-009))*x+(8.1038679581683454e-008))*x+(-1.6437958705826461e-006))*x+(3.3268130675369323e-005))*x+(-0.0006729194281267127))*x+(0.013609809051886849));
		rts[1] = (((((((((((((2.2676734564205009e-010))*x+(0))*x+(-1.4529177860822529e-010))*x+(1.2126596023639042e-011))*x+(-2.2235250677719401e-010))*x+(4.7201732892669189e-009))*x+(-8.547925241704965e-008))*x+(1.5306094033699462e-006))*x+(-2.7272775237637457e-005))*x+(0.00048508541015668261))*x+(-0.0086235670878180102))*x+(0.1532884981786744));
		wts[0] = (((((((((((((2.4010660126805305e-010))*x+(-6.0632980118195212e-013))*x+(-1.4930871354105571e-010))*x+(-9.0949470177292814e-013))*x+(1.0174971976084635e-011))*x+(5.2054597669363523e-010))*x+(-1.1941999981483301e-008))*x+(2.7440968697334256e-007))*x+(-6.4447369621338053e-006))*x+(0.00015862107178472398))*x+(-0.0043359657914335426))*x+(0.17777575041378638));
		wts[1] = (((((((((((((1.2732925824820995e-011))*x+(-4.5474735088646412e-013))*x+(-7.5791225147744025e-012))*x+(4.926429634603361e-013))*x+(-3.4982387357255594e-012))*x+(7.5216277650724805e-011))*x+(-1.3650309031258225e-009))*x+(2.8636121104005003e-008))*x+(-6.5522615668352679e-007))*x+(1.6038147692176243e-005))*x+(-0.00043805329082930637))*x+(0.017959033209151619));
		break;
	case 21:
		rts[0] = (((((((((((((2.076679569048186e-011))*x+(1.8947806286936002e-012))*x+(-1.3500311979441904e-011))*x+(-8.90546895485992e-013))*x+(-3.1441516057384429e-012))*x+(1.387651475207955e-010))*x+(-2.9887416615655598e-009))*x+(6.3779679611760288e-008))*x+(-1.3557875378697457e-006))*x+(2.8785988470851384e-005))*x+(-0.00061100915042694383))*x+(0.012968591212251825));
		rts[1] = (((((((((((((1.9038755757113296e-010))*x+(-8.4886172165473291e-012))*x+(-1.2043225675976524e-010))*x+(1.2505552149377762e-011))*x+(-1.4266750743748466e-010))*x+(3.257023687789721e-009))*x+(-6.1846672079942281e-008))*x+(1.1659526742609689e-006))*x+(-2.1918937740339484e-005))*x+(0.00041166176924656295))*x+(-0.0077294929027710672))*x+(0.14512419333629667));
		wts[0] = (((((((((((((1.7826096154749393e-010))*x+(-1.8189894035458565e-011))*x+(-1.1194363954321791e-010))*x+(9.6254855937634911e-012))*x+(8.2991391536779702e-012))*x+(3.863031376264795e-010))*x+(-9.2401781041454943e-009))*x+(2.2179605766818136e-007))*x+(-5.4568204172119232e-006))*x+(0.00014082128344933273))*x+(-0.0040370169452700758))*x+(0.17359222392616616));
		wts[1] = (((((((((((((2.1827872842550278e-011))*x+(-5.3053857603420807e-013))*x+(-1.3604524914020052e-011))*x+(6.6317322004276004e-013))*x+(9.9475983006414026e-014))*x+(4.8685500075862365e-011))*x+(-1.0005175946995828e-009))*x+(2.278855759652032e-008))*x+(-5.5298211809606801e-007))*x+(1.4231669815177825e-005))*x+(-0.00040783453491438518))*x+(0.01753639018162689));
		break;
	case 22:
		rts[0] = (((((((((((((1.5234036254696548e-011))*x+(-3.4106051316484809e-013))*x+(-9.2607403227399719e-012))*x+(3.0316490059097606e-013))*x+(-2.5342690908776904e-012))*x+(1.0140466244479284e-010))*x+(-2.2751725133514826e-009))*x+(5.071362742710879e-008))*x+(-1.1279878001565584e-006))*x+(2.5073373016524951e-005))*x+(-0.00055726357021101372))*x+(0.01238507318652011));
		rts[1] = (((((((((((((1.9766351518531639e-010))*x+(-6.0632980118195212e-013))*x+(-1.2513131271892536e-010))*x+(5.0022208597511053e-012))*x+(-8.5786192964102754e-011))*x+(2.2823414269623754e-009))*x+(-4.5422225092295314e-008))*x+(9.0022451063968367e-007))*x+(-1.7813893133248698e-005))*x+(0.00035232776505344138))*x+(-0.0069675531625418416))*x+(0.13778555046986216));
		wts[0] = (((((((((((((2.0979011120895544e-010))*x+(6.063298011819521e-012))*x+(-1.3119461073074487e-010))*x+(-4.3200998334214083e-012))*x+(1.6844599789086104e-011))*x+(2.9263939419858309e-010))*x+(-7.2187947471509988e-009))*x+(1.8090042589828195e-007))*x+(-4.6547917891455919e-006))*x+(0.0001256947123090176))*x+(-0.0037709016275900924))*x+(0.16969078437403468));
		wts[1] = (((((((((((((1.606773973132173e-011))*x+(-8.3370347662518418e-013))*x+(-9.5686421749026814e-012))*x+(5.6843418860808015e-013))*x+(1.2789769243681803e-013))*x+(3.3441989918022344e-011))*x+(-7.5713694573191026e-010))*x+(1.8433373198215954e-008))*x+(-4.7094243262972107e-007))*x+(1.2700130540502924e-005))*x+(-0.00038094371404836803))*x+(0.017142256168881504));
		break;
	case 23:
		rts[0] = (((((((((((((7.8822874153653775e-012))*x+(-3.7895612573872008e-014))*x+(-4.3958910585691529e-012))*x+(1.8947806286936003e-013))*x+(-2.4253192047278089e-012))*x+(7.4947603678765518e-011))*x+(-1.7503685908100881e-009))*x+(4.0716201169891761e-008))*x+(-9.4600114467861352e-007))*x+(2.1972373845846948e-005))*x+(-0.00051030872944245534))*x+(0.011851803537268307));
		rts[1] = (((((((((((((1.2005330063402653e-010))*x+(-6.6696278130014735e-012))*x+(-7.2532202466391027e-011))*x+(7.2759576141834259e-012))*x+(-6.2717238809758172e-011))*x+(1.6218919540733623e-009))*x+(-3.3833638409438052e-008))*x+(7.037382691403119e-007))*x+(-1.4625237316601146e-005))*x+(0.00030386522709340463))*x+(-0.0063129525731730344))*x+(0.13115336815775799));
		wts[0] = (((((((((((((2.6072181450823939e-010))*x+(1.2126596023639042e-012))*x+(-1.6621015674900261e-010))*x+(-8.3370347662518418e-013))*x+(2.8630135299560301e-011))*x+(2.2117300583583222e-010))*x+(-5.6941814226737116e-009))*x+(1.4880881948897695e-007))*x+(-3.9979117798331441e-006))*x+(0.00011274771323815934))*x+(-0.0035327873883024799))*x+(0.16604109663121636));
		wts[1] = (((((((((((((3.0013325158506632e-011))*x+(-2.1221543041368323e-012))*x+(-1.8796223836640518e-011))*x+(1.146342280359628e-012))*x+(3.0067800101581578e-012))*x+(2.385114328262716e-011))*x+(-5.8687780561209968e-010))*x+(1.5098130449568241e-008))*x+(-4.0416292017286798e-007))*x+(1.1390803024348415e-005))*x+(-0.00035688614191504292))*x+(0.016773559351202352));
		break;
	case 24:
		rts[0] = (((((((((((((1.0989727646422882e-011))*x+(-1.3263464400855203e-012))*x+(-6.7596298928644192e-012))*x+(9.047577502011942e-013))*x+(-9.012050365223936e-013))*x+(5.5830155313666793e-011))*x+(-1.3606410257753037e-009))*x+(3.2986351076550819e-008))*x+(-7.9924469795327369e-007))*x+(1.9362225485440705e-005))*x+(-0.00046904744351418187))*x+(0.011362560218304937));
		rts[1] = (((((((((((((1.4551915228366852e-010))*x+(2.4253192047278085e-012))*x+(-8.9433645674337939e-011))*x+(2.2737367544323206e-013))*x+(-3.4712381117666752e-011))*x+(1.171064430612508e-009))*x+(-2.5538871758120269e-008))*x+(5.5644088033564754e-007))*x+(-1.2118676434136333e-005))*x+(0.00026389642839204824))*x+(-0.0057464428195562649))*x+(0.12513032702866045));
		wts[0] = (((((((((((((2.3283064365386963e-010))*x+(1.9402553637822468e-011))*x+(-1.4673181188603243e-010))*x+(-1.2581343374525506e-011))*x+(2.6015338031963136e-011))*x+(1.719608159570877e-010))*x+(-4.5321009167764714e-009))*x+(1.2338818204208715e-007))*x+(-3.4554504853012702e-006))*x+(0.00010159306404996145))*x+(-0.0033187176484581883))*x+(0.1626172023749218));
		wts[1] = (((((((((((((1.9705718538413443e-011))*x+(-3.1832314562052488e-012))*x+(-1.284661266254261e-011))*x+(1.9800457569848127e-012))*x+(2.237025379751382e-012))*x+(1.7352637845154579e-011))*x+(-4.6261868410131979e-010))*x+(1.24915745155126e-008))*x+(-3.4919017448398199e-007))*x+(1.0263376835466704e-005))*x+(-0.00033525942778792344))*x+(0.016427674383976947));
		break;
	case 25:
		rts[0] = (((((((((((((1.3339255626002947e-011))*x+(-2.8042753304665285e-012))*x+(-8.3938781851126497e-012))*x+(1.7100395173959742e-012))*x+(1.7763568394002505e-013))*x+(4.194896282191015e-011))*x+(-1.0680773302832827e-009))*x+(2.6949494413841535e-008))*x+(-6.7986005779692893e-007))*x+(1.7149598361281687e-005))*x+(-0.00043259526331788223))*x+(0.01091210743517337));
		rts[1] = (((((((((((((1.13990002622207e-010))*x+(-9.0949470177292824e-012))*x+(-6.7757355282083141e-011))*x+(6.8212102632969618e-012))*x+(-2.400687056554792e-011))*x+(8.5487528167504934e-010))*x+(-1.9515419206565337e-008))*x+(4.4459590350006312e-007))*x+(-1.0126622410289164e-005))*x+(0.00023064016846667995))*x+(-0.0052529012485656975))*x+(0.1196361939838763));
		wts[0] = (((((((((((((1.1884064103166261e-010))*x+(9.701276818911234e-012))*x+(-7.0940586738288403e-011))*x+(-6.5938365878537289e-012))*x+(9.2749511774551755e-012))*x+(1.321846336092373e-010))*x+(-3.6372955018274906e-009))*x+(1.0307048666409931e-007))*x+(-3.0040184616497712e-006))*x+(9.192415909992091e-005))*x+(-0.0031254259928500073))*x+(0.15939674136207871));
		wts[1] = (((((((((((((3.5773458269735173e-011))*x+(2.8800665556142726e-012))*x+(-2.3722653471243877e-011))*x+(-1.9137284349805364e-012))*x+(5.0614327543977798e-012))*x+(1.3928413977737364e-011))*x+(-3.698592543344148e-010))*x+(1.0423106711066053e-008))*x+(-3.035155873021278e-007))*x+(9.2863843917032046e-006))*x+(-0.00031573248838061806))*x+(0.016102341189123157));
		break;
	case 26:
		rts[0] = (((((((((((((6.6696278130014735e-012))*x+(-1.8947806286936003e-013))*x+(-3.6190310008047764e-012))*x+(7.1054273576010006e-014))*x+(-6.5133084111342531e-013))*x+(3.2246945854315826e-011))*x+(-8.4596640803624713e-010))*x+(2.2189848125631073e-008))*x+(-5.8195083300442241e-007))*x+(1.526163663674758e-005))*x+(-0.00040023294601664332))*x+(0.010496007832377944));
		rts[1] = (((((((((((((1.2490393904348213e-010))*x+(-5.1538033100465928e-012))*x+(-7.7989170677028583e-011))*x+(3.5242919693700965e-012))*x+(-9.9854939132152725e-012))*x+(6.3370109160132415e-010))*x+(-1.5084048676783368e-008))*x+(3.5865638473945671e-007))*x+(-8.5274916335475997e-006))*x+(0.00020274482620307824))*x+(-0.0048203150824465196))*x+(0.11460423218269819));
		wts[0] = (((((((((((((2.3404330325623352e-010))*x+(-2.2434202643732228e-011))*x+(-1.5468989052654553e-010))*x+(1.3945585427184897e-011))*x+(3.2789178779542752e-011))*x+(9.8777282649583269e-011))*x+(-2.9472859708334905e-009))*x+(8.6692659273523973e-008))*x+(-2.6256452764032243e-006))*x+(8.3496027156839306e-005))*x+(-0.0029501948778699058))*x+(0.15636033507011635));
		wts[1] = (((((((((((((2.2737367544323206e-011))*x+(-7.5791225147744016e-014))*x+(-1.3718211751741668e-011))*x+(4.7369515717340008e-014))*x+(2.4880838130532843e-012))*x+(1.0392575688911165e-011))*x+(-2.9841166574821421e-010))*x+(8.7621275790539227e-009))*x+(-2.6526344751772358e-007))*x+(8.434875283720951e-006))*x+(-0.00029803034295016194))*x+(0.015795601636347995));
		break;
	case 27:
		rts[0] = (((((((((((((1.1292892547013858e-011))*x+(1.7053025658242404e-012))*x+(-7.005951374594587e-012))*x+(-1.0563402004966822e-012))*x+(5.8264504332328195e-013))*x+(2.5062470617361516e-011))*x+(-6.7604005726806804e-010))*x+(1.8403653212484269e-008))*x+(-5.0104680329385309e-007))*x+(1.3640922659935092e-005))*x+(-0.00037137081044529837))*x+(0.010110475947113395));
		rts[1] = (((((((((((((1.4794447148839632e-010))*x+(1.8189894035458565e-012))*x+(-9.2162129779656724e-011))*x+(-8.7159908919905626e-013))*x+(7.2949054204703511e-013))*x+(4.7584810166275316e-010))*x+(-1.1782371226824276e-008))*x+(2.9189380779115476e-007))*x+(-7.231885843321054e-006))*x+(0.00017917244328771731))*x+(-0.0044390450667413459))*x+(0.10997847861693907));
		wts[0] = (((((((((((((2.5344585689405597e-010))*x+(-1.8189894035458565e-012))*x+(-1.6075318853836504e-010))*x+(6.8212102632969618e-013))*x+(3.3016552454985984e-011))*x+(8.000000661922968e-011))*x+(-2.4046610628640033e-009))*x+(7.3383911984118783e-008))*x+(-2.3063954336932646e-006))*x+(7.6111263372508051e-005))*x+(-0.0027907471220370954))*x+(0.15349109442102926));
		wts[1] = (((((((((((((5.4569682106375694e-012))*x+(-2.5011104298755527e-012))*x+(-2.0842586915629608e-012))*x+(1.5252984060983483e-012))*x+(-3.2448118266377902e-013))*x+(7.8079764875838009e-012))*x+(-2.4282294693496925e-010))*x+(7.4150901715105038e-009))*x+(-2.3300106699597476e-007))*x+(7.688824450660426e-006))*x+(-0.00028192276522015963))*x+(0.015505749379219778));
		break;
	case 28:
		rts[0] = (((((((((((((1.1747639897900323e-011))*x+(-1.0231815394945443e-012))*x+(-7.2996423720420954e-012))*x+(5.8264504332328215e-013))*x+(8.7870451655665696e-013))*x+(1.9183913716839619e-011))*x+(-5.4453972812377549e-010))*x+(1.5366675950219861e-008))*x+(-4.3372502375159839e-007))*x+(1.2241799155791528e-005))*x+(-0.0003455217276401698))*x+(0.0097522627642190832));
		rts[1] = (((((((((((((9.4587448984384537e-011))*x+(9.0949470177292824e-013))*x+(-5.4418099656080208e-011))*x+(-9.0949470177292824e-013))*x+(-3.808509063674137e-012))*x+(3.6099952656816942e-010))*x+(-9.2920841391711893e-009))*x+(2.3950026480553294e-007))*x+(-6.1732400488123673e-006))*x+(0.00015911709058337439))*x+(-0.0041012844418000906))*x+(0.10571165467773097));
		wts[0] = (((((((((((((1.4066851387421289e-010))*x+(-6.063298011819521e-012))*x+(-8.3521930112813906e-011))*x+(2.5769016550232964e-012))*x+(1.4352963262354024e-011))*x+(6.3243040434220659e-011))*x+(-1.9743324012703547e-009))*x+(6.2488637671738901e-008))*x+(-2.0353632847284566e-006))*x+(6.9609512127403531e-005))*x+(-0.0026451617914051546))*x+(0.15077422322673437));
		wts[1] = (((((((((((((3.2287061912938952e-011))*x+(-1.4400332778071363e-012))*x+(-2.1231016944511794e-011))*x+(9.7581202377720412e-013))*x+(4.7476097127704025e-012))*x+(6.1956365963548397e-012))*x+(-1.9995468244123535e-010))*x+(6.3133759701609433e-009))*x+(-2.05616546069635e-007))*x+(7.0319988791263397e-006))*x+(-0.0002672156269050298))*x+(0.015231289617402501));
		break;
	case 29:
		rts[0] = (((((((((((((1.0838145196127394e-011))*x+(-3.4106051316484809e-013))*x+(-6.5985735394254626e-012))*x+(1.5158245029548806e-013))*x+(8.5146704501918659e-013))*x+(1.5105990532523112e-011))*x+(-4.418984252592868e-010))*x+(1.2911572607373264e-008))*x+(-3.7733937569816206e-007))*x+(1.1027655564944602e-005))*x+(-0.00032228044866847535))*x+(0.0094185639515924225));
		rts[1] = (((((((((((((1.6189005691558123e-010))*x+(5.1538033100465928e-012))*x+(-1.0250763201232378e-010))*x+(-3.7137700322394567e-012))*x+(1.2363443602225743e-011))*x+(2.7731417162613065e-010))*x+(-7.3965969645447176e-009))*x+(1.9799543737875067e-007))*x+(-5.3014053619145534e-006))*x+(0.00014194658512168185))*x+(-0.0038006563678769927))*x+(0.10176354464231165));
		wts[0] = (((((((((((((2.0857745160659153e-010))*x+(-7.8822874153653775e-012))*x+(-1.2975457745293775e-010))*x+(4.5474735088646404e-012))*x+(2.6432189770275727e-011))*x+(4.9910890235575302e-011))*x+(-1.634787120489515e-009))*x+(5.3506520399556237e-008))*x+(-1.803940489727059e-006))*x+(6.3859532172944045e-005))*x+(-0.0025118084017417227))*x+(0.14819669616104972));
		wts[1] = (((((((((((((1.3642420526593924e-011))*x+(-1.3642420526593924e-012))*x+(-8.6212518605558817e-012))*x+(8.6212518605558819e-013))*x+(1.7195134205394424e-012))*x+(4.9341271809074288e-012))*x+(-1.6511629101027361e-010))*x+(5.4055587043559204e-009))*x+(-1.8223624234185257e-007))*x+(6.4511268272962607e-006))*x+(-0.00025374418561161622))*x+(0.014970906492923392));
		break;
	case 30:
		rts[0] = (((((((((((((1.152026622245709e-011))*x+(-7.5791225147744016e-014))*x+(-6.906475391588173e-012))*x+(9.4739031434680004e-015))*x+(9.9890466268940738e-013))*x+(1.1954881529163686e-011))*x+(-3.6114137606328234e-010))*x+(1.0912417155080807e-008))*x+(-3.2982583791455833e-007))*x+(9.9689053120743925e-006))*x+(-0.00030130763112200118))*x+(0.0091069463035094271));
		rts[1] = (((((((((((((1.2308494963993627e-010))*x+(-2.7284841053187847e-012))*x+(-7.6890197912386299e-011))*x+(1.4021376652332644e-012))*x+(9.0570514051554093e-012))*x+(2.1354769804323343e-010))*x+(-5.9358152467344407e-009))*x+(1.6482932752026613e-007))*x+(-4.578186214900434e-006))*x+(0.00012716033265269361))*x+(-0.0035319108167552763))*x+(0.098099724321349571));
		wts[0] = (((((((((((((1.1884064103166261e-010))*x+(-5.4569682106375694e-012))*x+(-6.8212102632969618e-011))*x+(2.4253192047278089e-012))*x+(1.1359209869018134e-011))*x+(4.0626465154976657e-011))*x+(-1.3596566835379538e-009))*x+(4.6052909929983343e-008))*x+(-1.6052770356322907e-006))*x+(5.8753154400801685e-005))*x+(-0.0023892950014230141))*x+(0.14574699527421309));
		wts[1] = (((((((((((((1.1747639897900323e-011))*x+(7.5791225147744016e-014))*x+(-7.5459638537722624e-012))*x+(-3.7895612573872008e-014))*x+(1.5027978861326117e-012))*x+(4.1409838521152177e-012))*x+(-1.3742501581148758e-010))*x+(4.652403425472091e-009))*x+(-1.6216640498385262e-007))*x+(5.9352754816719318e-006))*x+(-0.00024136781361935468))*x+(0.014723436443451672));
		break;
	case 31:
		rts[0] = (((((((((((((2.0008883439004421e-011))*x+(4.926429634603361e-013))*x+(-1.266660850281672e-011))*x+(-4.0737783516912407e-013))*x+(2.4957813593573519e-012))*x+(9.6327390508577082e-012))*x+(-2.9723886315243436e-010))*x+(9.2734150543745849e-009))*x+(-2.895607807557043e-007))*x+(9.041463144618284e-006))*x+(-0.00028231738453151132))*x+(0.008815288314802246));
		rts[1] = (((((((((((((1.3824319466948509e-010))*x+(-4.850638409455617e-012))*x+(-8.7008326469610139e-011))*x+(2.3495279795800643e-012))*x+(1.3225568788281333e-011))*x+(1.6654174335902402e-010))*x+(-4.8012989140033824e-009))*x+(1.3811137359690898e-007))*x+(-3.9741937535309191e-006))*x+(0.00011435845714145391))*x+(-0.0032906938343911017))*x+(0.094690554752209569));
		wts[0] = (((((((((((((1.7583564234276611e-010))*x+(-1.2126596023639042e-011))*x+(-1.10730979940854e-010))*x+(7.5033312896266563e-012))*x+(2.3296327829787817e-011))*x+(3.1533886613033246e-011))*x+(-1.140111708745432e-009))*x+(3.9830066356216776e-008))*x+(-1.4338791226401841e-006))*x+(5.4200639213667724e-005))*x+(-0.002276426869959811))*x+(0.14341489288380205));
		wts[1] = (((((((((((((1.1823431123048067e-011))*x+(1.7053025658242404e-012))*x+(-7.0864795513140661e-012))*x+(-9.9475983006414026e-013))*x+(1.358320863194725e-012))*x+(3.545460221706283e-012))*x+(-1.1508749508948311e-010))*x+(4.0236700823056042e-009))*x+(-1.4485140517143483e-007))*x+(5.4753770891916255e-006))*x+(-0.00022996581483085941))*x+(0.014487846258019962));
		break;
	case 32:
		rts[0] = (((((((((((((9.2465294680247699e-012))*x+(5.3053857603420807e-013))*x+(-5.978032883528309e-012))*x+(-4.1685173831259204e-013))*x+(1.1214732846080247e-012))*x+(7.7481724739906586e-012))*x+(-2.4593530915476925e-010))*x+(7.9211261623986697e-009))*x+(-2.5525686370847506e-007))*x+(8.2255880087452969e-006))*x+(-0.00026506747682111847))*x+(0.0085417318182837588));
		rts[1] = (((((((((((((1.0792670461038748e-010))*x+(-3.0316490059097605e-012))*x+(-6.8136311407821865e-011))*x+(1.0231815394945441e-012))*x+(1.038339784524093e-011))*x+(1.3142435288197399e-010))*x+(-3.911388842444314e-009))*x+(1.1642546364024989e-007))*x+(-3.4666008803715029e-006))*x+(0.0001032189332293154))*x+(-0.0030733700924504182))*x+(0.091510378654089064));
		wts[0] = (((((((((((((1.2854191785057384e-010))*x+(-5.4569682106375694e-012))*x+(-7.3820653293902667e-011))*x+(2.7284841053187847e-012))*x+(1.2581343374525505e-011))*x+(2.6657194969933091e-011))*x+(-9.5893367320816968e-010))*x+(3.4604475137219496e-008))*x+(-1.2853096600003631e-006))*x+(5.0127078414128702e-005))*x+(-0.0021721734071835381))*x+(0.14119127149799313));
		wts[1] = (((((((((((((2.9558577807620168e-011))*x+(1.3263464400855203e-012))*x+(-1.7896203038011056e-011))*x+(-6.0632980118195212e-013))*x+(3.6900852743807872e-012))*x+(2.7985021707384777e-012))*x+(-9.7129230584395529e-011))*x+(3.4957823857872938e-009))*x+(-1.2984270888795796e-007))*x+(5.0638634970645345e-006))*x+(-0.00021943407556664145))*x+(0.014263214880837507));
		break;
	case 33:
		rts[0] = (((((((((((((1.3111881950559715e-011))*x+(-1.2126596023639042e-012))*x+(-8.1807153643846196e-012))*x+(7.2001663890356815e-013))*x+(1.5714836839227546e-012))*x+(6.0111915445304468e-012))*x+(-2.0477251376031327e-010))*x+(6.7987305600129373e-009))*x+(-2.2588572210976987e-007))*x+(7.5049958076917064e-006))*x+(-0.00024935157172149537))*x+(0.0082846423553332715));
		rts[1] = (((((((((((((1.0671404500802358e-010))*x+(-1.5158245029548803e-012))*x+(-6.7908937732378633e-011))*x+(1.0610771520684161e-012))*x+(1.1662374769609109e-011))*x+(1.0400095599531294e-010))*x+(-3.2084456573026423e-009))*x+(9.8700080849075292e-008))*x+(-3.037520217944826e-006))*x+(9.3480463396591871e-005))*x+(-0.0028768851191592957))*x+(0.088536873536384758));
		wts[0] = (((((((((((((1.9523819598058859e-010))*x+(4.2443086082736646e-012))*x+(-1.233123233153795e-010))*x+(-3.4106051316484801e-012))*x+(2.6564824414284275e-011))*x+(2.3161324709993398e-011))*x+(-8.1357528121846678e-010))*x+(3.01928594718485e-008))*x+(-1.155959685250618e-006))*x+(4.6469583408342841e-005))*x+(-0.0020756413958142907))*x+(0.13906797353206021));
		wts[1] = (((((((((((((1.8796223836640515e-011))*x+(2.5769016550232964e-012))*x+(-1.1141310096718369e-011))*x+(-1.6910917111090382e-012))*x+(2.1789977229976403e-012))*x+(2.6396662633487722e-012))*x+(-8.2122160923366508e-011))*x+(3.0500760805907134e-009))*x+(-1.1677567459307998e-007))*x+(4.6943813207800389e-006))*x+(-0.00020968236179446457))*x+(0.0140487182276763));
		break;
	case 34:
		rts[0] = (((((((((((((7.2001663890356813e-012))*x+(1.9705718538413444e-012))*x+(-4.3153628818496746e-012))*x+(-1.3642420526593922e-012))*x+(7.4903046728043888e-013))*x+(5.339432599763919e-012))*x+(-1.7135028581212927e-010))*x+(5.8618104074407516e-009))*x+(-2.0062014073040277e-007))*x+(6.866173304685465e-006))*x+(-0.00023499302984867514))*x+(0.0080425764937639092));
		rts[1] = (((((((((((((8.3673512563109398e-011))*x+(7.5791225147744009e-012))*x+(-5.0249582272954285e-011))*x+(-5.4190725980636963e-012))*x+(7.4654356770527865e-012))*x+(8.4738142428856619e-011))*x+(-2.6479420138040646e-009))*x+(8.4116221395665505e-008))*x+(-2.6728196283835421e-006))*x+(8.4929526826653848e-005))*x+(-0.002698657386063682))*x+(0.085750526954242887));
		wts[0] = (((((((((((((1.8068628075222173e-010))*x+(-2.4253192047278085e-012))*x+(-1.1300471669528632e-010))*x+(1.0610771520684161e-012))*x+(2.3817392502678555e-011))*x+(1.8251474405891106e-011))*x+(-6.9202984083934394e-010))*x+(2.6449737807373214e-008))*x+(-1.0428760492398046e-006))*x+(4.3175070907249445e-005))*x+(-0.0019860532631626954))*x+(0.13703767516330623));
		wts[1] = (((((((((((((2.0312048339595396e-011))*x+(-3.2211270687791207e-012))*x+(-1.3339255626002947e-011))*x+(2.1316282072803006e-012))*x+(3.0399386711602952e-012))*x+(1.3513634655737405e-012))*x+(-7.0000301851299199e-011))*x+(2.6720185878718419e-009))*x+(-1.0535188146402567e-007))*x+(4.3615679105226072e-006))*x+(-0.00020063212241948868))*x+(0.013843616441875027));
		break;
	case 35:
		rts[0] = (((((((((((((1.2278178473934531e-011))*x+(5.6843418860808015e-013))*x+(-7.617018127348274e-012))*x+(-3.3158661002138007e-013))*x+(1.5187850976872141e-012))*x+(4.1609678665584698e-012))*x+(-1.4423225576839133e-010))*x+(5.075695512039383e-009))*x+(-1.7879031263591991e-007))*x+(6.2978433011910461e-006))*x+(-0.00022183992363276978))*x+(0.0078142547125072629));
		rts[1] = (((((((((((((1.255102688446641e-010))*x+(-3.3348139065007367e-012))*x+(-8.0225011818887041e-011))*x+(1.9326762412674725e-012))*x+(1.602984411874786e-011))*x+(6.6709304746837006e-011))*x+(-2.1997833184646725e-009))*x+(7.2043626027825283e-008))*x+(-2.3612474789417672e-006))*x+(7.7390490737410292e-005))*x+(-0.002536493079799816))*x+(0.08313420782528505));
		wts[0] = (((((((((((((1.8189894035458565e-010))*x+(-1.4551915228366852e-011))*x+(-1.1596057447604835e-010))*x+(8.3370347662518416e-012))*x+(2.5636381906224415e-011))*x+(1.3623472720306989e-011))*x+(-5.9206743211840751e-010))*x+(2.3258519258699074e-008))*x+(-9.436268191646372e-007))*x+(4.0198506196076345e-005))*x+(-0.0019027292939517969))*x+(0.13509377987256294));
		wts[1] = (((((((((((((6.8212102632969618e-013))*x+(-1.8568850161197284e-012))*x+(1.0658141036401503e-012))*x+(9.8054897534893805e-013))*x+(-8.7870451655665716e-013))*x+(1.3821536507900114e-012))*x+(-5.9385404001706846e-011))*x+(2.349582806093764e-009))*x+(-9.532569324755917e-008))*x+(4.0608737909442888e-006))*x+(-0.00019221469213472807))*x+(0.013647243139545774));
		break;
	case 36:
		rts[0] = (((((((((((((5.3053857603420811e-012))*x+(-5.6843418860808015e-013))*x+(-2.9084882650446762e-012))*x+(3.1974423109204508e-013))*x+(3.7421917416698603e-013))*x+(3.3023953941816822e-012))*x+(-1.2182569767797225e-010))*x+(4.412748555449042e-009))*x+(-1.5985053082821313e-007))*x+(5.7905446285381789e-006))*x+(-0.00020976100188747741))*x+(0.0075985387774445195));
		rts[1] = (((((((((((((1.2126596023639041e-010))*x+(-1.0307606620093186e-011))*x+(-7.6549137399221451e-011))*x+(5.7980287238024167e-012))*x+(1.5309827479844291e-011))*x+(5.3276494327292312e-011))*x+(-1.8369388972890497e-009))*x+(6.1991639673427315e-008))*x+(-2.093781121148552e-006))*x+(7.0717993361113507e-005))*x+(-0.0023885182685059502))*x+(0.080672813899263257));
		wts[0] = (((((((((((((2.6193447411060333e-010))*x+(1.0913936421275139e-011))*x+(-1.7189449863508344e-010))*x+(-8.0338698656608666e-012))*x+(3.9904080040287226e-011))*x+(1.4802973661668752e-011))*x+(-5.1008797186113952e-010))*x+(2.0525079709917311e-008))*x+(-8.5619847027077845e-007))*x+(3.7501499762652525e-005))*x+(-0.0018250729882301798))*x+(0.1332303281415036));
		wts[1] = (((((((((((((4.4716822837168966e-012))*x+(4.850638409455617e-012))*x+(-2.9795425386206866e-012))*x+(-2.9653316839054846e-012))*x+(6.513308411134251e-013))*x+(1.9083993644623356e-012))*x+(-5.1188886462938399e-011))*x+(2.0734256904001809e-009))*x+(-8.6493625404276964e-008))*x+(3.7884208044467833e-006))*x+(-0.00018436981216230614))*x+(0.013458996287031101));
		break;
	case 37:
		rts[0] = (((((((((((((9.1707382428770253e-012))*x+(-1.3263464400855202e-013))*x+(-5.6985527407960027e-012))*x+(4.9737991503207e-014))*x+(1.1498949940384287e-012))*x+(2.7781480819536832e-012))*x+(-1.0355762543786302e-010))*x+(3.8510276726781232e-009))*x+(-1.433535629242107e-007))*x+(5.3362999118831151e-006))*x+(-0.00019864240277284281))*x+(0.0073944127638589487));
		rts[1] = (((((((((((((8.7917821171383054e-011))*x+(-1.5158245029548803e-012))*x+(-5.4077039142915354e-011))*x+(6.442254137558241e-013))*x+(1.009918075093689e-011))*x+(4.426089124838957e-011))*x+(-1.5415652458254194e-009))*x+(5.357647673657577e-008))*x+(-1.8631359237723335e-006))*x+(6.4791027776312876e-005))*x+(-0.0022531245209309043))*x+(0.078352980051900001));
		wts[0] = (((((((((((((1.3945585427184898e-010))*x+(-3.637978807091713e-012))*x+(-8.4961963390621038e-011))*x+(1.4400332778071365e-012))*x+(1.7356190558833379e-011))*x+(1.0577612859682025e-011))*x+(-4.375815265689198e-010))*x+(1.8174663255858075e-008))*x+(-7.7891505473326451e-007))*x+(3.5051178798521189e-005))*x+(-0.0017525589398080116))*x+(0.13144192048560158));
		wts[1] = (((((((((((((1.6219322181617219e-011))*x+(-7.5791225147744016e-014))*x+(-9.9760200100718066e-012))*x+(-4.7369515717340033e-015))*x+(2.0795217399912263e-012))*x+(1.0921633967579205e-012))*x+(-4.4237169483096743e-011))*x+(1.8360128602642098e-009))*x+(-7.8686398302200519e-008))*x+(3.5408881137027424e-006))*x+(-0.00017704440567468962))*x+(0.013278330425601566));
		break;
	case 38:
		rts[0] = (((((((((((((9.3602163057463859e-012))*x+(-3.2211270687791205e-013))*x+(-5.8193450058752205e-012))*x+(1.5868787765308901e-013))*x+(1.1889748445052342e-012))*x+(2.2859492077031969e-012))*x+(-8.8345913917819972e-011))*x+(3.3729702642038006e-009))*x+(-1.2893090429027626e-007))*x+(4.9283510267190845e-006))*x+(-0.00018838496063065875))*x+(0.0072009670577139464));
		rts[1] = (((((((((((((9.8831757592658193e-011))*x+(-2.4253192047278085e-012))*x+(-6.0898249406212316e-011))*x+(1.2126596023639042e-012))*x+(1.1818694171476333e-011))*x+(3.6161888298617357e-011))*x+(-1.3006942189974777e-009))*x+(4.6495632233245487e-008))*x+(-1.6633930384849871e-006))*x+(5.9508311141709402e-005))*x+(-0.0021289250133339692))*x+(0.076162835501701026));
		wts[0] = (((((((((((((1.5400776950021583e-010))*x+(-1.8189894035458565e-012))*x+(-9.5117987560418741e-011))*x+(3.0316490059097611e-013))*x+(1.9961513923287079e-011))*x+(9.1446850092324894e-012))*x+(-3.7907839830116547e-010))*x+(1.6144819407296989e-008))*x+(-7.1037386112360313e-007))*x+(3.2819274305012629e-005))*x+(-0.0016847227475118146))*x+(0.12972365155840307));
		wts[1] = (((((((((((((1.5688783605583012e-011))*x+(1.1368683772161603e-013))*x+(-9.687065964196032e-012))*x+(-1.3737159558028603e-013))*x+(2.035704937952687e-012))*x+(9.5464377144101787e-013))*x+(-3.829727276046431e-011))*x+(1.6309559813798558e-009))*x+(-7.1762332695448253e-008))*x+(3.315419973667794e-006))*x+(-0.00017019155863171365))*x+(0.013104750014640629));
		break;
	case 39:
		rts[0] = (((((((((((((8.7538865045644343e-012))*x+(1.5158245029548803e-013))*x+(-5.3740715581322247e-012))*x+(-1.3263464400855202e-013))*x+(1.0806170773018191e-012))*x+(1.9664270212160773e-012))*x+(-7.5666019746141913e-011))*x+(2.9643812959889711e-009))*x+(-1.1627729005978435e-007))*x+(4.560947120936752e-006))*x+(-0.00017890198718156219))*x+(0.0070173848041817886));
		rts[1] = (((((((((((((8.3673512563109398e-011))*x+(6.0632980118195212e-013))*x+(-5.0704329623840749e-011))*x+(-9.0949470177292814e-013))*x+(9.5496943686157465e-012))*x+(3.0295173777024801e-011))*x+(-1.1022972164672258e-009))*x+(4.0508566871248299e-008))*x+(-1.4897145618752992e-006))*x+(5.4784633524827354e-005))*x+(-0.0020147188749239176))*x+(0.074091800637759261));
		wts[0] = (((((((((((((1.4066851387421289e-010))*x+(-4.850638409455617e-012))*x+(-8.6856744019314647e-011))*x+(2.5011104298755527e-012))*x+(1.8142524519741223e-011))*x+(7.2001663890356805e-012))*x+(-3.2924714806388989e-010))*x+(1.4385375261364667e-008))*x+(-6.4939612731684804e-007))*x+(3.0781378022130358e-005))*x+(-0.0016211525757913526))*x+(0.12807105348751435));
		wts[1] = (((((((((((((1.3794002976889411e-011))*x+(-3.0316490059097606e-013))*x+(-8.4412477008299886e-012))*x+(1.3737159558028603e-013))*x+(1.7372769889334446e-012))*x+(7.531752999057062e-013))*x+(-3.3248700089435105e-011))*x+(1.4532154368751549e-009))*x+(-6.5602331518477262e-008))*x+(3.1095506428819677e-006))*x+(-0.00016376966718185181))*x+(0.012937803707367407));
		break;
	case 40:
		rts[0] = (((((((((((((7.5791225147744009e-012))*x+(1.7053025658242404e-013))*x+(-4.6232647340123849e-012))*x+(-1.4684549872375402e-013))*x+(9.2015284280932974e-013))*x+(1.6596353920779923e-012))*x+(-6.5055146455013827e-011))*x+(2.6137737807463424e-009))*x+(-1.0513860735269127e-007))*x+(4.2291737206298745e-006))*x+(-0.00017011743391779174))*x+(0.006842930377519341));
		rts[1] = (((((((((((((8.6705161569019154e-011))*x+(9.0949470177292824e-013))*x+(-5.3849665467472115e-011))*x+(-9.4739031434680011e-013))*x+(1.0828671292983924e-011))*x+(2.5133080801727676e-011))*x+(-9.3868720204189527e-010))*x+(3.5423244041747161e-008))*x+(-1.3381235429617739e-006))*x+(5.0547959083865883e-005))*x+(-0.001909462050553026))*x+(0.072130416118038415));
		wts[0] = (((((((((((((1.3945585427184898e-010))*x+(-4.850638409455617e-012))*x+(-8.5416710741507502e-011))*x+(2.1221543041368323e-012))*x+(1.7706724975141693e-011))*x+(6.2433021715454134e-012))*x+(-2.8708443030230529e-010))*x+(1.285463261761303e-008))*x+(-5.9498627489699507e-007))*x+(2.8916334468886973e-005))*x+(-0.001561482061217246))*x+(0.12648004695860574));
		wts[1] = (((((((((((((1.5688783605583012e-011))*x+(-1.5158245029548803e-013))*x+(-9.8386484144915211e-012))*x+(1.4210854715202004e-014))*x+(2.1257070178156332e-012))*x+(6.7087076634682786e-013))*x+(-2.9043193775872091e-011))*x+(1.298578540994318e-009))*x+(-6.0105817423911065e-008))*x+(2.9211429836579574e-006))*x+(-0.0001577417211031018))*x+(0.012777079409349768));
		break;
	case 41:
		rts[0] = (((((((((((((8.5644084416950737e-012))*x+(-1.3263464400855202e-013))*x+(-5.3290705182007514e-012))*x+(5.6843418860808002e-014))*x+(1.113775738303957e-012))*x+(1.3549901941208493e-012))*x+(-5.6174898066529977e-011))*x+(2.3117744292940517e-009))*x+(-9.5302326198522705e-008))*x+(3.9288141909085347e-006))*x+(-0.00016196436266420456))*x+(0.0066769395290891785));
		rts[1] = (((((((((((((9.943808739384015e-011))*x+(-6.0632980118195212e-013))*x+(-6.2906716872627528e-011))*x+(1.1368683772161603e-013))*x+(1.3377151238576818e-011))*x+(2.0724163126336254e-011))*x+(-8.0292394954994951e-010))*x+(3.1085104416443223e-008))*x+(-1.2053333514986757e-006))*x+(4.6737109741531078e-005))*x+(-0.0018122433541615617))*x+(0.070270198412731258));
		wts[0] = (((((((((((((1.5158245029548803e-010))*x+(2.4253192047278085e-012))*x+(-9.3298998156872884e-011))*x+(-2.1979455292845764e-012))*x+(1.9592031700691827e-011))*x+(6.1627739948259351e-012))*x+(-2.5141636920504118e-010))*x+(1.1518297723019561e-008))*x+(-5.4629997586763679e-007))*x+(2.7205740783076138e-005))*x+(-0.0015053843231428244))*x+(0.12494689882085383));
		wts[1] = (((((((((((((1.5537201155287523e-011))*x+(0))*x+(-9.658644254765628e-012))*x+(-6.1580370432542012e-014))*x+(2.0629424094901574e-012))*x+(5.8619775700208255e-013))*x+(-2.5410877106205969e-011))*x+(1.1635875966457356e-009))*x+(-5.5187503850371668e-008))*x+(2.7483379293711621e-006))*x+(-0.00015207469874424178))*x+(0.012622199995771084));
		break;
	case 42:
		rts[0] = (((((((((((((8.4507216039734577e-012))*x+(-2.0842586915629605e-013))*x+(-5.3172281392714159e-012))*x+(1.0184445879228102e-013))*x+(1.1315393066979595e-012))*x+(1.1364983028746185e-012))*x+(-4.8666061921072882e-011))*x+(2.0506911446727116e-009))*x+(-8.6589906212256027e-008))*x+(3.6562368130949158e-006))*x+(-0.00015438366661936907))*x+(0.0065188109353125721));
		rts[1] = (((((((((((((9.0949470177292824e-011))*x+(-5.4569682106375694e-012))*x+(-5.7070792536251247e-011))*x+(2.9937533933358886e-012))*x+(1.2012909185917428e-011))*x+(1.6761703136580763e-011))*x+(-6.8918115658789247e-010))*x+(2.736916234387839e-008))*x+(-1.0886140502190203e-006))*x+(4.32999028352384e-005))*x+(-0.0017222646823264196))*x+(0.068503517138518946));
		wts[0] = (((((((((((((1.5400776950021583e-010))*x+(-2.4253192047278085e-012))*x+(-9.6179064712487148e-011))*x+(7.5791225147744013e-013))*x+(2.0672056659047179e-011))*x+(4.7701102327361395e-012))*x+(-2.2090744048834191e-010))*x+(1.0347991796777478e-008))*x+(-5.0261825181493092e-007))*x+(2.5633533264753556e-005))*x+(-0.0014525668848524448))*x+(0.12346818521244961));
		wts[1] = (((((((((((((1.5309827479844291e-011))*x+(-2.2737367544323206e-013))*x+(-9.559168271759214e-012))*x+(7.1054273576010019e-014))*x+(2.0522842684537559e-012))*x+(4.8050452505776775e-013))*x+(-2.2312633222535776e-011))*x+(1.0453600947831394e-009))*x+(-5.0774754477289623e-008))*x+(2.5895127171056405e-006))*x+(-0.00014673905395706915))*x+(0.012472819586350071));
		break;
	case 43:
		rts[0] = (((((((((((((7.3896444519050419e-012))*x+(-3.4106051316484809e-013))*x+(-4.5403680815070402e-012))*x+(1.9421501444109404e-013))*x+(9.3436369752453174e-013))*x+(9.3954473830611574e-013))*x+(-4.2280947261848681e-011))*x+(1.8242056569010381e-009))*x+(-7.8850718479457155e-008))*x+(3.4083022701191187e-006))*x+(-0.0001473229960707166))*x+(0.0063679989188458888));
		rts[1] = (((((((((((((8.1248193358381585e-011))*x+(1.8189894035458565e-012))*x+(-4.9112713895738125e-011))*x+(-1.4400332778071363e-012))*x+(9.630222545335224e-012))*x+(1.494745068460664e-011))*x+(-5.9358976992977353e-010))*x+(2.4173609632545851e-008))*x+(-9.8568714137122382e-007))*x+(4.0191645078818672e-005))*x+(-0.0016388245820186619))*x+(0.066823490442856209));
		wts[0] = (((((((((((((1.5643308870494366e-010))*x+(-1.2126596023639042e-012))*x+(-9.7543306765146554e-011))*x+(7.5791225147743953e-014))*x+(2.0880482528203476e-011))*x+(4.2348347051301963e-012))*x+(-1.9458716119894839e-010))*x+(9.3197461599932759e-009))*x+(-4.6332646758129309e-007))*x+(2.4185643953548532e-005))*x+(-0.0014027673491502899))*x+(0.1220407593760747));
		wts[1] = (((((((((((((1.5158245029548802e-011))*x+(-2.6526928801710404e-013))*x+(-9.3791641120333208e-012))*x+(9.4739031434679991e-014))*x+(1.9800457569848122e-012))*x+(4.084140433254409e-013))*x+(-1.9641177573248566e-011))*x+(9.4148746206575607e-010))*x+(-4.6805479048117604e-008))*x+(2.4432461940265132e-006))*x+(-0.0001417082792418602))*x+(0.012328620294043597));
		break;
	case 44:
		rts[0] = (((((((((((((7.73070496506989e-012))*x+(-2.8421709430404007e-013))*x+(-4.7748471843078732e-012))*x+(1.3500311979441904e-013))*x+(9.9594406795707369e-013))*x+(8.1468165546993987e-013))*x+(-3.6875428636543951e-011))*x+(1.627079295370611e-009))*x+(-7.1957167920947779e-008))*x+(3.1822874863715249e-006))*x+(-0.00014073585218817003))*x+(0.0062240071572797215));
		rts[1] = (((((((((((((8.0035533756017685e-011))*x+(-9.0949470177292824e-013))*x+(-4.9719043696920075e-011))*x+(2.6526928801710409e-013))*x+(1.0364450038953995e-011))*x+(1.2284099663399198e-011))*x+(-5.1353706472430838e-010))*x+(2.1415593890831509e-008))*x+(-8.9464221878869188e-007))*x+(3.7373907911452301e-005))*x+(-0.0015613045381282658))*x+(0.065223895413762223));
		wts[0] = (((((((((((((1.5400776950021583e-010))*x+(-1.2126596023639042e-012))*x+(-9.6936976963964597e-011))*x+(3.7895612573871976e-014))*x+(2.119312133193792e-011))*x+(3.6853483228090527e-012))*x+(-1.7204519290695919e-010))*x+(8.4136709451361932e-009))*x+(-4.278972109787264e-007))*x+(2.2849714080674932e-005))*x+(-0.0013557497019700076))*x+(0.12066172347530424));
		wts[1] = (((((((((((((1.4400332778071363e-011))*x+(1.1368683772161603e-013))*x+(-8.9528384705772623e-012))*x+(-1.3263464400855202e-013))*x+(1.91491267287347e-012))*x+(3.9923619965520629e-013))*x+(-1.7352970912061967e-011))*x+(8.4995120201251473e-010))*x+(-4.3226397699695308e-008))*x+(2.3082898711815113e-006))*x+(-0.00013695853233625313))*x+(0.012189309377925299));
		break;
	default:
		double fr = 1/X;
		double fw = sqrt(fr);
		for(unsigned int i = 0 ; i < 2 ; i++){
			double DUM = fr*hermite_roots[2][i]*hermite_roots[2][i];
			rts[i] = DUM/(1.0-DUM);
			wts[i] = fw*hermite_weights[2][i];
		}
		break;
	}
}

void __Root3(double X , double rts[] , double wts[]){
	int n = int(X);
	double x = X - double(n) - 0.5;

	switch(n){
	case 0:
		rts[0] = (((((((((((((1.152026622245709e-011))*x+(-7.73070496506989e-012))*x+(4.3579954459952822e-012))*x+(-3.5451345562857263e-011))*x+(-5.1534243539208536e-010))*x+(2.2246862722378559e-008))*x+(-4.3171804546086412e-007))*x+(6.41802550534661e-006))*x+(-8.1536512818789861e-005))*x+(0.00089643775901301209))*x+(-0.0083278193502929442))*x+(0.05597829853502162));
		rts[1] = (((((((((((((9.8467959711949017e-010))*x+(4.1230426480372742e-011))*x+(-5.9450637005890406e-010))*x+(3.6076623170326155e-010))*x+(-1.284259572760978e-008))*x+(3.189623498656146e-008))*x+(1.7245348556590065e-006))*x+(-1.1670843606500132e-005))*x+(-0.00035799234364438282))*x+(0.0092253037382937775))*x+(-0.11002385445173578))*x+(0.7194611364462461));
		rts[2] = (((((((((((((8.2266827424367258e-009))*x+(1.7462298274040222e-010))*x+(-4.7924307485421496e-009))*x+(4.2806883963445817e-009))*x+(-8.3534056708837543e-009))*x+(-3.3745292663904059e-007))*x+(-3.4645181585801761e-006))*x+(-1.4771375987265854e-005))*x+(0.00022251728134155732))*x+(0.049827756383144184))*x+(-0.9753916072845531))*x+(6.162675611437777));
		wts[0] = (((((((((((((3.1044085820515949e-010))*x+(2.4253192047278085e-012))*x+(-8.7978454151501251e-010))*x+(8.1974273295296971e-009))*x+(-8.9152119168526639e-008))*x+(9.3361280543528368e-007))*x+(-9.2641440758711707e-006))*x+(8.6607318001104744e-005))*x+(-0.0007608744771268049))*x+(0.0062582517993059108))*x+(-0.049612400018778376))*x+(0.44144234452416525));
		wts[1] = (((((((((((((1.721976635356744e-010))*x+(2.1815746246526637e-009))*x+(-2.4822687313038234e-008))*x+(2.5581130103091704e-007))*x+(-2.4295187586176326e-006))*x+(2.0875200831937946e-005))*x+(-0.0001604060162557393))*x+(0.0010851377516865786))*x+(-0.0063150272674011845))*x+(0.030470002759837522))*x+(-0.11327402076212566))*x+(0.29564450356578331));
		wts[2] = (((((((((((((-4.8021320253610611e-010))*x+(6.0972524806857109e-009))*x+(-6.7035519653776035e-008))*x+(6.6979555413126945e-007))*x+(-6.0021651317280576e-006))*x+(4.7579640446807993e-005))*x+(-0.00032767101805338444))*x+(0.0019125678978924772))*x+(-0.0091277689918659952))*x+(0.033647013853796606))*x+(-0.08620731139860284))*x+(0.11853754380220041));
		break;
	case 1:
		rts[0] = (((((((((((((-3.3954468866189317e-011))*x+(3.7895612573872005e-012))*x+(2.683009370230138e-011))*x+(-6.6885756192884092e-012))*x+(-6.6704804642843852e-010))*x+(1.7972332363077232e-008))*x+(-3.1056205251900332e-007))*x+(4.5730949624900319e-006))*x+(-5.9756362428646056e-005))*x+(0.00068634121501934481))*x+(-0.006755910235385772))*x+(0.04847138843815893));
		rts[1] = (((((((((((((7.0819320778052009e-010))*x+(-2.9103830456733704e-011))*x+(-4.2867516943564011e-010))*x+(7.3396222433075309e-010))*x+(-8.1083726399810968e-009))*x+(-4.3808332369129247e-008))*x+(1.6717573908901309e-006))*x+(-2.9900856333142656e-006))*x+(-0.00038722051455541967))*x+(0.0080987656366897642))*x+(-0.092685180605700607))*x+(0.61829466643905651));
		rts[2] = (((((((((((((8.9251746733983347e-009))*x+(1.9402553637822466e-009))*x+(-5.806214176118373e-009))*x+(3.3639177369574709e-009))*x+(2.9788376802268129e-008))*x+(-2.7116432950909558e-007))*x+(-5.4252755224600451e-006))*x+(-3.7159989327998723e-005))*x+(0.00012196731621472166))*x+(0.050366904738382345))*x+(-0.87514700437651904))*x+(5.237315699696631));
		wts[0] = (((((((((((((4.8021320253610611e-010))*x+(4.850638409455617e-012))*x+(-6.054203064801792e-010))*x+(3.7894096749369055e-009))*x+(-4.3733128525976398e-008))*x+(4.8845131080573379e-007))*x+(-5.1551090779848136e-006))*x+(5.1662055049916944e-005))*x+(-0.00049113197425036204))*x+(0.004414967672480433))*x+(-0.039073374403821914))*x+(0.39740551694760601));
		wts[1] = (((((((((((((4.1230426480372745e-010))*x+(8.5492501966655254e-010))*x+(-1.0532251811431099e-008))*x+(1.0863050192710944e-007))*x+(-1.0568771434312414e-006))*x+(9.3504974785219019e-006))*x+(-7.4473902108943932e-005))*x+(0.00052641257737029434))*x+(-0.0032335735686876972))*x+(0.016700160569584472))*x+(-0.067630486810111023))*x+(0.20746886889213764));
		wts[2] = (((((((((((((-1.2187229003757238e-010))*x+(2.4562420245880881e-009))*x+(-2.7172859518032055e-008))*x+(2.7296346161165269e-007))*x+(-2.4672844081881822e-006))*x+(1.9763478240027627e-005))*x+(-0.00013784934139815516))*x+(0.00081739927133088008))*x+(-0.0039801582951871917))*x+(0.015066642681859957))*x+(-0.040036400683367876))*x+(0.058476560000590934));
		break;
	case 2:
		rts[0] = (((((((((((((8.6705161569019154e-011))*x+(6.063298011819521e-012))*x+(-5.2561214639960469e-011))*x+(5.7411853049416095e-012))*x+(-6.1215151466361328e-010))*x+(1.3417007949101389e-008))*x+(-2.1653899014613859e-007))*x+(3.2667617627287387e-006))*x+(-4.4233309650078726e-005))*x+(0.0005316607537589797))*x+(-0.0055456541288854168))*x+(0.042346342897353915));
		rts[1] = (((((((((((((7.7125150710344315e-010))*x+(-8.7311491370201111e-011))*x+(-5.0476955948397517e-010))*x+(6.6120264818891883e-010))*x+(-2.5668972133037942e-009))*x+(-8.134973465227327e-008))*x+(1.276809291776241e-006))*x+(4.4749528337698994e-006))*x+(-0.00038358601145938032))*x+(0.0069350721151766317))*x+(-0.077653226862548844))*x+(0.53331966134978503));
		rts[2] = (((((((((((((2.0178655783335366e-009))*x+(-3.4924596548080444e-010))*x+(-1.5910093983014424e-009))*x+(2.2676734564205008e-009))*x+(5.7360618181216218e-008))*x+(4.0150249939567097e-008))*x+(-6.220288393402976e-006))*x+(-6.7058527311777042e-005))*x+(-8.511055264411499e-005))*x+(0.050452245947396314))*x+(-0.77422445212890323))*x+(4.412614743785821));
		wts[0] = (((((((((((((4.6323596810301143e-010))*x+(2.1827872842550278e-011))*x+(-4.2822042208475364e-010))*x+(1.8061048952707399e-009))*x+(-2.2370272745320104e-008))*x+(2.6573617143791728e-007))*x+(-2.9666124958064679e-006))*x+(3.1910067055681182e-005))*x+(-0.00032761063691355563))*x+(0.0032064956697847036))*x+(-0.031533310490872372))*x+(0.36230293333965097));
		wts[1] = (((((((((((((1.5158245029548803e-010))*x+(3.4682064627607662e-010))*x+(-4.4282539117072393e-009))*x+(4.6988589019747444e-008))*x+(-4.6955212458973011e-007))*x+(4.2917629343719454e-006))*x+(-3.5578550630373705e-005))*x+(0.00026378702896678874))*x+(-0.0017173262520379649))*x+(0.0095339473461589774))*x+(-0.042148116153000063))*x+(0.15376530052631357));
		wts[2] = (((((((((((((-3.9108272176235914e-011))*x+(9.9771568784490228e-010))*x+(-1.1065158863251174e-008))*x+(1.1200855472755696e-007))*x+(-1.0225820877470444e-006))*x+(8.2900072963335934e-006))*x+(-5.8679100558641409e-005))*x+(0.00035439342622645142))*x+(-0.0017668693325251922))*x+(0.0069034755113486779))*x+(-0.01915996798837788))*x+(0.030223737919183341));
		break;
	case 3:
		rts[0] = (((((((((((((7.7913379451880844e-011))*x+(-3.9411437076826888e-012))*x+(-4.9434826602616035e-011))*x+(1.6105635343895603e-011))*x+(-5.1275842830970453e-010))*x+(9.3827997223646289e-009))*x+(-1.4849340919849871e-007))*x+(2.364276210956954e-006))*x+(-3.3084525266832698e-005))*x+(0.00041658446814068123))*x+(-0.00460297197504928))*x+(0.037291179239607501));
		rts[1] = (((((((((((((5.5297277867794037e-010))*x+(-7.0334256937106446e-011))*x+(-3.6440421051035326e-010))*x+(3.6789060686714942e-010))*x+(1.1923475540243089e-009))*x+(-8.5411926420420059e-008))*x+(7.6328054158617909e-007))*x+(9.5846950595538747e-006))*x+(-0.0003546063964884697))*x+(0.0058226719223020505))*x+(-0.064910058854876315))*x+(0.46222358893502447));
		rts[2] = (((((((((((((3.1044085820515949e-010))*x+(9.1192002097765601e-010))*x+(-5.0931703299283981e-010))*x+(-2.7454613397518792e-009))*x+(5.7172352777949222e-008))*x+(4.6078071136435023e-007))*x+(-4.718434316449323e-006))*x+(-9.5466723962545061e-005))*x+(-0.00041266379301418965))*x+(0.049734205767014622))*x+(-0.67387397353308631))*x+(3.6886842472217447));
		wts[0] = (((((((((((((5.7965128992994619e-010))*x+(0))*x+(-4.4337866711430246e-010))*x+(9.0388615111199511e-010))*x+(-1.1912068960858354e-008))*x+(1.4945013049327827e-007))*x+(-1.7572640557498669e-006))*x+(2.038902110849487e-005))*x+(-0.00022501602565550002))*x+(0.0023890191783088781))*x+(-0.025988893105816178))*x+(0.33367769632707422));
		wts[1] = (((((((((((((4.8506384094556168e-011))*x+(1.5522042910257974e-010))*x+(-1.8922037270385772e-009))*x+(2.0726550549928408e-008))*x+(-2.1336030423905564e-007))*x+(2.0225056734564837e-006))*x+(-1.7522293651595078e-005))*x+(0.0001366478758327479))*x+(-0.00094625613078055005))*x+(0.0056645954789059458))*x+(-0.027332140988465613))*x+(0.11966587913264574));
		wts[2] = (((((((((((((1.8189894035458565e-012))*x+(4.0563463699072599e-010))*x+(-4.5431913046437931e-009))*x+(4.6327841118909419e-008))*x+(-4.2778927896354918e-007))*x+(3.5161635191608789e-006))*x+(-2.5315524584623716e-005))*x+(0.00015619108890777925))*x+(-0.00080062510719492808))*x+(0.0032480921936288661))*x+(-0.009486059017050498))*x+(0.016503459741903655));
		break;
	case 4:
		rts[0] = (((((((((((((4.9112713895738125e-011))*x+(-3.9411437076826888e-012))*x+(-3.1908105787200235e-011))*x+(1.7469877396554995e-011))*x+(-4.0113690147336456e-010))*x+(6.1164927937322009e-009))*x+(-1.0239613808712041e-007))*x+(1.7452230599938427e-006))*x+(-2.4942220444273963e-005))*x+(0.00033016176926758495))*x+(-0.0038602892264766836))*x+(0.033073931864666471));
		rts[1] = (((((((((((((5.7722597072521842e-010))*x+(1.2126596023639042e-011))*x+(-3.992681740783155e-010))*x+(7.9580786405131221e-011))*x+(2.8068522321215519e-009))*x+(-7.0841177072603984e-008))*x+(2.8900727144787197e-007))*x+(1.2178492099224059e-005))*x+(-0.00031028773954185529))*x+(0.0048227443589906605))*x+(-0.054286881208563183))*x+(0.40279185960248903));
		rts[2] = (((((((((((((3.9775234957536059e-009))*x+(2.3283064365386963e-010))*x+(-2.826709533110261e-009))*x+(-5.8522952410082017e-009))*x+(2.4768572378282745e-008))*x+(7.6212745625525713e-007))*x+(-9.3351576898233657e-007))*x+(-0.00011035832091010887))*x+(-0.00083066124178691548))*x+(0.047884262893140545))*x+(-0.57604586972934368))*x+(3.0640321457210096));
		wts[0] = (((((((((((((2.9588894297679264e-010))*x+(3.152914966146151e-011))*x+(-2.1767239862432081e-010))*x+(4.4989671247700842e-010))*x+(-6.680863862129626e-009))*x+(8.5954913705184766e-008))*x+(-1.0693826837382403e-006))*x+(1.3480172498248065e-005))*x+(-0.00015841801101879049))*x+(0.001820745509531337))*x+(-0.021812313648480491))*x+(0.30987157643059748));
		wts[1] = (((((((((((((1.5764574830730755e-011))*x+(6.8818432434151561e-011))*x+(-8.1710519831782824e-010))*x+(9.3401316310822348e-009))*x+(-9.9275808906895677e-008))*x+(9.8078518936025217e-007))*x+(-8.9074414318564728e-006))*x+(7.315171552961057e-005))*x+(-0.00054088397441885239))*x+(0.0034968680786021432))*x+(-0.018371946408706884))*x+(0.097173031225498113));
		wts[2] = (((((((((((((-1.3794002976889411e-011))*x+(1.6412589805743966e-010))*x+(-1.8646630906005153e-009))*x+(1.9335791042370449e-008))*x+(-1.8085649126457307e-007))*x+(1.5102354834854264e-006))*x+(-1.1089668461491026e-005))*x+(7.0131101838122309e-005))*x+(-0.00037140759656350414))*x+(0.0015751178086862339))*x+(-0.0048751271697316826))*x+(0.0095988739244203692));
		break;
	case 5:
		rts[0] = (((((((((((((1.7583564234276612e-011))*x+(-4.6990559591601287e-012))*x+(-1.0156024169797698e-011))*x+(1.8332002582610585e-011))*x+(-2.8653583209840383e-010))*x+(3.6740098371031609e-009))*x+(-7.3439573237502983e-008))*x+(1.3117436776788338e-006))*x+(-1.8876407461907812e-005))*x+(0.00026486608503599229))*x+(-0.0032682894726401156))*x+(0.029520510738012162));
		rts[1] = (((((((((((((4.9233979855974508e-010))*x+(-1.5764574830730755e-011))*x+(-3.1544307906491059e-010))*x+(-6.0632980118195324e-013))*x+(3.0208866519387807e-009))*x+(-5.0539043172648228e-008))*x+(-7.5897580960789427e-008))*x+(1.2660307136869163e-005))*x+(-0.00026000171627042301))*x+(0.003966838578844778))*x+(-0.045522502135145144))*x+(0.35302983446770742));
		rts[2] = (((((((((((((2.0566706856091814e-009))*x+(2.3283064365386963e-010))*x+(-1.0404619388282299e-009))*x+(-5.9359687535713111e-009))*x+(-2.4189830583054569e-008))*x+(7.617719196180891e-007))*x+(3.8100114068129187e-006))*x+(-0.00010316636156441442))*x+(-0.001265674023773163))*x+(0.044732567955219515))*x+(-0.48321073367182982))*x+(2.5349293662455348));
		wts[0] = (((((((((((((5.7480065152049065e-010))*x+(-6.063298011819521e-012))*x+(-3.86383665803199e-010))*x+(2.6072181450823945e-010))*x+(-3.8369876165234018e-009))*x+(4.9669386233593585e-008))*x+(-6.7224737361944631e-007))*x+(9.216348713536604e-006))*x+(-0.00011368363756684521))*x+(0.0014168388570418205))*x+(-0.018597030739759872))*x+(0.28973408074138407));
		wts[1] = (((((((((((((1.0913936421275139e-010))*x+(2.4859521848460037e-011))*x+(-4.3595112704982358e-010))*x+(4.3049794840044342e-009))*x+(-4.7337276024942789e-008))*x+(4.9086335470368181e-007))*x+(-4.6723637900925033e-006))*x+(4.0415426171650871e-005))*x+(-0.00032074846721545181))*x+(0.0022369140509884977))*x+(-0.012747534706852758))*x+(0.081822203295527987));
		wts[2] = (((((((((((((2.8042753304665285e-012))*x+(6.7075234255753458e-011))*x+(-7.8235018463601581e-010))*x+(8.1515452166058822e-009))*x+(-7.7360038375218196e-008))*x+(6.5800712227096858e-007))*x+(-4.9426794880846892e-006))*x+(3.2155180053154243e-005))*x+(-0.00017696140810830155))*x+(0.00079012142327729762))*x+(-0.0026061034624065096))*x+(0.0059878454007170293));
		break;
	case 6:
		rts[0] = (((((((((((((4.2594668533032135e-011))*x+(-1.0610771520684161e-012))*x+(-2.9549103904476695e-011))*x+(1.6285639503621496e-011))*x+(-1.5496463371770611e-010))*x+(2.0939854294965699e-009))*x+(-5.6576548816226563e-008))*x+(9.9065877538310555e-007))*x+(-1.4299561248249288e-005))*x+(0.00021542242598873948))*x+(-0.0027902865951677227))*x+(0.026499452648778815));
		rts[1] = (((((((((((((4.3898277605573333e-010))*x+(1.2126596023639042e-012))*x+(-2.7148416847921908e-010))*x+(-1.39455854271849e-011))*x+(2.9006817688544593e-009))*x+(-3.024913534469912e-008))*x+(-3.1785093135283654e-007))*x+(1.1625243188836029e-005))*x+(-0.00021102749824641887))*x+(0.0032613399641314156))*x+(-0.038318851006859493))*x+(0.31122670601400071));
		rts[2] = (((((((((((((2.5417345265547433e-009))*x+(-8.7311491370201111e-011))*x+(-1.0877556633204222e-009))*x+(-2.4313825027396279e-009))*x+(-5.8940713643096381e-008))*x+(4.5303064174125513e-007))*x+(7.5774144695136174e-006))*x+(-7.3918034459552473e-005))*x+(-0.0016261630180839741))*x+(0.040365407459743263))*x+(-0.39793187996977897))*x+(2.0950869019143141));
		wts[0] = (((((((((((((3.92901711165905e-010))*x+(-1.2126596023639042e-011))*x+(-2.5314269199346501e-010))*x+(1.673470251262188e-010))*x+(-2.2405401978176087e-009))*x+(2.8356633189711524e-008))*x+(-4.4382750867081689e-007))*x+(6.4792531973741534e-006))*x+(-8.2671244123681362e-005))*x+(0.0011250330364287835))*x+(-0.016070627242681445))*x+(0.2724487953213594));
		wts[1] = (((((((((((((6.4877288726468877e-011))*x+(1.849305893604954e-011))*x+(-2.0255204920734588e-010))*x+(2.0124086101228991e-009))*x+(-2.3245509813326255e-008))*x+(2.5431816771022869e-007))*x+(-2.5203589578322765e-006))*x+(2.3019729562682535e-005))*x+(-0.00019743709815803198))*x+(0.0014769146276594526))*x+(-0.0090950070041871198))*x+(0.071027024711010647));
		wts[2] = (((((((((((((2.3495279795800643e-012))*x+(2.7455371309770271e-011))*x+(-3.3007552246999694e-010))*x+(3.474530293109031e-009))*x+(-3.3526807404390034e-008))*x+(2.9145138443394575e-007))*x+(-2.2458639096408399e-006))*x+(1.5089492211545206e-005))*x+(-8.6916500566130761e-005))*x+(0.00041119003005715606))*x+(-0.001449372166673149))*x+(0.004022702536674856));
		break;
	case 7:
		rts[0] = (((((((((((((1.606773973132173e-011))*x+(8.4886172165473291e-012))*x+(-1.009918075093689e-011))*x+(7.8633396090784426e-012))*x+(-4.0553042405614782e-011))*x+(1.3914759714831841e-009))*x+(-4.6545059140257194e-008))*x+(7.3460980158183519e-007))*x+(-1.086560090106381e-005))*x+(0.00017793038155025181))*x+(-0.0023986491161764136))*x+(0.023911224948882356));
		rts[1] = (((((((((((((4.9719043696920074e-010))*x+(1.4551915228366852e-011))*x+(-3.2029371747436619e-010))*x+(-3.7137700322394565e-011))*x+(2.8065301194146741e-009))*x+(-1.0662404292816063e-008))*x+(-4.4025875863458924e-007))*x+(9.6810089438292835e-006))*x+(-0.00016821109157960645))*x+(0.0026944361126884551))*x+(-0.032384503518904185))*x+(0.27596944745188701));
		rts[2] = (((((((((((((2.7551626165707903e-009))*x+(-2.9103830456733704e-010))*x+(-1.3290749241908391e-009))*x+(1.8044374883174896e-009))*x+(-6.1681475926889093e-008))*x+(8.7430483593683058e-009))*x+(8.9722108782552823e-006))*x+(-3.142326252714156e-005))*x+(-0.0018391733554346719))*x+(0.035124683166212492))*x+(-0.32233505127087381))*x+(1.7358283175543714));
		wts[0] = (((((((((((((3.2499277343352634e-010))*x+(3.0316490059097604e-011))*x+(-2.0433314299831787e-010))*x+(9.4132701633498073e-011))*x+(-1.1637553143373223e-009))*x+(1.6332852699936968e-008))*x+(-3.1356668965069423e-007))*x+(4.6157505971441042e-006))*x+(-6.0697071212478797e-005))*x+(0.00091183808194796501))*x+(-0.014044721681374115))*x+(0.25742659151985547));
		wts[1] = (((((((((((((8.7311491370201111e-011))*x+(-1.2429760924230019e-011))*x+(-1.3884952447066704e-010))*x+(9.6679286798462272e-010))*x+(-1.1881449305898665e-008))*x+(1.3619577169758182e-007))*x+(-1.3881804458530191e-006))*x+(1.3541247601297119e-005))*x+(-0.00012618904226298819))*x+(0.0010008955351110637))*x+(-0.0066526340382840419))*x+(0.06323222753338055));
		wts[2] = (((((((((((((-8.7159908919905616e-013))*x+(1.133078815958773e-011))*x+(-1.3930190334576764e-010))*x+(1.4974131564334432e-009))*x+(-1.4755666910559738e-008))*x+(1.3157385062948868e-007))*x+(-1.041713825468878e-006))*x+(7.2657089792612269e-006))*x+(-4.4191483323380874e-005))*x+(0.00022227319267173069))*x+(-0.00083707383421225811))*x+(0.0029107086249425813));
		break;
	case 8:
		rts[0] = (((((((((((((7.4275400644789134e-012))*x+(1.8947806286936002e-012))*x+(-5.1822250194769968e-012))*x+(3.3821834222180769e-012))*x+(3.3644198538240744e-011))*x+(1.3964565800013891e-009))*x+(-3.8451689129045022e-008))*x+(5.2208456606065801e-007))*x+(-8.3656117827850731e-006))*x+(0.00014929609626957926))*x+(-0.0020726712967457212))*x+(0.021680330038708551));
		rts[1] = (((((((((((((1.4309383307894069e-010))*x+(-3.637978807091713e-012))*x+(-9.1101052627588303e-011))*x+(-1.0353081355181833e-010))*x+(2.2682039949965351e-009))*x+(7.1827296703001293e-009))*x+(-4.4904068789245838e-007))*x+(7.4129656285985366e-006))*x+(-0.00013400904572302694))*x+(0.002243382928910409))*x+(-0.027463786886486329))*x+(0.24612040175067462));
		rts[2] = (((((((((((((1.9693591942389803e-009))*x+(-1.8432425955931345e-010))*x+(-1.1477823136374352e-009))*x+(4.0084463156138854e-009))*x+(-3.7643834123931206e-008))*x+(-3.5174506744321355e-007))*x+(7.8575889143432196e-006))*x+(1.1557923803214484e-005))*x+(-0.0018770175571707348))*x+(0.029507233843995593))*x+(-0.2576844020450858))*x+(1.4467562738153681));
		wts[0] = (((((((((((((2.5708383570114768e-010))*x+(-4.850638409455617e-012))*x+(-1.6461854102089999e-010))*x+(7.2911158592129738e-011))*x+(-4.2693197125724208e-010))*x+(1.0692540778715436e-008))*x+(-2.3511364706981416e-007))*x+(3.2580559565786866e-006))*x+(-4.5079340718438367e-005))*x+(0.0007545283694168069))*x+(-0.012386151144245067))*x+(0.24423732826872488));
		wts[1] = (((((((((((((1.279355880493919e-010))*x+(-6.5180453627059852e-012))*x+(-1.1751429459157709e-010))*x+(4.7742787501192641e-010))*x+(-6.4219420892186463e-009))*x+(7.4257627010373043e-008))*x+(-7.757267685981617e-007))*x+(8.285218270491038e-006))*x+(-8.3550587891436282e-005))*x+(0.00069151146847563677))*x+(-0.0049814450826996147))*x+(0.057466578241809396));
		wts[2] = (((((((((((((6.2527760746888816e-012))*x+(4.7558993780209367e-012))*x+(-6.4289906731573865e-011))*x+(6.5315456746854273e-010))*x+(-6.625510066508392e-009))*x+(6.0628362626620914e-008))*x+(-4.9323048038433604e-007))*x+(3.6037756090863864e-006))*x+(-2.335732551653838e-005))*x+(0.00012457699290512796))*x+(-0.00050055064505038008))*x+(0.002258058682366104));
		break;
	case 9:
		rts[0] = (((((((((((((2.2131037743141253e-011))*x+(-4.2443086082736646e-012))*x+(-1.313082975684665e-011))*x+(-2.0747847884194925e-012))*x+(3.3836045076895964e-011))*x+(1.666986548798377e-009))*x+(-2.9255513049146011e-008))*x+(3.5211537160092138e-007))*x+(-6.6325409320139306e-006))*x+(0.00012696897879608629))*x+(-0.0017972712241171268))*x+(0.019749074292086791));
		rts[1] = (((((((((((((3.6743585951626301e-010))*x+(-2.0008883439004421e-011))*x+(-2.3927289779142785e-010))*x+(-1.6818072860284397e-010))*x+(1.1229038439826884e-009))*x+(1.9182865666304373e-008))*x+(-3.6576307464268132e-007))*x+(5.3457765210040975e-006))*x+(-0.00010863176194984373))*x+(0.0018814949612857845))*x+(-0.023351583558069041))*x+(0.2207729619949084));
		rts[2] = (((((((((((((1.823840041955312e-009))*x+(-7.7610214551289872e-011))*x+(-1.2975457745293775e-009))*x+(3.637978807091713e-009))*x+(-6.0740603657905004e-009))*x+(-5.0502353587944526e-007))*x+(5.1757687818583991e-006))*x+(4.4523843437597556e-005))*x+(-0.0017603469843769186))*x+(0.024018144698784084))*x+(-0.20421781109666023))*x+(1.2167211179374005));
		wts[0] = (((((((((((((2.7891170854369796e-010))*x+(2.1827872842550278e-011))*x+(-1.83566347307836e-010))*x+(6.4422541375582406e-012))*x+(-5.5460229001861691e-011))*x+(8.9827570567043348e-009))*x+(-1.773784893780809e-007))*x+(2.2310066250715481e-006))*x+(-3.4197014518603616e-005))*x+(0.0006366400626662827))*x+(-0.011000414313560643))*x+(0.23256365939507045));
		wts[1] = (((((((((((((6.0632980118195207e-011))*x+(1.2429760924230019e-011))*x+(-5.6767627635660262e-011))*x+(2.5285847489916097e-010))*x+(-3.6220579128591148e-009))*x+(3.9979796658447718e-008))*x+(-4.4276215079482501e-007))*x+(5.3242196879447574e-006))*x+(-5.6883414213282357e-005))*x+(0.00048380446156628493))*x+(-0.0038194077077630269))*x+(0.053100671790407707));
		wts[2] = (((((((((((((-1.8947806286936003e-013))*x+(2.5769016550232964e-012))*x+(-2.5411376706567047e-011))*x+(2.9068540167524287e-010))*x+(-3.0533978308729575e-009))*x+(2.8417619516811026e-008))*x+(-2.3845860320596357e-007))*x+(1.8542500321155895e-006))*x+(-1.2861791732121999e-005))*x+(7.1981974190672753e-005))*x+(-0.00030919756842746052))*x+(0.0018618928496365946));
		break;
	case 10:
		rts[0] = (((((((((((((4.2443086082736646e-012))*x+(1.5916157281026244e-012))*x+(-1.3642420526593922e-012))*x+(-8.7538865045644343e-012))*x+(-2.5835333872237243e-011))*x+(1.7046835054657095e-009))*x+(-1.8933490775197015e-008))*x+(2.3154192145084332e-007))*x+(-5.4824985382950775e-006))*x+(0.00010891701392090035))*x+(-0.00156195852241881))*x+(0.01807246405951653));
		rts[1] = (((((((((((((2.1342809001604715e-010))*x+(-7.2759576141834259e-012))*x+(-1.2065963043520847e-010))*x+(-1.5165824152063578e-010))*x+(-3.3003288990585133e-010))*x+(2.1560727721710766e-008))*x+(-2.3846937343326619e-007))*x+(3.8293343690061947e-006))*x+(-9.0495383805381608e-005))*x+(0.0015843218546329012))*x+(-0.019894813474286177))*x+(0.19919924172608844));
		rts[2] = (((((((((((((1.4260876923799515e-009))*x+(4.8506384094556168e-011))*x+(-1.1356557176137965e-009))*x+(1.8183830737446745e-009))*x+(1.6177940172686551e-008))*x+(-4.6302909595397063e-007))*x+(2.1932578159559548e-006))*x+(6.28374328736451e-005))*x+(-0.0015406274196660221))*x+(0.019048391672359014))*x+(-0.16126163533076771))*x+(1.0348102962891179));
		wts[0] = (((((((((((((3.7834979593753815e-010))*x+(-2.6072181450823941e-011))*x+(-2.4435090987632674e-010))*x+(-1.4400332778071385e-012))*x+(-4.3428372009657323e-011))*x+(8.4734850247514243e-009))*x+(-1.2499372559204858e-007))*x+(1.4762694346970304e-006))*x+(-2.6869779713223352e-005))*x+(0.00054579438184877249))*x+(-0.0098216347543099887))*x+(0.22216775066074995));
		wts[1] = (((((((((((((1.3824319466948509e-010))*x+(5.7601331112285452e-012))*x+(-9.936229616869241e-011))*x+(1.5849839959021966e-010))*x+(-1.9612921657123175e-009))*x+(2.0776720788262537e-008))*x+(-2.6624678432322446e-007))*x+(3.5994878793133012e-006))*x+(-3.9328281510061146e-005))*x+(0.0003412021122086763))*x+(-0.0030031495538434269))*x+(0.049713103180782606));
		wts[2] = (((((((((((((1.5158245029548803e-013))*x+(2.5105843330190203e-013))*x+(-1.1226575225009583e-011))*x+(1.3557984364827766e-010))*x+(-1.4343063033569099e-009))*x+(1.3429399647879592e-008))*x+(-1.1852458076111459e-007))*x+(9.9890472533605457e-007))*x+(-7.3535116913136141e-006))*x+(4.2506972385573777e-005))*x+(-0.00019744303846293024))*x+(0.0016134568867392459));
		break;
	case 11:
		rts[0] = (((((((((((((7.2759576141834259e-012))*x+(1.3642420526593924e-012))*x+(-4.4148388648560894e-012))*x+(-4.8316906031686813e-012))*x+(-7.7495343475675327e-011))*x+(1.3191883141416838e-009))*x+(-9.6744091996707003e-009))*x+(1.6099621613641091e-007))*x+(-4.7129174412704105e-006))*x+(9.3694240020386149e-005))*x+(-0.0013597305067912162))*x+(0.016614154331694189));
		rts[1] = (((((((((((((1.673470251262188e-010))*x+(6.6696278130014735e-012))*x+(-8.806940362167856e-011))*x+(-5.0628538398693003e-011))*x+(-1.1643237485259306e-009))*x+(1.564314070871357e-008))*x+(-1.2394470338961128e-007))*x+(2.9383703899673228e-006))*x+(-7.7151821657017727e-005))*x+(0.001333738975025857))*x+(-0.016983405199146467))*x+(0.18080186664855719));
		rts[2] = (((((((((((((1.4357889691988626e-009))*x+(-1.9402553637822468e-011))*x+(-1.0525885348518689e-009))*x+(1.6765019002680978e-010))*x+(2.3878631812597934e-008))*x+(-3.1625207460213761e-007))*x+(-1.7135295138359652e-007))*x+(6.7521287820208428e-005))*x+(-0.001275960083751452))*x+(0.014818901108012648))*x+(-0.12752707158673324))*x+(0.89112101050030634));
		wts[0] = (((((((((((((2.5950915490587551e-010))*x+(-3.637978807091713e-012))*x+(-1.5779733075760305e-010))*x+(-2.0160465889299907e-011))*x+(-2.3214852262753991e-010))*x+(7.2247559046445523e-009))*x+(-7.7287134914172384e-008))*x+(9.7370717178080213e-007))*x+(-2.2049537264442105e-005))*x+(0.00047291734449833589))*x+(-0.0088053251694170769))*x+(0.21286640014940153));
		wts[1] = (((((((((((((4.7293724492192268e-011))*x+(4.5474735088646412e-013))*x+(-3.4409216217075787e-011))*x+(9.7770680440589786e-011))*x+(-9.4516868405965693e-010))*x+(1.0808087462047903e-008))*x+(-1.7509893623923742e-007))*x+(2.5208999814285704e-006))*x+(-2.7238215088080477e-005))*x+(0.00024242601394399108))*x+(-0.0024255514414385291))*x+(0.047015179648447591));
		wts[2] = (((((((((((((1.8189894035458565e-012))*x+(8.5265128291212022e-013))*x+(-6.6056789667830645e-012))*x+(6.467892887940252e-011))*x+(-6.6842028208687521e-010))*x+(6.3927535857525673e-009))*x+(-6.1713104941111638e-008))*x+(5.6574145645508589e-007))*x+(-4.3180236215268715e-006))*x+(2.5429360266942858e-005))*x+(-0.00013101510711606616))*x+(0.0014520598091044717));
		break;
	case 12:
		rts[0] = (((((((((((((1.2278178473934531e-011))*x+(-3.4106051316484809e-012))*x+(-7.0391100355967264e-012))*x+(3.836930773104541e-012))*x+(-8.5151441453490406e-011))*x+(7.1097942348311938e-010))*x+(-3.5559034605725515e-009))*x+(1.2945474070491514e-007))*x+(-4.142222025098341e-006))*x+(8.0442764355684079e-005))*x+(-0.0011858778290988023))*x+(0.015343557706317564));
		rts[1] = (((((((((((((2.352559628585974e-010))*x+(-1.9402553637822468e-011))*x+(-1.3869794202037153e-010))*x+(5.8738199489501611e-011))*x+(-1.1032928644757096e-009))*x+(7.0834052697440102e-009))*x+(-5.5970638494310762e-008))*x+(2.5102041417331593e-006))*x+(-6.6367891162803311e-005))*x+(0.0011188832308603827))*x+(-0.014536163639872497))*x+(0.16507787745440436));
		rts[2] = (((((((((((((8.3916044483582175e-010))*x+(9.4587448984384537e-011))*x+(-5.6843418860808005e-010))*x+(-8.2915600311631954e-010))*x+(2.0752243775253493e-008))*x+(-1.5675924676846381e-007))*x+(-1.5793899936037783e-006))*x+(6.2743629505016926e-005))*x+(-0.0010130872359774092))*x+(0.011390188143076794))*x+(-0.1014496528994442))*x+(0.77720393733474191));
		wts[0] = (((((((((((((2.5102053768932819e-010))*x+(-1.3339255626002947e-011))*x+(-1.513550766200448e-010))*x+(4.850638409455617e-012))*x+(-3.2963498597382568e-010))*x+(4.9423505288359593e-009))*x+(-4.044207072932219e-008))*x+(6.8514241865121528e-007))*x+(-1.879336082634871e-005))*x+(0.0004119404093400243))*x+(-0.0079220893465974992))*x+(0.20451284615001242));
		wts[1] = (((((((((((((7.5488060247153044e-011))*x+(1.3794002976889411e-011))*x+(-5.5157064101270713e-011))*x+(3.78387691550112e-011))*x+(-3.6959590943297371e-010))*x+(6.3867637104901096e-009))*x+(-1.2550591210747086e-007))*x+(1.7803296476307888e-006))*x+(-1.8717751409385214e-005))*x+(0.00017423045704487852))*x+(-0.0020131470309532533))*x+(0.044807171756326217));
		wts[2] = (((((((((((((1.5631940186722204e-012))*x+(1.1842378929335001e-013))*x+(-3.7321257195799262e-012))*x+(3.0451493178892023e-011))*x+(-3.0238345161137659e-010))*x+(3.1527074839665654e-009))*x+(-3.4347617530276299e-008))*x+(3.3361009993635815e-007))*x+(-2.5645075615051611e-006))*x+(1.533609761057368e-005))*x+(-9.1121906615251525e-005))*x+(0.0013426658509744208));
		break;
	case 13:
		rts[0] = (((((((((((((4.7748471843078732e-012))*x+(-2.3874235921539366e-012))*x+(-1.8047785488306545e-012))*x+(5.878556900521895e-012))*x+(-5.7706728284756537e-011))*x+(1.9250601113185437e-010))*x+(-9.4683244578064318e-010))*x+(1.1950116205842556e-007))*x+(-3.6486237558833639e-006))*x+(6.8766188076624491e-005))*x+(-0.0010369152459543214))*x+(0.014234106945493435));
		rts[1] = (((((((((((((1.3339255626002947e-010))*x+(-2.4253192047278085e-012))*x+(-7.9126039054244757e-011))*x+(7.0258465711958706e-011))*x+(-5.9688431974791446e-010))*x+(8.6952430441063667e-010))*x+(-3.3963962901376967e-008))*x+(2.3009696707987359e-006))*x+(-5.6781595397607333e-005))*x+(0.00093436511205805906))*x+(-0.012487704866524818))*x+(0.15159668939528628));
		rts[2] = (((((((((((((3.1529149661461509e-010))*x+(-1.4551915228366852e-011))*x+(-1.7431981783981124e-010))*x+(-9.3829536732907083e-010))*x+(1.3399130693869665e-008))*x+(-3.6932855588626502e-008))*x+(-2.1347309212179271e-006))*x+(5.3158353383745784e-005))*x+(-0.00078036631649373389))*x+(0.0087096531253253815))*x+(-0.081466263415411772))*x+(0.68619241264533659));
		wts[0] = (((((((((((((2.801243681460619e-010))*x+(-3.637978807091713e-012))*x+(-1.7227345476082215e-010))*x+(1.4855080128957827e-011))*x+(-2.7222313292440958e-010))*x+(2.5197787560197562e-009))*x+(-1.8241025578902281e-008))*x+(5.4454569919926133e-007))*x+(-1.6370923668074244e-005))*x+(0.00035933335645697378))*x+(-0.0071520231082154682))*x+(0.19698455313644186));
		wts[1] = (((((((((((((4.4262075486282505e-011))*x+(1.9705718538413444e-012))*x+(-2.9748055870489523e-011))*x+(1.3339255626002947e-011))*x+(-1.4853659043486306e-010))*x+(4.6626163670756179e-009))*x+(-9.3149817785113471e-008))*x+(1.2379232285919528e-006))*x+(-1.2734909721099735e-005))*x+(0.00012759303275025843))*x+(-0.0017143096067499209))*x+(0.042951198301208353));
		wts[2] = (((((((((((((4.1685173831259208e-012))*x+(3.5053441630831606e-013))*x+(-4.0098295054728315e-012))*x+(1.2875034371973015e-011))*x+(-1.3650428935344886e-010))*x+(1.6941524849656275e-009))*x+(-2.0380586912560616e-008))*x+(2.0039612275609314e-007))*x+(-1.5195832445043709e-006))*x+(9.3424575450516152e-006))*x+(-6.696351294045132e-005))*x+(0.0012646176748966034));
		break;
	case 14:
		rts[0] = (((((((((((((-2.3495279795800643e-012))*x+(1.5916157281026244e-012))*x+(3.2069162140639187e-012))*x+(2.8516448461838682e-012))*x+(-2.3406461953830633e-011))*x+(-8.2400752887679106e-011))*x+(-7.4293203070989011e-010))*x+(1.159624180753956e-007))*x+(-3.1779937367075461e-006))*x+(5.8529663466277741e-005))*x+(-0.00090985468153087295))*x+(0.013262427957756772));
		rts[1] = (((((((((((((8.0035533756017685e-011))*x+(-8.4886172165473291e-012))*x+(-4.6687394691010318e-011))*x+(5.0325373498102025e-011))*x+(-1.1909643641653625e-010))*x+(-1.5977879760005938e-009))*x+(-3.7862155484920855e-008))*x+(2.1275137817392911e-006))*x+(-4.7917556810402516e-005))*x+(0.00077748862367290239))*x+(-0.010780283881861891))*x+(0.13998883537849019));
		rts[2] = (((((((((((((5.3842086344957352e-010))*x+(-6.0632980118195207e-011))*x+(-3.0407439529274904e-010))*x+(-7.0152357996751868e-010))*x+(6.5666654336382635e-009))*x+(3.1528117006018868e-008))*x+(-2.1267780248024337e-006))*x+(4.2333970906582863e-005))*x+(-0.0005894029948368591))*x+(0.0066658576212647765))*x+(-0.066186231850976787))*x+(0.61270643516087264));
		wts[0] = (((((((((((((1.5279510989785194e-010))*x+(9.0949470177292824e-012))*x+(-9.2010547329361244e-011))*x+(1.0156024169797697e-011))*x+(-1.6154899640241638e-010))*x+(7.9467336414988188e-010))*x+(-8.7588431322653069e-009))*x+(4.8138117580975859e-007))*x+(-1.4334716692432357e-005))*x+(0.00031333719471370492))*x+(-0.0064803691024648852))*x+(0.1901760209937961));
		wts[1] = (((((((((((((7.1546916539470346e-011))*x+(-8.033869865660865e-012))*x+(-4.9870626147215561e-011))*x+(5.0211686660380402e-012))*x+(-9.4715346676821355e-011))*x+(3.808628079582376e-009))*x+(-6.7891114359971042e-008))*x+(8.3742846856971188e-007))*x+(-8.6262549460758287e-006))*x+(9.595136236698748e-005))*x+(-0.0014928153362882858))*x+(0.041352896111481449));
		wts[2] = (((((((((((((4.4148388648560886e-012))*x+(4.452734477429961e-013))*x+(-3.364419853824074e-012))*x+(4.9933390755541041e-012))*x+(-6.8138975943080979e-011))*x+(1.0095854152680772e-009))*x+(-1.2505586774458344e-008))*x+(1.1987441175809188e-007))*x+(-8.9208896013008338e-007))*x+(5.8051338029554804e-006))*x+(-5.2128367395867716e-005))*x+(0.001205658620670463));
		break;
	case 15:
		rts[0] = (((((((((((((1.1065518871570626e-011))*x+(2.1221543041368323e-012))*x+(-7.2096402921791488e-012))*x+(7.4843834833397247e-013))*x+(2.8090122820382622e-012))*x+(-1.4533796388604969e-010))*x+(-1.5092318876123536e-009))*x+(1.1048422687842673e-007))*x+(-2.7237966815663967e-006))*x+(4.9682425964539076e-005))*x+(-0.00080186982214999454))*x+(0.012408040064322931));
		rts[1] = (((((((((((((5.6995001311103501e-011))*x+(5.4569682106375694e-012))*x+(-3.1908105787200228e-011))*x+(1.2505552149377763e-011))*x+(1.2132280365525125e-010))*x+(-1.4812044923928624e-009))*x+(-4.7946605204648072e-008))*x+(1.9126302337468815e-006))*x+(-3.9820179086602625e-005))*x+(0.00064609698209586175))*x+(-0.0093607486859884088))*x+(0.12994021053491334));
		rts[2] = (((((((((((((6.6938810050487518e-010))*x+(-5.8207660913467407e-011))*x+(-3.9411437076826894e-010))*x+(-3.9835867937654257e-010))*x+(1.9496913713131408e-009))*x+(5.9323099321773043e-008))*x+(-1.837967696853108e-006))*x+(3.2353366471227218e-005))*x+(-0.00044051508330615141))*x+(0.0051309748026163353))*x+(-0.054463794474874039))*x+(0.55263690246259112));
		wts[0] = (((((((((((((1.6128372711439926e-010))*x+(2.4253192047278084e-011))*x+(-1.0724458358405778e-010))*x+(-3.8653524825349434e-012))*x+(-3.9676706364843988e-011))*x+(-3.4503955248510465e-011))*x+(-6.900430153204221e-009))*x+(4.4430690652556371e-007))*x+(-1.2486303072323233e-005))*x+(0.00027314232721975523))*x+(-0.0058948134967835046))*x+(0.18399512762255213));
		wts[1] = (((((((((((((1.9099388737231493e-011))*x+(-4.2443086082736646e-012))*x+(-9.5307465623288116e-012))*x+(1.1747639897900318e-012))*x+(-1.1064808328834866e-010))*x+(3.0481951777498275e-009))*x+(-4.7296349429496822e-008))*x+(5.5136285848078614e-007))*x+(-5.8830017801112886e-006))*x+(7.4473163064433135e-005))*x+(-0.0013237590042328761))*x+(0.039948179123664947));
		wts[2] = (((((((((((((2.0368891758456203e-012))*x+(1.6579330501069003e-013))*x+(-1.5412856176529506e-012))*x+(2.1813661987835076e-012))*x+(-4.0587755378851398e-011))*x+(6.3901015960136454e-010))*x+(-7.6560720009092674e-009))*x+(7.0390267746522905e-008))*x+(-5.1961023400818565e-007))*x+(3.7368857651220448e-006))*x+(-4.2771783486751348e-005))*x+(0.0011585516124921372));
		break;
	case 16:
		rts[0] = (((((((((((((1.4021376652332643e-011))*x+(-3.4106051316484809e-013))*x+(-8.7870451655665712e-012))*x+(4.2158868988432608e-013))*x+(1.1603162874962436e-011))*x+(-9.9784921066733049e-011))*x+(-2.2744570856344142e-009))*x+(1.0090780812784435e-007))*x+(-2.2997276100030863e-006))*x+(4.2156739841943285e-005))*x+(-0.00071024281978691623))*x+(0.011653237704020037));
		rts[1] = (((((((((((((1.988761747876803e-010))*x+(-7.2759576141834259e-012))*x+(-1.303609072541197e-010))*x+(1.8947806286936006e-012))*x+(1.8932648041906453e-010))*x+(-4.2937150131668506e-010))*x+(-5.3821610871788536e-008))*x+(1.6555415314201127e-006))*x+(-3.267400251331469e-005))*x+(0.00053761333707856096))*x+(-0.0081806124402804235))*x+(0.12118760198397399));
		rts[2] = (((((((((((((7.2759576141834259e-010))*x+(-1.9402553637822468e-011))*x+(-4.4140809526046121e-010))*x+(-1.8462742445990441e-010))*x+(-4.8184271387678257e-010))*x+(6.2670001928684841e-008))*x+(-1.4634758969123138e-006))*x+(2.4091997855653819e-005))*x+(-0.00032825133229049303))*x+(0.0039860880601888153))*x+(-0.045402800669074539))*x+(0.50289414389704901));
		wts[0] = (((((((((((((1.7098500393331051e-010))*x+(2.1827872842550278e-011))*x+(-1.0754774848464876e-010))*x+(-1.0080232944649955e-011))*x+(2.2832106575757887e-011))*x+(-2.304053244491418e-010))*x+(-7.9410211739627795e-009))*x+(4.0768920091712363e-007))*x+(-1.0780499278698988e-005))*x+(0.00023827864744093338))*x+(-0.0053842456083042214))*x+(0.17836140746716883));
		wts[1] = (((((((((((((2.2434202643732228e-011))*x+(5.0022208597511053e-012))*x+(-1.0497084682962546e-011))*x+(-1.7621459846850485e-012))*x+(-1.0858514087885851e-010))*x+(2.2643818671970921e-009))*x+(-3.136821809709052e-008))*x+(3.5666770699845546e-007))*x+(-4.093484352679643e-006))*x+(5.970273516493068e-005))*x+(-0.0011904752104687436))*x+(0.038693517283219632));
		wts[2] = (((((((((((((2.2737367544323206e-013))*x+(1.8000415972589204e-013))*x+(9.5923269327613525e-014))*x+(1.1948960339699017e-012))*x+(-2.7244354920223181e-011))*x+(4.0525235019591338e-010))*x+(-4.5712391696003012e-009))*x+(4.0404287924659478e-008))*x+(-3.0314652901067735e-007))*x+(2.5326203256743314e-006))*x+(-3.6609997387262768e-005))*x+(0.0011190604389645184));
		break;
	case 17:
		rts[0] = (((((((((((((2.0084674664152164e-011))*x+(0))*x+(-1.3220831836709596e-011))*x+(-5.9211894646675012e-013))*x+(1.2308968659150802e-011))*x+(-2.9962402929110489e-011))*x+(-2.6623266739337717e-009))*x+(8.8391063209532675e-008))*x+(-1.9204842472339092e-006))*x+(3.5838974082667376e-005))*x+(-0.00063243679206938166))*x+(0.010982950440144712));
		rts[1] = (((((((((((((1.0732037480920553e-010))*x+(-1.152026622245709e-011))*x+(-6.6052052716258913e-011))*x+(-1.5158245029548799e-012))*x+(1.2490393904348213e-010))*x+(5.433165028989605e-010))*x+(-5.3298098527202832e-008))*x+(1.3853070125099025e-006))*x+(-2.6593233747993862e-005))*x+(0.0004489832071011371))*x+(-0.0071970561852096595))*x+(0.11351353032839691));
		rts[2] = (((((((((((((3.3469405025243759e-010))*x+(-6.063298011819521e-012))*x+(-1.8402109465872249e-010))*x+(-5.2144362901647888e-011))*x+(-1.4846743094191575e-009))*x+(5.4646008607051038e-008))*x+(-1.1082762760850071e-006))*x+(1.7683036724373359e-005))*x+(-0.00024529432526221306))*x+(0.0031321744283666813))*x+(-0.038325957332100369))*x+(0.4611718703988153));
		wts[0] = (((((((((((((1.8068628075222173e-010))*x+(-6.063298011819521e-012))*x+(-1.0815407828583071e-010))*x+(9.8528592692067199e-013))*x+(4.2840990014762305e-011))*x+(-1.3954111940014022e-010))*x+(-9.1379162014959547e-009))*x+(3.6475703820334116e-007))*x+(-9.2335859039708694e-006))*x+(0.00020830050142576589))*x+(-0.0049384401191825212))*x+(0.17320505952765203));
		wts[1] = (((((((((((((9.6406438387930393e-011))*x+(-1.2126596023639042e-012))*x+(-6.2527760746888816e-011))*x+(3.637978807091713e-012))*x+(-7.6712562228446274e-011))*x+(1.5540232804293432e-009))*x+(-1.9980388010765179e-008))*x+(2.3007656446694114e-007))*x+(-2.938956705213676e-006))*x+(4.9280309018009019e-005))*x+(-0.0010820675348791225))*x+(0.037558978778804646));
		wts[2] = (((((((((((((2.3968974952974045e-012))*x+(9.9475983006414026e-014))*x+(-1.5531279965822855e-012))*x+(8.6508578078792198e-013))*x+(-1.7757499174801222e-011))*x+(2.4875677443840039e-010))*x+(-2.6409150907791279e-009))*x+(2.276425880437527e-008))*x+(-1.8001625216304204e-007))*x+(1.8254381900489919e-006))*x+(-3.2313183773862075e-005))*x+(0.0010847161277856758));
		break;
	case 18:
		rts[0] = (((((((((((((1.4172959102628131e-011))*x+(-4.2064129956997931e-012))*x+(-8.7207278435622957e-012))*x+(2.1363651588520347e-012))*x+(7.6407028852069435e-012))*x+(2.2691626355708646e-011))*x+(-2.670325645789025e-009))*x+(7.4926923017878025e-008))*x+(-1.5938389146946212e-006))*x+(3.0580980285402001e-005))*x+(-0.00056618016113636847))*x+(0.01038451784575972));
		rts[1] = (((((((((((((1.3824319466948509e-010))*x+(9.0949470177292824e-013))*x+(-8.7159908919905618e-011))*x+(-8.6780952794166897e-012))*x+(6.8534215339847521e-011))*x+(1.1024508713338339e-009))*x+(-4.8141486648963408e-008))*x+(1.1303241659691803e-006))*x+(-2.1570639806234304e-005))*x+(0.00037699265719015146))*x+(-0.0063735907478936361))*x+(0.10674019677418067));
		rts[2] = (((((((((((((3.1044085820515949e-010))*x+(4.2443086082736649e-011))*x+(-1.6795335492740074e-010))*x+(-1.9857300988708932e-011))*x+(-1.618332134967204e-009))*x+(4.3249528403066506e-008))*x+(-8.1420057777374189e-007))*x+(1.2905521572884972e-005))*x+(-0.00018460746519988189))*x+(0.0024920935099223174))*x+(-0.032731983792396273))*x+(0.42574942101294694));
		wts[0] = (((((((((((((1.964508555829525e-010))*x+(-1.8189894035458565e-012))*x+(-1.2323653209023178e-010))*x+(-1.4400332778071361e-012))*x+(4.7123194235609844e-011))*x+(1.3052670055913039e-011))*x+(-9.5178804097410339e-009))*x+(3.1774118121793055e-007))*x+(-7.8679587833437488e-006))*x+(0.00018269527779588013))*x+(-0.0045481272164297126))*x+(0.16846604182622074));
		wts[1] = (((((((((((((1.2429760924230019e-011))*x+(1.3794002976889411e-011))*x+(-6.006454592958713e-012))*x+(-5.9117155615240335e-012))*x+(-6.6068632046759987e-011))*x+(1.0023620452178268e-009))*x+(-1.2402040209617363e-008))*x+(1.5050907194632163e-007))*x+(-2.1903842892292045e-006))*x+(4.1665587640462666e-005))*x+(-0.00099149466578930833))*x+(0.036523464159654004));
		wts[2] = (((((((((((((1.9800457569848122e-012))*x+(-3.4579746473658207e-013))*x+(-1.2700951401711789e-012))*x+(9.1719224807699586e-013))*x+(-1.1270169982443198e-011))*x+(1.4616054662871156e-010))*x+(-1.4789801860056369e-009))*x+(1.2720344354233413e-008))*x+(-1.1097597071924153e-007))*x+(1.398942693585847e-006))*x+(-2.9123130465694033e-005))*x+(0.0010540687208832162));
		break;
	case 19:
		rts[0] = (((((((((((((1.6522487082208194e-011))*x+(2.9937533933358886e-012))*x+(-1.0847619099270862e-011))*x+(-2.3400540764365965e-012))*x+(4.9974839081793708e-012))*x+(5.2247243568596481e-011))*x+(-2.4336169005915549e-009))*x+(6.209691055802935e-008))*x+(-1.3201898264060077e-006))*x+(2.6222781250113149e-005))*x+(-0.00050951318411788019))*x+(0.0098473971113005009));
		rts[1] = (((((((((((((1.4127484367539484e-010))*x+(3.637978807091713e-012))*x+(-8.9698914962355035e-011))*x+(-6.8970014884447055e-012))*x+(2.4726887204451483e-011))*x+(1.2789153439977479e-009))*x+(-4.0845434442123477e-008))*x+(9.0743082174308631e-007))*x+(-1.7507341869347583e-005))*x+(0.00031859866426821776))*x+(-0.0056800298519339562))*x+(0.10072311137253318));
		rts[2] = (((((((((((((5.6995001311103499e-010))*x+(-3.759244767328103e-011))*x+(-3.5424818634055555e-010))*x+(5.7449748661989958e-011))*x+(-1.3516607092848669e-009))*x+(3.2360991516119007e-008))*x+(-5.8817318127069029e-007))*x+(9.4268517027984427e-006))*x+(-0.00014031917501899915))*x+(0.0020081767671015767))*x+(-0.028253820025867932))*x+(0.39533705619829468));
		wts[0] = (((((((((((((1.4673181188603241e-010))*x+(1.9402553637822468e-011))*x+(-8.8448359747417258e-011))*x+(-1.3642420526593922e-011))*x+(2.9804899289350331e-011))*x+(1.293424626661969e-010))*x+(-9.0711690011365428e-009))*x+(2.7099201223753272e-007))*x+(-6.6912439117087592e-006))*x+(0.00016090327973992494))*x+(-0.0042051169407447998))*x+(0.16409305018629075));
		wts[1] = (((((((((((((4.0927261579781771e-011))*x+(-1.3794002976889411e-011))*x+(-2.5977442419389263e-011))*x+(1.0857093002414331e-011))*x+(-3.8646419397991849e-011))*x+(6.1258672208926624e-010))*x+(-7.6375247607766515e-009))*x+(1.0137497626535226e-007))*x+(-1.6945314713588215e-006))*x+(3.5887155902259341e-005))*x+(-0.00091418905823497135))*x+(0.035571583740947987));
		wts[2] = (((((((((((((7.9580786405131221e-013))*x+(7.5791225147744016e-014))*x+(-4.3461530670659465e-013))*x+(4.0678571622265736e-013))*x+(-6.9021085143579813e-012))*x+(8.2493382495367002e-011))*x+(-8.0890249591162678e-010))*x+(7.1595107990300253e-009))*x+(-7.2327682687963371e-008))*x+(1.1295163226600056e-006))*x+(-2.6613884681461769e-005))*x+(0.0010262449338538924));
		break;
	case 20:
		rts[0] = (((((((((((((1.3339255626002947e-011))*x+(2.0842586915629604e-012))*x+(-7.5507008053439969e-012))*x+(-1.6721439048221023e-012))*x+(1.6668148343039013e-012))*x+(6.1200378098646966e-011))*x+(-2.0879725726175025e-009))*x+(5.0771423787399066e-008))*x+(-1.0950313479122598e-006))*x+(2.2611279403944931e-005))*x+(-0.00046079164476645247))*x+(0.0093628462361054106));
		rts[1] = (((((((((((((1.152026622245709e-010))*x+(3.637978807091713e-012))*x+(-7.2683784916686506e-011))*x+(-4.5474735088646412e-012))*x+(-2.7569058147491887e-012))*x+(1.2185428962159979e-009))*x+(-3.3274664505237674e-008))*x+(7.2229496280347872e-007))*x+(-1.4260534768809988e-005))*x+(0.00027113195329830919))*x+(-0.0050919213722785206))*x+(0.095345040709241324));
		rts[2] = (((((((((((((5.2629426742593444e-010))*x+(9.701276818911234e-012))*x+(-3.3636145720568794e-010))*x+(3.1680732111757002e-011))*x+(-1.0409545817916903e-009))*x+(2.3452040901853856e-008))*x+(-4.2182913576975045e-007))*x+(6.9241704766890661e-006))*x+(-0.00010789400331689956))*x+(0.0016383552210203305))*x+(-0.024623472952107046))*x+(0.36895996342328974));
		wts[0] = (((((((((((((1.7583564234276611e-010))*x+(-2.7284841053187847e-011))*x+(-1.0603192398169388e-010))*x+(1.5688783605583012e-011))*x+(2.6621667833145083e-011))*x+(1.7949020048035891e-010))*x+(-8.1170214253726629e-009))*x+(2.2788914015118658e-007))*x+(-5.6950817623468986e-006))*x+(0.00014236692266397788))*x+(-0.0039023446589910335))*x+(0.16004240734114644));
		wts[1] = (((((((((((((1.6370904631912708e-011))*x+(1.5158245029548803e-013))*x+(-6.518045362705986e-012))*x+(1.2126596023639042e-012))*x+(-2.7424581124553996e-011))*x+(3.6714986606511952e-010))*x+(-4.7518608307465611e-009))*x+(7.1018795807139171e-008))*x+(-1.3545327926800521e-006))*x+(3.1343792296049014e-005))*x+(-0.00084712763137754696))*x+(0.034691681617410569));
		wts[2] = (((((((((((((1.1368683772161603e-013))*x+(1.3263464400855202e-013))*x+(5.9211894646675007e-014))*x+(2.0842586915629607e-013))*x+(-4.049501474886104e-012))*x+(4.4990122738397525e-011))*x+(-4.3692613416190795e-010))*x+(4.1382645759221086e-009))*x+(-5.0348604168961211e-008))*x+(9.4850450429991831e-007))*x+(-2.4546791894643936e-005))*x+(0.0010006946643811724));
		break;
	case 21:
		rts[0] = (((((((((((((8.9433645674337933e-012))*x+(-5.3053857603420807e-013))*x+(-5.5232855326418449e-012))*x+(3.7421917416698603e-013))*x+(3.6000831945178403e-013))*x+(5.8336446784323912e-011))*x+(-1.7261750917541008e-009))*x+(4.1242690299962227e-008))*x+(-9.1160741529788803e-007))*x+(1.9610848791825942e-005))*x+(-0.00041866116804578217))*x+(0.0089236195839011209));
		rts[1] = (((((((((((((7.8822874153653772e-011))*x+(6.3664629124104977e-012))*x+(-4.5095778962907687e-011))*x+(-4.9264296346033608e-012))*x+(-1.9137284349805366e-011))*x+(1.0504415115519803e-009))*x+(-2.644270254611077e-008))*x+(5.7343091179144301e-007))*x+(-1.1680477351135496e-005))*x+(0.00023236921384364265))*x+(-0.004589709093999938))*x+(0.090510680974605115));
		rts[2] = (((((((((((((3.4924596548080444e-010))*x+(2.4253192047278084e-011))*x+(-2.1645973902195692e-010))*x+(1.4551915228366852e-011))*x+(-7.7822429981703556e-010))*x+(1.6695897405346234e-008))*x+(-3.0242879726453487e-007))*x+(5.1304346667298733e-006))*x+(-8.3983444607582655e-005))*x+(0.0013523294087297206))*x+(-0.021644723751186624))*x+(0.3458734764099049));
		wts[0] = (((((((((((((1.4915713109076023e-010))*x+(1.2732925824820995e-011))*x+(-8.9357854449190199e-011))*x+(-8.7917821171383058e-012))*x+(1.7706724975141697e-011))*x+(1.9748587950137639e-010))*x+(-6.9641362306545789e-009))*x+(1.9016342663510005e-007))*x+(-4.8609032304303126e-006))*x+(0.0001265706762783684))*x+(-0.0036338239564392585))*x+(0.15627695448337284));
		wts[1] = (((((((((((((1.0913936421275139e-011))*x+(1.5158245029548803e-013))*x+(-5.3053857603420819e-012))*x+(-1.8947806286936001e-014))*x+(-1.5807207394876361e-011))*x+(2.1760430494547717e-010))*x+(-3.0389927611433145e-009))*x+(5.1913835896755238e-008))*x+(-1.1115092938274174e-006))*x+(2.7663759661472147e-005))*x+(-0.00078824130752872554))*x+(0.033874609853444961));
		wts[2] = (((((((((((((1.1179205709292242e-012))*x+(-8.5265128291212022e-014))*x+(-6.6554169582862711e-013))*x+(2.078337502098293e-013))*x+(-2.0477693614869468e-012))*x+(2.3925935307052743e-011))*x+(-2.3651513155383453e-010))*x+(2.5069901155028163e-009))*x+(-3.739006442741305e-008))*x+(8.1851733631146256e-007))*x+(-2.2786216215226284e-005))*x+(0.00097704977097538967));
		break;
	case 22:
		rts[0] = (((((((((((((3.5621875819439688e-012))*x+(-2.2737367544323206e-013))*x+(-2.0700478368477584e-012))*x+(2.2737367544323206e-013))*x+(-8.3844042819691822e-013))*x+(5.0895584043549505e-011))*x+(-1.3963197820210382e-009))*x+(3.3455650971792039e-008))*x+(-7.627608940748154e-007))*x+(1.710707956435048e-005))*x+(-0.00038201760792004087))*x+(0.0085236972314024564));
		rts[1] = (((((((((((((1.2187229003757238e-010))*x+(1.8189894035458565e-012))*x+(-7.5753329535170152e-011))*x+(-9.0949470177292824e-013))*x+(-1.1245523031296515e-011))*x+(8.5425947797072388e-010))*x+(-2.073361053215687e-008))*x+(4.5598471546763142e-007))*x+(-9.6311624807332557e-006))*x+(0.00020051910218731503))*x+(-0.0041578444837157809))*x+(0.086142208627488281));
		rts[2] = (((((((((((((4.7293724492192268e-010))*x+(2.1827872842550278e-011))*x+(-3.0089116383654374e-010))*x+(1.0156024169797697e-011))*x+(-5.2182258514221758e-010))*x+(1.1791276695779136e-008))*x+(-2.1781977643797745e-007))*x+(3.8420773928275285e-006))*x+(-6.6179162864258651e-005))*x+(0.0011283714079828311))*x+(-0.019172911012654219))*x+(0.32550194253268683));
		wts[0] = (((((((((((((2.7284841053187847e-010))*x+(1.0307606620093186e-011))*x+(-1.7818517032234618e-010))*x+(-7.8822874153653775e-012))*x+(3.8482994568767026e-011))*x+(1.8466295159669241e-010))*x+(-5.8240206731359949e-009))*x+(1.5823933659693998e-007))*x+(-4.1660041112575224e-006))*x+(0.00011306223247843174))*x+(-0.0033945383063388535))*x+(0.15276502369546299));
		wts[1] = (((((((((((((6.8212102632969618e-011))*x+(-1.9705718538413444e-012))*x+(-4.3030468077631667e-011))*x+(1.3452942463724562e-012))*x+(9.0002079862946562e-014))*x+(1.2963911425837674e-010))*x+(-2.0235958834528369e-009))*x+(3.9476867848738571e-008))*x+(-9.3041360342549506e-007))*x+(2.4613268892042607e-005))*x+(-0.00073605465855509195))*x+(0.033112969873030522));
		wts[2] = (((((((((((((7.2949054204703612e-013))*x+(4.736951571734001e-015))*x+(-3.6178467629118433e-013))*x+(6.4837024638109142e-014))*x+(-1.1180686006658409e-012))*x+(1.2578956395022562e-011))*x+(-1.3058424018034623e-010))*x+(1.6175077226695163e-009))*x+(-2.9316404526914575e-008))*x+(7.1934148049023329e-007))*x+(-2.1252376745894958e-005))*x+(0.00095504697442288719));
		break;
	case 23:
		rts[0] = (((((((((((((1.2126596023639042e-011))*x+(9.4739031434680011e-013))*x+(-7.4654356770527849e-012))*x+(-5.6369723703634601e-013))*x+(3.3277084791431345e-013))*x+(4.2255532406443308e-011))*x+(-1.1170426065613508e-009))*x+(2.7194828574235903e-008))*x+(-6.4192559185808718e-007))*x+(1.5006306179662341e-005))*x+(-0.00034996459325787227))*x+(0.008158056051229776));
		rts[1] = (((((((((((((9.3374789382020624e-011))*x+(6.0632980118195212e-013))*x+(-5.5554968033296362e-011))*x+(-2.6526928801710404e-013))*x+(-1.3083460241129312e-011))*x+(6.7290055009531591e-010))*x+(-1.6165752884470898e-008))*x+(3.6419548532506951e-007))*x+(-7.9984097742236138e-006))*x+(0.00017416644213226007))*x+(-0.0037839745551689814))*x+(0.082175688162740276));
		rts[2] = (((((((((((((3.4439532707134879e-010))*x+(-1.5764574830730755e-011))*x+(-2.1403441981722909e-010))*x+(2.622376390111943e-011))*x+(-3.6768218099799316e-010))*x+(8.3162348119003582e-009))*x+(-1.5811647813279706e-007))*x+(2.9109195960330676e-006))*x+(-5.277246564250327e-005))*x+(0.00095087339276069449))*x+(-0.017100359639594161))*x+(0.30739485925287413));
		wts[0] = (((((((((((((1.3096723705530167e-010))*x+(8.4886172165473291e-012))*x+(-7.9126039054244757e-011))*x+(-6.1390892369672648e-012))*x+(1.2486604343090828e-011))*x+(1.6027949338119166e-010))*x+(-4.7942994759371986e-009))*x+(1.3176680369042515e-007))*x+(-3.587703666670568e-006))*x+(0.00010145813112538704))*x+(-0.0031803069217447391))*x+(0.1494795342164664));
		wts[1] = (((((((((((((5.5176011907557644e-011))*x+(-1.3642420526593924e-011))*x+(-3.7213491547542312e-011))*x+(8.5454606354081388e-012))*x+(3.7114015564535894e-012))*x+(7.7761797001585351e-011))*x+(-1.410148738519486e-009))*x+(3.1021916221026416e-008))*x+(-7.904343090521978e-007))*x+(2.2040427147050158e-005))*x+(-0.00068947085054882232))*x+(0.03240063564478269));
		wts[2] = (((((((((((((2.1221543041368323e-012))*x+(1.1842378929335001e-013))*x+(-1.3914795241968627e-012))*x+(-3.6119255734471745e-014))*x+(-2.7762977102459751e-013))*x+(6.6190571542297984e-012))*x+(-7.5069760592979165e-011))*x+(1.1182667801016657e-009))*x+(-2.3936780738665713e-008))*x+(6.3995798743805322e-007))*x+(-1.9895757923441319e-005))*x+(0.0009344861211696623));
		break;
	case 24:
		rts[0] = (((((((((((((-1.5158245029548803e-012))*x+(1.4400332778071363e-012))*x+(1.7053025658242404e-012))*x+(-9.1896860491639611e-013))*x+(-1.7822780288649178e-012))*x+(3.3995621132968751e-011))*x+(-8.8957633851786478e-010))*x+(2.2199202254213898e-008))*x+(-5.4351599922120009e-007))*x+(1.3233135243822155e-005))*x+(-0.00032177431879292444))*x+(0.0078224819573718112));
		rts[1] = (((((((((((((1.1095835361629725e-010))*x+(1.8189894035458565e-012))*x+(-7.0751108675419047e-011))*x+(-1.2884508275116484e-012))*x+(-3.680611371237319e-012))*x+(5.2106704136652604e-010))*x+(-1.2603135868261006e-008))*x+(2.9265897142731018e-007))*x+(-6.6906341619858232e-006))*x+(0.00015220433656401575))*x+(-0.0034582570711311064))*x+(0.078558230319591776));
		rts[2] = (((((((((((((5.1901830981175101e-010))*x+(-1.6977234433094658e-011))*x+(-3.3378455555066466e-010))*x+(2.3495279795800642e-011))*x+(-2.1229122163883102e-010))*x+(5.8902192752915052e-009))*x+(-1.1592798069652113e-007))*x+(2.2318843993692403e-006))*x+(-4.2557031893227425e-005))*x+(0.0008085569725683196))*x+(-0.015346029979917348))*x+(0.29119536126952317));
		wts[0] = (((((((((((((8.6098831767837198e-011))*x+(6.0632980118195212e-013))*x+(-5.0704329623840749e-011))*x+(-2.3495279795800643e-012))*x+(5.9306633678109685e-012))*x+(1.3337597692952841e-010))*x+(-3.920152794970969e-009))*x+(1.1005105597187519e-007))*x+(-3.1055231648295196e-006))*x+(9.1439993481147924e-005))*x+(-0.0029876497418425555))*x+(0.14639722485104664));
		wts[1] = (((((((((((((6.972792713592449e-011))*x+(2.2737367544323206e-012))*x+(-4.5512630701220282e-011))*x+(-9.8528592692067239e-013))*x+(7.3991183550485094e-012))*x+(5.099861274023472e-011))*x+(-1.0272063200034152e-009))*x+(2.5004767441790438e-008))*x+(-6.7901689732955783e-007))*x+(1.9842252916506261e-005))*x+(-0.00064764381573713219))*x+(0.031732444474127014));
		wts[2] = (((((((((((((-7.1054273576010019e-013))*x+(-1.0894988614988202e-013))*x+(5.9626377909201744e-013))*x+(7.312668988864364e-014))*x+(-4.9316106753849454e-013))*x+(3.5171310308612643e-012))*x+(-4.5673962297450757e-011))*x+(8.2406122666374892e-010))*x+(-2.0100679905410653e-008))*x+(5.7419448163688856e-007))*x+(-1.8683518665042119e-005))*x+(0.00091520743372526905));
		break;
	case 25:
		rts[0] = (((((((((((((1.152026622245709e-011))*x+(-1.7431981783981123e-012))*x+(-7.7875483839306964e-012))*x+(1.0563402004966822e-012))*x+(9.8291745113480512e-013))*x+(2.6466828728644032e-011))*x+(-7.0919818166241088e-010))*x+(1.8220294624911773e-008))*x+(-4.6297791681434064e-007))*x+(1.1727369754204835e-005))*x+(-0.00029685405274408366))*x+(0.007513418600056004));
		rts[1] = (((((((((((((6.7908937732378633e-011))*x+(-7.5791225147744009e-012))*x+(-4.0320931778599814e-011))*x+(5.4948638232114401e-012))*x+(-7.285431517326895e-012))*x+(3.9840486465436692e-010))*x+(-9.8571065384097291e-009))*x+(2.3681557707414902e-007))*x+(-5.6362553942553477e-006))*x+(0.00013376978531565623))*x+(-0.0031728096818479262))*x+(0.075245767509733219));
		rts[2] = (((((((((((((1.7462298274040222e-010))*x+(7.2759576141834259e-012))*x+(-9.6103273487339421e-011))*x+(3.637978807091713e-012))*x+(-1.8404004246500941e-010))*x+(4.2065361564406576e-009))*x+(-8.5933771506082238e-008))*x+(1.7314574147775375e-006))*x+(-3.4680226764708756e-005))*x+(0.00069320066999034591))*x+(-0.01384820575660497))*x+(0.27661745281084438));
		wts[0] = (((((((((((((2.4010660126805305e-010))*x+(1.4551915228366852e-011))*x+(-1.6082897976351282e-010))*x+(-8.9433645674337949e-012))*x+(3.516712846855323e-011))*x+(1.101009653818134e-010))*x+(-3.2033735664072079e-009))*x+(9.2314280072021873e-008))*x+(-2.7019913795648756e-006))*x+(8.2746445896878879e-005))*x+(-0.0028136649483481314))*x+(0.14349801583991051));
		wts[1] = (((((((((((((5.5782341708739594e-011))*x+(8.7917821171383058e-012))*x+(-3.4333424991928041e-011))*x+(-5.1348555037596571e-012))*x+(5.461705162209304e-012))*x+(3.5062915533975079e-011))*x+(-7.7694709924950668e-010))*x+(2.0540056322460032e-008))*x+(-5.8834202530203916e-007))*x+(1.7945670781986205e-005))*x+(-0.00060990118805326679))*x+(0.031103987920829294));
		wts[2] = (((((((((((((3.8843002888218807e-012))*x+(5.447494307494101e-014))*x+(-2.6633510212074421e-012))*x+(-3.6119255734471757e-014))*x+(4.9693582582222007e-013))*x+(1.9625504924884272e-012))*x+(-2.9888577723902188e-011))*x+(6.3916846699633533e-010))*x+(-1.7200503103139787e-008))*x+(5.1842681717891926e-007))*x+(-1.7592344830886207e-005))*x+(0.00089707879046211085));
		break;
	case 26:
		rts[0] = (((((((((((((1.6863547595373042e-011))*x+(-7.5791225147744016e-014))*x+(-1.0892620139202334e-011))*x+(1.6579330501069002e-014))*x+(1.7497114868092465e-012))*x+(2.0932588995492548e-011))*x+(-5.670980814572364e-010))*x+(1.504501062621344e-008))*x+(-3.9668400423550443e-007))*x+(1.0441049236966277e-005))*x+(-0.00027471875705172266))*x+(0.0072278464762058877));
		rts[1] = (((((((((((((1.1035202381511529e-010))*x+(-4.850638409455617e-012))*x+(-6.851526753356059e-011))*x+(3.6000831945178407e-012))*x+(3.0932293763423007e-012))*x+(3.054504797243377e-010))*x+(-7.7529337024391972e-009))*x+(1.9302799862212319e-007))*x+(-4.7800725862893563e-006))*x+(0.00011818903424545835))*x+(-0.0029212786034489035))*x+(0.072201318701563391));
		rts[2] = (((((((((((((4.0017766878008842e-010))*x+(-8.4886172165473291e-012))*x+(-2.6147972675971687e-010))*x+(1.1217101321866114e-011))*x+(-7.9334464923401044e-011))*x+(3.0283568245674055e-009))*x+(-6.4445602632190444e-008))*x+(1.3584581276167758e-006))*x+(-2.8536147604933206e-005))*x+(0.00059874852164334036))*x+(-0.012559325032211681))*x+(0.26342941703574541));
		wts[0] = (((((((((((((1.152026622245709e-010))*x+(-3.637978807091713e-012))*x+(-6.7529981606639922e-011))*x+(2.0463630789890885e-012))*x+(1.0468662973532142e-011))*x+(8.6738320230021288e-011))*x+(-2.6166603698622266e-009))*x+(7.7828730127293966e-008))*x+(-2.362677440415073e-006))*x+(7.5163917758173465e-005))*x+(-0.0026559241445382317))*x+(0.14076448456579385));
		wts[1] = (((((((((((((2.0312048339595396e-011))*x+(-5.3053857603420811e-012))*x+(-1.2486604343090827e-011))*x+(3.5527136788005005e-012))*x+(1.5513516397428853e-012))*x+(2.3043493039646514e-011))*x+(-6.0549617172019521e-010))*x+(1.7111390896810498e-008))*x+(-5.1332344089734705e-007))*x+(1.6296596353356875e-005))*x+(-0.00057569640181550589))*x+(0.030511463857577026));
		wts[2] = (((((((((((((-9.1423165334466217e-013))*x+(5.2106467289074012e-014))*x+(7.7064280882647529e-013))*x+(-5.8619775700208265e-014))*x+(-3.1833794859418652e-013))*x+(1.1600165272795948e-012))*x+(-2.08083955159181e-011))*x+(5.145296642454037e-010))*x+(-1.4907977541030525e-008))*x+(4.7038833087948855e-007))*x+(-1.6604674464063862e-005))*x+(0.00087998828309355072));
		break;
	case 27:
		rts[0] = (((((((((((((1.1596057447604835e-011))*x+(1.6484591469634324e-012))*x+(-7.4322770160506479e-012))*x+(-1.0563402004966822e-012))*x+(1.0971964078028882e-012))*x+(1.6640096707950153e-011))*x+(-4.5563602890652527e-010))*x+(1.2500440469779642e-008))*x+(-3.4177849854086229e-007))*x+(9.335897747766244e-006))*x+(-0.00025496924428607273))*x+(0.0069631865827415491));
		rts[1] = (((((((((((((6.972792713592449e-011))*x+(-3.3348139065007367e-012))*x+(-4.3845223747969911e-011))*x+(2.0084674664152163e-012))*x+(7.3896444519050419e-013))*x+(2.3503924732419062e-010))*x+(-6.137752676475353e-009))*x+(1.5848355516823176e-007))*x+(-4.0797376309372373e-006))*x+(0.00010493382777922165))*x+(-0.0026985056402505305))*x+(0.069393634631000012));
		rts[2] = (((((((((((((3.5409660389026004e-010))*x+(-7.2759576141834259e-012))*x+(-2.2373569663614032e-010))*x+(8.4886172165473291e-012))*x+(-4.8904288026581837e-011))*x+(2.2047193700321563e-009))*x+(-4.888384808054979e-008))*x+(1.0772151869768247e-006))*x+(-2.3690687171044424e-005))*x+(0.00052068910125158119))*x+(-0.011442307553046675))*x+(0.25144160129130266));
		wts[0] = (((((((((((((1.4066851387421289e-010))*x+(1.8796223836640515e-011))*x+(-8.8069403621678547e-011))*x+(-1.0838145196127393e-011))*x+(1.6513013179064728e-011))*x+(7.2150877864866431e-011))*x+(-2.1476882494653182e-009))*x+(6.5966532976820716e-008))*x+(-2.0758685632671359e-006))*x+(6.8517952099176688e-005))*x+(-0.0025123856009469578))*x+(0.13818143695900509));
		wts[1] = (((((((((((((1.303609072541197e-011))*x+(-1.303609072541197e-011))*x+(-6.1580370432542013e-012))*x+(7.9012352216523125e-012))*x+(-5.2106467289073879e-014))*x+(1.5822602487484495e-011))*x+(-4.8262038809809827e-010))*x+(1.4407521176096338e-008))*x+(-4.5048992748653044e-007))*x+(1.4853577060556603e-005))*x+(-0.00054457762479410651))*x+(0.02995156725750742));
		wts[2] = (((((((((((((-2.5579538487363607e-013))*x+(-3.4816594052244909e-013))*x+(3.4402110789718182e-013))*x+(1.9806378759312793e-013))*x+(-1.8962609260597674e-013))*x+(6.7208275981537702e-013))*x+(-1.5418862945685653e-011))*x+(4.248845638747204e-010))*x+(-1.3038094920399024e-008))*x+(4.2855866712397222e-007))*x+(-1.5706661514568866e-005))*x+(0.00086383958373648074));
		break;
	case 28:
		rts[0] = (((((((((((((7.920183027939249e-012))*x+(6.0632980118195212e-013))*x+(-5.1135392216868541e-012))*x+(-4.5237887510059705e-013))*x+(7.5080682411983913e-013))*x+(1.2997010874945166e-011))*x+(-3.6826061644568142e-010))*x+(1.0450189176965569e-008))*x+(-2.9602259146316778e-007))*x+(8.381244601451952e-006))*x+(-0.0002372749653549987))*x+(0.0067172235185203105));
		rts[1] = (((((((((((((5.4569682106375694e-011))*x+(-5.1538033100465928e-012))*x+(-3.4106051316484809e-011))*x+(2.7663797178926562e-012))*x+(6.7738407475796325e-013))*x+(1.8130090021865422e-010))*x+(-4.8941804683029959e-009))*x+(1.3104119049126931e-007))*x+(-3.5027579429007059e-006))*x+(9.3587499970057553e-005))*x+(-0.0025002725954816245))*x+(0.066796135654297289));
		rts[2] = (((((((((((((2.0372681319713593e-010))*x+(-4.850638409455617e-012))*x+(-1.1944697083284458e-010))*x+(4.9264296346033608e-012))*x+(-4.6914768366453544e-011))*x+(1.623637520727546e-009))*x+(-3.7492569049391016e-008))*x+(8.627403615217113e-007))*x+(-1.9829723575319015e-005))*x+(0.00045562266955419728))*x+(-0.010467924370797334))*x+(0.24049732259931914));
		wts[0] = (((((((((((((1.0792670461038748e-010))*x+(-2.0615213240186371e-011))*x+(-6.6468904454571501e-011))*x+(1.2581343374525505e-011))*x+(1.1776061607330727e-011))*x+(5.3598607034170215e-011))*x+(-1.7702541654784907e-009))*x+(5.6212481780448798e-008))*x+(-1.8321381822968457e-006))*x+(6.2665689475086911e-005))*x+(-0.0023813237618425394))*x+(0.13573555732989276));
		wts[1] = (((((((((((((7.6700719849516944e-011))*x+(-5.3053857603420811e-012))*x+(-4.9359035377468289e-011))*x+(3.6285049039482447e-012))*x+(1.0651035609043902e-011))*x+(1.2381799289566212e-011))*x+(-3.9242083656650567e-010))*x+(1.2232865165273664e-008))*x+(-3.9736140748647392e-007))*x+(1.3583972513717586e-005))*x+(-0.00051616662427706275))*x+(0.029421406661343658));
		wts[2] = (((((((((((((3.2969182939268649e-012))*x+(-1.4684549872375402e-013))*x+(-2.1328124451732342e-012))*x+(1.0006810195288076e-013))*x+(4.6222285258560681e-013))*x+(4.484375833631778e-013))*x+(-1.20135151826517e-011))*x+(3.5693778719740149e-010))*x+(-1.1480230030502803e-008))*x+(3.9184901125710782e-007))*x+(-1.4887032190468581e-005))*x+(0.00084854885290051949));
		break;
	case 29:
		rts[0] = (((((((((((((4.6990559591601287e-012))*x+(2.0842586915629605e-013))*x+(-3.5527136788005005e-012))*x+(-1.8474111129762605e-013))*x+(6.300145590406221e-013))*x+(1.0215902198259148e-011))*x+(-2.9950801098503155e-010))*x+(8.7881522707148694e-009))*x+(-2.5766032166890657e-007))*x+(7.5523809012625776e-006))*x+(-0.00022136050954836632))*x+(0.0064880438696818905));
		rts[1] = (((((((((((((8.1248193358381585e-011))*x+(-5.1538033100465928e-012))*x+(-5.1234868199874953e-011))*x+(3.2211270687791203e-012))*x+(6.3333042514083591e-012))*x+(1.4053943194388313e-010))*x+(-3.9317757938306386e-009))*x+(1.0908161603614037e-007))*x+(-3.0241152723653464e-006))*x+(8.3819129461412665e-005))*x+(-0.0023231051271712651))*x+(0.064386074123697803));
		rts[2] = (((((((((((((2.6193447411060333e-010))*x+(-2.4253192047278085e-012))*x+(-1.5825207810848951e-010))*x+(2.1979455292845764e-012))*x+(-1.7431981783981116e-011))*x+(1.20906899307253e-009))*x+(-2.9065371146922793e-008))*x+(6.9739092841321815e-007))*x+(-1.6723484936864704e-005))*x+(0.00040095799920295916))*x+(-0.0096128954198954706))*x+(0.23046601798056809));
		wts[0] = (((((((((((((1.9523819598058859e-010))*x+(-1.5158245029548802e-011))*x+(-1.2285757596449304e-010))*x+(9.2465294680247683e-012))*x+(2.5702699228228689e-011))*x+(4.3260210228860764e-011))*x+(-1.4688312788280198e-009))*x+(4.8150512910183352e-008))*x+(-1.6239173383225667e-006))*x+(5.7489662562609789e-005))*x+(-0.0022612724697487776))*x+(0.13341512161677685));
		wts[1] = (((((((((((((7.0485839387401938e-011))*x+(-2.9558577807620168e-012))*x+(-4.4442079646008402e-011))*x+(1.6958286626807724e-012))*x+(9.4099542972495945e-012))*x+(9.9780924263844408e-012))*x+(-3.2223960536962676e-010))*x+(1.0458268584478956e-008))*x+(-3.5209587963963562e-007))*x+(1.2461559554418493e-005))*x+(-0.00049014371332501479))*x+(0.028918438502288746));
		wts[2] = (((((((((((((1.6389852438199644e-012))*x+(-3.1737575530617807e-013))*x+(-1.0723274120512845e-012))*x+(2.1138646388862978e-013))*x+(2.3077835938541586e-013))*x+(2.8801035630484268e-013))*x+(-9.5909969780964348e-012))*x+(3.034387255351767e-010))*x+(-1.0163480029945724e-008))*x+(3.5943687619109015e-007))*x+(-1.4136404280047061e-005))*x+(0.00083404253490761799));
		break;
	case 30:
		rts[0] = (((((((((((((1.4551915228366852e-011))*x+(-1.0042337332076081e-012))*x+(-9.284425080598643e-012))*x+(6.3238303482648906e-013))*x+(1.8355687340469257e-012))*x+(7.9300270054242593e-012))*x+(-2.4521666179092943e-010))*x+(7.4323718568525265e-009))*x+(-2.2530981287627314e-007))*x+(6.8292804312865621e-006))*x+(-0.00020699501441982589))*x+(0.0062739865792993824));
		rts[1] = (((((((((((((1.0125707679738601e-010))*x+(-3.637978807091713e-012))*x+(-6.3550942286383348e-011))*x+(2.4632148173016808e-012))*x+(1.0241289298088909e-011))*x+(1.0994227750416029e-010))*x+(-3.1814016606309297e-009))*x+(9.1381157455809145e-008))*x+(-2.6244395265051508e-006))*x+(7.5363982270324856e-005))*x+(-0.002164121728404141))*x+(0.062143869297823638));
		rts[2] = (((((((((((((2.8618766615788138e-010))*x+(-6.6696278130014735e-012))*x+(-1.8189894035458562e-010))*x+(3.9411437076826888e-012))*x+(4.414838864856087e-012))*x+(9.0959654623172048e-010))*x+(-2.2759522266824203e-008))*x+(5.6859087601187253e-007))*x+(-1.4202016676530723e-005))*x+(0.00035469839742379344))*x+(-0.008858498708489879))*x+(0.22123802656377137));
		wts[0] = (((((((((((((2.2676734564205009e-010))*x+(-4.850638409455617e-012))*x+(-1.4423070145615685e-010))*x+(2.6526928801710406e-012))*x+(3.1121771826292388e-011))*x+(3.6166625250189099e-011))*x+(-1.2249167606152391e-009))*x+(4.1451049407707303e-008))*x+(-1.4451215618789999e-006))*x+(5.2892798932927893e-005))*x+(-0.002150979365445943))*x+(0.13120976162001569));
		wts[1] = (((((((((((((-1.0913936421275139e-011))*x+(-1.8189894035458565e-012))*x+(8.0338698656608666e-012))*x+(3.694822225952521e-013))*x+(-2.5437429940211587e-012))*x+(8.2754543958192991e-012))*x+(-2.6612519595422174e-010))*x+(8.9940752623363096e-009))*x+(-3.1328264345672113e-007))*x+(1.146495482512444e-005))*x+(-0.00046623659644841331))*x+(0.02844041439943689));
		wts[2] = (((((((((((((-1.3263464400855202e-013))*x+(-2.3684757858670005e-015))*x+(1.5513516397428853e-013))*x+(8.2896652505345011e-015))*x+(-8.008408750962795e-014))*x+(2.4729292687671511e-013))*x+(-7.8008109231456988e-012))*x+(2.601863828555206e-010))*x+(-9.0391595449976214e-009))*x+(3.3067612474215922e-007))*x+(-1.3446853148740368e-005))*x+(0.00082025569821216168));
		break;
	case 31:
		rts[0] = (((((((((((((9.587589981189618e-012))*x+(0))*x+(-6.2883032114768866e-012))*x+(-1.0658141036401503e-013))*x+(1.2245019812932392e-012))*x+(6.4925842480079154e-012))*x+(-2.0188263098278963e-010))*x+(6.3194779964526049e-009))*x+(-1.9787815738111597e-007))*x+(6.1956105238391655e-006))*x+(-0.000193983832092773))*x+(0.0060736027306372955));
		rts[1] = (((((((((((((6.1239309919377164e-011))*x+(3.0316490059097605e-012))*x+(-3.6493474908638746e-011))*x+(-2.2926845607192563e-012))*x+(4.2727303177040686e-012))*x+(8.7697552923297436e-011))*x+(-2.5912073967996698e-009))*x+(7.7012382397138396e-008))*x+(-2.2886337037453237e-006))*x+(6.8008729346508145e-005))*x+(-0.002020916821638275))*x+(0.060052575419890772));
		rts[2] = (((((((((((((1.6855968472858268e-010))*x+(-1.8189894035458565e-012))*x+(-9.6785394513669105e-011))*x+(8.3370347662518429e-013))*x+(-8.8675733422860503e-012))*x+(6.9214204737969942e-010))*x+(-1.7986220216907135e-008))*x+(4.6728198939878968e-007))*x+(-1.2138210295313071e-005))*x+(0.00031528925702381522))*x+(-0.0081895421638576403))*x+(0.2127205709458746));
		wts[0] = (((((((((((((2.0615213240186373e-010))*x+(1.8189894035458565e-012))*x+(-1.3445363341209787e-010))*x+(-1.5158245029548803e-012))*x+(3.014595980251518e-011))*x+(3.0143591326729315e-011))*x+(-1.026860374508942e-009))*x+(3.5853466862079124e-008))*x+(-1.2908423423866702e-006))*x+(4.8794446882965963e-005))*x+(-0.0020493692262560119))*x+(0.12911027019641927));
		wts[1] = (((((((((((((1.3945585427184899e-011))*x+(2.8800665556142726e-012))*x+(-7.9580786405131221e-012))*x+(-1.7526720815415804e-012))*x+(1.2766084485823133e-012))*x+(6.9236468410357085e-012))*x+(-2.2269682394456442e-010))*x+(7.7754815179057816e-009))*x+(-2.7981631116798711e-007))*x+(1.0576524216101647e-005))*x+(-0.00044421184327832902))*x+(0.027985338210759492));
		wts[2] = (((((((((((((3.0079642480510907e-012))*x+(3.7895612573872008e-014))*x+(-2.152056310933403e-012))*x+(2.9605947323337718e-016))*x+(5.5555560152242823e-013))*x+(1.8958908517182257e-013))*x+(-6.5422424422312275e-012))*x+(2.2459490286082701e-010))*x+(-8.0718245440512121e-009))*x+(3.0504520942611446e-007))*x+(-1.2811615257271671e-005))*x+(0.00080713073464333258));
		break;
	case 32:
		rts[0] = (((((((((((((4.2443086082736646e-012))*x+(-9.0949470177292824e-013))*x+(-2.0179413695586845e-012))*x+(6.229091316830212e-013))*x+(8.1120295665944704e-014))*x+(5.0235371418239075e-012))*x+(-1.671026650384988e-010))*x+(5.4004994365364212e-009))*x+(-1.7449589933179094e-007))*x+(5.6379678049859241e-006))*x+(-0.00018216193912984016))*x+(0.0058856227548756941));
		rts[1] = (((((((((((((6.8818432434151561e-011))*x+(7.5791225147744013e-013))*x+(-4.2007286538137117e-011))*x+(-6.6317322004276004e-013))*x+(6.3996215734126346e-012))*x+(6.9331799560738247e-011))*x+(-2.1252060111720539e-009))*x+(6.5269042985131393e-008))*x+(-2.0048468213860562e-006))*x+(6.1580242965858956e-005))*x+(-0.0018914696651842848))*x+(0.058097453199856083));
		rts[2] = (((((((((((((2.9831426218152046e-010))*x+(-1.6370904631912708e-011))*x+(-1.8568850161197284e-010))*x+(9.4739031434680019e-012))*x+(2.0198361501873783e-011))*x+(5.2977829530694476e-010))*x+(-1.434336797482653e-008))*x+(3.8686931969067468e-007))*x+(-1.0435975092500568e-005))*x+(0.0002815083116680383))*x+(-0.0075935951063137372))*x+(0.20483462979172826));
		wts[0] = (((((((((((((1.3945585427184898e-010))*x+(-2.849750065555175e-011))*x+(-8.2081896835006761e-011))*x+(1.720460810853789e-011))*x+(1.5414040414422438e-011))*x+(2.0707583795835184e-011))*x+(-8.6356314691708269e-010))*x+(3.1151633569000595e-008))*x+(-1.1571015991843996e-006))*x+(4.5127230237039046e-005))*x+(-0.0019555143926715426))*x+(0.12710843943311853));
		wts[1] = (((((((((((((3.698611787209908e-011))*x+(3.1074402310575047e-012))*x+(-2.3684757858670004e-011))*x+(-2.6526928801710406e-012))*x+(5.0306425691815093e-012))*x+(6.0926078996696252e-012))*x+(-1.8766395844712253e-010))*x+(6.7538850438234972e-009))*x+(-2.5081621610190114e-007))*x+(9.7815963423335245e-006))*x+(-0.00042386821687857905))*x+(0.027551430634638135));
		wts[2] = (((((((((((((6.6317322004276009e-014))*x+(2.4632148173016805e-013))*x+(-1.9539925233402752e-014))*x+(-1.459573203040539e-013))*x+(-5.6991448597424713e-015))*x+(1.8681352761025966e-013))*x+(-5.4245150038489945e-012))*x+(1.9493515135415862e-010))*x+(-7.2345176826913342e-009))*x+(2.8211532712765308e-007))*x+(-1.2224873200470279e-005))*x+(0.00079461631107399582));
		break;
	case 33:
		rts[0] = (((((((((((((1.1179205709292242e-011))*x+(8.3370347662518418e-013))*x+(-7.0793741239564635e-012))*x+(-5.8501351910914912e-013))*x+(1.4767446524880748e-012))*x+(4.3230604281537426e-012))*x+(-1.3935400056119818e-010))*x+(4.6371726088641667e-009))*x+(-1.5446702393967043e-007))*x+(5.1452862198907616e-006))*x+(-0.0001713886948924391))*x+(0.0057089295260424472));
		rts[1] = (((((((((((((7.3669070843607187e-011))*x+(2.5769016550232964e-012))*x+(-4.5114726769194626e-011))*x+(-2.2547889481453841e-012))*x+(7.6833354493525511e-012))*x+(5.5933332040088616e-011))*x+(-1.7539572017000182e-009))*x+(5.5609188291209463e-008))*x+(-1.7637084685449369e-006))*x+(5.5937062876499265e-005))*x+(-0.0017740728667128133))*x+(0.056265622142258775));
		rts[2] = (((((((((((((2.6799777212242282e-010))*x+(9.0949470177292824e-012))*x+(-1.6818072860284397e-010))*x+(-7.2759576141834259e-012))*x+(2.1695238198541724e-011))*x+(4.1413509658620262e-010))*x+(-1.153051017629044e-008))*x+(3.2249836667830323e-007))*x+(-9.0219213287704801e-006))*x+(0.00025238577785841965))*x+(-0.0070604075757406655))*x+(0.19751248006348635));
		wts[0] = (((((((((((((1.4066851387421289e-010))*x+(0))*x+(-8.3370347662518413e-011))*x+(-1.8947806286936002e-012))*x+(1.6124583150182538e-011))*x+(2.0904167286062147e-011))*x+(-7.3138295419994392e-010))*x+(2.7180605025970785e-008))*x+(-1.0406577298412616e-006))*x+(4.183455961790742e-005))*x+(-0.0018686108027217937))*x+(0.12519692548161113));
		wts[1] = (((((((((((((2.3343697345505156e-011))*x+(9.8528592692067219e-013))*x+(-1.521508844840961e-011))*x+(-4.6422125402993209e-013))*x+(3.2590226813529926e-012))*x+(4.4358590874556593e-012))*x+(-1.586663393264113e-010))*x+(5.8923157834437721e-009))*x+(-2.255716372255116e-007))*x+(9.0678757102800878e-006))*x+(-0.00040503136232092308))*x+(0.02713709976977766));
		wts[2] = (((((((((((((1.2742399727964462e-012))*x+(-1.7289873236829104e-013))*x+(-7.8603790143461073e-013))*x+(1.293779898029849e-013))*x+(1.7119639039719911e-013))*x+(9.3897112307672602e-014))*x+(-4.5961486931182325e-012))*x+(1.7000699574961273e-010))*x+(-6.5060426823893248e-009))*x+(2.6152940433683678e-007))*x+(-1.168159256531521e-005))*x+(0.00078266650834777924));
		break;
	case 34:
		rts[0] = (((((((((((((4.3579954459952806e-012))*x+(-6.2527760746888816e-013))*x+(-3.1192826099868394e-012))*x+(3.5763984366591711e-013))*x+(7.3600385045817041e-013))*x+(3.3257100776988105e-012))*x+(-1.1667147803429145e-010))*x+(3.9997210821152143e-009))*x+(-1.3723090368407412e-007))*x+(4.7083763931284389e-006))*x+(-0.000161543646573171))*x+(0.0055425361523835587));
		rts[1] = (((((((((((((6.7908937732378633e-011))*x+(-1.6674069532503684e-012))*x+(-4.1078844030077257e-011))*x+(8.5265128291212022e-013))*x+(7.0106883261663208e-012))*x+(4.4377538680843522e-011))*x+(-1.4559731198460211e-009))*x+(4.7614797068125839e-008))*x+(-1.5577563267088479e-006))*x+(5.0962854729305153e-005))*x+(-0.0016672758756053176))*x+(0.054545776539564321));
		rts[2] = (((((((((((((2.1221543041368324e-010))*x+(6.0632980118195212e-013))*x+(-1.2588922497040281e-010))*x+(-2.1221543041368323e-012))*x+(1.3490838076298434e-011))*x+(3.2330405019820313e-010))*x+(-9.3391199958621947e-009))*x+(2.7056015235634356e-007))*x+(-7.8394492800855816e-006))*x+(0.00022714561534225203))*x+(-0.0065814670542240234))*x+(0.19069574771311149));
		wts[0] = (((((((((((((8.6098831767837198e-011))*x+(-1.0307606620093186e-011))*x+(-4.9946417372363307e-011))*x+(5.0780120848988483e-012))*x+(8.8012560202817732e-012))*x+(1.580010196751876e-011))*x+(-6.2162216115287572e-010))*x+(2.3811290716935218e-008))*x+(-9.3885523324196052e-007))*x+(3.8868657881061891e-005))*x+(-0.0017879584683502061))*x+(0.12336913505079719));
		wts[1] = (((((((((((((9.0949470177292824e-012))*x+(3.9411437076826888e-012))*x+(-2.6905884927449128e-012))*x+(-2.5958494613102325e-012))*x+(-6.3475151061235603e-013))*x+(4.1768070483764551e-012))*x+(-1.3444460359816426e-010))*x+(5.1614905682839654e-009))*x+(-2.0350338696591605e-007))*x+(8.4249936043029328e-006))*x+(-0.00038754952320147899))*x+(0.026740916449692544));
		wts[2] = (((((((((((((1.2363443602225743e-012))*x+(-1.4921397450962104e-013))*x+(-8.0735418350741384e-013))*x+(9.0002079862946019e-014))*x+(1.8999616694751845e-013))*x+(8.4478720315435866e-014))*x+(-3.9095127598217277e-012))*x+(1.4889319753981961e-010))*x+(-5.8694011211609526e-009))*x+(2.4298733692895496e-007))*x+(-1.11773940297814e-005))*x+(0.0007712401046916247));
		break;
	case 35:
		rts[0] = (((((((((((((3.8274568699610727e-012))*x+(-2.0084674664152163e-012))*x+(-1.9018860560512012e-012))*x+(1.153447707717229e-012))*x+(1.6401694817128976e-013))*x+(2.5558814324237273e-012))*x+(-9.8109085670354076e-011))*x+(3.4645618411192434e-009))*x+(-1.2233312281055561e-007))*x+(4.3195652089170209e-006))*x+(-0.00015252315079238913))*x+(0.0053855675377405448));
		rts[1] = (((((((((((((6.972792713592449e-011))*x+(-3.0316490059097605e-012))*x+(-4.3921014973117657e-011))*x+(2.0084674664152163e-012))*x+(8.5217758775494677e-012))*x+(3.5581611731079952e-011))*x+(-1.2156819254964071e-009))*x+(4.096043223119257e-008))*x+(-1.381006414437798e-006))*x+(4.6561360758858486e-005))*x+(-0.0015698399950323902))*x+(0.052927951964960689));
		rts[2] = (((((((((((((2.3768128206332523e-010))*x+(1.6370904631912708e-011))*x+(-1.4703497678662339e-010))*x+(-1.0762353970979651e-011))*x+(2.2585785094027717e-011))*x+(2.5678303927634261e-010))*x+(-7.6202096484697287e-009))*x+(2.2834205607817162e-007))*x+(-6.8445071766583734e-006))*x+(0.00020516186457270971))*x+(-0.0061496567591649799))*x+(0.18433384835923022));
		wts[0] = (((((((((((((9.943808739384015e-011))*x+(-9.0949470177292824e-012))*x+(-6.1087727469081671e-011))*x+(6.3664629124104977e-012))*x+(1.2448708730516952e-011))*x+(1.2110016693137974e-011))*x+(-5.3182761898066622e-010))*x+(2.0938585384063419e-008))*x+(-8.4950619527734961e-007))*x+(3.6188987184724665e-005))*x+(-0.00171294548275133))*x+(0.12161912959133177));
		wts[1] = (((((((((((((5.1689615550761417e-011))*x+(6.8212102632969618e-012))*x+(-3.3717621287602619e-011))*x+(-4.5948430245819809e-012))*x+(7.6999147798536179e-012))*x+(4.0530541885649045e-012))*x+(-1.1583064137473306e-010))*x+(4.5385481299102058e-009))*x+(-1.8413559765145801e-007))*x+(7.8441577110894643e-006))*x+(-0.0003712900524975234))*x+(0.026361593447076753));
		wts[2] = (((((((((((((9.3317945963159811e-013))*x+(-1.4447702293788703e-013))*x+(-6.0721797960165225e-013))*x+(7.0166095156309893e-014))*x+(1.4262665123017843e-013))*x+(7.6873692596753543e-014))*x+(-3.3365544123883004e-012))*x+(1.3091110718603063e-010))*x+(-5.3107422681864195e-009))*x+(2.2623509065323286e-007))*x+(-1.0708450837124435e-005))*x+(0.00076029997370034093));
		break;
	case 36:
		rts[0] = (((((((((((((-3.2969182939268649e-012))*x+(2.2737367544323206e-013))*x+(2.7403264842481194e-012))*x+(-2.2737367544323206e-013))*x+(-8.7100697025258944e-013))*x+(2.3594459719333827e-012))*x+(-8.2880489508478178e-011))*x+(3.0130279937701232e-009))*x+(-1.0940316543956347e-007))*x+(3.9724120487501001e-006))*x+(-0.00014423763599484966))*x+(0.005237244988168523));
		rts[1] = (((((((((((((9.3677954282611609e-011))*x+(-7.8822874153653775e-012))*x+(-6.0083493735874072e-011))*x+(5.1348555037596571e-012))*x+(1.2818190953112207e-011))*x+(2.8206178133890109e-011))*x+(-1.0207583667209974e-009))*x+(3.5391377236256481e-008))*x+(-1.2286284676541839e-006))*x+(4.2652474122698944e-005))*x+(-0.0014807023165783388))*x+(0.051403332104782248));
		rts[2] = (((((((((((((2.4131926087041694e-010))*x+(-1.8796223836640515e-011))*x+(-1.537803958247726e-010))*x+(1.0307606620093184e-011))*x+(2.7682744985213503e-011))*x+(2.0021910055826686e-010))*x+(-6.2593423777457247e-009))*x+(1.9378768782255901e-007))*x+(-6.0025140882769001e-006))*x+(0.00018592586116162696))*x+(-0.0057589898033841812))*x+(0.17838272992793655));
		wts[0] = (((((((((((((1.8068628075222173e-010))*x+(-8.4886172165473291e-012))*x+(-1.1649111305208254e-010))*x+(4.8506384094556162e-012))*x+(2.6365872448271447e-011))*x+(1.059656066596896e-011))*x+(-4.5816476538599693e-010))*x+(1.8478030661128741e-008))*x+(-7.7079852887444278e-007))*x+(3.3760989234872987e-005))*x+(-0.001643034847606964))*x+(0.11994154401051882));
		wts[1] = (((((((((((((3.7137700322394565e-011))*x+(2.4253192047278085e-012))*x+(-2.3523701505231049e-011))*x+(-1.8853067255501324e-012))*x+(4.978536101892435e-012))*x+(2.9973061070146891e-012))*x+(-9.916293712090389e-011))*x+(4.0052029100697455e-009))*x+(-1.6707496180295986e-007))*x+(7.3178749643021401e-006))*x+(-0.00035613654744015495))*x+(0.025997967843131038));
		wts[2] = (((((((((((((1.3737159558028603e-013))*x+(7.3422749361877011e-014))*x+(1.2138438402568382e-014))*x+(-5.0034050976440378e-014))*x+(-4.0782192437897421e-014))*x+(8.3979119954354532e-014))*x+(-2.8394242975367709e-012))*x+(1.1551977777135569e-010))*x+(-4.8186644944035505e-009))*x+(2.1105636347081792e-007))*x+(-1.0271405344275096e-005))*x+(0.00074981257488484967));
		break;
	case 37:
		rts[0] = (((((((((((((9.8907548817805946e-012))*x+(-8.1475567033824815e-013))*x+(-6.610415918354799e-012))*x+(4.8316906031686803e-013))*x+(1.547798926064085e-012))*x+(1.7899015603006772e-012))*x+(-7.0666185865893752e-011))*x+(2.6303362728648709e-009))*x+(-9.8137209602356765e-008))*x+(3.6614839939560239e-006))*x+(-0.00013660937084671187))*x+(0.0050968732933425326));
		rts[1] = (((((((((((((5.7904496012876429e-011))*x+(-1.5158245029548803e-012))*x+(-3.6777692002942779e-011))*x+(7.3896444519050409e-013))*x+(7.489120434911456e-012))*x+(2.3972527666652845e-011))*x+(-8.6048642285637312e-010))*x+(3.0706490979544768e-008))*x+(-1.0966989443204436e-006))*x+(3.9169165039899347e-005))*x+(-0.0013989466155969502))*x+(0.049964088034175742));
		rts[2] = (((((((((((((2.1827872842550278e-010))*x+(-6.0632980118195212e-013))*x+(-1.3490838076298436e-010))*x+(-4.5474735088646412e-013))*x+(2.3457384183226775e-011))*x+(1.6216716858252767e-010))*x+(-5.1726954571525612e-009))*x+(1.6532145163949963e-007))*x+(-5.2861039879411233e-006))*x+(0.00016902137976636716))*x+(-0.0054044005867907533))*x+(0.17280385119850569));
		wts[0] = (((((((((((((1.2126596023639041e-010))*x+(3.0316490059097606e-013))*x+(-7.5639642697448523e-011))*x+(-1.8568850161197284e-012))*x+(1.6020370215604391e-011))*x+(1.0462741784067474e-011))*x+(-3.9403798742417473e-010))*x+(1.636173167322378e-008))*x+(-7.0122367505180217e-007))*x+(3.15550709670126e-005))*x+(-0.001577753564392069))*x+(0.1183315173870708));
		wts[1] = (((((((((((((2.1524707941959299e-011))*x+(2.8042753304665285e-012))*x+(-1.1577109641317898e-011))*x+(-1.7526720815415802e-012))*x+(1.726618847897043e-012))*x+(2.4937089430447181e-012))*x+(-8.5138488851536437e-011))*x+(3.546500981777001e-009))*x+(-1.5199409136394207e-007))*x+(6.83972990845813e-006))*x+(-0.00034198648074318117))*x+(0.025648986004600586));
		wts[2] = (((((((((((((9.4739031434680011e-013))*x+(3.5763984366591706e-013))*x+(-5.3527552760594211e-013))*x+(-2.4217664910490078e-013))*x+(9.5257135512838419e-014))*x+(1.1691573635156752e-013))*x+(-2.4598055074302274e-012))*x+(1.0228329641592815e-010))*x+(-4.3837007270702832e-009))*x+(1.9726604427290482e-007))*x+(-9.8633003527899672e-006))*x+(0.00073974751998203141));
		break;
	case 38:
		rts[0] = (((((((((((((4.7748471843078732e-012))*x+(-5.6843418860808015e-013))*x+(-2.5295321393059567e-012))*x+(4.0500935938325711e-013))*x+(3.3661962106634746e-013))*x+(1.4663825709249068e-012))*x+(-6.0156879477801795e-011))*x+(2.3045042355877379e-009))*x+(-8.8284806818115597e-008))*x+(3.3821766374462583e-006))*x+(-0.00012957063469795421))*x+(0.0049638298309426891));
		rts[1] = (((((((((((((6.7908937732378633e-011))*x+(1.3642420526593924e-012))*x+(-4.3200998334214085e-011))*x+(-1.1747639897900322e-012))*x+(9.1044209208727498e-012))*x+(2.0174084625068641e-011))*x+(-7.2936442071143881e-010))*x+(2.6746459343603608e-008))*x+(-9.8201159337563105e-007))*x+(3.6055057034636386e-005))*x+(-0.0013237797153407441))*x+(0.048603243754808956));
		rts[2] = (((((((((((((1.8796223836640516e-010))*x+(-7.2759576141834259e-012))*x+(-1.1679427795267353e-010))*x+(4.0169349328304333e-012))*x+(2.1297334266516067e-011))*x+(1.2963141671207265e-010))*x+(-4.3003050009815516e-009))*x+(1.417287217956679e-007))*x+(-4.6734560306682651e-006))*x+(0.00015410561676953982))*x+(-0.0050815797690392942))*x+(0.16756334619540536));
		wts[0] = (((((((((((((1.4673181188603241e-010))*x+(2.7284841053187847e-012))*x+(-9.2237921004804464e-011))*x+(-2.7284841053187847e-012))*x+(2.0018357342147887e-011))*x+(8.9611281358277958e-012))*x+(-3.4155878125829986e-010))*x+(1.4534401386138521e-008))*x+(-6.3951902605034283e-007))*x+(2.9545783380662456e-005))*x+(-0.0015166835535591443))*x+(0.11678463364848364));
		wts[1] = (((((((((((((2.4253192047278084e-011))*x+(0))*x+(-1.6143530956469476e-011))*x+(-5.5896028546461208e-013))*x+(3.8700894341066787e-012))*x+(2.0534685063466895e-012))*x+(-7.4064014180900501e-011))*x+(3.1503932055680175e-009))*x+(-1.3861919155126284e-007))*x+(6.4042059119279182e-006))*x+(-0.00032874923045303137))*x+(0.025313690723139708));
		wts[2] = (((((((((((((1.6674069532503684e-012))*x+(-7.3422749361877011e-014))*x+(-1.0705510552118842e-012))*x+(4.7665575190573379e-014))*x+(2.3995620305565047e-013))*x+(4.1624111564904823e-014))*x+(-2.1464219290834304e-012))*x+(9.0863695040299662e-011))*x+(-3.9979472325294783e-009))*x+(1.8470499208616317e-007))*x+(-9.4815221377482053e-006))*x+(0.00073007720186481467));
		break;
	case 39:
		rts[0] = (((((((((((((3.9032480951088165e-012))*x+(-5.4948638232114411e-013))*x+(-2.1055749736357634e-012))*x+(3.1974423109204503e-013))*x+(3.2033635003851175e-013))*x+(1.2475206053371342e-012))*x+(-5.1553159889176456e-011))*x+(2.0259184422647771e-009))*x+(-7.9638344325944993e-008))*x+(3.1305703652905032e-006))*x+(-0.00012306220949020332))*x+(0.0048375553339474681));
		rts[1] = (((((((((((((8.1854523159563541e-011))*x+(-6.0632980118195212e-013))*x+(-5.240963218966499e-011))*x+(4.5474735088646407e-013))*x+(1.1382894626876805e-011))*x+(1.6316429688837765e-011))*x+(-6.2110035633130179e-010))*x+(2.3383804966433292e-008))*x+(-8.8193168237826747e-007))*x+(3.326250302562727e-005))*x+(-0.0012545121771723219))*x+(0.047314563122211252));
		rts[2] = (((((((((((((2.1585340922077495e-010))*x+(-6.6696278130014735e-012))*x+(-1.3627262281564373e-010))*x+(4.0169349328304325e-012))*x+(2.679219808972751e-011))*x+(1.0497795225698306e-010))*x+(-3.595384730677627e-009))*x+(1.2206299526695827e-007))*x+(-4.1470473685079057e-006))*x+(0.00014089451490204016))*x+(-0.0047868427242780008))*x+(0.16263133614411912));
		wts[0] = (((((((((((((1.5582675890376169e-010))*x+(-6.0632980118195212e-013))*x+(-9.4397970921515168e-011))*x+(-1.8947806286936008e-013))*x+(1.9146758252948829e-011))*x+(7.0367415598108591e-012))*x+(-2.9652443463608813e-010))*x+(1.2950479799656023e-008))*x+(-5.8462344292483271e-007))*x+(2.7711152939100904e-005))*x+(-0.0014594540576136322))*x+(0.1152968705618664));
		wts[1] = (((((((((((((2.7284841053187847e-011))*x+(-2.2737367544323206e-013))*x+(-1.8265685260606308e-011))*x+(-1.7053025658242404e-013))*x+(4.2372031809160644e-012))*x+(1.60789899913046e-012))*x+(-6.4358888588837246e-011))*x+(2.8070762381204872e-009))*x+(-1.2672025381799121e-007))*x+(6.0065399086680713e-006))*x+(-0.00031634443249468669))*x+(0.024991210157894503));
		wts[2] = (((((((((((((-8.5265128291212022e-014))*x+(-1.1605531350748302e-013))*x+(1.2256862191861728e-013))*x+(5.447494307494101e-014))*x+(-5.3808809260165922e-014))*x+(3.487025483176845e-014))*x+(-1.835672817455484e-012))*x+(8.0960836414586014e-011))*x+(-3.6547665627391364e-009))*x+(1.7323582029527085e-007))*x+(-9.1237528698036215e-006))*x+(0.00072077647555974492));
		break;
	case 40:
		rts[0] = (((((((((((((5.6085506609330569e-012))*x+(8.7159908919905616e-013))*x+(-3.2637596329247267e-012))*x+(-5.4948638232114411e-013))*x+(5.9596771961878403e-013))*x+(1.2182847323553385e-012))*x+(-4.4365677798197112e-011))*x+(1.7867733403953421e-009))*x+(-7.2024960969900104e-008))*x+(2.9033144328532989e-006))*x+(-0.00011703213018294391))*x+(0.0047175460321337119));
		rts[1] = (((((((((((((4.1230426480372742e-011))*x+(-1.6674069532503684e-012))*x+(-2.4177400822130341e-011))*x+(1.0421293457814802e-012))*x+(4.3958910585691521e-012))*x+(1.3457087296349831e-011))*x+(-5.3025613529674343e-010))*x+(2.0515892762418275e-008))*x+(-7.9428244344666621e-007))*x+(3.0751048318032597e-005))*x+(-0.0011905424354602726))*x+(0.046092454296147799));
		rts[2] = (((((((((((((1.8553691916167736e-010))*x+(-3.0316490059097605e-012))*x+(-1.146721236485367e-010))*x+(8.3370347662518408e-013))*x+(2.2273146290293276e-011))*x+(8.6394891241070569e-011))*x+(-3.0209988584791367e-009))*x+(1.0558248764169775e-007))*x+(-3.6927122653943969e-006))*x+(0.00012915134596897895))*x+(-0.0045170239354151856))*x+(0.1579813594602093));
		wts[0] = (((((((((((((2.0190782379359007e-010))*x+(4.2443086082736646e-012))*x+(-1.2713978018534058e-010))*x+(-4.2064129956997923e-012))*x+(2.8004857692091416e-011))*x+(7.1977979132498149e-012))*x+(-2.5975384806050289e-010))*x+(1.1572296010342598e-008))*x+(-5.3564052509188121e-007))*x+(2.6032134346422781e-005))*x+(-0.0014057352554518517))*x+(0.11386455569585704));
		wts[1] = (((((((((((((4.1685173831259207e-011))*x+(-2.5011104298755527e-012))*x+(-2.8469078946121346e-011))*x+(1.0705510552118844e-012))*x+(6.906475391588173e-012))*x+(1.15966495665513e-012))*x+(-5.6454211675808587e-011))*x+(2.5083921976568981e-009))*x+(-1.1610293408857257e-007))*x+(5.6426036552821579e-006))*x+(-0.0003047005962163123))*x+(0.02468074828963001));
		wts[2] = (((((((((((((1.7100395173959744e-012))*x+(-2.2026824808563106e-013))*x+(-1.0761761852033183e-012))*x+(1.3145040611561853e-013))*x+(2.2500519965736504e-013))*x+(1.0186296250935811e-014))*x+(-1.6242481896503829e-012))*x+(7.2347152574314677e-011))*x+(-3.3485492041945143e-009))*x+(1.6273945925235084e-007))*x+(-8.7879306590857872e-006))*x+(0.00071182238290177992));
		break;
	case 41:
		rts[0] = (((((((((((((3.1832314562052488e-012))*x+(2.0842586915629605e-013))*x+(-1.5395092608135505e-012))*x+(-1.8000415972589204e-013))*x+(1.4062824978585314e-013))*x+(9.8535994178898047e-013))*x+(-3.8248015865605112e-011))*x+(1.5807287423452721e-009))*x+(-6.5300017589956877e-008))*x+(2.6975329297110671e-006))*x+(-0.00011143464428512252))*x+(0.0046033469349527484));
		rts[1] = (((((((((((((6.3361464223513992e-011))*x+(-3.0316490059097605e-012))*x+(-3.9771445396278672e-011))*x+(1.4210854715202002e-012))*x+(8.3796673303974477e-012))*x+(1.1283418643870391e-011))*x+(-4.5548490904915673e-010))*x+(1.8059847839424492e-008))*x+(-7.1725620950461688e-007))*x+(2.8486195200294606e-005))*x+(-0.0011313436925321919))*x+(0.044931888625857473));
		rts[2] = (((((((((((((2.255546860396862e-010))*x+(1.2126596023639042e-012))*x+(-1.4642864698544145e-010))*x+(-2.4253192047278085e-012))*x+(3.1424936726883366e-011))*x+(7.1883240101063477e-011))*x+(-2.5521747678188453e-009))*x+(9.1701259326744834e-008))*x+(-3.2989267612082429e-006))*x+(0.00011867776056216174))*x+(-0.0042693916434141379))*x+(0.1535898968060285));
		wts[0] = (((((((((((((9.822542779147625e-011))*x+(-3.213547946264346e-011))*x+(-5.1159076974727213e-011))*x+(1.9629927313265697e-011))*x+(7.3328010330442339e-012))*x+(7.9817633983717948e-013))*x+(-2.2491075668540361e-010))*x+(1.0369847203151037e-008))*x+(-4.918104913135638e-007))*x+(2.4492160292016729e-005))*x+(-0.0013552328705203284))*x+(0.11248432825513112));
		wts[1] = (((((((((((((4.411049303598702e-011))*x+(2.1979455292845764e-012))*x+(-2.8848035071860068e-011))*x+(-1.4779288903810082e-012))*x+(6.7264712318622815e-012))*x+(1.4160524604752329e-012))*x+(-4.9424279483882096e-011))*x+(2.2476147979825592e-009))*x+(-1.066025051635333e-007))*x+(5.3088060730614719e-006))*x+(-0.00029375393553806282))*x+(0.024381576647996152));
		wts[2] = (((((((((((((-2.9842794901924208e-013))*x+(-8.0528176719478013e-014))*x+(3.6267285471088445e-013))*x+(5.2698586235540753e-014))*x+(-1.3877787807814457e-013))*x+(1.7671049808617074e-014))*x+(-1.3845649164216192e-012))*x+(6.4826371123001992e-011))*x+(-3.074546424238512e-009))*x+(1.5311233532961112e-007))*x+(-8.4722158328655192e-006))*x+(0.00070319391392587526));
		break;
	case 42:
		rts[0] = (((((((((((((9.3602163057463859e-012))*x+(2.4632148173016805e-013))*x+(-6.0040861171728466e-012))*x+(-1.3263464400855202e-013))*x+(1.3521036142568239e-012))*x+(8.0668804969263864e-013))*x+(-3.3281756979993325e-011))*x+(1.4025550628312307e-009))*x+(-5.9341942505152421e-008))*x+(2.5107480962768942e-006))*x+(-0.00010622934144139704))*x+(0.0044945460669589942));
		rts[1] = (((((((((((((5.3963352305193738e-011))*x+(1.5158245029548803e-013))*x+(-3.3613408353024468e-011))*x+(-3.6000831945178403e-013))*x+(7.0154252777380553e-012))*x+(9.7717389735407778e-012))*x+(-3.9232424716336328e-010))*x+(1.594831933182661e-008))*x+(-6.4934481274388678e-007))*x+(2.643840420577202e-005))*x+(-0.0010764530383326574))*x+(0.043828331488583977));
		rts[2] = (((((((((((((1.3581787546475727e-010))*x+(-9.701276818911234e-012))*x+(-7.7003884750107916e-011))*x+(4.7748471843078732e-012))*x+(1.2259230667647593e-011))*x+(5.7809756981441745e-011))*x+(-2.163098145047115e-009))*x+(7.9953714759994909e-008))*x+(-2.9562606476130071e-006))*x+(0.00010930672084745))*x+(-0.004041578430750657))*x+(0.14943597321760124));
		wts[0] = (((((((((((((2.4253192047278083e-010))*x+(-6.063298011819521e-012))*x+(-1.5734258340671656e-010))*x+(3.7137700322394567e-012))*x+(3.6057675364039213e-011))*x+(3.4485007442223532e-012))*x+(-2.0075674456165871e-010))*x+(9.3159539342006318e-009))*x+(-4.5248554636501126e-007))*x+(2.3076769381273156e-005))*x+(-0.001307683598626763))*x+(0.11115310588394009));
		wts[1] = (((((((((((((2.319211489520967e-011))*x+(-7.5791225147744009e-012))*x+(-1.3708737848598201e-011))*x+(4.7085298623035962e-012))*x+(2.5934809855243657e-012))*x+(-1.1487107561454946e-013))*x+(-4.2912821444455553e-011))*x+(2.0193629731342826e-009))*x+(-9.8078680642321725e-008))*x+(5.0020125504507407e-006))*x+(-0.00028344737784258549))*x+(0.024093027115950235));
		wts[2] = (((((((((((((2.0700478368477584e-012))*x+(3.7895612573872008e-014))*x+(-1.3852622752589619e-012))*x+(-1.1842378929335002e-014))*x+(3.3410311554386374e-013))*x+(2.5646151868841113e-014))*x+(-1.2683153138848267e-012))*x+(5.8238631509925184e-011))*x+(-2.8287053600081079e-009))*x+(1.4426404180819272e-007))*x+(-8.1749623461041199e-006))*x+(0.0006948717993325342));
		break;
	case 43:
		rts[0] = (((((((((((((5.5327594357853132e-012))*x+(-9.4739031434680016e-014))*x+(-3.4153420832202142e-012))*x+(4.2632564145606005e-014))*x+(7.111348547065668e-013))*x+(6.5969452123226802e-013))*x+(-2.887480995047061e-011))*x+(1.2479422865456038e-009))*x+(-5.4048170056395867e-008))*x+(2.3408174736648407e-006))*x+(-0.00010138042203810811))*x+(0.004390769501839485));
		rts[1] = (((((((((((((5.2750692702829838e-011))*x+(-7.5791225147744013e-013))*x+(-3.2249166300365083e-011))*x+(2.46321481730168e-013))*x+(6.5275192658494542e-012))*x+(8.1256483023632118e-012))*x+(-3.3916558450641782e-010))*x+(1.4126249281432022e-008))*x+(-5.8928401964567867e-007))*x+(2.4582282250627807e-005))*x+(-0.0010254623734478057))*x+(0.042777683075660905));
		rts[2] = (((((((((((((1.8189894035458565e-010))*x+(-1.8189894035458565e-012))*x+(-1.1308050792043407e-010))*x+(3.7895612573872017e-013))*x+(2.2936319510336034e-011))*x+(4.8655598069065789e-011))*x+(-1.8444730187638925e-009))*x+(6.9966441825404971e-008))*x+(-2.6569530975721158e-006))*x+(0.00010089688243879642))*x+(-0.0038315244279713508))*x+(0.14550082309533893));
		wts[0] = (((((((((((((1.3399888606121141e-010))*x+(-3.0316490059097606e-013))*x+(-8.3635616950535522e-011))*x+(-4.5474735088646407e-013))*x+(1.7934098650584929e-011))*x+(3.9328540424321545e-012))*x+(-1.751134052578133e-010))*x+(8.3901556813259504e-009))*x+(-4.1711292617097051e-007))*x+(2.1773296810555693e-005))*x+(-0.0012628512148443499))*x+(0.10986805569145501));
		wts[1] = (((((((((((((2.986174270821114e-011))*x+(-4.5474735088646412e-013))*x+(-1.867306309577543e-011))*x+(1.4210854715202004e-013))*x+(4.0193034086162998e-012))*x+(7.9995269667657943e-013))*x+(-3.797025656856097e-011))*x+(1.8186156284608992e-009))*x+(-9.0411445675027873e-008))*x+(4.7194779333574926e-006))*x+(-0.00027372972010706329))*x+(0.023814485649313596));
		wts[2] = (((((((((((((8.6212518605558819e-013))*x+(0))*x+(-5.3942036023120932e-013))*x+(-4.1448326252672506e-015))*x+(1.1605531350748302e-013))*x+(2.4868995751603503e-014))*x+(-1.0950846710914655e-012))*x+(5.2450909356534695e-011))*x+(-2.6075745363588385e-009))*x+(1.3611540416753193e-007))*x+(-7.8946934408016497e-006))*x+(0.00068683832934972398));
		break;
	case 44:
		rts[0] = (((((((((((((4.2443086082736646e-012))*x+(-1.3263464400855202e-013))*x+(-2.5390060424494245e-012))*x+(6.3948846218409004e-014))*x+(4.9560355819266988e-013))*x+(5.5814612191322033e-013))*x+(-2.5162982808524248e-011))*x+(1.1133366913570104e-009))*x+(-4.9331757593270201e-008))*x+(2.1858821357293697e-006))*x+(-9.6856080021231444e-005))*x+(0.0042916770688816146));
		rts[1] = (((((((((((((4.6687394691010312e-011))*x+(3.0316490059097606e-013))*x+(-2.8232231367534645e-011))*x+(-3.7895612573872007e-013))*x+(5.6227615156482589e-012))*x+(7.0177937535239234e-012))*x+(-2.9420954561487633e-010))*x+(1.2548338368389977e-008))*x+(-5.360095268099514e-007))*x+(2.2895919181910768e-005))*x+(-0.00097801080179276616))*x+(0.041776227495984933));
		rts[2] = (((((((((((((1.7947362114985782e-010))*x+(-7.2759576141834259e-012))*x+(-1.1110993606659272e-010))*x+(3.7895612573872013e-012))*x+(2.2652102416031994e-011))*x+(3.9837762718282946e-011))*x+(-1.5783753563406813e-009))*x+(6.1439549151979606e-008))*x+(-2.3945842300143734e-006))*x+(9.3328099224687655e-005))*x+(-0.0036374305864422737))*x+(0.14176760676796069));
		wts[0] = (((((((((((((1.3339255626002947e-010))*x+(-1.5158245029548803e-012))*x+(-8.3218765212222934e-011))*x+(3.4106051316484799e-013))*x+(1.7867781328580652e-011))*x+(3.2412591129589901e-012))*x+(-1.5471179892756481e-010))*x+(7.5744742330149003e-009))*x+(-3.8521749801123661e-007))*x+(2.057061650517315e-005))*x+(-0.0012205232458499826))*x+(0.1086265688806472));
		wts[1] = (((((((((((((2.8952248006438214e-011))*x+(-7.5791225147744013e-013))*x+(-1.8009889875732672e-011))*x+(3.3158661002138002e-013))*x+(3.8535101036056095e-012))*x+(6.4718600848815789e-013))*x+(-3.3531510901241284e-011))*x+(1.6418127598190797e-009))*x+(-8.3497942483801157e-008))*x+(4.4587905779884989e-006))*x+(-0.00026455490761186735))*x+(0.023545386777455664));
		wts[2] = (((((((((((((9.0949470177292824e-013))*x+(-7.1054273576010019e-015))*x+(-5.7435537807274762e-013))*x+(0))*x+(1.2589929099249275e-013))*x+(2.0862941004414399e-014))*x+(-9.6882224465133504e-013))*x+(4.7351635344231959e-011))*x+(-2.408180728904104e-009))*x+(1.28596868175427e-007))*x+(-7.6300808441208093e-006))*x+(0.00067907719512669187));
		break;
	case 45:
		rts[0] = (((((((((((((4.964325247177233e-012))*x+(-3.7895612573872008e-014))*x+(-3.0955978521281695e-012))*x+(-4.7369515717340033e-015))*x+(6.5991656583719305e-013))*x+(4.9397523108988628e-013))*x+(-2.2035493800013718e-011))*x+(9.9578118898750257e-010))*x+(-4.5118763261978161e-008))*x+(2.0443238637173297e-006))*x+(-9.2627979994031122e-005))*x+(0.0041969586280028344));
		rts[1] = (((((((((((((4.4565240386873484e-011))*x+(1.9705718538413444e-012))*x+(-2.7152206409179296e-011))*x+(-1.5347723092418162e-012))*x+(5.50433772635491e-012))*x+(6.2711317620293504e-012))*x+(-2.5612956200404819e-010))*x+(1.1177257563943499e-008))*x+(-4.8862163272433978e-007))*x+(2.1360342955460687e-005))*x+(-0.00093377822726260459))*x+(0.040820588865151164));
		rts[2] = (((((((((((((1.673470251262188e-010))*x+(6.063298011819521e-012))*x+(-1.0413714335300028e-010))*x+(-4.3200998334214083e-012))*x+(2.148681232938543e-011))*x+(3.4958702599396929e-011))*x+(-1.3559814012372347e-009))*x+(5.4129584962462708e-008))*x+(-2.1638160601448555e-006))*x+(8.6497805184400825e-005))*x+(-0.0034577200291065363))*x+(0.13822116959902256));
		wts[0] = (((((((((((((1.3278622645884752e-010))*x+(-3.0316490059097606e-013))*x+(-8.340824327509229e-011))*x+(-3.7895612573872012e-013))*x+(1.8142524519741226e-011))*x+(2.9712528733701524e-012))*x+(-1.3715710049192845e-010))*x+(6.8536224103373416e-009))*x+(-3.5639052060424764e-007))*x+(1.9458924973935383e-005))*x+(-0.001180508114925164))*x+(0.1074262384581639));
		wts[1] = (((((((((((((2.6981676152596869e-011))*x+(-8.3370347662518418e-013))*x+(-1.6806704176512234e-011))*x+(3.694822225952521e-013))*x+(3.6000831945178407e-012))*x+(5.527430365267112e-013))*x+(-2.9690398288077326e-011))*x+(1.4855664476343122e-009))*x+(-7.7249543544340605e-008))*x+(4.2178255235681321e-006))*x+(-0.00025588141507419757))*x+(0.02328520877174908));
		wts[2] = (((((((((((((9.3791641120333225e-013))*x+(-1.6579330501069002e-014))*x+(-5.9507954119908391e-013))*x+(5.3290705182007498e-015))*x+(1.3174646558885192e-013))*x+(1.725471617438264e-014))*x+(-8.5943058225623759e-013))*x+(4.2845390429979702e-011))*x+(-2.2279693447496232e-009))*x+(1.2164714698648769e-007))*x+(-7.3799269163017446e-006))*x+(0.00067157334938319996));
		break;
	case 46:
		rts[0] = (((((((((((((5.722237498654673e-012))*x+(-2.0842586915629605e-013))*x+(-3.6356103313058457e-012))*x+(1.0421293457814802e-013))*x+(7.9847239931041248e-013))*x+(4.0093854162629822e-013))*x+(-1.9351751682587327e-011))*x+(8.9281423920617442e-010))*x+(-4.1346063697188698e-008))*x+(1.9147295520849719e-006))*x+(-8.8670812478542916e-005))*x+(0.004106330827387818));
		rts[1] = (((((((((((((5.0628538398693003e-011))*x+(-9.0949470177292824e-013))*x+(-3.132072379230521e-011))*x+(3.0316490059097611e-013))*x+(6.5369931689929201e-012))*x+(4.9974839081793708e-012))*x+(-2.2378299213698938e-010))*x+(9.9821377830266994e-009))*x+(-4.4635677179845806e-007))*x+(1.9959070044946646e-005))*x+(-0.0008924799412901726))*x+(0.039907693286541333));
		rts[2] = (((((((((((((1.7826096154749393e-010))*x+(-1.2126596023639042e-012))*x+(-1.1164047464262694e-010))*x+(-3.7895612573872017e-013))*x+(2.3627914439809199e-011))*x+(2.8900141539149139e-011))*x+(-1.1696572599362298e-009))*x+(4.783898995460352e-008))*x+(-1.9601892901991804e-006))*x+(8.0318084935156645e-005))*x+(-0.0032910059213048801))*x+(0.13484783636763215));
		wts[0] = (((((((((((((1.1884064103166261e-010))*x+(6.0632980118195212e-013))*x+(-7.3214323492720723e-011))*x+(-9.0949470177292814e-013))*x+(1.549930554271365e-011))*x+(2.7071678232459817e-012))*x+(-1.2158748082432189e-010))*x+(6.214878389698697e-009))*x+(-3.3027880819158634e-007))*x+(1.8429559419247399e-005))*x+(-0.0011426326838540957))*x+(0.10626483959841744));
		wts[1] = (((((((((((((2.5011104298755527e-011))*x+(-4.5474735088646412e-013))*x+(-1.5414040414422441e-011))*x+(1.5158245029548806e-013))*x+(3.2519172539953916e-012))*x+(5.1691984026547278e-013))*x+(-2.6341336519427234e-011))*x+(1.3471130137313971e-009))*x+(-7.1589689891460293e-008))*x+(3.9947050627537704e-006))*x+(-0.00024767171386464224))*x+(0.023033469389410009));
		wts[2] = (((((((((((((8.3844042819691822e-013))*x+(-9.473903143468002e-015))*x+(-5.2313708920337376e-013))*x+(1.4802973661668749e-015))*x+(1.1294668903853258e-013))*x+(1.5709655798445965e-014))*x+(-7.6176218111179129e-013))*x+(3.8852259372686625e-011))*x+(-2.0647324325533817e-009))*x+(1.1521208528549909e-007))*x+(-7.1431492866568534e-006))*x+(0.00066431288365895766));
		break;
	case 47:
		rts[0] = (((((((((((((5.6085506609330569e-012))*x+(-2.2737367544323206e-013))*x+(-3.4911333083679588e-012))*x+(1.1842378929335004e-013))*x+(7.4399745623547154e-013))*x+(3.3869203737898107e-013))*x+(-1.7023697266675221e-011))*x+(8.0236232472922586e-010))*x+(-3.7959577957787559e-008))*x+(1.795861507417525e-006))*x+(-8.4961914275879602e-005))*x+(0.0040195342723376715));
		rts[1] = (((((((((((((4.3049415883918599e-011))*x+(-9.0949470177292824e-013))*x+(-2.6299555126267173e-011))*x+(3.6000831945178413e-013))*x+(5.3930193644191604e-012))*x+(4.2490455598453983e-012))*x+(-1.9593186332637438e-010))*x+(8.9371060181993763e-009))*x+(-4.0856447855452949e-007))*x+(1.8677732815728744e-005))*x+(-0.00085386202995830238))*x+(0.039034735822304309));
		rts[2] = (((((((((((((1.6007106751203537e-010))*x+(6.0632980118195212e-013))*x+(-9.8831757592658206e-011))*x+(-9.8528592692067219e-013))*x+(2.0349943952169269e-011))*x+(2.4454512489076777e-011))*x+(-1.0119786490273932e-009))*x+(4.2405576827775342e-008))*x+(-1.7799618683422835e-006))*x+(7.4713289264995611e-005))*x+(-0.0031360646346447565))*x+(0.13163523504125971));
		wts[0] = (((((((((((((1.3399888606121141e-010))*x+(-1.8189894035458565e-012))*x+(-8.4090364301421986e-011))*x+(7.2001663890356826e-013))*x+(1.8341476485754051e-011))*x+(2.0345207000597534e-012))*x+(-1.086249608780084e-010))*x+(5.6474392569801539e-009))*x+(-3.0657616420515232e-007))*x+(1.747484415027626e-005))*x+(-0.0011067401293907955))*x+(0.10514031229209836));
		wts[1] = (((((((((((((2.8194335754960775e-011))*x+(7.5791225147744016e-014))*x+(-1.7754094490859036e-011))*x+(-1.5158245029548803e-013))*x+(3.8843002888218807e-012))*x+(5.1129471027403873e-013))*x+(-2.3536802136921626e-011))*x+(1.2241061127700919e-009))*x+(-6.6452015302457618e-008))*x+(3.7877654486644101e-006))*x+(-0.00023989181171015731))*x+(0.022789722112459877));
		wts[2] = (((((((((((((7.4843834833397216e-013))*x+(-1.1842378929335002e-014))*x+(-4.6599761086933234e-013))*x+(4.1448326252672506e-015))*x+(1.0029014655780579e-013))*x+(1.2869335227113273e-014))*x+(-6.7757142489336774e-013))*x+(3.5304868981992727e-011))*x+(-1.9165558721942941e-009))*x+(1.0924369859897024e-007))*x+(-6.9187675772631691e-006))*x+(0.00065728291983990729));
		break;
	case 48:
		rts[0] = (((((((((((((4.3200998334214091e-012))*x+(-5.6843418860808015e-014))*x+(-2.6811145896014446e-012))*x+(2.6053233644537009e-014))*x+(5.6517753440251306e-013))*x+(3.0590345071838477e-013))*x+(-1.5006736594121623e-011))*x+(7.2268563355848404e-010))*x+(-3.4912817501592253e-008))*x+(1.6866325612705999e-006))*x+(-8.1480943254512921e-005))*x+(0.0039363310457421388));
		rts[1] = (((((((((((((5.1234868199874953e-011))*x+(-7.5791225147744013e-013))*x+(-3.238180094437363e-011))*x+(2.46321481730168e-013))*x+(7.041478511382592e-012))*x+(3.6847562038625857e-012))*x+(-1.7232045420219794e-010))*x+(8.0206384496979873e-009))*x+(-3.7468860877391352e-007))*x+(1.7503769303874962e-005))*x+(-0.00081769746180564986))*x+(0.038199151706473325));
		rts[2] = (((((((((((((1.8311159995694953e-010))*x+(-5.4569682106375694e-012))*x+(-1.1512687099942316e-010))*x+(2.880066555614273e-012))*x+(2.4736361107594952e-011))*x+(1.9907038980212139e-011))*x+(-8.7939759178349653e-010))*x+(3.769620171567567e-008))*x+(-1.6199799418766443e-006))*x+(6.9618084021607241e-005))*x+(-0.0029918132301456424))*x+(0.12857214515284288));
		wts[0] = (((((((((((((1.1944697083284456e-010))*x+(0))*x+(-7.3934340131624283e-011))*x+(-4.926429634603361e-013))*x+(1.5679309702439543e-011))*x+(2.0368891758456207e-012))*x+(-9.6718040983508529e-011))*x+(5.1420145178819139e-009))*x+(-2.8501646854676527e-007))*x+(1.6587960354678504e-005))*x+(-0.0010726881028157715))*x+(0.10405074597312053));
		wts[1] = (((((((((((((2.6072181450823941e-011))*x+(0))*x+(-1.606773973132173e-011))*x+(-1.2316074086508402e-013))*x+(3.3845518980039433e-012))*x+(4.5001039931473008e-013))*x+(-2.0959234348083552e-011))*x+(1.1145576313727663e-009))*x+(-6.1778836555707388e-008))*x+(3.5955286669988222e-006))*x+(-0.0002325108537683899))*x+(0.022553552815533923));
		wts[2] = (((((((((((((7.4370139676223813e-013))*x+(-7.1054273576010019e-015))*x+(-4.5918824298496475e-013))*x+(5.9211894646675042e-016))*x+(9.6959477483930329e-014))*x+(1.2166193978184007e-014))*x+(-6.0446670816875303e-013))*x+(3.2145234390990041e-011))*x+(-1.7817757423568142e-009))*x+(1.0369935925254342e-007))*x+(-6.7058918974620473e-006))*x+(0.00065047151405382448));
		break;
	case 49:
		rts[0] = (((((((((((((4.3579954459952806e-012))*x+(-1.1368683772161603e-013))*x+(-2.6976939201025134e-012))*x+(5.0922229396140515e-014))*x+(5.6813812913484674e-013))*x+(2.623086932847703e-013))*x+(-1.3276204210062778e-011))*x+(6.5231790339718521e-010))*x+(-3.2165693427653928e-008))*x+(1.5860851383161373e-006))*x+(-7.8209598828796631e-005))*x+(0.003856502530259715));
		rts[1] = (((((((((((((5.0628538398693003e-011))*x+(-9.0949470177292824e-013))*x+(-3.1737575530617804e-011))*x+(3.7895612573872012e-013))*x+(6.8377895937980303e-012))*x+(3.1334934647020414e-012))*x+(-1.5180220043949552e-010))*x+(7.2146773000270051e-009))*x+(-3.4425208988534772e-007))*x+(1.6426163916116728e-005))*x+(-0.00078378274343420191))*x+(0.037398591177897851));
		rts[2] = (((((((((((((1.697723443309466e-010))*x+(-3.637978807091713e-012))*x+(-1.0671404500802356e-010))*x+(1.8947806286936006e-012))*x+(2.2945793413479497e-011))*x+(1.7057762609814137e-011))*x+(-7.6614152059543516e-010))*x+(3.3600615327126583e-008))*x+(-1.4775747819347389e-006))*x+(6.4975845799712203e-005))*x+(-0.0028572904840742978))*x+(0.12564836686565684));
		wts[0] = (((((((((((((1.2914824765175581e-010))*x+(-4.850638409455617e-012))*x+(-8.0149220593739301e-011))*x+(2.7284841053187843e-012))*x+(1.7128816883390147e-011))*x+(1.0373923942097463e-012))*x+(-8.6733139189239708e-011))*x+(4.6908856058773072e-009))*x+(-2.6536755938037315e-007))*x+(1.5762835300747732e-005))*x+(-0.0010403471299249721))*x+(0.10299436586255717));
		wts[1] = (((((((((((((2.8345918205256261e-011))*x+(-2.2737367544323206e-013))*x+(-1.7744620587715566e-011))*x+(7.5791225147744028e-014))*x+(3.8345622973186737e-012))*x+(3.4076445369161468e-013))*x+(-1.8815134635493298e-011))*x+(1.0167630071222789e-009))*x+(-5.7519829869031223e-008))*x+(3.4166784216779298e-006))*x+(-0.0002255007758167582))*x+(0.022324576805856627));
		wts[2] = (((((((((((((7.3896444519050419e-013))*x+(-2.1316282072803006e-014))*x+(-4.5474735088646412e-013))*x+(1.0066022089934753e-014))*x+(9.5627209854380142e-014))*x+(8.4654505627668186e-015))*x+(-5.4095154281933822e-013))*x+(2.9324749804363982e-011))*x+(-1.6589409617429978e-009))*x+(9.854110366222784e-008))*x+(-6.5037128414099838e-006))*x+(0.00064386757129966058));
		break;
	case 50:
		rts[0] = (((((((((((((5.1538033100465928e-012))*x+(-2.0842586915629605e-013))*x+(-3.2163901172073866e-012))*x+(1.0776564825694852e-013))*x+(6.8952251316053049e-013))*x+(2.1590137085543881e-013))*x+(-1.1786849274386668e-011))*x+(5.9001514784995379e-010))*x+(-2.9683529298903572e-008))*x+(1.4933735861229547e-006))*x+(-7.5131380936163726e-005))*x+(0.003779847490226649));
		rts[1] = (((((((((((((4.3655745685100555e-011))*x+(-1.8189894035458565e-012))*x+(-2.6830093702301383e-011))*x+(9.8528592692067219e-013))*x+(5.618024564076526e-012))*x+(2.5674277518798285e-012))*x+(-1.3397964219545125e-010))*x+(6.5039812054597706e-009))*x+(-3.1684426791504328e-007))*x+(1.5435229828988001e-005))*x+(-0.00075193505065598962))*x+(0.036630897412853872));
		rts[2] = (((((((((((((1.697723443309466e-010))*x+(-6.0632980118195212e-013))*x+(-1.0686562745831906e-010))*x+(3.7895612573871976e-014))*x+(2.3106849766918455e-011))*x+(1.494745068460664e-011))*x+(-6.6972975313698646e-010))*x+(3.002753127627026e-008))*x+(-1.3504791087637358e-006))*x+(6.0737336555862401e-005))*x+(-0.002731640833495546))*x+(0.12285460750603878));
		wts[0] = (((((((((((((1.3703053506712118e-010))*x+(-6.0632980118195212e-013))*x+(-8.5871458092393966e-011))*x+(-3.4106051316484809e-013))*x+(1.8682536998918899e-011))*x+(1.6555645743210334e-012))*x+(-7.8040388965897962e-011))*x+(4.2870447932349025e-009))*x+(-2.4742648228418907e-007))*x+(1.4994047764033123e-005))*x+(-0.0010095992159154924))*x+(0.10196952080744018));
		wts[1] = (((((((((((((3.0316490059097604e-011))*x+(-4.5474735088646412e-013))*x+(-1.8909910674362131e-011))*x+(1.1368683772161603e-013))*x+(4.0856207306205753e-012))*x+(3.238890637173123e-013))*x+(-1.6914321795032567e-011))*x+(9.2924186863759429e-010))*x+(-5.3631006857735031e-008))*x+(3.2500396321202825e-006))*x+(-0.00021883600185388684))*x+(0.02210243618723684));
		wts[2] = (((((((((((((9.0949470177292824e-013))*x+(-1.1842378929335002e-014))*x+(-5.7317114017981418e-013))*x+(3.2566542055671253e-015))*x+(1.2560323151925937e-013))*x+(9.1130806604648261e-015))*x+(-4.8873405322780162e-013))*x+(2.6800498163318902e-011))*x+(-1.5467825244021756e-009))*x+(9.3735041103233849e-008))*x+(-6.3114927665565827e-006))*x+(0.00063746076942200079));
		break;
	case 51:
		rts[0] = (((((((((((((4.0548305454043048e-012))*x+(0))*x+(-2.5508484213787597e-012))*x+(-2.4868995751603507e-014))*x+(5.5303909599994461e-013))*x+(2.1538326677728037e-013))*x+(-1.0469911974434846e-011))*x+(5.347150407638186e-010))*x+(-2.7436242837237484e-008))*x+(1.4077492059271872e-006))*x+(-7.2231381569992948e-005))*x+(0.0037061803778610904));
		rts[1] = (((((((((((((4.2139921182145671e-011))*x+(-1.0610771520684161e-012))*x+(-2.593954680681539e-011))*x+(5.3053857603420807e-013))*x+(5.4238095496354309e-012))*x+(2.3015663449162576e-012))*x+(-1.1863125296921831e-010))*x+(5.8756437493201466e-009))*x+(-2.9211057002431762e-007))*x+(1.4522425685191409e-005))*x+(-0.00072198975943955121))*x+(0.035894087120894501));
		rts[2] = (((((((((((((1.3703053506712118e-010))*x+(2.4253192047278085e-012))*x+(-8.4507216039734573e-011))*x+(-2.1979455292845764e-012))*x+(1.7507773009128869e-011))*x+(1.3386625141720288e-011))*x+(-5.8654266628839947e-010))*x+(2.6900820830159471e-008))*x+(-1.2367597091074896e-006))*x+(5.6859603792591689e-005))*x+(-0.002614100739124338))*x+(0.12018238290435154));
		wts[0] = (((((((((((((1.2005330063402653e-010))*x+(-6.0632980118195212e-013))*x+(-7.495752167111884e-011))*x+(-1.5158245029548801e-013))*x+(1.6124583150182541e-011))*x+(1.3950322378756634e-012))*x+(-6.9960925941359164e-011))*x+(3.9249844855741376e-009))*x+(-2.3101528673352689e-007))*x+(1.4276746975026382e-005))*x+(-0.00098033662548368291))*x+(0.10097467242480687));
		wts[1] = (((((((((((((2.379844469639162e-011))*x+(7.5791225147744016e-014))*x+(-1.4694023775518872e-011))*x+(-1.8947806286936003e-013))*x+(3.1003348036999033e-012))*x+(3.4431716737041523e-013))*x+(-1.5120978543355549e-011))*x+(8.5075653929086081e-010))*x+(-5.0073794455781272e-008))*x+(3.0945608697543572e-006))*x+(-0.00021249317967944243))*x+(0.021886797506982074));
		wts[2] = (((((((((((((7.2475359047530219e-013))*x+(-1.4210854715202004e-014))*x+(-4.4734586405562976e-013))*x+(5.0330110449673766e-015))*x+(9.4591001698063337e-014))*x+(7.6050277186823207e-015))*x+(-4.3658710905762155e-013))*x+(2.4537041380205217e-011))*x+(-1.4441882754060119e-009))*x+(8.9250847111231477e-008))*x+(-6.1285581674294733e-006))*x+(0.00063124149124524798));
		break;
	case 52:
		rts[0] = (((((((((((((4.6232647340123849e-012))*x+(-1.5158245029548803e-013))*x+(-2.8705926524708048e-012))*x+(6.6317322004276009e-014))*x+(6.1077069328045275e-013))*x+(1.7038222684580734e-013))*x+(-9.3330898565113768e-012))*x+(4.855233344998785e-010))*x+(-2.5397660341717567e-008))*x+(1.3285475276448436e-006))*x+(-6.9496103938053246e-005))*x+(0.0036353298337476062));
		rts[1] = (((((((((((((3.7895612573872008e-011))*x+(-9.0949470177292824e-013))*x+(-2.3097375863774989e-011))*x+(3.4106051316484809e-013))*x+(4.7558993780209367e-012))*x+(2.049915792667889e-012))*x+(-1.0525217734406547e-010))*x+(5.318761431283292e-009))*x+(-2.6974393016003051e-007))*x+(1.368020063007939e-005))*x+(-0.00069379831422929756))*x+(0.035186333436347403));
		rts[2] = (((((((((((((1.4551915228366852e-010))*x+(1.2126596023639042e-012))*x+(-9.0191557925815388e-011))*x+(-1.5916157281026244e-012))*x+(1.9052019221514154e-011))*x+(1.1510792319313623e-011))*x+(-5.1587238184917317e-010))*x+(2.4156827057216408e-008))*x+(-1.1347621524659957e-006))*x+(5.3305064005915164e-005))*x+(-0.0025039870583010828))*x+(0.11762393133751209));
		wts[0] = (((((((((((((1.1156468341747919e-010))*x+(-4.5474735088646412e-012))*x+(-6.9273179785038026e-011))*x+(2.4253192047278085e-012))*x+(1.4741393291236211e-011))*x+(6.477781274346246e-013))*x+(-6.2919743489449801e-011))*x+(3.599651095716657e-009))*x+(-2.1597748130671354e-007))*x+(1.3606583046133861e-005))*x+(-0.0009524608132245963))*x+(0.10000838538859756));
		wts[1] = (((((((((((((2.076679569048186e-011))*x+(-1.0610771520684161e-012))*x+(-1.2685556309103655e-011))*x+(5.5896028546461198e-013))*x+(2.6266396465265034e-012))*x+(1.3855583347321954e-013))*x+(-1.3580433074385685e-011))*x+(7.8024253724606751e-010))*x+(-4.6814270221925039e-008))*x+(2.9492992723266034e-006))*x+(-0.0002064509490526567))*x+(0.021677349650531887));
		wts[2] = (((((((((((((6.6791017161449417e-013))*x+(-3.3158661002138004e-014))*x+(-4.1477932199995848e-013))*x+(1.7763568394002501e-014))*x+(8.8114700721083253e-014))*x+(3.6452322641859301e-015))*x+(-3.9297616087156462e-013))*x+(2.2503159058384625e-011))*x+(-1.3501796539168208e-009))*x+(8.5061328418328683e-008))*x+(-5.9542929890690457e-006))*x+(0.00062520076385232733));
		break;
	case 53:
		rts[0] = (((((((((((((4.964325247177233e-012))*x+(-9.473903143468002e-015))*x+(-3.1334934647020418e-012))*x+(-1.4210854715202002e-014))*x+(6.8715403737466352e-013))*x+(1.6375789613221059e-013))*x+(-8.3464809138196935e-012))*x+(4.416609809358244e-010))*x+(-2.3544948522686664e-008))*x+(1.2551774597282549e-006))*x+(-6.6913305140365518e-005))*x+(0.0035671373560915444));
		rts[1] = (((((((((((((4.3049415883918599e-011))*x+(-1.9705718538413444e-012))*x+(-2.679219808972751e-011))*x+(9.8528592692067219e-013))*x+(5.750659208085077e-012))*x+(1.6526039795886997e-012))*x+(-9.3781427068506673e-011))*x+(4.8240449412872968e-009))*x+(-2.4947762802818296e-007))*x+(1.2901862853883598e-005))*x+(-0.00066722638196233485))*x+(0.034505950794729658));
		rts[2] = (((((((((((((1.3945585427184898e-010))*x+(3.0316490059097606e-013))*x+(-8.6477787893575922e-011))*x+(-1.1747639897900322e-012))*x+(1.8379372098327924e-011))*x+(9.970098820607138e-012))*x+(-4.5478968739113651e-010))*x+(2.1741943504830864e-008))*x+(-1.0430660157637976e-006))*x+(5.0040735753214181e-005))*x+(-0.0024006870964463777))*x+(0.11517213823438707));
		wts[0] = (((((((((((((1.1702165162811676e-010))*x+(1.5158245029548803e-012))*x+(-7.2721680529260383e-011))*x+(-1.3642420526593922e-012))*x+(1.5575096767861396e-011))*x+(1.3677947663381929e-012))*x+(-5.6940674397765179e-011))*x+(3.3065504408587758e-009))*x+(-2.0217515159237642e-007))*x+(1.2979646965750416e-005))*x+(-0.00092588148336351407))*x+(0.09906931871988621));
		wts[1] = (((((((((((((2.622376390111943e-011))*x+(3.0316490059097606e-013))*x+(-1.6399326341343109e-011))*x+(-2.6526928801710404e-013))*x+(3.5550821545863674e-012))*x+(2.8540133219697361e-013))*x+(-1.2365849085445763e-011))*x+(7.1671379942017666e-010))*x+(-4.3822538350427959e-008))*x+(2.8134075409682233e-006))*x+(-0.00020068973788388506))*x+(0.021473801953569099));
		wts[2] = (((((((((((((8.1001871876651421e-013))*x+(7.1054273576010019e-015))*x+(-5.1307106711343898e-013))*x+(-7.1054273576010019e-015))*x+(1.1331676338007432e-013))*x+(8.2989171090730451e-015))*x+(-3.5787923550560186e-013))*x+(2.0670848135025583e-011))*x+(-1.2638945141487065e-009))*x+(8.1142047900470825e-008))*x+(-5.7881327489339084e-006))*x+(0.00061933020413570646));
		break;
	case 54:
		rts[0] = (((((((((((((4.2822042208475369e-012))*x+(-1.0421293457814802e-013))*x+(-2.6787461138155777e-012))*x+(4.500103993147301e-014))*x+(5.7790809175154812e-013))*x+(1.3215354736454782e-013))*x+(-7.4605599476029722e-012))*x+(4.0247070028550291e-010))*x+(-2.1858138549736096e-008))*x+(1.187112005926385e-006))*x+(-6.4471858934495523e-005))*x+(0.0035014561169904959));
		rts[1] = (((((((((((((3.8501942375053958e-011))*x+(-9.0949470177292824e-013))*x+(-2.3552123214661453e-011))*x+(3.6000831945178413e-013))*x+(4.8482699336697497e-012))*x+(1.5572728292075528e-012))*x+(-8.3529701673986282e-011))*x+(4.3835122198743193e-009))*x+(-2.3107939182050635e-007))*x+(1.2181467700151751e-005))*x+(-0.00064215224884451411))*x+(0.033851381530506625));
		rts[2] = (((((((((((((1.4551915228366852e-010))*x+(-2.7284841053187847e-012))*x+(-9.1858964879065752e-011))*x+(1.3642420526593924e-012))*x+(1.9952040020143613e-011))*x+(7.949788975262587e-012))*x+(-4.0218495200861071e-010))*x+(1.9611128868983009e-008))*x+(-9.6044763978990001e-007))*x+(4.7037595395996168e-005))*x+(-0.0023036500656988209))*x+(0.11282047010570689));
		wts[0] = (((((((((((((1.3460521586239338e-010))*x+(-4.2443086082736646e-012))*x+(-8.5416710741507515e-011))*x+(2.0084674664152163e-012))*x+(1.8947806286936004e-011))*x+(5.8501351910914922e-013))*x+(-5.1948667589840625e-011))*x+(3.0422138882120939e-009))*x+(-1.8948647130997048e-007))*x+(1.2392418732308046e-005))*x+(-0.00090051576110323247))*x+(0.098156217960214745));
		wts[1] = (((((((((((((2.9710160257915654e-011))*x+(-3.7895612573872007e-013))*x+(-1.8758328224066645e-011))*x+(8.5265128291211997e-014))*x+(4.1258848189803148e-012))*x+(2.057613338971957e-013))*x+(-1.1255737083123071e-011))*x+(6.5940886084803196e-010))*x+(-4.1072201519461636e-008))*x+(2.6861226971562624e-006))*x+(-0.00019519158261976401))*x+(0.021275882505548269));
		wts[2] = (((((((((((((8.1949262190998218e-013))*x+(-1.8947806286936004e-014))*x+(-5.1840013763163973e-013))*x+(7.1054273576010011e-015))*x+(1.1398289719484939e-013))*x+(5.0145073278902909e-015))*x+(-3.2410763887528538e-013))*x+(1.9018212930414315e-011))*x+(-1.1845715794985693e-009))*x+(7.7471000334674079e-008))*x+(-5.629559356598864e-006))*x+(0.0006136219698691241));
		break;
	case 55:
		rts[0] = (((((((((((((3.9600915139696245e-012))*x+(-1.0421293457814802e-013))*x+(-2.4099241121196729e-012))*x+(4.2632564145606011e-014))*x+(4.9530749871943647e-013))*x+(1.166104250197956e-013))*x+(-6.6806051431574539e-012))*x+(3.6737945556068275e-010))*x+(-2.0319717698088581e-008))*x+(1.1238803015215016e-006))*x+(-6.2161635709903111e-005))*x+(0.0034381499071163713));
		rts[1] = (((((((((((((3.9108272176235914e-011))*x+(-2.4253192047278085e-012))*x+(-2.3931079340400174e-011))*x+(1.3452942463724562e-012))*x+(4.964325247177233e-012))*x+(1.1309471877514927e-012))*x+(-7.4681964316406863e-011))*x+(3.9904171818723926e-009))*x+(-2.1434632722916458e-007))*x+(1.1513722120673475e-005))*x+(-0.00061846542407865122))*x+(0.033221183971875394));
		rts[2] = (((((((((((((1.3521154566357532e-010))*x+(-4.2443086082736646e-012))*x+(-8.3862990625978754e-011))*x+(2.1600499167107042e-012))*x+(1.7820411812863313e-011))*x+(6.7619983686502865e-012))*x+(-3.5621209685624911e-010))*x+(1.7725990453243412e-008))*x+(-8.8584965443616593e-007))*x+(4.4270033922535104e-005))*x+(-0.0022123797277603923))*x+(0.11056291640641076));
		wts[0] = (((((((((((((1.13990002622207e-010))*x+(-4.2443086082736646e-012))*x+(-7.0637421837697418e-011))*x+(2.1221543041368323e-012))*x+(1.5025610385540251e-011))*x+(4.2869411724192718e-013))*x+(-4.6704566140457843e-011))*x+(2.8032207666228715e-009))*x+(-1.7780360883623556e-007))*x+(1.1841722441017591e-005))*x+(-0.0008762874605777759))*x+(0.09726790812412496));
		wts[1] = (((((((((((((2.3343697345505156e-011))*x+(-6.0632980118195212e-013))*x+(-1.4229802521488939e-011))*x+(2.3684757858670003e-013))*x+(2.9440154018326812e-012))*x+(1.5039821240255452e-013))*x+(-1.0084007702933681e-011))*x+(6.0760655766027105e-010))*x+(-3.8539880217736133e-008))*x+(2.5667563459859837e-006))*x+(-0.00018993996956863989))*x+(0.021083336622119583));
		wts[2] = (((((((((((((7.531752999057062e-013))*x+(-2.3684757858670004e-014))*x+(-4.6570155139609903e-013))*x+(1.0658141036401501e-014))*x+(9.8957878928255611e-014))*x+(3.5157062446463288e-015))*x+(-2.9238995484052549e-013))*x+(1.7524178867282338e-011))*x+(-1.1115363067904643e-009))*x+(7.4028331596409175e-008))*x+(-5.4780965373916237e-006))*x+(0.00060806871565046176));
		break;
	case 56:
		rts[0] = (((((((((((((3.8274568699610727e-012))*x+(1.3263464400855202e-013))*x+(-2.3613703585093995e-012))*x+(-9.9475983006414001e-014))*x+(4.9649173661237e-013))*x+(1.3182048045716024e-013))*x+(-6.0055941701146285e-012))*x+(3.3589397929745246e-010))*x+(-1.8914292313510866e-008))*x+(1.0650607601145681e-006))*x+(-5.9973397248213297e-005))*x+(0.0033770921928451231));
		rts[1] = (((((((((((((3.6076623170326151e-011))*x+(-1.5158245029548803e-013))*x+(-2.2187881162002061e-011))*x+(-5.6843418860808015e-014))*x+(4.6540549192286562e-012))*x+(1.2665424264923786e-012))*x+(-6.6886718386172106e-011))*x+(3.6388279796758143e-009))*x+(-1.9910081969683652e-007))*x+(1.0893902853787347e-005))*x+(-0.00059606542056108076))*x+(0.03261402184105204));
		rts[2] = (((((((((((((1.303609072541197e-010))*x+(-1.5158245029548803e-012))*x+(-8.1134506520659969e-011))*x+(4.9264296346033599e-013))*x+(1.7214082011681359e-011))*x+(6.1829060390058048e-012))*x+(-3.1637788685164503e-010))*x+(1.6054151637708476e-008))*x+(-8.1835560282924225e-007))*x+(4.1715397280812451e-005))*x+(-0.0021264280369651554))*x+(0.10839393824111651));
		wts[0] = (((((((((((((1.0974569401393333e-010))*x+(-9.0949470177292824e-013))*x+(-6.787104211980477e-011))*x+(3.7895612573872077e-014))*x+(1.4409806681214832e-011))*x+(8.1357143244531471e-013))*x+(-4.2398233072541793e-011))*x+(2.5867247603154433e-009))*x+(-1.6703075490324495e-007))*x+(1.1324687214694928e-005))*x+(-0.00085312643664465539))*x+(0.096403287340838764));
		wts[1] = (((((((((((((2.3495279795800645e-011))*x+(1.5158245029548803e-013))*x+(-1.4637180356658061e-011))*x+(-2.4632148173016805e-013))*x+(3.1477043194172434e-012))*x+(2.3862393542610028e-013))*x+(-9.1985308259268095e-012))*x+(5.6068061304870288e-010))*x+(-3.6204804272632618e-008))*x+(2.45468620953491e-006))*x+(-0.00018491969439762154))*x+(0.020895925466929102));
		wts[2] = (((((((((((((7.4843834833397216e-013))*x+(-4.736951571734001e-015))*x+(-4.6718184876226577e-013))*x+(-1.1842378929335e-015))*x+(1.0103029524088923e-013))*x+(5.6066262743570397e-015))*x+(-2.6632168692586333e-013))*x+(1.6170798496547199e-011))*x+(-1.0441899343157737e-009))*x+(7.0796094445519403e-008))*x+(-5.3333057801144338e-006))*x+(0.00060266355315281015));
		break;
	case 57:
		rts[0] = (((((((((((((4.0358827391173691e-012))*x+(-9.4739031434680016e-014))*x+(-2.4951892404108853e-012))*x+(4.7369515717340008e-014))*x+(5.2876221919480792e-013))*x+(8.6079291842603808e-014))*x+(-5.4111391293668963e-012))*x+(3.0759676287554305e-010))*x+(-1.7628301872928128e-008))*x+(1.0102751599076637e-006))*x+(-5.7898704223866864e-005))*x+(0.0033181652720993817));
		rts[1] = (((((((((((((4.1230426480372742e-011))*x+(3.0316490059097606e-013))*x+(-2.5806912162806836e-011))*x+(-3.7895612573872007e-013))*x+(5.5919713304319877e-012))*x+(1.2020014613275029e-012))*x+(-6.0144926076569988e-011))*x+(3.3237780675913582e-009))*x+(-1.8518695847162073e-007))*x+(1.03177861207245e-005))*x+(-0.00057486068737547767))*x+(0.032028654796041424));
		rts[2] = (((((((((((((1.3157356685648361e-010))*x+(-3.0316490059097606e-013))*x+(-8.1513462646398693e-011))*x+(-3.4106051316484804e-013))*x+(1.7280399333685637e-011))*x+(5.6144718503977247e-012))*x+(-2.8173981666175979e-010))*x+(1.4568001175755777e-008))*x+(-7.5716891772178074e-007))*x+(3.9353596128198963e-005))*x+(-0.0020453896311291935))*x+(0.1063084229910761));
		wts[0] = (((((((((((((1.1580899202575286e-010))*x+(-2.4253192047278085e-012))*x+(-7.2039559502930687e-011))*x+(1.2126596023639042e-012))*x+(1.5442462123852842e-011))*x+(3.8369307731045405e-013))*x+(-3.8713772928152438e-011))*x+(2.390404911049397e-009))*x+(-1.5708276634070667e-007))*x+(1.0838713168999833e-005))*x+(-0.00083096800962466875))*x+(0.095561321106834074));
		wts[1] = (((((((((((((2.3646862246096134e-011))*x+(-5.3053857603420807e-013))*x+(-1.4589810840940725e-011))*x+(2.2737367544323201e-013))*x+(3.0884924247705685e-012))*x+(1.056932319443149e-013))*x+(-8.3635320891062293e-012))*x+(5.1812846605751395e-010))*x+(-3.4048526637020515e-008))*x+(2.3493487495591936e-006))*x+(-0.00018011673744201297))*x+(0.020713424805834112));
		wts[2] = (((((((((((((6.9633188104489818e-013))*x+(-7.1054273576010019e-015))*x+(-4.2484534408989322e-013))*x+(1.7763568394002505e-015))*x+(8.8188715589391593e-014))*x+(4.0800696154974503e-015))*x+(-2.4084091202839869e-013))*x+(1.4943350954791747e-011))*x+(-9.8200037677564455e-010))*x+(6.7758035761013004e-008))*x+(-5.1947827408213148e-006))*x+(0.00059740001519454592));
		break;
	case 58:
		rts[0] = (((((((((((((4.1495695768389851e-012))*x+(-1.8947806286936004e-014))*x+(-2.5733489413444963e-012))*x+(-1.1842378929335008e-015))*x+(5.4889426337467739e-013))*x+(8.6227321579220474e-014))*x+(-4.8843660597578751e-012))*x+(2.8210908609160867e-010))*x+(-1.6449771013798502e-008))*x+(9.5918352856303596e-007))*x+(-5.5929834712674203e-005))*x+(0.003261259517053704));
		rts[1] = (((((((((((((3.6076623170326151e-011))*x+(-6.0632980118195212e-013))*x+(-2.2566837287740782e-011))*x+(2.4632148173016805e-013))*x+(4.8624807883849517e-012))*x+(9.2607403227399731e-013))*x+(-5.4032112117852193e-011))*x+(3.0409219586857716e-009))*x+(-1.7246758335827858e-007))*x+(9.7815870785343071e-006))*x+(-0.00055476767286067317))*x+(0.031463929973004276));
		rts[2] = (((((((((((((1.1702165162811676e-010))*x+(-6.0632980118195212e-013))*x+(-7.1812185827487454e-011))*x+(-2.6526928801710404e-013))*x+(1.4968766966679443e-011))*x+(4.9572198198196328e-012))*x+(-2.512160849713988e-010))*x+(1.3243935725881784e-008))*x+(-7.0159533931598206e-007))*x+(3.716677337109453e-005))*x+(-0.0019688970433842882))*x+(0.10430164408015961));
		wts[0] = (((((((((((((1.1217101321866115e-010))*x+(-3.0316490059097605e-012))*x+(-6.908370172216867e-011))*x+(1.5158245029548803e-012))*x+(1.4570863034653787e-011))*x+(3.1027032794857711e-013))*x+(-3.5218198727685974e-011))*x+(2.2119402605843179e-009))*x+(-1.4788375724920458e-007))*x+(1.038144171510343e-005))*x+(-0.00080975245368494232))*x+(0.094741037081141483));
		wts[1] = (((((((((((((2.4253192047278084e-011))*x+(-9.8528592692067219e-013))*x+(-1.5006662579253316e-011))*x+(5.1159076974727203e-013))*x+(3.1950738351345836e-012))*x+(2.9902006796570874e-014))*x+(-7.6432193907294277e-012))*x+(4.7945318086088185e-010))*x+(-3.2054590296907527e-008))*x+(2.2502327284834125e-006))*x+(-0.00017551815280990603))*x+(0.020535623878755942));
		wts[2] = (((((((((((((6.4896236532755814e-013))*x+(-3.7895612573872008e-014))*x+(-3.9464727782008896e-013))*x+(2.0724163126336254e-014))*x+(8.1601392309949006e-014))*x+(-4.0708177569589047e-016))*x+(-2.1916149450795785e-013))*x+(1.3828114579321021e-011))*x+(-9.2449289203500496e-010))*x+(6.4899410825904739e-008))*x+(-5.0621540444634915e-006))*x+(0.00059227202320221329));
		break;
	case 59:
		rts[0] = (((((((((((((3.7327178385263924e-012))*x+(-7.5791225147744016e-014))*x+(-2.2915003228263227e-012))*x+(3.4342898895071507e-014))*x+(4.8050452505776765e-013))*x+(6.9573976209843126e-014))*x+(-4.407923100598528e-012))*x+(2.5911545131762637e-010))*x+(-1.5368102572061355e-008))*x+(9.1147970450108907e-007))*x+(-5.4059712235885516e-005))*x+(0.0032062726934505188));
		rts[1] = (((((((((((((3.6076623170326151e-011))*x+(-6.0632980118195212e-013))*x+(-2.2036298711706572e-011))*x+(1.8000415972589201e-013))*x+(4.5735267425091779e-012))*x+(8.4909856923331962e-013))*x+(-4.8641461229218898e-011))*x+(2.7864482573155178e-009))*x+(-1.6082171906683929e-007))*x+(9.2819075126436088e-006))*x+(-0.00053571000031503414))*x+(0.030918774407864363));
		rts[2] = (((((((((((((1.3763686486830312e-010))*x+(-4.5474735088646412e-012))*x+(-8.6136727380411074e-011))*x+(2.5390060424494245e-012))*x+(1.8578324064340752e-011))*x+(3.6652162786291837e-012))*x+(-2.2507373742541856e-010))*x+(1.2061766548517502e-008))*x+(-6.5102809509072935e-007))*x+(3.5139020063602401e-005))*x+(-0.0018966165291459489))*x+(0.10236922521338437));
		wts[0] = (((((((((((((1.0671404500802358e-010))*x+(-6.0632980118195212e-013))*x+(-6.5938365878537284e-011))*x+(-1.5158245029548801e-013))*x+(1.3992954942902238e-011))*x+(6.5606779268515904e-013))*x+(-3.2160940577341528e-011))*x+(2.0494631177333153e-009))*x+(-1.3936592990759777e-007))*x+(9.950729509368891e-006))*x+(-0.00078942454087246633))*x+(0.093941520363817393));
		wts[1] = (((((((((((((2.3040532444914181e-011))*x+(-9.8528592692067219e-013))*x+(-1.4210854715202002e-011))*x+(4.926429634603361e-013))*x+(3.0150696754086913e-012))*x+(2.6349293117770373e-014))*x+(-6.9708683270164329e-012))*x+(4.4424304975384154e-010))*x+(-3.0208306615412774e-008))*x+(2.1568735658651635e-006))*x+(-0.00017111196954846562))*x+(0.020362324376263865));
		wts[2] = (((((((((((((6.8685797790143011e-013))*x+(-1.4210854715202004e-014))*x+(-4.2366110619695969e-013))*x+(5.0330110449673766e-015))*x+(8.9928064994637667e-014))*x+(2.886579864025407e-015))*x+(-2.0131234642247381e-013))*x+(1.281229520625852e-011))*x+(-8.7124378581107198e-010))*x+(6.2206820612755815e-008))*x+(-4.9350744344038778e-006))*x+(0.00058727385769397642));
		break;
	default:
		double fr = 1/X;
		double fw = sqrt(fr);
		for(unsigned int i = 0 ; i < 3 ; i++){
			double DUM = fr*hermite_roots[3][i]*hermite_roots[3][i];
			rts[i] = DUM/(1.0-DUM);
			wts[i] = fw*hermite_weights[3][i];
		}
		break;
	}
}

void __Root4(double X , double rts[] , double wts[]){
	int n = int(X);
	double x = X - double(n) - 0.5;

	switch(n){
	case 0:
		rts[0] = (((((((((((((-5.5176011907557644e-011))*x+(-1.2126596023639042e-012))*x+(3.698611787209908e-011))*x+(7.4654356770527865e-012))*x+(-2.042881419583864e-010))*x+(4.5105205496535437e-009))*x+(-8.7187888316483012e-008))*x+(1.4879055165728516e-006))*x+(-2.291485790781311e-005))*x+(0.00031620381831790056))*x+(-0.003762296478091134))*x+(0.032856737964511773));
		rts[1] = (((((((((((((5.8207660913467407e-011))*x+(-8.1248193358381585e-011))*x+(-2.6678511252005897e-011))*x+(1.3566629301446179e-010))*x+(-6.1390892369672656e-012))*x+(-1.9009486133351554e-008))*x+(2.5072065075922484e-007))*x+(1.9688642141820383e-006))*x+(-0.00013846632434422188))*x+(0.0030166575589429252))*x+(-0.041768847240483076))*x+(0.35991117385703131));
		rts[2] = (((((((((((((1.6880221664905548e-009))*x+(-3.1044085820515949e-010))*x+(-9.0100608455638098e-010))*x+(5.2144362901647868e-011))*x+(1.9119094455769905e-009))*x+(3.9884980651549995e-008))*x+(-1.4807915723243542e-007))*x+(-1.1876397550736328e-005))*x+(-0.00010244178627605294))*x+(0.01024651334362995))*x+(-0.19407163048461784))*x+(1.6376977576956644));
		rts[3] = (((((((((((((2.0799537499745686e-008))*x+(5.4327150185902907e-010))*x+(-1.3620592653751373e-008))*x+(-8.8766682893037786e-010))*x+(-1.236912794411182e-009))*x+(-5.5743839766364545e-008))*x+(-4.1622032161588624e-007))*x+(2.594477753821896e-006))*x+(0.0001739938872683903))*x+(0.047485185543923329))*x+(-1.3463269100971151))*x+(11.16129247164238));
		wts[0] = (((((((((((((2.1585340922077495e-010))*x+(-9.701276818911234e-012))*x+(-1.9811826253620285e-010))*x+(8.634136368830998e-010))*x+(-1.1401690850713445e-008))*x+(1.4745821393565467e-007))*x+(-1.8292114448333527e-006))*x+(2.1710324003739359e-005))*x+(-0.00024588010713910702))*x+(0.0026616708748941806))*x+(-0.028526893871683084))*x+(0.34772276725554102));
		wts[1] = (((((((((((((4.6081064889828361e-010))*x+(2.1342809001604715e-010))*x+(-4.3758821751301485e-009))*x+(4.6832155931042507e-008))*x+(-4.9506913531634678e-007))*x+(4.8329129261522512e-006))*x+(-4.307755633448096e-005))*x+(0.00034603654393094985))*x+(-0.0024565420349254761))*x+(0.014925794394925324))*x+(-0.072848979927689475))*x+(0.27322058652985393));
		wts[2] = (((((((((((((1.1884064103166261e-010))*x+(3.06560347477595e-009))*x+(-3.4244446093604587e-008))*x+(3.5156009895824048e-007))*x+(-3.2953034292404477e-006))*x+(2.767001549841552e-005))*x+(-0.00020498757375205418))*x+(0.0013119906614988963))*x+(-0.0070342857818441367))*x+(0.030063098142113869))*x+(-0.093249932750932338))*x+(0.16727214300997398));
		wts[3] = (((((((((((((-2.1827872842550278e-010))*x+(4.9879721094233292e-009))*x+(-5.431805523888518e-008))*x+(5.3456070266596112e-007))*x+(-4.7189604686082021e-006))*x+(3.6738065611293294e-005))*x+(-0.00024744684834310249))*x+(0.0014045754382085993))*x+(-0.0064669628119175347))*x+(0.022724705001010651))*x+(-0.054467925629211204))*x+(0.067408895096780011));
		break;
	case 1:
		rts[0] = (((((((((((((5.4569682106375694e-011))*x+(1.5158245029548802e-011))*x+(-4.0207244940878205e-011))*x+(-4.1400956736955152e-012))*x+(-1.3923084907219163e-010))*x+(3.3032894937908472e-009))*x+(-6.3911058223453665e-008))*x+(1.1131845397323778e-006))*x+(-1.7751423350790642e-005))*x+(0.00025557851193136011))*x+(-0.0031930919927466847))*x+(0.029389135484953016));
		rts[1] = (((((((((((((4.9961575617392851e-010))*x+(1.3339255626002947e-011))*x+(-3.3257189594830072e-010))*x+(2.8649083105847239e-011))*x+(5.6460673173811904e-010))*x+(-1.7107069538724318e-008))*x+(1.4066269097649334e-007))*x+(2.9425242503341069e-006))*x+(-0.00012845955771401127))*x+(0.0026152960446685354))*x+(-0.036141915443717192))*x+(0.32102271850975389));
		rts[2] = (((((((((((((1.7074247201283772e-009))*x+(-1.3096723705530167e-010))*x+(-1.0913936421275137e-009))*x+(-1.7037867413212854e-010))*x+(4.8642808299822105e-010))*x+(4.7352367952650333e-008))*x+(1.1917475717382328e-007))*x+(-1.1967332708214446e-005))*x+(-0.000150576523004986))*x+(0.0098670805693573289))*x+(-0.173933924397559))*x+(1.4537582158401827));
		rts[3] = (((((((((((((2.3205454150835671e-008))*x+(-2.2895013292630511e-009))*x+(-1.4440350544949372e-008))*x+(1.6395157823959983e-009))*x+(-2.8254968735078973e-009))*x+(-9.3495903759806736e-008))*x+(-8.577908943152579e-007))*x+(-4.9592235503344761e-007))*x+(0.0001789251423609528))*x+(0.048017635878005997))*x+(-1.2508266276407034))*x+(9.8626268589235089));
		wts[0] = (((((((((((((4.7293724492192268e-010))*x+(2.4253192047278084e-011))*x+(-3.4333424991928041e-010))*x+(4.3883119360543782e-010))*x+(-6.3110216312149224e-009))*x+(8.69560115764519e-008))*x+(-1.143505726849033e-006))*x+(1.4428906022582547e-005))*x+(-0.00017473867421439562))*x+(0.0020379941282198852))*x+(-0.023862686131339017))*x+(0.32163168209211168));
		wts[1] = (((((((((((((1.0428872580329576e-010))*x+(5.4569682106375694e-011))*x+(-1.883411944921439e-009))*x+(2.1543807330696531e-008))*x+(-2.3558137248376926e-007))*x+(2.3920553028726013e-006))*x+(-2.230155686255841e-005))*x+(0.00018863289614282999))*x+(-0.0014215314935380008))*x+(0.0092648838840139001))*x+(-0.049172386839553439))*x+(0.21314819873078272));
		wts[2] = (((((((((((((-4.850638409455617e-012))*x+(1.2332748156040907e-009))*x+(-1.4167198969516903e-008))*x+(1.482023890275741e-007))*x+(-1.4139015812967652e-006))*x+(1.2124546377852614e-005))*x+(-9.2107049277719469e-005))*x+(0.00060765187766461293))*x+(-0.0033809788532093896))*x+(0.015136900232573245))*x+(-0.049858082150415726))*x+(0.098182720733271223));
		wts[3] = (((((((((((((-1.1368683772161603e-010))*x+(1.9795152184087783e-009))*x+(-2.1724474663642468e-008))*x+(2.1521589133044472e-007))*x+(-1.912140788817851e-006))*x+(1.4998864892016664e-005))*x+(-0.00010192623760718611))*x+(0.00058476022438506503))*x+(-0.0027276148172218394))*x+(0.0097419926791025725))*x+(-0.023847106775993016))*x+(0.030388344284168957));
		break;
	case 2:
		rts[0] = (((((((((((((4.5171570188055434e-011))*x+(-3.9411437076826888e-012))*x+(-2.4954260879894715e-011))*x+(7.863339609078441e-012))*x+(-1.0483110675825931e-010))*x+(2.396478275083306e-009))*x+(-4.69588740485231e-008))*x+(8.3827141813171591e-007))*x+(-1.3876714749547214e-005))*x+(0.00020841076676429704))*x+(-0.0027310372501189802))*x+(0.02643492301208944));
		rts[1] = (((((((((((((4.5838532969355583e-010))*x+(1.0913936421275139e-011))*x+(-2.9088672211704153e-010))*x+(2.2737367544323206e-012))*x+(7.3964656621683389e-010))*x+(-1.2876043342657795e-008))*x+(5.0045644073293261e-008))*x+(3.4086645014734054e-006))*x+(-0.0001156059298609291))*x+(0.0022487338121064591))*x+(-0.031284327535195819))*x+(0.28737070616179489));
		rts[2] = (((((((((((((1.3872825851043065e-009))*x+(1.8432425955931345e-010))*x+(-8.567440090700983e-010))*x+(-3.1468516681343317e-010))*x+(-1.2908761467163763e-009))*x+(4.2964340233690258e-008))*x+(3.9610184643379393e-007))*x+(-1.0667951097313258e-005))*x+(-0.00019631063524257658))*x+(0.0093454482213831298))*x+(-0.15469848210940965))*x+(1.2895289947301927));
		rts[3] = (((((((((((((4.8894435167312622e-009))*x+(1.9402553637822467e-010))*x+(-2.6630004867911339e-009))*x+(1.2126596023639041e-010))*x+(-4.1036400943994522e-009))*x+(-1.3232768954670368e-007))*x+(-1.5386944861954057e-006))*x+(-6.3867588361669432e-006))*x+(0.00016629643823880733))*x+(0.048541338974058476))*x+(-1.1542614521722119))*x+(8.6599953397641087));
		wts[0] = (((((((((((((2.2312936683495838e-010))*x+(-3.759244767328103e-011))*x+(-1.3763686486830312e-010))*x+(2.722420807306965e-010))*x+(-3.6442315831664018e-009))*x+(5.2721783087387543e-008))*x+(-7.3392655745389368e-007))*x+(9.8204393612633095e-006))*x+(-0.00012691945707299365))*x+(0.0015900984202406598))*x+(-0.020258435379002893))*x+(0.29964561781417759));
		wts[1] = (((((((((((((2.7042309132715065e-010))*x+(9.519377878556648e-011))*x+(-1.0211351764155552e-009))*x+(1.0095770145805242e-008))*x+(-1.1500492291816043e-007))*x+(1.2173577369859836e-006))*x+(-1.1891071610333388e-005))*x+(0.00010606197570428577))*x+(-0.00084935390006518618))*x+(0.0059405468194104099))*x+(-0.034251329646686146))*x+(0.1719876718973847));
		wts[2] = (((((((((((((1.2732925824820995e-010))*x+(4.6050748399769265e-010))*x+(-6.03949956712313e-009))*x+(6.3359948399011046e-008))*x+(-6.1625438263490651e-007))*x+(5.4099913372832962e-006))*x+(-4.2261374914550246e-005))*x+(0.00028832269957416534))*x+(-0.0016711913131161233))*x+(0.0078746724073361311))*x+(-0.027693226198456388))*x+(0.060606950651821076));
		wts[3] = (((((((((((((-4.2291503632441163e-011))*x+(7.9406466587291403e-010))*x+(-8.7420535995382417e-009))*x+(8.7109659337632664e-008))*x+(-7.7959145746338732e-007))*x+(6.1674278629316372e-006))*x+(-4.2337892228997788e-005))*x+(0.00024588540834184303))*x+(-0.0011643415511259382))*x+(0.0042386008802747024))*x+(-0.010638403408106302))*x+(0.014051731421764994));
		break;
	case 3:
		rts[0] = (((((((((((((-2.1524707941959299e-011))*x+(3.1832314562052488e-012))*x+(1.6200374375330284e-011))*x+(1.9516240475544082e-012))*x+(-8.115819127851863e-011))*x+(1.7534222962467536e-009))*x+(-3.4620242154540883e-008))*x+(6.3593023062284238e-007))*x+(-1.0948836762877943e-005))*x+(0.00017137445933531012))*x+(-0.0023527139121383559))*x+(0.023899213419460899));
		rts[1] = (((((((((((((1.3824319466948509e-010))*x+(0))*x+(-7.9580786405131221e-011))*x+(-1.1975013573343555e-011))*x+(6.6463220112685418e-010))*x+(-8.1345964038822168e-009))*x+(-1.2884943482542136e-008))*x+(3.4896770901108689e-006))*x+(-0.00010170438860768181))*x+(0.0019226897067024702))*x+(-0.027119865271440485))*x+(0.25822295302952325));
		rts[2] = (((((((((((((3.2693302879730859e-009))*x+(-2.0372681319713593e-010))*x+(-2.1336745703592892e-009))*x+(1.8189894035458565e-011))*x+(-2.1459527488332242e-009))*x+(2.806098109431332e-008))*x+(6.132459565340771e-007))*x+(-8.1070537779244952e-006))*x+(-0.00023422398237782358))*x+(0.0086970779031185028))*x+(-0.13663696291753591))*x+(1.143969419656647));
		rts[3] = (((((((((((((1.0011717677116394e-008))*x+(-1.5522042910257974e-010))*x+(-6.048746096591155e-009))*x+(1.1641532182693481e-009))*x+(2.6714891040076809e-009))*x+(-1.4667784853372723e-007))*x+(-2.3971581602684941e-006))*x+(-1.6189103841194687e-005))*x+(0.00012258243693826404))*x+(0.048984452147318315))*x+(-1.0567139481198431))*x+(7.5544334610348747));
		wts[0] = (((((((((((((3.8077511514226592e-010))*x+(-3.637978807091713e-012))*x+(-2.5177844994080562e-010))*x+(1.4051693142391741e-010))*x+(-2.0959115924294261e-009))*x+(3.2880919320632529e-008))*x+(-4.8237388424373273e-007))*x+(6.8290663831997254e-006))*x+(-9.4037957810081757e-005))*x+(0.001261643818808907))*x+(-0.017423092213199941))*x+(0.28085949720817982));
		wts[1] = (((((((((((((3.9047639196117717e-010))*x+(4.4868405287464455e-011))*x+(-6.5104662401912106e-010))*x+(4.8712536226958036e-009))*x+(-5.7631268646218814e-008))*x+(6.3693753797148622e-007))*x+(-6.5271243527102261e-006))*x+(6.1455514077361301e-005))*x+(-0.00052319279031757626))*x+(0.0039260464748599082))*x+(-0.024546932344349504))*x+(0.14292281772479448));
		wts[2] = (((((((((((((-6.3664629124104977e-011))*x+(2.3374013835564256e-010))*x+(-2.4919017960201018e-009))*x+(2.7457095560142381e-008))*x+(-2.7328033525009232e-007))*x+(2.4618714024408441e-006))*x+(-1.9832245697977886e-005))*x+(0.00014037676193382845))*x+(-0.00085078077665448615))*x+(0.0042382096133278396))*x+(-0.01598686742385419))*x+(0.039368118462123777));
		wts[3] = (((((((((((((2.8800665556142726e-012))*x+(3.184368324582465e-010))*x+(-3.547105128139568e-009))*x+(3.5469758093616591e-008))*x+(-3.2003733529961664e-007))*x+(2.5564334165117941e-006))*x+(-1.7753340069740865e-005))*x+(0.00010456664316751037))*x+(-0.00050388573881056148))*x+(0.0018758069438519203))*x+(-0.004850201129926855))*x+(0.0066966018065256682));
		break;
	case 4:
		rts[0] = (((((((((((((-1.6219322181617219e-011))*x+(-5.4569682106375694e-012))*x+(1.1074992774714094e-011))*x+(5.9875067866717773e-012))*x+(-5.6890788376525351e-011))*x+(1.3010345393619596e-009))*x+(-2.5534307002139652e-008))*x+(4.8666697138877158e-007))*x+(-8.7187596285939767e-006))*x+(0.00014202210335562587))*x+(-0.002040430877426897))*x+(0.021707528119265834));
		rts[1] = (((((((((((((2.4253192047278084e-011))*x+(-5.0931703299283981e-011))*x+(3.0316490059097597e-012))*x+(8.8675733422860503e-012))*x+(4.9728517600063548e-010))*x+(-4.0498567462539841e-009))*x+(-4.8903738540199505e-008))*x+(3.3249534432400196e-006))*x+(-8.8015263739545547e-005))*x+(0.0016382770042312107))*x+(-0.0235657491021669))*x+(0.23292754237127705));
		rts[2] = (((((((((((((9.7012768189112332e-010))*x+(-7.7610214551289872e-011))*x+(-4.8748916015028954e-010))*x+(8.2460852960745485e-011))*x+(-2.8406551185374456e-009))*x+(8.1010587867543417e-009))*x+(7.2282808597871418e-007))*x+(-4.7165744874178009e-006))*x+(-0.00026005411703700071))*x+(0.0079522602142344141))*x+(-0.11997469143358114))*x+(1.0157878422577311));
		rts[3] = (((((((((((((1.0399768749872843e-008))*x+(7.7610214551289872e-011))*x+(-7.1207371850808459e-009))*x+(1.1568772606551647e-009))*x+(1.2999104607539872e-008))*x+(-1.0379426385043189e-007))*x+(-3.1835731230482151e-006))*x+(-3.0246471093657114e-005))*x+(3.1033507821594711e-005))*x+(0.049228954598505695))*x+(-0.95845489962698804))*x+(6.5468078171657611));
		wts[0] = (((((((((((((1.6249638671676317e-010))*x+(-2.7891170854369797e-011))*x+(-9.2616877130543188e-011))*x+(9.7770680440589786e-011))*x+(-1.2780484818601205e-009))*x+(2.1107595671310264e-008))*x+(-3.2338434211946299e-007))*x+(4.8439683896598727e-006))*x+(-7.0955868380573315e-005))*x+(0.001016132332821847))*x+(-0.015156830751054744))*x+(0.26461038841533752));
		wts[1] = (((((((((((((2.0615213240186373e-010))*x+(4.6687394691010312e-011))*x+(-3.0574180224599934e-010))*x+(2.3934110989406081e-009))*x+(-2.9684845988716308e-008))*x+(3.4243387148080728e-007))*x+(-3.686135960023762e-006))*x+(3.6652972023413596e-005))*x+(-0.00033167854102970435))*x+(0.0026683963867988976))*x+(-0.018047777714288577))*x+(0.12183425122312785));
		wts[2] = (((((((((((((7.7003884750107916e-011))*x+(1.014086592476815e-010))*x+(-1.1495634074284074e-009))*x+(1.2104275507833032e-008))*x+(-1.2343304452618514e-007))*x+(1.1441733705671215e-006))*x+(-9.5325916868264464e-006))*x+(7.022368272324718e-005))*x+(-0.00044657400271971842))*x+(0.0023616817321803602))*x+(-0.0095873874040693623))*x+(0.026891438130013434));
		wts[3] = (((((((((((((-6.3664629124104977e-012))*x+(1.3013353357867646e-010))*x+(-1.4370963678326612e-009))*x+(1.4537922273423948e-008))*x+(-1.3240020753831533e-007))*x+(1.0692596343157372e-006))*x+(-7.5243816289501568e-006))*x+(4.5042366724035166e-005))*x+(-0.00022150116989939903))*x+(0.00084652094502717795))*x+(-0.0022673913575038257))*x+(0.0033074038120368262));
		break;
	case 5:
		rts[0] = (((((((((((((4.2746250983327627e-011))*x+(-5.9117155615240335e-012))*x+(-2.6697459058292832e-011))*x+(4.5569474120081095e-012))*x+(-3.4307371758283502e-011))*x+(9.7672092636003072e-010))*x+(-1.8745690851436809e-008))*x+(3.7677647505655421e-007))*x+(-7.0031727113182649e-006))*x+(0.00011854893367816097))*x+(-0.0017807165045431092))*x+(0.019800862967907115));
		rts[1] = (((((((((((((2.8376234695315361e-010))*x+(-2.2434202643732228e-011))*x+(-1.7932203869956234e-010))*x+(-1.1975013573343556e-011))*x+(3.5633244503211847e-010))*x+(-1.1561359277341881e-009))*x+(-6.3841005371045867e-008))*x+(3.0358660412233007e-006))*x+(-7.5268959699411234e-005))*x+(0.0013936412022062619))*x+(-0.020540206504765048))*x+(0.21091532749639075));
		rts[2] = (((((((((((((1.1593025798598924e-009))*x+(-2.5950915490587551e-010))*x+(-7.2426094751184178e-010))*x+(2.5344585689405597e-010))*x+(-2.2290957228202992e-009))*x+(-1.0823640650414744e-008))*x+(7.129450771969913e-007))*x+(-1.0796518653914213e-006))*x+(-0.00027162951321213491))*x+(0.0071510883406198014))*x+(-0.10486555691295822))*x+(0.90350136841360051));
		rts[3] = (((((((((((((2.7551626165707903e-009))*x+(9.3132257461547852e-010))*x+(-1.9523819598058858e-009))*x+(3.7349915752808239e-010))*x+(2.1491359802894294e-008))*x+(1.0907266793462137e-008))*x+(-3.4972267239178714e-006))*x+(-4.7235344633615263e-005))*x+(-0.00012339555872564742))*x+(0.049107457946372314))*x+(-0.86004132650195675))*x+(5.6375793845057389));
		wts[0] = (((((((((((((4.5110937207937241e-010))*x+(-1.2126596023639042e-011))*x+(-2.8921931516379118e-010))*x+(4.880954899514714e-011))*x+(-7.3598963960345521e-010))*x+(1.3952359267932479e-008))*x+(-2.1991337225320726e-007))*x+(3.5035576271269515e-006))*x+(-5.4432707717137298e-005))*x+(0.00082938632178053407))*x+(-0.013319556511898164))*x+(0.2504032746080232));
		wts[1] = (((((((((((((-1.0550138540565968e-010))*x+(1.7583564234276612e-011))*x+(-1.2808717049968735e-011))*x+(1.2214892800936166e-009))*x+(-1.572090961114251e-008))*x+(1.8900034367182644e-007))*x+(-2.1404859783894872e-006))*x+(2.2467249487216158e-005))*x+(-0.00021599801647022762))*x+(0.001860991341059113))*x+(-0.013575974947947133))*x+(0.10615647315617982));
		wts[2] = (((((((((((((2.3646862246096134e-011))*x+(3.2893391714120902e-011))*x+(-4.9381772745012609e-010))*x+(5.4394888593378701e-009))*x+(-5.6884635076433668e-008))*x+(5.4379590075370743e-007))*x+(-4.6991203267824728e-006))*x+(3.6130019933041283e-005))*x+(-0.00024184592874018637))*x+(0.0013628496853981657))*x+(-0.0059644253583125738))*x+(0.019280881377116192));
		wts[3] = (((((((((((((-2.3305801732931286e-012))*x+(5.1992780451352395e-011))*x+(-5.8836135963247216e-010))*x+(6.0038622962110813e-009))*x+(-5.5248622861843913e-008))*x+(4.5179247898374797e-007))*x+(-3.227764640720276e-006))*x+(1.9686127707779777e-005))*x+(-9.9116860272729278e-005))*x+(0.00039064698307997477))*x+(-0.001090712090856265))*x+(0.0017035002963097139));
		break;
	case 6:
		rts[0] = (((((((((((((2.0463630789890885e-011))*x+(-1.9705718538413444e-012))*x+(-1.4769815000666615e-011))*x+(1.7053025658242402e-012))*x+(-2.8934484438044209e-011))*x+(7.2492885768345628e-010))*x+(-1.3663461658393789e-008))*x+(2.9638500476103502e-007))*x+(-5.66531175692081e-006))*x+(9.9626472684919781e-005))*x+(-0.0015632091828234437))*x+(0.018132051193991808));
		rts[1] = (((((((((((((3.8683841315408546e-010))*x+(-2.1221543041368324e-011))*x+(-2.5079316401388491e-010))*x+(-8.2612435411040971e-012))*x+(1.9497292669257147e-010))*x+(4.1891468072208221e-010))*x+(-6.5406161967966143e-008))*x+(2.7088392953918588e-006))*x+(-6.3777157394639961e-005))*x+(0.0011853998385116342))*x+(-0.017966911595226093))*x+(0.19169646440204799));
		rts[2] = (((((((((((((1.1204974725842476e-009))*x+(-6.305829932292302e-011))*x+(-7.3881286274020874e-010))*x+(1.4946029599135119e-010))*x+(-1.3105060740296417e-009))*x+(-2.4453337725086992e-008))*x+(6.0402037268166464e-007))*x+(2.24702822748668e-006))*x+(-0.00026911215863963567))*x+(0.0063366423070361968))*x+(-0.091379103249057278))*x+(0.80551489055344916));
		rts[3] = (((((((((((((4.9670537312825518e-009))*x+(1.4551915228366852e-009))*x+(-3.0316490059097605e-009))*x+(-1.0574391732613246e-009))*x+(2.5380662312575925e-008))*x+(1.7664729057287332e-007))*x+(-2.949256232417004e-006))*x+(-6.3768044725520654e-005))*x+(-0.00034631090838625295))*x+(0.04841951448866854))*x+(-0.76240280573077002))*x+(4.8264714205621857));
		wts[0] = (((((((((((((3.5409660389026004e-010))*x+(-3.637978807091713e-011))*x+(-2.3313380855446059e-010))*x+(4.6838977141305804e-011))*x+(-4.6778344161187612e-010))*x+(9.4182250146938405e-009))*x+(-1.5075978036331131e-007))*x+(2.5881788066802374e-006))*x+(-4.2364167315141657e-005))*x+(0.00068510413676525761))*x+(-0.011811088844158235))*x+(0.23786196855535491));
		wts[1] = (((((((((((((4.2443086082736649e-011))*x+(3.152914966146151e-011))*x+(-6.7075234255753458e-011))*x+(6.2319334877732524e-010))*x+(-8.4972195206015986e-009))*x+(1.0702136421514295e-007))*x+(-1.2774494229835416e-006))*x+(1.4126003879807076e-005))*x+(-0.00014424159622367094))*x+(0.0013289325634641691))*x+(-0.010421786600321758))*x+(0.094245992736080503));
		wts[2] = (((((((((((((-3.637978807091713e-012))*x+(1.8796223836640515e-011))*x+(-2.0946799850207753e-010))*x+(2.4849290033065094e-009))*x+(-2.6773935957180584e-008))*x+(2.6460077921323466e-007))*x+(-2.3782374301746971e-006))*x+(1.9127841796066452e-005))*x+(-0.00013516372887191949))*x+(0.00081419971278623893))*x+(-0.003840335187470022))*x+(0.014469382577912408));
		wts[3] = (((((((((((((1.1937117960769683e-012))*x+(2.1074697542644572e-011))*x+(-2.4404182378627104e-010))*x+(2.5000232994898397e-009))*x+(-2.3278268646009792e-008))*x+(1.9308534521256249e-007))*x+(-1.4036036872823916e-006))*x+(8.7464505506308164e-006))*x+(-4.5255350422364282e-005))*x+(0.00018490128112867441))*x+(-0.00054179578159211901))*x+(0.00092117869969687491));
		break;
	case 7:
		rts[0] = (((((((((((((1.8644641386345029e-011))*x+(-4.850638409455617e-012))*x+(-1.0601297617540695e-011))*x+(3.3442878096442046e-012))*x+(-2.7323920903654653e-011))*x+(5.0841049888579925e-010))*x+(-9.9728449572585483e-009))*x+(2.378353403849805e-007))*x+(-4.603017610754304e-006))*x+(8.4282420424915128e-005))*x+(-0.0013798308223315213))*x+(0.01666308658693735));
		rts[1] = (((((((((((((2.3646862246096134e-010))*x+(-3.4560798667371273e-011))*x+(-1.4044114019876966e-010))*x+(5.9875067866717797e-012))*x+(2.2112089936854318e-011))*x+(8.4432609052479768e-010))*x+(-6.1091822267655971e-008))*x+(2.3915612278694689e-006))*x+(-5.3583709056855458e-005))*x+(0.0010096760259590924))*x+(-0.015776931712691972))*x+(0.17485381946428386));
		rts[2] = (((((((((((((6.7423873891433073e-010))*x+(5.0931703299283981e-011))*x+(-4.0048083368067938e-010))*x+(7.0031092036515474e-011))*x+(-5.056790541857481e-010))*x+(-3.1592103747849855e-008))*x+(4.3272001093441759e-007))*x+(4.856766993318236e-006))*x+(-0.00025461798931029434))*x+(0.0055484337815003464))*x+(-0.079501302948697852))*x+(0.72020614270312944));
		rts[3] = (((((((((((((3.5312647620836892e-009))*x+(6.4028427004814148e-010))*x+(-2.5296079305311041e-009))*x+(-1.886898341278235e-009))*x+(1.9009955091557153e-008))*x+(3.3447584731523722e-007))*x+(-1.394344934624314e-006))*x+(-7.502494031541572e-005))*x+(-0.00062649589352462942))*x+(0.04697164109047916))*x+(-0.66687129742904994))*x+(4.1120753021780736));
		wts[0] = (((((((((((((2.9346362377206481e-010))*x+(1.8796223836640515e-011))*x+(-1.7356190558833379e-010))*x+(1.591615728102626e-012))*x+(-3.3289400865517865e-010))*x+(6.3696674601487757e-009))*x+(-1.039245981123334e-007))*x+(1.9590985986065825e-006))*x+(-3.3347489252100182e-005))*x+(0.00057216421111911753))*x+(-0.010558321055341347))*x+(0.22669606602959491));
		wts[1] = (((((((((((((1.255102688446641e-010))*x+(4.4868405287464455e-011))*x+(-1.0811618267325684e-010))*x+(3.1316934231047827e-010))*x+(-4.6781091593099209e-009))*x+(6.2206979123402562e-008))*x+(-7.8301105022049455e-007))*x+(9.0862161190585766e-006))*x+(-9.8636831037233558e-005))*x+(0.0009696324967501021))*x+(-0.0081459421428423748))*x+(0.08502184477334461));
		wts[2] = (((((((((((((2.4177400822130341e-011))*x+(9.5117987560418734e-012))*x+(-1.1299050584057113e-010))*x+(1.1586962500587106e-009))*x+(-1.2873434466579662e-008))*x+(1.3194989945120028e-007))*x+(-1.2367395019752259e-006))*x+(1.0418980303276518e-005))*x+(-7.7956600378078833e-005))*x+(0.00050316262475581049))*x+(-0.0025513884458725307))*x+(0.011325073095401436));
		wts[3] = (((((((((((((7.815970093361102e-013))*x+(9.0688937840847448e-012))*x+(-1.0157415649321895e-010))*x+(1.0503962144525756e-009))*x+(-9.9149524146469048e-009))*x+(8.3583631081222493e-008))*x+(-6.1978580595187238e-007))*x+(3.9584114945485915e-006))*x+(-2.113667613899904e-005))*x+(9.0047477121763648e-005))*x+(-0.00027877790981333569))*x+(0.00052654377983755161));
		break;
	case 8:
		rts[0] = (((((((((((((5.1538033100465928e-012))*x+(-6.5180453627059852e-012))*x+(-3.6758744196655844e-012))*x+(4.4527344774299609e-012))*x+(-2.5147291656442878e-011))*x+(3.1346599390265817e-010))*x+(-7.5136075139425884e-009))*x+(1.9460714713777824e-007))*x+(-3.7422280829470709e-006))*x+(7.1807682581923952e-005))*x+(-0.0012241707047083367))*x+(0.015363163510094003));
		rts[1] = (((((((((((((1.4915713109076023e-010))*x+(-1.5764574830730755e-011))*x+(-8.7993612396530807e-011))*x+(2.197945529284576e-012))*x+(-6.993635300508079e-011))*x+(4.7689259948432061e-010))*x+(-5.6825617100741959e-008))*x+(2.0977230642908271e-006))*x+(-4.4612345795095688e-005))*x+(0.00086267559017866302))*x+(-0.013909065053611567))*x+(0.16003531136829172));
		rts[2] = (((((((((((((9.8953023552894592e-010))*x+(-9.701276818911234e-012))*x+(-6.3907161044577754e-010))*x+(8.3067182761927441e-011))*x+(2.9134146946792799e-010))*x+(-3.3025306341490555e-008))*x+(2.3629294313802043e-007))*x+(6.5328632932922411e-006))*x+(-0.0002315105177676339))*x+(0.0048175642253972884))*x+(-0.069146891534383997))*x+(0.64600391295737503));
		rts[3] = (((((((((((((6.7520886659622192e-009))*x+(5.9177788595358527e-010))*x+(-4.2297566930452985e-009))*x+(-2.7672892125944295e-009))*x+(3.4897311707027256e-009))*x+(4.1213066500252654e-007))*x+(9.0075597351339332e-007))*x+(-7.6454715464061934e-005))*x+(-0.00093329906888683922))*x+(0.044633417817461218))*x+(-0.57511245174077097))*x+(3.4914730819351245));
		wts[0] = (((((((((((((1.7947362114985782e-010))*x+(-2.4253192047278084e-011))*x+(-1.0550138540565968e-010))*x+(2.4859521848460034e-011))*x+(-2.5971758077503177e-010))*x+(4.1227679048461141e-009))*x+(-7.2745701610680641e-008))*x+(1.5230219313859075e-006))*x+(-2.643511076771965e-005))*x+(0.00048292527150558162))*x+(-0.0095066825800379975))*x+(0.21667842288576572));
		wts[1] = (((((((((((((1.6795335492740074e-010))*x+(3.152914966146151e-011))*x+(-1.1751429459157709e-010))*x+(1.6802914615254849e-010))*x+(-2.6192168434135961e-009))*x+(3.723076484144864e-008))*x+(-4.9188491013651969e-007))*x+(5.9610615415669104e-006))*x+(-6.9025105694814348e-005))*x+(0.00072125236212837907))*x+(-0.0064698149652293131))*x+(0.077755259326060366));
		wts[2] = (((((((((((((7.2001663890356813e-012))*x+(5.1159076974727213e-012))*x+(-4.9003764009588245e-011))*x+(5.5187854286486981e-010))*x+(-6.3314532875817049e-009))*x+(6.7522342532081809e-008))*x+(-6.610173545381256e-007))*x+(5.8342610980699483e-006))*x+(-4.640212016424871e-005))*x+(0.00032117744818106346))*x+(-0.0017427307349209336))*x+(0.0092081930578450898));
		wts[3] = (((((((((((((-4.2632564145606011e-013))*x+(3.7564025963850627e-012))*x+(-4.2057616648586795e-011))*x+(4.4603950162998746e-010))*x+(-4.2745956404151757e-009))*x+(3.670500658969899e-008))*x+(-2.7842129654796305e-007))*x+(1.8287051066628866e-006))*x+(-1.0124917615454495e-005))*x+(4.5261748984950089e-005))*x+(-0.00014891859180426843))*x+(0.00032008992322919775));
		break;
	case 9:
		rts[0] = (((((((((((((1.152026622245709e-011))*x+(-1.2126596023639042e-012))*x+(-4.5095778962907681e-012))*x+(1.4400332778071363e-012))*x+(-2.0150991986156441e-011))*x+(1.4929509480528699e-010))*x+(-6.1431711569544705e-009))*x+(1.6087878751402937e-007))*x+(-3.033533127416721e-006))*x+(6.1677686237271434e-005))*x+(-0.0010910394559906864))*x+(0.014207245642137495));
		rts[1] = (((((((((((((2.3161798405150572e-010))*x+(9.701276818911234e-012))*x+(-1.4589810840940723e-010))*x+(-1.2884508275116478e-012))*x+(-5.6559201766503975e-011))*x+(-1.9043019013527857e-010))*x+(-5.5963643497136673e-008))*x+(1.8174600822836358e-006))*x+(-3.6783420531316668e-005))*x+(0.00074086186128739329))*x+(-0.012309441920526068))*x+(0.14694635084358298));
		rts[2] = (((((((((((((6.0147916277249647e-010))*x+(-4.3655745685100555e-011))*x+(-3.7774346613635618e-010))*x+(9.8831757592658193e-011))*x+(8.3192238283421216e-010))*x+(-2.9860435309577347e-008))*x+(4.5539761591347393e-008))*x+(7.2295544129019609e-006))*x+(-0.0002036670432747911))*x+(0.0041641027824609687))*x+(-0.060179178158112301))*x+(0.58144981149889419));
		rts[3] = (((((((((((((2.1730860074361163e-009))*x+(3.2984341184298194e-010))*x+(-1.1593025798598924e-009))*x+(-2.313754521310329e-009))*x+(-1.5768212809537847e-008))*x+(3.6403184822120238e-007))*x+(3.2944221857178491e-006))*x+(-6.5845896945878238e-005))*x+(-0.001221911536039973))*x+(0.041389968920563604))*x+(-0.48894435670168723))*x+(2.9599856073085951));
		wts[0] = (((((((((((((2.9467628337442875e-010))*x+(-4.850638409455617e-012))*x+(-1.8318739118209729e-010))*x+(7.806496190217633e-012))*x+(-1.7566511208618368e-010))*x+(2.3939226897103558e-009))*x+(-5.3413548251057812e-008))*x+(1.2119689068631108e-006))*x+(-2.0997279146265736e-005))*x+(0.00041208687241534037))*x+(-0.0086143861400299147))*x+(0.20762968459842895));
		wts[1] = (((((((((((((9.7619097990294293e-011))*x+(-1.9099388737231493e-011))*x+(-7.3555384005885558e-011))*x+(1.1444474997309347e-010))*x+(-1.4977056631929977e-009))*x+(2.3070944858242605e-008))*x+(-3.1491102688481953e-007))*x+(3.9792683141174718e-006))*x+(-4.9438095992976321e-005))*x+(0.00054553233258669098))*x+(-0.005212794466209458))*x+(0.071943175556317643));
		wts[2] = (((((((((((((1.1141310096718371e-011))*x+(-2.7663797178926566e-012))*x+(-2.8255916125393316e-011))*x+(2.7143206201192999e-010))*x+(-3.1824794651432358e-009))*x+(3.5528407623293859e-008))*x+(-3.6278569887082668e-007))*x+(3.3540830046881651e-006))*x+(-2.8518858483949961e-005))*x+(0.00021126034843791007))*x+(-0.0012191853815728018))*x+(0.0077454725960272334));
		wts[3] = (((((((((((((6.7738407475796214e-013))*x+(1.3642420526593924e-012))*x+(-1.8398023845141626e-011))*x+(1.9173329590671528e-010))*x+(-1.8675359407064698e-009))*x+(1.6380174809131155e-008))*x+(-1.2748956089089769e-007))*x+(8.6415659241179566e-007))*x+(-4.9879868270480896e-006))*x+(2.3546944972849765e-005))*x+(-8.2653601938942656e-005))*x+(0.00020789128434100661));
		break;
	case 10:
		rts[0] = (((((((((((((1.8114102810310819e-011))*x+(4.1685173831259209e-013))*x+(-1.0066022089934752e-011))*x+(1.5442462123852845e-012))*x+(-7.9403150721191196e-012))*x+(4.15343315296468e-011))*x+(-5.6075910396617222e-009))*x+(1.3177245918501632e-007))*x+(-2.4491113464648879e-006))*x+(5.3482771655979804e-005))*x+(-0.00097617112143716345))*x+(0.013175005204892136));
		rts[1] = (((((((((((((1.7098500393331051e-010))*x+(6.6696278130014735e-012))*x+(-1.0239394517460218e-010))*x+(7.427540064478915e-012))*x+(1.1387631578448541e-011))*x+(-5.7733255213558244e-010))*x+(-5.8557456661390006e-008))*x+(1.5321579909984469e-006))*x+(-3.0079764275769971e-005))*x+(0.00064085218621457807))*x+(-0.010931080147173875))*x+(0.13534274858836928));
		rts[2] = (((((((((((((2.6193447411060333e-010))*x+(-6.305829932292302e-011))*x+(-1.4733814168721437e-010))*x+(1.0580455030625065e-010))*x+(1.3430963008431718e-009))*x+(-2.259344000776764e-008))*x+(-1.1376875145667023e-007))*x+(7.040811260831485e-006))*x+(-0.00017486012558013778))*x+(0.0035965044118470382))*x+(-0.05243300107008933))*x+(0.5252383151484642));
		rts[3] = (((((((((((((3.647680083910624e-009))*x+(2.1342809001604715e-010))*x+(-2.1197289849321046e-009))*x+(-1.0307606620093186e-009))*x+(-2.792906646694367e-008))*x+(2.0275971716425073e-007))*x+(5.0383498167623965e-006))*x+(-4.4607775729825036e-005))*x+(-0.0014457401198354107))*x+(0.037367171855681384))*x+(-0.4100750088782314))*x+(2.5111471025144456));
		wts[0] = (((((((((((((1.8553691916167736e-010))*x+(-1.7583564234276612e-011))*x+(-1.0724458358405779e-010))*x+(1.9781509763561189e-011))*x+(-1.2187229003757238e-010))*x+(1.1278231681899342e-009))*x+(-4.3102991102254386e-008))*x+(9.7385425679163973e-007))*x+(-1.664272647533549e-005))*x+(0.00035586434538106837))*x+(-0.0078486104929666629))*x+(0.19940754879610087));
		wts[1] = (((((((((((((2.6678511252005894e-011))*x+(-1.152026622245709e-011))*x+(-2.2434202643732228e-011))*x+(6.07845625684907e-011))*x+(-8.9830602216049249e-010))*x+(1.4837970259880724e-008))*x+(-2.0329902679823891e-007))*x+(2.7042222116394994e-006))*x+(-3.6256426416099899e-005))*x+(0.00041826150961158748))*x+(-0.0042555729579878436))*x+(0.067230161340975592));
		wts[2] = (((((((((((((8.3370347662518416e-012))*x+(1.4210854715202004e-012))*x+(-1.588773557159584e-011))*x+(1.3241911271203813e-010))*x+(-1.6403411962073733e-009))*x+(1.926928046754502e-008))*x+(-2.0374436963492096e-007))*x+(1.9780938038764053e-006))*x+(-1.8117795966922368e-005))*x+(0.0001426733156646729))*x+(-0.00087042599566209105))*x+(0.0067120525958899316));
		wts[3] = (((((((((((((2.2145248597856454e-013))*x+(6.4955448427402485e-013))*x+(-7.8341037360966457e-012))*x+(8.3358209224115853e-011))*x+(-8.2816594323039305e-010))*x+(7.4438451074428543e-009))*x+(-5.9613390689973456e-008))*x+(4.1849182110063193e-007))*x+(-2.5346242847507565e-006))*x+(1.2704295783245824e-005))*x+(-4.7617899997278372e-005))*x+(0.00014454799530551492));
		break;
	case 11:
		rts[0] = (((((((((((((1.5916157281026244e-012))*x+(1.5537201155287523e-012))*x+(-2.605323364453701e-013))*x+(9.2844250805986418e-013))*x+(3.1773102667405811e-012))*x+(1.9154307769516286e-011))*x+(-5.4716282060773827e-009))*x+(1.0413074341686367e-007))*x+(-1.9775158372539272e-006))*x+(4.6870461363625902e-005))*x+(-0.00087605366575382751))*x+(0.012249993942156539));
		rts[1] = (((((((((((((1.7098500393331051e-010))*x+(-1.0307606620093186e-011))*x+(-1.0542559418051194e-010))*x+(2.0539422015038628e-011))*x+(1.3297570452171687e-010))*x+(-2.285602818119514e-010))*x+(-6.1405008781415888e-008))*x+(1.2313817826144675e-006))*x+(-2.4547795552665171e-005))*x+(0.00055921179857014902))*x+(-0.0097337826417945618))*x+(0.12502391389090781));
		rts[2] = (((((((((((((5.4812214026848472e-010))*x+(-8.7311491370201111e-011))*x+(-3.7016434362158179e-010))*x+(8.746307382049659e-011))*x+(1.8099323521407009e-009))*x+(-1.1772442576329922e-008))*x+(-2.1824907866137741e-007))*x+(6.1836356503401167e-006))*x+(-0.00014823662957967146))*x+(0.0031127218936294701))*x+(-0.045737103993792667))*x+(0.47623386420463582));
		rts[3] = (((((((((((((2.3865140974521637e-009))*x+(4.8506384094556168e-011))*x+(-1.3642420526593924e-009))*x+(5.6024873629212369e-010))*x+(-2.9060174711048603e-008))*x+(-6.6683014665613882e-009))*x+(5.6297972956069007e-006))*x+(-1.7410171035218504e-005))*x+(-0.0015707628224435053))*x+(0.032815114121689984))*x+(-0.33983011282118714))*x+(2.1369541295769223));
		wts[0] = (((((((((((((3.0073958138624824e-010))*x+(-2.5465851649641991e-011))*x+(-1.8705274366463223e-010))*x+(2.7891170854369797e-011))*x+(-8.5075650228342705e-012))*x+(4.5221308179558645e-010))*x+(-3.8678004206834281e-008))*x+(7.7110132856716973e-007))*x+(-1.3160085264640742e-005))*x+(0.00031136254281292442))*x+(-0.0071831242030857044))*x+(0.19189909167282723));
		wts[1] = (((((((((((((5.6995001311103501e-011))*x+(-1.2732925824820995e-011))*x+(-4.1306217705520489e-011))*x+(3.4750276730240629e-011))*x+(-5.7609857625114569e-010))*x+(9.7524737914985362e-009))*x+(-1.3062268215217426e-007))*x+(1.8820727346972415e-006))*x+(-2.7204598984698066e-005))*x+(0.00032388959601585093))*x+(-0.003517935705494865))*x+(0.063359108376708384));
		wts[2] = (((((((((((((1.3263464400855202e-011))*x+(2.2737367544323206e-012))*x+(-1.3438731609009361e-011))*x+(6.4657020478383246e-011))*x+(-8.7513522354735563e-010))*x+(1.0763127870442682e-008))*x+(-1.1630311452792697e-007))*x+(1.1990882372026057e-006))*x+(-1.1908285576737314e-005))*x+(9.8408989517395171e-005))*x+(-0.00063243399800973091))*x+(0.0059679742202355113));
		wts[3] = (((((((((((((2.8303285641110654e-013))*x+(2.5638750382010278e-013))*x+(-3.5175566163540375e-012))*x+(3.6742682970232941e-011))*x+(-3.734662209116853e-010))*x+(3.4528577289028028e-009))*x+(-2.8496839392551373e-008))*x+(2.0808675446395047e-007))*x+(-1.3328060798249882e-006))*x+(7.1115903494515544e-006))*x+(-2.8397811382157486e-005))*x+(0.00010746533718262548));
		break;
	case 12:
		rts[0] = (((((((((((((7.1243751638879376e-012))*x+(1.6295113406764963e-012))*x+(-3.666400516522117e-012))*x+(-3.6474527102351796e-013))*x+(1.3359387670182816e-011))*x+(8.0935110465437291e-011))*x+(-5.2063774402810736e-009))*x+(7.7279399305722293e-008))*x+(-1.6151261321960728e-006))*x+(4.1508381118786693e-005))*x+(-0.00078785597556089797))*x+(0.011418931905000967));
		rts[1] = (((((((((((((1.4309383307894069e-010))*x+(6.6696278130014735e-012))*x+(-8.8978898323451475e-011))*x+(-9.8528592692067199e-013))*x+(2.0863429502545233e-010))*x+(8.7975848828136794e-010))*x+(-5.9734685346294711e-008))*x+(9.2575068884788913e-007))*x+(-2.0236218444306491e-005))*x+(0.0004923419683403133))*x+(-0.0086843843987602642))*x+(0.11582596512795842));
		rts[2] = (((((((((((((8.246085296074549e-010))*x+(-3.637978807091713e-011))*x+(-5.4509049126257492e-010))*x+(-2.7739588404074311e-011))*x+(1.7861718030568832e-009))*x+(4.4581346022217378e-010))*x+(-2.5196817195668087e-007))*x+(4.9774448610169957e-006))*x+(-0.0001258583490488796))*x+(0.0027027917693980643))*x+(-0.039932785080217172))*x+(0.43346720085546109));
		rts[3] = (((((((((((((3.279031564791997e-009))*x+(-2.0372681319713593e-010))*x+(-2.1112403677155571e-009))*x+(1.7062120605260134e-009))*x+(-1.960097506525926e-008))*x+(-1.8456099345106242e-007))*x+(5.0232763868507391e-006))*x+(9.6696211121146299e-006))*x+(-0.0015852220856767592))*x+(0.028053967393626571))*x+(-0.27895390433031664))*x+(1.8283565523823659));
		wts[0] = (((((((((((((1.9766351518531639e-010))*x+(6.063298011819521e-012))*x+(-1.1679427795267353e-010))*x+(3.1832314562052488e-012))*x+(6.163721385140282e-011))*x+(4.4150757124346757e-010))*x+(-3.6301080956017501e-008))*x+(5.8369669690231752e-007))*x+(-1.0454343423301388e-005))*x+(0.0002761282980701662))*x+(-0.0065969858522545366))*x+(0.18501490277274754));
		wts[1] = (((((((((((((7.6397554948925972e-011))*x+(-9.701276818911234e-012))*x+(-5.350860495430728e-011))*x+(2.1051012784785897e-011))*x+(-4.0668150328807917e-010))*x+(6.2864321156060523e-009))*x+(-8.3073242507225573e-008))*x+(1.3564780424838809e-006))*x+(-2.0806557526287239e-005))*x+(0.00025239673038060512))*x+(-0.0029448405019458709))*x+(0.06013961831291291));
		wts[2] = (((((((((((((-3.8274568699610727e-012))*x+(7.5791225147744016e-014))*x+(3.765876499528531e-013))*x+(3.3637093110883136e-011))*x+(-4.9416056432013034e-010))*x+(6.1166177308299057e-009))*x+(-6.6996474433015735e-008))*x+(7.5238006687812953e-007))*x+(-8.08708393780673e-006))*x+(6.8860341732819574e-005))*x+(-0.00046706711299332747))*x+(0.0054231336586458108));
		wts[3] = (((((((((((((9.8291745113480517e-014))*x+(1.3026616822268503e-013))*x+(-1.5191551720287557e-012))*x+(1.6399585393382189e-011))*x+(-1.7197556341959813e-010))*x+(1.6373868788610577e-009))*x+(-1.3923750719242733e-008))*x+(1.0652731783234587e-007))*x+(-7.276349575655929e-007))*x+(4.1215938131053641e-006))*x+(-1.7464816971861277e-005))*x+(8.5029013006782421e-005));
		break;
	case 13:
		rts[0] = (((((((((((((-2.8800665556142726e-012))*x+(-3.2211270687791207e-012))*x+(3.2306009719225886e-012))*x+(1.3358203432289883e-012))*x+(1.2088700411065171e-011))*x+(1.7883516889583007e-010))*x+(-4.4273842740120512e-009))*x+(5.2944894191053749e-008))*x+(-1.3559753938597689e-006))*x+(3.7076113596803149e-005))*x+(-0.00070940092644471132))*x+(0.010671041351707822));
		rts[1] = (((((((((((((9.0343140376110867e-011))*x+(-4.2443086082736646e-012))*x+(-5.5896028546461204e-011))*x+(-8.0338698656608666e-012))*x+(1.7214082011681359e-010))*x+(2.1804495986543766e-009))*x+(-5.0451066879730881e-008))*x+(6.4699922930344655e-007))*x+(-1.7106225053918161e-005))*x+(0.00043660771630620499))*x+(-0.00775699815866594))*x+(0.10761455356799864));
		rts[2] = (((((((((((((5.7722597072521842e-010))*x+(2.4253192047278084e-011))*x+(-3.7925929063931108e-010))*x+(-1.3202831420737007e-010))*x+(1.072635313903447e-009))*x+(1.0032636055257171e-008))*x+(-2.181478571117168e-007))*x+(3.7781031553644575e-006))*x+(-0.00010840441086235053))*x+(0.0023526018035625964))*x+(-0.034886112726381639))*x+(0.39611607673812943));
		rts[3] = (((((((((((((2.0954757928848267e-009))*x+(-1.9402553637822467e-010))*x+(-1.3460521586239338e-009))*x+(1.7904919028903046e-009))*x+(-6.2074529220505302e-009))*x+(-2.7820624382002279e-007))*x+(3.5870854067828377e-006))*x+(3.1430114982337415e-005))*x+(-0.0015006128503500802))*x+(0.023403407589979018))*x+(-0.22753907563251208))*x+(1.5758858832849083));
		wts[0] = (((((((((((((2.5950915490587551e-010))*x+(-2.4253192047278084e-011))*x+(-1.6446695857060451e-010))*x+(1.6749860757651426e-011))*x+(1.1709744285326451e-010))*x+(8.9436487845280977e-010))*x+(-3.2433980242293117e-008))*x+(4.1070662189686874e-007))*x+(-8.4719374919458214e-006))*x+(0.00024791210178206252))*x+(-0.0060739360173126368))*x+(0.17868413875980094));
		wts[1] = (((((((((((((9.4587448984384537e-011))*x+(3.637978807091713e-012))*x+(-6.2376178296593324e-011))*x+(1.0894988614988202e-011))*x+(-2.9378099952737102e-010))*x+(3.7480631931430253e-009))*x+(-5.3357730974331233e-008))*x+(1.0217524404332321e-006))*x+(-1.6099492756012818e-005))*x+(0.00019737111186006925))*x+(-0.0024974212580228445))*x+(0.057427647272229002));
		wts[2] = (((((((((((((5.6464462735069292e-012))*x+(-1.1558161835030962e-012))*x+(-4.4314181953571579e-012))*x+(1.9430975347252872e-011))*x+(-2.9062915037532849e-010))*x+(3.4388016138346225e-009))*x+(-3.9031937173102563e-008))*x+(4.9396881832142181e-007))*x+(-5.6407608783459046e-006))*x+(4.852565673792713e-005))*x+(-0.00035089964854641156))*x+(0.0050175308415971696));
		wts[3] = (((((((((((((-1.0066022089934752e-013))*x+(3.7895612573872008e-014))*x+(-5.7953641885433171e-013))*x+(7.4826071265003212e-012))*x+(-8.1294966129223198e-011))*x+(7.9217174486778674e-010))*x+(-6.9491882485663474e-009))*x+(5.6437479739370369e-008))*x+(-4.1322540488397338e-007))*x+(2.4599763598910775e-006))*x+(-1.1039304026304785e-005))*x+(7.1052238919867123e-005));
		break;
	case 14:
		rts[0] = (((((((((((((-8.6401996668428183e-012))*x+(1.5158245029548803e-013))*x+(7.4370139676223825e-012))*x+(-1.5489831639570184e-012))*x+(2.01320441798695e-012))*x+(2.4499483923060928e-010))*x+(-3.1228628201892166e-009))*x+(3.3901742043281516e-008))*x+(-1.1844667924231409e-006))*x+(3.328452689025397e-005))*x+(-0.00063912582134302521))*x+(0.0099974092725686886));
		rts[1] = (((((((((((((7.2153246340652303e-011))*x+(-9.0949470177292824e-012))*x+(-4.2329399245015033e-011))*x+(-1.2770821437394865e-011))*x+(4.3210472237357557e-011))*x+(2.9026973417482318e-009))*x+(-3.4748584898380834e-008))*x+(4.3217890569972422e-007))*x+(-1.4974189323530007e-005))*x+(0.0003887022814479853))*x+(-0.0069327515403145006))*x+(0.10027765577951479));
		rts[2] = (((((((((((((6.7423873891433073e-010))*x+(7.1546916539470346e-011))*x+(-4.3989227075750626e-010))*x+(-1.5961632016114891e-010))*x+(1.222512461633111e-010))*x+(1.3555606415138755e-008))*x+(-1.4400600771106534e-007))*x+(2.8639683744557942e-006))*x+(-9.5244983686256404e-005))*x+(0.0020480436046616162))*x+(-0.030492034510638612))*x+(0.36347773226450286));
		rts[3] = (((((((((((((3.8611081739266711e-009))*x+(-5.8207660913467407e-011))*x+(-2.620557400708397e-009))*x+(1.1835557719071705e-009))*x+(5.7240564880582196e-009))*x+(-2.8040729678953841e-007))*x+(1.8703913961341336e-006))*x+(4.5078246396694034e-005))*x+(-0.0013447213613379343))*x+(0.019121757402416801))*x+(-0.18509214444728306))*x+(1.3702843365813879));
		wts[0] = (((((((((((((2.0372681319713593e-010))*x+(-4.2443086082736646e-012))*x+(-1.2914824765175581e-010))*x+(-4.0927261579781771e-012))*x+(8.3161921793362126e-011))*x+(1.4067254028304887e-009))*x+(-2.5425496374964496e-008))*x+(2.6478210172579486e-007))*x+(-7.1326709284077099e-006))*x+(0.00022465137264344551))*x+(-0.0056020410038476881))*x+(0.17285002216089987));
		wts[1] = (((((((((((((8.276401786133647e-011))*x+(-6.063298011819521e-012))*x+(-5.3717030823463574e-011))*x+(1.6427748050773516e-011))*x+(-1.8813750557455933e-010))*x+(1.9642219702594348e-009))*x+(-3.6599010414898693e-008))*x+(8.0132555095128544e-007))*x+(-1.2481141562941295e-005))*x+(0.00015471969542329989))*x+(-0.0021471368512522419))*x+(0.05511246948189831));
		wts[2] = (((((((((((((-6.8212102632969618e-013))*x+(-1.7621459846850485e-012))*x+(6.300145590406221e-013))*x+(1.3294254586071474e-011))*x+(-1.7133198563594002e-010))*x+(1.8518384603538607e-009))*x+(-2.3578250518685447e-008))*x+(3.413949660654077e-007))*x+(-3.9956497799714195e-006))*x+(3.4222825606405126e-005))*x+(-0.00026897116608460712))*x+(0.004709974191236416));
		wts[3] = (((((((((((((-1.4506914188435377e-013))*x+(-1.3914795241968628e-014))*x+(-1.8907098109366413e-013))*x+(3.5503822104487877e-012))*x+(-3.9402481277761574e-011))*x+(3.8807142106282255e-010))*x+(-3.5536267405274213e-009))*x+(3.1181612334853455e-008))*x+(-2.4359830261923971e-007))*x+(1.4997972054433762e-006))*x+(-7.1637849641850936e-006))*x+(6.2109891913448924e-005));
		break;
	case 15:
		rts[0] = (((((((((((((7.9580786405131221e-012))*x+(7.2001663890356815e-013))*x+(-5.2343314867660711e-012))*x+(-1.6579330501069003e-012))*x+(-5.6671704366332652e-012))*x+(2.3501571059606852e-010))*x+(-1.6437368318319063e-009))*x+(2.2010432606152836e-008))*x+(-1.0751217219609013e-006))*x+(2.9907030250924185e-005))*x+(-0.00057598868821881369))*x+(0.0093904145377651481));
		rts[1] = (((((((((((((1.1095835361629725e-010))*x+(2.4253192047278085e-012))*x+(-6.9159492947316422e-011))*x+(-1.5916157281026244e-011))*x+(-8.3881938432265685e-011))*x+(2.6558240051599569e-009))*x+(-1.7596821629458265e-008))*x+(3.0195442501934622e-007))*x+(-1.3534669722379636e-005))*x+(0.0003460690891171625))*x+(-0.0061986970479712272))*x+(0.09371903268272222));
		rts[2] = (((((((((((((3.2984341184298194e-010))*x+(4.7293724492192268e-011))*x+(-1.9523819598058859e-010))*x+(-8.625041421813269e-011))*x+(-6.3982952269725491e-010))*x+(1.0936365886967298e-008))*x+(-6.8104924366707564e-008))*x+(2.3404151156351341e-006))*x+(-8.4963530612232788e-005))*x+(0.0017782530354283899))*x+(-0.026670865830108338))*x+(0.33494122980163032));
		rts[3] = (((((((((((((1.0477378964424133e-009))*x+(6.7908937732378633e-011))*x+(-7.1789448459943139e-010))*x+(3.4015101846307516e-010))*x+(1.1428710422478616e-008))*x+(-2.19374593749914e-007))*x+(3.4949597231085739e-007))*x+(5.047386247743664e-005))*x+(-0.0011510750488816037))*x+(0.015372698168780136))*x+(-0.15069476655075351))*x+(1.2030159026643903));
		wts[0] = (((((((((((((2.6921043172478676e-010))*x+(2.5465851649641991e-011))*x+(-1.7568405989247063e-010))*x+(-2.5314269199346502e-011))*x+(3.0259646640236802e-011))*x+(1.575969577061187e-009))*x+(-1.6259146325599733e-008))*x+(1.6016977196405455e-007))*x+(-6.2981228442504636e-006))*x+(0.00020460987718205295))*x+(-0.0051731954890900907))*x+(0.16746574067263101));
		wts[1] = (((((((((((((1.482476363889873e-010))*x+(1.3339255626002947e-011))*x+(-9.4037962602063388e-011))*x+(2.7853275241795927e-012))*x+(-7.7217047570835946e-011))*x+(9.3219180522889157e-010))*x+(-2.8276616973836134e-008))*x+(6.41725108459686e-007))*x+(-9.6087908336752372e-006))*x+(0.00012174388108896854))*x+(-0.0018721080801881297))*x+(0.053108337689787212));
		wts[2] = (((((((((((((9.587589981189618e-012))*x+(1.0231815394945443e-012))*x+(-6.5772572573526605e-012))*x+(7.6075442242048049e-012))*x+(-8.8996365832372248e-011))*x+(9.5620844575705612e-010))*x+(-1.5434809347292244e-008))*x+(2.4609328800699143e-007))*x+(-2.8341524646250068e-006))*x+(2.4072978490405583e-005))*x+(-0.00021125476673352088))*x+(0.0044715497104951575));
		wts[3] = (((((((((((((-2.6053233644537006e-014))*x+(1.5395092608135503e-014))*x+(-1.1442698640469948e-013))*x+(1.7366663662699011e-012))*x+(-1.9216600533056294e-011))*x+(1.912715888452432e-010))*x+(-1.8855466632494711e-009))*x+(1.8071569847192871e-008))*x+(-1.4784884413933039e-007))*x+(9.2563929941770257e-007))*x+(-4.7859484915327761e-006))*x+(5.6230285795654139e-005));
		break;
	case 16:
		rts[0] = (((((((((((((1.1368683772161603e-011))*x+(-3.637978807091713e-012))*x+(-6.518045362705986e-012))*x+(1.8900436771218665e-012))*x+(-1.1938894317609083e-011))*x+(1.5988928699547006e-010))*x+(-4.357784503620602e-010))*x+(1.700066494988069e-008))*x+(-9.9912016036698037e-007))*x+(2.6800639363546337e-005))*x+(-0.00051931881701359833))*x+(0.0088432783517742846));
		rts[1] = (((((((((((((1.570394185061256e-010))*x+(3.0316490059097605e-012))*x+(-1.0129497240995988e-010))*x+(-3.7137700322394567e-012))*x+(-1.378547646406029e-010))*x+(1.6888108689272485e-009))*x+(-4.3497423440896901e-009))*x+(2.495404792431562e-007))*x+(-1.2453832126992543e-005))*x+(0.00030713825916429494))*x+(-0.0055460279001054201))*x+(0.087853156956609307));
		rts[2] = (((((((((((((3.4924596548080444e-010))*x+(2.4253192047278085e-012))*x+(-2.0342364829654497e-010))*x+(1.2732925824820995e-011))*x+(-7.830180948076304e-010))*x+(5.3266546728991671e-009))*x+(-1.885032100782761e-008))*x+(2.1372118024961155e-006))*x+(-7.6090527475702885e-005))*x+(0.0015368723048594009))*x+(-0.02336016875931362))*x+(0.30996593599090116));
		rts[3] = (((((((((((((1.2611659864584604e-009))*x+(-7.2759576141834259e-011))*x+(-7.8337810312708212e-010))*x+(-1.2247861983875433e-010))*x+(1.2178058265514361e-008))*x+(-1.3507919523666107e-007))*x+(-7.1633382958680158e-007))*x+(4.934467461718365e-005))*x+(-0.00094966079518628754))*x+(0.012222766137386449))*x+(-0.12320018712274571))*x+(1.0665933748329881));
		wts[0] = (((((((((((((2.6072181450823939e-010))*x+(-1.8189894035458565e-011))*x+(-1.6590699184841165e-010))*x+(4.3958910585691537e-012))*x+(-2.7360632278335587e-011))*x+(1.2910561508761018e-009))*x+(-7.473194507667813e-009))*x+(1.0156541148849858e-007))*x+(-5.7893588127725738e-006))*x+(0.00018653711673473811))*x+(-0.0047823014037418256))*x+(0.16249100240624881));
		wts[1] = (((((((((((((9.7012768189112337e-011))*x+(1.0610771520684161e-012))*x+(-6.3209881773218513e-011))*x+(6.1011936243933941e-012))*x+(-9.5875899811896196e-012))*x+(5.2756199409031979e-010))*x+(-2.416269199538116e-008))*x+(5.1163010354275207e-007))*x+(-7.3088491568210987e-006))*x+(9.649731809696406e-005))*x+(-0.0016550161786558399))*x+(0.051348978993779479));
		wts[2] = (((((((((((((1.1368683772161603e-011))*x+(-1.6863547595373043e-012))*x+(-7.4938573864831905e-012))*x+(5.7459222565133424e-012))*x+(-3.7474023883987684e-011))*x+(5.1880788554115032e-010))*x+(-1.1189040804993056e-008))*x+(1.8061910351622562e-007))*x+(-1.9877441576517567e-006))*x+(1.6905391493217112e-005))*x+(-0.00017069890182138905))*x+(0.0042817653018693922));
		wts[3] = (((((((((((((1.2404891928478415e-013))*x+(-8.4376949871511897e-015))*x+(-1.5152693914425677e-013))*x+(8.7204317840890622e-013))*x+(-9.1672040329153024e-012))*x+(9.5917556883207121e-011))*x+(-1.0587938381225134e-009))*x+(1.0947091530503239e-008))*x+(-9.1177879926428702e-008))*x+(5.741765898260686e-007))*x+(-3.3143319433349559e-006))*x+(5.223848745545117e-005));
		break;
	case 17:
		rts[0] = (((((((((((((2.5390060424494244e-011))*x+(1.3263464400855203e-012))*x+(-1.6366167680340972e-011))*x+(-5.068538181755381e-013))*x+(-8.6585553541832886e-012))*x+(6.7339763395087487e-011))*x+(2.4349661176259474e-010))*x+(1.6755937156294934e-008))*x+(-9.3273861663870083e-007))*x+(2.3903048700899099e-005))*x+(-0.00046864820659204865))*x+(0.0083497777658395941));
		rts[1] = (((((((((((((1.4430649268130461e-010))*x+(-5.4569682106375694e-012))*x+(-8.8296777297121779e-011))*x+(9.587589981189618e-012))*x+(-1.2060278701634766e-010))*x+(5.9474558611327656e-010))*x+(2.4230658960770293e-009))*x+(2.4748578889936346e-007))*x+(-1.1471039794615686e-005))*x+(0.00027125245374949125))*x+(-0.0049681274585195636))*x+(0.082602060202678296));
		rts[2] = (((((((((((((4.268561800320943e-010))*x+(-8.4886172165473291e-012))*x+(-2.6163130921001232e-010))*x+(4.8657966544851661e-011))*x+(-4.9781571457666962e-010))*x+(3.4886227240349399e-010))*x+(-2.7970668744122422e-009))*x+(2.095632019324019e-006))*x+(-6.7651271154378634e-005))*x+(0.0013212986762950278))*x+(-0.020506214777196254))*x+(0.28806867189432517));
		rts[3] = (((((((((((((1.3969838619232178e-009))*x+(4.8506384094556168e-011))*x+(-8.9615544614692532e-010))*x+(-4.5596001048882801e-010))*x+(9.6501177419365068e-009))*x+(-5.8656837609305512e-008))*x+(-1.2883671397882306e-006))*x+(4.4141381010831537e-005))*x+(-0.00076173838571591535))*x+(0.0096609090298536895))*x+(-0.10141056805749414))*x+(0.95471479815671545));
		wts[0] = (((((((((((((2.0251415359477201e-010))*x+(-6.6696278130014735e-012))*x+(-1.1558161835030961e-010))*x+(3.0316490059097605e-012))*x+(-5.7847652594015627e-011))*x+(7.6251419992937975e-010))*x+(-1.2531116884891465e-009))*x+(8.1098340191469262e-008))*x+(-5.4344126490524216e-006))*x+(0.00016972165795933744))*x+(-0.0044262190633059762))*x+(0.15788954407974373));
		wts[1] = (((((((((((((1.0853303441156943e-010))*x+(-6.9727927135924493e-012))*x+(-7.2039559502930687e-011))*x+(5.6843418860808007e-012))*x+(2.6076918402395674e-011))*x+(4.9825506683494792e-010))*x+(-2.1198169886105234e-008))*x+(3.9829550161722216e-007))*x+(-5.4939015369885134e-006))*x+(7.7406515537887605e-005))*x+(-0.0014820193300915702))*x+(0.04978363926252681));
		wts[2] = (((((((((((((5.3432813729159534e-012))*x+(-1.0231815394945443e-012))*x+(-4.1993075683421921e-012))*x+(2.5413745182352914e-012))*x+(-1.1919650451848913e-011))*x+(3.4986783840433111e-010))*x+(-8.6728327390132396e-009))*x+(1.3138112218517387e-007))*x+(-1.3679071987054287e-006))*x+(1.1921069767805921e-005))*x+(-0.00014218194398700075))*x+(0.0041261539619182747));
		wts[3] = (((((((((((((-3.4638958368304884e-014))*x+(-5.1810407815840636e-015))*x+(-2.1038726316646716e-014))*x+(4.126328908190165e-013))*x+(-4.2910628753981915e-012))*x+(5.0867575776547547e-011))*x+(-6.3543561088589184e-010))*x+(6.8230931478425782e-009))*x+(-5.6337455573314621e-008))*x+(3.5700536115223564e-007))*x+(-2.400500451736168e-006))*x+(4.9417130053636546e-005));
		break;
	case 18:
		rts[0] = (((((((((((((1.6674069532503684e-012))*x+(-1.5158245029548803e-012))*x+(-1.0800249583553521e-012))*x+(1.5205614545266142e-012))*x+(-7.3251034867401667e-012))*x+(-4.1990115088689582e-012))*x+(4.1579080919026029e-010))*x+(1.858357591884759e-008))*x+(-8.6234037123313523e-007))*x+(2.1208566863121826e-005))*x+(-0.00042357176232913924))*x+(0.0079041169243071405));
		rts[1] = (((((((((((((9.398111918320258e-011))*x+(-1.2126596023639042e-012))*x+(-5.9609798578700663e-011))*x+(7.617018127348274e-012))*x+(-6.3408833739231341e-011))*x+(-1.6848626197922081e-010))*x+(3.4788730414921547e-009))*x+(2.6416276928860799e-007))*x+(-1.0449426415583735e-005))*x+(0.00023835469371488724))*x+(-0.0044590309526073013))*x+(0.077893964531290286));
		rts[2] = (((((((((((((3.6137256150444347e-010))*x+(-2.9103830456733704e-011))*x+(-2.3055690689943728e-010))*x+(5.8662408264353871e-011))*x+(-1.3701158726083426e-010))*x+(-2.2256093264635029e-009))*x+(-9.7110082937964145e-009))*x+(2.0707991226961058e-006))*x+(-5.9306452130924996e-005))*x+(0.0011308856427410714))*x+(-0.018058204082015056))*x+(0.26881819720354616));
		rts[3] = (((((((((((((1.1447506646315255e-009))*x+(2.6678511252005894e-011))*x+(-6.8879065414269758e-010))*x+(-4.5474735088646407e-010))*x+(6.0339668076873441e-009))*x+(-4.9244495888463762e-009))*x+(-1.4665793059975838e-006))*x+(3.7119741798837439e-005))*x+(-0.00059892330678608852))*x+(0.0076269649990746702))*x+(-0.084204130671065053))*x+(0.86224620413006492));
		wts[0] = (((((((((((((2.3283064365386963e-010))*x+(1.7583564234276612e-011))*x+(-1.5234036254696548e-010))*x+(-8.5644084416950737e-012))*x+(-2.5816386065950298e-011))*x+(2.5707673027379013e-010))*x+(1.7299068844067733e-009))*x+(8.3580546631859904e-008))*x+(-5.1100073319432227e-006))*x+(0.00015390228915034462))*x+(-0.0041027568244348406))*x+(0.15362769279229421));
		wts[1] = (((((((((((((1.0974569401393333e-010))*x+(-5.1538033100465928e-012))*x+(-7.1205856026305498e-011))*x+(2.5390060424494241e-012))*x+(2.6654826494147223e-011))*x+(5.7880692831228464e-010))*x+(-1.7965473109171622e-008))*x+(3.0018654095798064e-007))*x+(-4.1023243424938745e-006))*x+(6.31103277297142e-005))*x+(-0.0013421977367918674))*x+(0.048373910154738853));
		wts[2] = (((((((((((((9.2465294680247699e-012))*x+(-1.1368683772161603e-012))*x+(-5.9022416583805653e-012))*x+(1.0729195309977513e-012))*x+(-3.5497530840681674e-012))*x+(2.9521081875335159e-010))*x+(-6.7647894323267597e-009))*x+(9.2920313378893241e-008))*x+(-9.2247513449467133e-007))*x+(8.5239308662375425e-006))*x+(-0.00012195934270638745))*x+(0.0039946482276065846));
		wts[3] = (((((((((((((5.2106467289074012e-014))*x+(1.9539925233402755e-014))*x+(-4.8183679268731788e-014))*x+(1.6457205968360236e-013))*x+(-2.0580898096866913e-012))*x+(2.9707227418758933e-011))*x+(-4.0142592057137067e-010))*x+(4.2833136606445126e-009))*x+(-3.4512100035149575e-008))*x+(2.2326037821027264e-007))*x+(-1.8311087536895842e-006))*x+(4.7323532118349228e-005));
		break;
	case 19:
		rts[0] = (((((((((((((6.8212102632969618e-012))*x+(2.6526928801710404e-013))*x+(-4.0548305454043048e-012))*x+(2.6290081223123707e-013))*x+(-1.7390533457728452e-012))*x+(-3.8279749740392312e-011))*x+(2.7056949273666453e-010))*x+(2.0385063896159274e-008))*x+(-7.841550611180822e-007))*x+(1.8737005128659799e-005))*x+(-0.00038366530805561752))*x+(0.007500910376934098));
		rts[1] = (((((((((((((3.698611787209908e-011))*x+(-2.0918378140777349e-011))*x+(-1.7621459846850485e-011))*x+(1.8682536998918899e-011))*x+(-1.6195637423758551e-011))*x+(-4.8940644129894884e-010))*x+(1.3065621177569635e-009))*x+(2.7691706661059351e-007))*x+(-9.3635753052786121e-006))*x+(0.00020862228000763372))*x+(-0.0040125972766082776))*x+(0.073663106251576918));
		rts[2] = (((((((((((((2.5708383570114768e-010))*x+(1.6977234433094658e-011))*x+(-1.5612992380435267e-010))*x+(8.6401996668428183e-012))*x+(9.3526371832316116e-011))*x+(-2.5629750174023984e-009))*x+(-2.4949236158514999e-008))*x+(1.9849783020238947e-006))*x+(-5.1169204097941311e-005))*x+(0.00096525781984002623))*x+(-0.015966131825382965))*x+(0.25183363103384065));
		rts[3] = (((((((((((((1.0040821507573128e-009))*x+(7.2759576141834259e-012))*x+(-5.9814434886599577e-010))*x+(-3.3257189594830072e-010))*x+(2.9463838776185485e-009))*x+(2.5024983566860705e-008))*x+(-1.395525727569217e-006))*x+(2.9889918388666576e-005))*x+(-0.00046502600128239807))*x+(0.0060382857602643645))*x+(-0.070605816208626035))*x+(0.78510576885986849));
		wts[0] = (((((((((((((1.2126596023639042e-011))*x+(-1.3945585427184899e-011))*x+(5.6085506609330569e-012))*x+(1.1520266222457089e-011))*x+(-3.7914560380158946e-011))*x+(-7.4040921541988311e-011))*x+(2.1741038599050926e-009))*x+(9.4163500996558014e-008))*x+(-4.7552156891746593e-006))*x+(0.00013909370851192257))*x+(-0.0038099381545905176))*x+(0.14967381376009015));
		wts[1] = (((((((((((((7.1850081440061331e-011))*x+(-4.2443086082736646e-012))*x+(-4.7198985460757591e-011))*x+(6.6317322004275963e-013))*x+(9.9049657364957966e-012))*x+(6.1297337576130906e-010))*x+(-1.4344429125993466e-008))*x+(2.193331744374897e-007))*x+(-3.0693334971271242e-006))*x+(5.243371133151209e-005))*x+(-0.0012271695877140647))*x+(0.047091003232621845));
		wts[2] = (((((((((((((5.9875067866717773e-012))*x+(2.8421709430404007e-013))*x+(-3.9885132234000285e-012))*x+(-4.7369515717340006e-013))*x+(-4.0918379795584769e-012))*x+(2.6358019470743937e-010))*x+(-5.0868641521262248e-009))*x+(6.3370126969960097e-008))*x+(-6.1269126937791663e-007))*x+(6.2507158182659511e-006))*x+(-0.0001073393082315573))*x+(0.0038803767870488936));
		wts[3] = (((((((((((((2.0102438232546166e-013))*x+(1.7615538657385816e-014))*x+(-1.4449552665496412e-013))*x+(6.2709097174244263e-014))*x+(-1.0956050881342585e-012))*x+(1.9004196942969582e-011))*x+(-2.5853757033092916e-010))*x+(2.659934523870667e-009))*x+(-2.0862685198435969e-008))*x+(1.4181629577118013e-007))*x+(-1.4728331245260418e-006))*x+(4.5685081331777448e-005));
		break;
	case 20:
		rts[0] = (((((((((((((1.5991948506173987e-011))*x+(-6.2527760746888816e-013))*x+(-9.9807569616435395e-012))*x+(5.2580162446247414e-013))*x+(2.9552656618155498e-012))*x+(-4.2958155551294411e-011))*x+(1.5061119018611177e-011))*x+(2.1110447713986364e-008))*x+(-7.0073462753057281e-007))*x+(1.6508943124706084e-005))*x+(-0.0003484611131149781))*x+(0.007135218534294341));
		rts[1] = (((((((((((((1.0125707679738601e-010))*x+(-3.3348139065007367e-012))*x+(-6.6506800067145364e-011))*x+(4.2064129956997931e-012))*x+(3.106966535900331e-011))*x+(-4.7758064170011494e-010))*x+(-1.7047141476211891e-009))*x+(2.758931424059104e-007))*x+(-8.2529001508568883e-006))*x+(0.00018219859743274131))*x+(-0.0036223322438847694))*x+(0.069850045403969038));
		rts[2] = (((((((((((((1.673470251262188e-010))*x+(4.850638409455617e-012))*x+(-1.0049916454590857e-010))*x+(-1.3642420526593922e-012))*x+(1.7560826866732288e-010))*x+(-1.718272339227648e-009))*x+(-3.8132342320788361e-008))*x+(1.825128443636951e-006))*x+(-4.3526907544536961e-005))*x+(0.00082337393664192826))*x+(-0.014181323430052616))*x+(0.23678354537094448));
		rts[3] = (((((((((((((8.7311491370201111e-010))*x+(-3.3954468866189317e-011))*x+(-5.1174235219756759e-010))*x+(-1.7856412644808489e-010))*x+(8.6568737363753213e-010))*x+(3.6934371413129462e-008))*x+(-1.2024494774702057e-006))*x+(2.3365545305390849e-005))*x+(-0.00035883926139934624))*x+(0.0048090181091315918))*x+(-0.059811573187699231))*x+(0.72010173434512903));
		wts[0] = (((((((((((((2.4131926087041694e-010))*x+(-1.8796223836640515e-011))*x+(-1.5756995708215982e-010))*x+(1.3794002976889409e-011))*x+(2.9549103904476695e-011))*x+(-2.0534921911045481e-010))*x+(1.2567307194899511e-009))*x+(1.0306931101193109e-007))*x+(-4.3592014612644139e-006))*x+(0.00012541311269266089))*x+(-0.0035456294964770056))*x+(0.14599831033377675));
		wts[1] = (((((((((((((4.5474735088646412e-011))*x+(1.4703497678662338e-011))*x+(-2.6489033189136535e-011))*x+(-1.0440241264101737e-011))*x+(-7.0438469871684577e-012))*x+(5.6567669067438453e-010))*x+(-1.0775226784905575e-008))*x+(1.5666355050273731e-007))*x+(-2.3232994942612439e-006))*x+(4.4407405832745654e-005))*x+(-0.0011307008910719362))*x+(0.045913403623041305));
		wts[2] = (((((((((((((9.4739031434680019e-012))*x+(9.0949470177292824e-013))*x+(-6.1769848495411371e-012))*x+(-7.3896444519050419e-013))*x+(-5.3767360933913251e-012))*x+(2.2176497675256238e-010))*x+(-3.6249804269417041e-009))*x+(4.1695931883115968e-008))*x+(-4.0499787099315676e-007))*x+(4.7458353133669516e-006))*x+(-9.6446359827451558e-005))*x+(0.0037787340449626102));
		wts[3] = (((((((((((((1.0006810195288077e-013))*x+(-4.4408920985006262e-016))*x+(-7.0647191800314119e-014))*x+(3.6748382115092681e-014))*x+(-7.1054736168936939e-013))*x+(1.2676720205958187e-011))*x+(-1.6488506841711808e-010))*x+(1.6171155843078034e-009))*x+(-1.2464209163566683e-008))*x+(9.2865635885134559e-008))*x+(-1.2423348881740308e-006))*x+(4.4335621157431834e-005));
		break;
	case 21:
		rts[0] = (((((((((((((4.3958910585691529e-012))*x+(-1.0800249583553523e-012))*x+(-2.5390060424494245e-012))*x+(6.2054065589715413e-013))*x+(2.4792020288562826e-012))*x+(-3.2182774963492498e-011))*x+(-2.1414625628324299e-010))*x+(2.0585629488071668e-008))*x+(-6.1695876252496974e-007))*x+(1.4532933431860422e-005))*x+(-0.0003174611629275393))*x+(0.0068025867134619018));
		rts[1] = (((((((((((((7.2759576141834259e-011))*x+(8.7917821171383058e-012))*x+(-4.4792614062316716e-011))*x+(-5.7980287238024167e-012))*x+(3.5285552257846575e-011))*x+(-3.1808748227983108e-010))*x+(-4.129844022315865e-009))*x+(2.6091187566024132e-007))*x+(-7.1752351027409844e-006))*x+(0.00015907145606377607))*x+(-0.0032816014289078427))*x+(0.066401932587928605));
		rts[2] = (((((((((((((2.4859521848460037e-010))*x+(5.4569682106375694e-012))*x+(-1.4817184516383955e-010))*x+(-7.5791225147744009e-012))*x+(1.7704830194513002e-010))*x+(-6.153892210628934e-010))*x+(-4.5105983836890566e-008))*x+(1.6142606347931594e-006))*x+(-3.663651992545184e-005))*x+(0.00070334022124238227))*x+(-0.012658055626321812))*x+(0.22338385440647687));
		rts[3] = (((((((((((((1.1156468341747918e-009))*x+(4.6081064889828362e-011))*x+(-6.9303496275097121e-010))*x+(-1.239944443417092e-010))*x+(-2.0425735177317012e-010))*x+(3.7875537373111001e-008))*x+(-9.7414507393978035e-007))*x+(1.7922018984724751e-005))*x+(-0.00027664594512192636))*x+(0.0038612342223796423))*x+(-0.051182379277305907))*x+(0.66476254062410067));
		wts[0] = (((((((((((((1.6492170592149097e-010))*x+(-4.850638409455617e-012))*x+(-1.0807828706068297e-010))*x+(2.5011104298755527e-012))*x+(3.1216510857727066e-011))*x+(-2.0164729145714469e-010))*x+(-2.3465673848477309e-012))*x+(1.0621457728158626e-007))*x+(-3.9385183027521951e-006))*x+(0.00011296338864428637))*x+(-0.0033074635489601396))*x+(0.14257383886984662));
		wts[1] = (((((((((((((3.8198777474462986e-011))*x+(1.5158245029548803e-013))*x+(-2.4518461335295189e-011))*x+(5.1159076974727213e-013))*x+(-1.1202890467150912e-011))*x+(4.5873053503934591e-010))*x+(-7.6910580126821043e-009))*x+(1.1076288412385318e-007))*x+(-1.7935924518097668e-006))*x+(3.8277916113653443e-005))*x+(-0.0010482799077942528))*x+(0.044824933277706085));
		wts[2] = (((((((((((((2.8421709430404007e-012))*x+(-1.6674069532503684e-012))*x+(-1.7029340900383736e-012))*x+(1.0764722446765518e-012))*x+(-7.0589460203033614e-012))*x+(1.7052892431479449e-010))*x+(-2.4456554651811993e-009))*x+(2.6647515879070955e-008))*x+(-2.7027700485494905e-007))*x+(3.7479458567512649e-006))*x+(-8.8019742463853038e-005))*x+(0.0036866668083296952));
		wts[3] = (((((((((((((-1.1220654035544915e-013))*x+(1.0362081563168126e-015))*x+(7.625381807467116e-014))*x+(2.0927704014184198e-014))*x+(-5.3009448682435801e-013))*x+(8.4022470694019199e-012))*x+(-1.023952222924812e-010))*x+(9.5957491265686213e-010))*x+(-7.4147214036190263e-009))*x+(6.3702650725649168e-008))*x+(-1.0882809669465775e-006))*x+(4.3175151910784983e-005));
		break;
	case 22:
		rts[0] = (((((((((((((4.1685173831259208e-012))*x+(6.6317322004276014e-013))*x+(-2.6384820254558386e-012))*x+(-4.0264088359739009e-013))*x+(2.599402174989033e-012))*x+(-1.7452927991712386e-011))*x+(-3.6281013378787935e-010))*x+(1.9106753040842861e-008))*x+(-5.373263664923873e-007))*x+(1.280299196265219e-005))*x+(-0.00029016507848908849))*x+(0.0064990618666855458));
		rts[1] = (((((((((((((9.3374789382020624e-011))*x+(9.701276818911234e-012))*x+(-5.9799276641570032e-011))*x+(-7.048583938740193e-012))*x+(3.6427157586634465e-011))*x+(-1.4167274760742049e-010))*x+(-5.5068172244432381e-009))*x+(2.3638154293218841e-007))*x+(-6.178357578157101e-006))*x+(0.00013906568623185214))*x+(-0.0029839629542073669))*x+(0.063272483869428506));
		rts[2] = (((((((((((((2.5587117609878379e-010))*x+(-2.7891170854369797e-011))*x+(-1.5984369383659214e-010))*x+(8.5644084416950721e-012))*x+(1.3312728697201237e-010))*x+(2.5183055640809471e-010))*x+(-4.6016766397372066e-008))*x+(1.3842862702044081e-006))*x+(-3.0637968066182797e-005))*x+(0.00060265890011621892))*x+(-0.01135505592419013))*x+(0.21139407116480177));
		rts[3] = (((((((((((((7.9065406074126555e-010))*x+(-6.305829932292302e-011))*x+(-4.8718599524969852e-010))*x+(3.637978807091713e-012))*x+(-7.1649234693419806e-010))*x+(3.3436985328686809e-008))*x+(-7.5860349705673481e-007))*x+(1.3601415830066799e-005))*x+(-0.0002139588349803952))*x+(0.0031296454006595935))*x+(-0.044222807210685673))*x+(0.61718173493771711));
		wts[0] = (((((((((((((1.0913936421275139e-010))*x+(2.849750065555175e-011))*x+(-6.2451969521741077e-011))*x+(-1.9023597512083747e-011))*x+(2.1382599394807283e-011))*x+(-1.3833082827356219e-010))*x+(-1.0482861985868415e-009))*x+(1.0344648337934358e-007))*x+(-3.5174442735153018e-006))*x+(0.00010178224239207333))*x+(-0.0030929286303031977))*x+(0.13937550621090328));
		wts[1] = (((((((((((((3.5470293369144201e-011))*x+(3.0316490059097606e-013))*x+(-2.0368891758456207e-011))*x+(-6.442254137558241e-013))*x+(-1.2614502035527643e-011))*x+(3.4163486854292085e-010))*x+(-5.2913757079645994e-009))*x+(7.8604298625606348e-008))*x+(-1.4188564125688916e-006))*x+(3.3491341975569466e-005))*x+(-0.00097669761793560839))*x+(0.043813241208074241));
		wts[2] = (((((((((((((5.1916989226204651e-012))*x+(9.473903143468002e-015))*x+(-3.0198066269804258e-012))*x+(1.8474111129762605e-013))*x+(-6.0052703550657798e-012))*x+(1.2111226836234815e-010))*x+(-1.5729856028823264e-009))*x+(1.67254541096525e-008))*x+(-1.8498456722491896e-007))*x+(3.0749506352071724e-006))*x+(-8.1239346888251765e-005))*x+(0.0036021490999754613));
		wts[3] = (((((((((((((8.7337544603845644e-014))*x+(1.4802973661668753e-016))*x+(-5.9600472705293812e-014))*x+(1.8059627867235879e-014))*x+(-3.4317456284090514e-013))*x+(5.3868327622626682e-012))*x+(-6.1564554597210816e-011))*x+(5.5719766250325131e-010))*x+(-4.4490557039214493e-009))*x+(4.6307858780342306e-008))*x+(-9.797465098808435e-007))*x+(4.2144023963380158e-005));
		break;
	case 23:
		rts[0] = (((((((((((((1.038339784524093e-011))*x+(1.8379372098327922e-012))*x+(-6.6459430551428032e-012))*x+(-1.2410813117943081e-012))*x+(2.9493444723508824e-012))*x+(-5.0845994081782911e-012))*x+(-4.2950892842341654e-010))*x+(1.7095986524588248e-008))*x+(-4.6481044926535703e-007))*x+(1.1301803567013585e-005))*x+(-0.0002660965519279832))*x+(0.0062211811822280539));
		rts[1] = (((((((((((((8.6098831767837198e-011))*x+(9.3981119183202574e-012))*x+(-5.4645473331523434e-011))*x+(-6.9727927135924485e-012))*x+(2.721852373118357e-011))*x+(-7.0095040882733883e-012))*x+(-5.9338415662561293e-009))*x+(2.0744833154987913e-007))*x+(-5.2899942283117039e-006))*x+(0.00012189215911439602))*x+(-0.0027234493604774181))*x+(0.060421638998951845));
		rts[2] = (((((((((((((2.7527372973660625e-010))*x+(7.2759576141834259e-012))*x+(-1.7136396005904922e-010))*x+(-1.0838145196127394e-011))*x+(8.5871458092393966e-011))*x+(7.6497030931932386e-010))*x+(-4.2786530170720503e-008))*x+(1.1610236452241907e-006))*x+(-2.5552791277638761e-005))*x+(0.00051859627683918186))*x+(-0.010236342788811846))*x+(0.20061237479135968));
		rts[3] = (((((((((((((5.4327150185902907e-010))*x+(1.9402553637822468e-011))*x+(-3.1711048601816094e-010))*x+(-6.3664629124104969e-012))*x+(-8.4708062786376093e-010))*x+(2.7233511445956538e-008))*x+(-5.7627998965396421e-007))*x+(1.0279840109224853e-005))*x+(-0.00016650028498510491))*x+(0.0025622751691589669))*x+(-0.038554585515784216))*x+(0.57588748970948722));
		wts[0] = (((((((((((((9.7012768189112337e-011))*x+(2.5465851649641991e-011))*x+(-5.7146583761398987e-011))*x+(-1.6977234433094662e-011))*x+(1.9790983666704655e-011))*x+(-7.1930609616780813e-011))*x+(-1.700703577967033e-009))*x+(9.6408797981932068e-008))*x+(-3.11664590639064e-006))*x+(9.1838178720401079e-005))*x+(-0.0028995087169657666))*x+(0.13638094464500941));
		wts[1] = (((((((((((((3.0316490059097604e-011))*x+(-7.8822874153653775e-012))*x+(-1.6370904631912708e-011))*x+(5.0590642786119125e-012))*x+(-1.0534980295536419e-011))*x+(2.3615479941933393e-010))*x+(-3.5671516111316728e-009))*x+(5.6719452690145999e-008))*x+(-1.1510789078017503e-006))*x+(2.9658271847407547e-005))*x+(-0.0009136816060245945))*x+(0.042868689714098338));
		wts[2] = (((((((((((((-2.4063713984408724e-012))*x+(-1.2600291180812442e-012))*x+(2.0096517043081499e-012))*x+(9.3554793541746518e-013))*x+(-5.6867103618666688e-012))*x+(8.0052890242635996e-011))*x+(-9.742390644218444e-010))*x+(1.0459672697415989e-008))*x+(-1.3161026521640168e-007))*x+(2.6063036980543118e-006))*x+(-7.5584680192627524e-005))*x+(0.003523814986373722));
		wts[3] = (((((((((((((8.8817841970012523e-016))*x+(-3.9375909940038881e-014))*x+(5.680641142665384e-015))*x+(3.536060333431123e-014))*x+(-2.4357367974422079e-013))*x+(3.3112656135555101e-012))*x+(-3.5865179677403249e-011))*x+(3.1879592412090152e-010))*x+(-2.7397605668315669e-009))*x+(3.576200296352202e-008))*x+(-8.9852703253153823e-007))*x+(4.120663693727923e-005));
		break;
	case 24:
		rts[0] = (((((((((((((-5.0780120848988491e-012))*x+(1.6105635343895604e-012))*x+(3.9458806592544225e-012))*x+(-1.1321314256444262e-012))*x+(-3.6652162786291831e-013))*x+(2.8459457013241259e-012))*x+(-4.3531295235155193e-010))*x+(1.4913984390056236e-008))*x+(-4.0078091748223704e-007))*x+(1.000560250181305e-005))*x+(-0.00024482116155637461))*x+(0.0059659382860741276));
		rts[1] = (((((((((((((7.4881730445971087e-011))*x+(4.5474735088646412e-013))*x+(-4.7919002099661157e-011))*x+(-1.2316074086508402e-012))*x+(1.8739380417779707e-011))*x+(7.271516722084924e-011))*x+(-5.7156731939992751e-009))*x+(1.7812770850926066e-007))*x+(-4.5192138706749247e-006))*x+(0.00010720770792917399))*x+(-0.0024947348460512462))*x+(0.057814993324940882));
		rts[2] = (((((((((((((2.1221543041368324e-010))*x+(1.152026622245709e-011))*x+(-1.2831454417513061e-010))*x+(-1.3718211751741667e-011))*x+(3.9392489270539954e-011))*x+(9.7148481851642511e-010))*x+(-3.7463207943252044e-008))*x+(9.5990544313195869e-007))*x+(-2.1319844485223612e-005))*x+(0.00044848854199677768))*x+(-0.0092713735503869351))*x+(0.19087019453549492));
		rts[3] = (((((((((((((7.5669959187507629e-010))*x+(-7.2759576141834259e-012))*x+(-4.7900054293374217e-010))*x+(1.6370904631912708e-011))*x+(-7.1304384618997574e-010))*x+(2.1124482903663495e-008))*x+(-4.3154111513861909e-007))*x+(7.7756246810167795e-006))*x+(-0.0001306304863636735))*x+(0.0021190801633131917))*x+(-0.033891140974023473))*x+(0.53973840897096137));
		wts[0] = (((((((((((((6.9121597334742546e-011))*x+(-8.4886172165473291e-012))*x+(-3.6455579296064876e-011))*x+(3.0316490059097597e-012))*x+(1.1738165994756855e-011))*x+(-2.3201588798353139e-011))*x+(-1.986762458254058e-009))*x+(8.7060048651702956e-008))*x+(-2.7492329131203102e-006))*x+(8.3048736110757915e-005))*x+(-0.002724805555974482))*x+(0.13357025210274062));
		wts[1] = (((((((((((((7.5791225147744016e-011))*x+(0))*x+(-4.6573707853288696e-011))*x+(5.4948638232114411e-013))*x+(4.7369515717340066e-013))*x+(1.5741955886975725e-010))*x+(-2.3971119903857617e-009))*x+(4.201046355234439e-008))*x+(-9.5556635186973727e-007))*x+(2.6512972966061251e-005))*x+(-0.00085760792293456236))*x+(0.041983568677700651));
		wts[2] = (((((((((((((2.9179621681881445e-012))*x+(-2.9369099744750804e-013))*x+(-1.4660865114516732e-012))*x+(3.7185069838111906e-013))*x+(-3.3253400033572685e-012))*x+(5.0240959540796361e-011))*x+(-5.8830252706402553e-010))*x+(6.6278200844260829e-009))*x+(-9.8076859213318726e-008))*x+(2.2655899233350006e-006))*x+(-7.0729489194608372e-005))*x+(0.0034507145602925655));
		wts[3] = (((((((((((((1.1309471877514928e-013))*x+(-8.8817841970012523e-016))*x+(-7.4643994688964683e-014))*x+(9.8994886362409781e-015))*x+(-1.3498924200661122e-013))*x+(1.9603670538733318e-012))*x+(-2.0344573971089092e-011))*x+(1.8165243542584789e-010))*x+(-1.7646344456830024e-009))*x+(2.9141878619028838e-008))*x+(-8.3410814130194202e-007))*x+(4.0341418165118423e-005));
		break;
	case 25:
		rts[0] = (((((((((((((6.5559409752798574e-012))*x+(-2.9937533933358886e-012))*x+(-3.5787669124450377e-012))*x+(1.8332002582610585e-012))*x+(9.4620607645386648e-013))*x+(6.375196666870882e-012))*x+(-4.0572697979079919e-010))*x+(1.2800602633422642e-008))*x+(-3.4540192808974379e-007))*x+(8.8884437734974148e-006))*x+(-0.00022595479973065721))*x+(0.0057307364280045842));
		rts[1] = (((((((((((((1.546140993013978e-011))*x+(-1.1065518871570626e-011))*x+(-3.3537617127876729e-012))*x+(6.6885756192884092e-012))*x+(1.3879268105180622e-012))*x+(1.0810019546170224e-010))*x+(-5.1491924057955885e-009))*x+(1.5087449756201465e-007))*x+(-3.8621575120014367e-006))*x+(9.4662922664289856e-005))*x+(-0.0022931926486393682))*x+(0.055423119465816101));
		rts[2] = (((((((((((((4.2443086082736648e-010))*x+(-1.0307606620093186e-011))*x+(-2.8209493999990321e-010))*x+(4.3200998334214083e-012))*x+(5.8832938520936295e-011))*x+(9.7558701857754682e-010))*x+(-3.1559705959693929e-008))*x+(7.8735378128413913e-007))*x+(-1.7835195914472912e-005))*x+(0.00038992853606215072))*x+(-0.0084346978084489169))*x+(0.18202691310518643));
		rts[3] = (((((((((((((8.0035533756017685e-010))*x+(-7.5184895346562059e-011))*x+(-5.1507716610406839e-010))*x+(6.3058299322923007e-011))*x+(-5.5198749275101966e-010))*x+(1.5897200000836165e-008))*x+(-3.2098774364423355e-007))*x+(5.907403583194081e-006))*x+(-0.00010344851069728672))*x+(0.0017698272781092224))*x+(-0.030015806119979074))*x+(0.507843082088415));
		wts[0] = (((((((((((((1.988761747876803e-010))*x+(-2.4253192047278084e-011))*x+(-1.2687451089732346e-010))*x+(1.4779288903810081e-011))*x+(3.1765997240048208e-011))*x+(7.6122811757765411e-012))*x+(-2.0162141585918412e-009))*x+(7.6975239515775229e-008))*x+(-2.4211207692026449e-006))*x+(7.5303307424575319e-005))*x+(-0.0025666175725205819))*x+(0.13092583110630146));
		wts[1] = (((((((((((((7.97323688554267e-011))*x+(1.1975013573343555e-011))*x+(-5.6634992991651715e-011))*x+(-7.863339609078441e-012))*x+(8.5501975869798717e-012))*x+(1.0376943748724442e-010))*x+(-1.6313992379224371e-009))*x+(3.2084704892909592e-008))*x+(-8.0864953969546815e-007))*x+(2.3876546745175975e-005))*x+(-0.00080729173436595771))*x+(0.041151557923892232));
		wts[2] = (((((((((((((3.5053441630831608e-012))*x+(5.6843418860808015e-014))*x+(-2.443082773121811e-012))*x+(2.6053233644537003e-014))*x+(-1.6407616006593646e-012))*x+(3.0291695078214311e-011))*x+(-3.5115248209205413e-010))*x+(4.3293181817283255e-009))*x+(-7.6556493226106541e-008))*x+(2.0059284007829916e-006))*x+(-6.6468691721639076e-005))*x+(0.0033821586706138402));
		wts[3] = (((((((((((((5.3290705182007514e-015))*x+(3.2862601528904634e-014))*x+(-4.3298697960381105e-015))*x+(-1.4858484812900013e-014))*x+(-9.0760732263106547e-014))*x+(1.124159793031154e-012))*x+(-1.1312943781991805e-011))*x+(1.0460854925342655e-010))*x+(-1.2070919814643599e-009))*x+(2.476091383202735e-008))*x+(-7.8048262510037717e-007))*x+(3.9534850394525473e-005));
		break;
	case 26:
		rts[0] = (((((((((((((1.2088700411065171e-011))*x+(-3.6000831945178408e-013))*x+(-7.3067477993996964e-012))*x+(-2.3684757858670023e-014))*x+(1.6087871775501599e-012))*x+(8.4038701923342761e-012))*x+(-3.594231116436456e-010))*x+(1.0884164134787136e-008))*x+(-2.981101426818612e-007))*x+(7.9250928258966253e-006))*x+(-0.0002091649012353589))*x+(0.0055133370720968728));
		rts[1] = (((((((((((((1.0246973639974991e-010))*x+(-3.637978807091713e-012))*x+(-6.6431008841997625e-011))*x+(2.0842586915629604e-012))*x+(1.5153508077977069e-011))*x+(1.17942988708819e-010))*x+(-4.4557659784061335e-009))*x+(1.2684305472632218e-007))*x+(-3.3078852954652551e-006))*x+(8.3931894004379823e-005))*x+(-0.002114874851618328))*x+(0.053220873419218918));
		rts[2] = (((((((((((((2.2191670723259449e-010))*x+(1.0307606620093186e-011))*x+(-1.4104746999995163e-010))*x+(-9.5496943686157449e-012))*x+(1.3945585427184902e-011))*x+(8.8587389276047657e-010))*x+(-2.5943378704577448e-008))*x+(6.4385579919464431e-007))*x+(-1.4982141212223818e-005))*x+(0.00034084597990954868))*x+(-0.0077053488829945498))*x+(0.17396506540450765));
		rts[3] = (((((((((((((5.2871958663066221e-010))*x+(1.2126596023639042e-011))*x+(-3.3499721515302855e-010))*x+(6.5180453627059868e-012))*x+(-4.4152178209818282e-010))*x+(1.1775332116788679e-008))*x+(-2.3848784636015807e-007))*x+(4.5190868907714803e-006))*x+(-8.2732844352007007e-005))*x+(0.0014919414947153948))*x+(-0.026764381456645267))*x+(0.47949925641851676));
		wts[0] = (((((((((((((9.3374789382020624e-011))*x+(6.0632980118195212e-013))*x+(-4.9794834922067821e-011))*x+(-1.7431981783981123e-012))*x+(9.4075858214637248e-012))*x+(2.9172516254523849e-011))*x+(-1.8888094051779563e-009))*x+(6.7174988534664707e-008))*x+(-2.133031473912824e-006))*x+(6.8481887711015668e-005))*x+(-0.0024229764009211703))*x+(0.12843217069578472));
		wts[1] = (((((((((((((1.2126596023639042e-011))*x+(3.0316490059097606e-013))*x+(-7.3517488393311688e-012))*x+(7.9580786405131221e-013))*x+(-2.7237471537470506e-012))*x+(6.4934132145329685e-011))*x+(-1.1367159065874452e-009))*x+(2.526045757752134e-008))*x+(-6.9477787704534189e-007))*x+(2.1628211767830512e-005))*x+(-0.00076184382996461245))*x+(0.040367364637605707));
		wts[2] = (((((((((((((4.8695862157425527e-012))*x+(-1.5158245029548803e-013))*x+(-3.2199428308861871e-012))*x+(1.6579330501069003e-013))*x+(-6.1935641800422059e-013))*x+(1.7675934789925425e-011))*x+(-2.1043004838627866e-010))*x+(2.9570570066657829e-009))*x+(-6.2217251452975146e-008))*x+(1.7991337855806596e-006))*x+(-6.2670775849003418e-005))*x+(0.0033176233571532501));
		wts[3] = (((((((((((((6.3652786745175633e-014))*x+(-2.8125649957170631e-015))*x+(-4.3206179374995671e-014))*x+(6.1617377866696188e-015))*x+(-4.291243286639694e-014))*x+(6.2055048599685136e-013))*x+(-6.2264233844043036e-012))*x+(6.2004340825478705e-011))*x+(-8.8229953039676981e-010))*x+(2.1669183518876421e-008))*x+(-7.342140825008483e-007))*x+(3.8778015920740014e-005));
		break;
	case 27:
		rts[0] = (((((((((((((6.1390892369672656e-012))*x+(-1.0800249583553523e-012))*x+(-3.7469286932415952e-012))*x+(8.0528176719478018e-013))*x+(7.1291121154596725e-013))*x+(8.1497031345634225e-012))*x+(-3.0866007897737785e-010))*x+(9.2144357236959938e-009))*x+(-2.5799764690493759e-007))*x+(7.0926008979910072e-006))*x+(-0.00019416725528531537))*x+(0.0053118096868321179));
		rts[1] = (((((((((((((4.699055959160129e-011))*x+(-2.2737367544323206e-012))*x+(-2.8668030912134171e-011))*x+(1.7621459846850485e-012))*x+(4.4479975258582264e-012))*x+(1.1123013621272548e-010))*x+(-3.7588077095307426e-009))*x+(1.0632876631018935e-007))*x+(-2.8427036522643556e-006))*x+(7.4726521299604831e-005))*x+(-0.001956448910905048))*x+(0.051186745083097625));
		rts[2] = (((((((((((((1.9281287677586079e-010))*x+(9.701276818911234e-012))*x+(-1.1709744285326451e-010))*x+(-7.73070496506989e-012))*x+(4.4906300900038332e-012))*x+(7.5337898882329069e-010))*x+(-2.1031184793685043e-008))*x+(5.2676258555095501e-007))*x+(-1.2649091499246829e-005))*x+(0.00029951615747945504))*x+(-0.0070661524515744974))*x+(0.16658619914101808));
		rts[3] = (((((((((((((4.9961575617392851e-010))*x+(-2.1827872842550278e-011))*x+(-2.9740476747974748e-010))*x+(2.4556356947869062e-011))*x+(-3.2688755406221992e-010))*x+(8.6360974667816955e-009))*x+(-1.7771688357962978e-007))*x+(3.4864297286200476e-006))*x+(-6.6822937448825684e-005))*x+(0.0012686389142121388))*x+(-0.024011745895130967))*x+(0.45414837549198012));
		wts[0] = (((((((((((((1.1641532182693481e-010))*x+(1.5764574830730755e-011))*x+(-7.1546916539470359e-011))*x+(-7.5791225147744009e-012))*x+(1.48929757415317e-011))*x+(3.6455579296064869e-011))*x+(-1.69328847240043e-009))*x+(5.8205663104142026e-008))*x+(-1.8825985158936001e-006))*x+(6.2467415520757921e-005))*x+(-0.0022921522812398192))*x+(0.12607560846759489));
		wts[1] = (((((((((((((5.0325373498102025e-011))*x+(4.2443086082736646e-012))*x+(-3.1946001399774104e-011))*x+(-4.3200998334214083e-012))*x+(4.4053649617126212e-012))*x+(4.3666403826136957e-011))*x+(-8.2041558731778719e-010))*x+(2.0426528468675542e-008))*x+(-6.0392980408274788e-007))*x+(1.968497245287415e-005))*x+(-0.0007205760172351403))*x+(0.039626478426649861));
		wts[2] = (((((((((((((6.0254023992456496e-012))*x+(8.5265128291212022e-014))*x+(-4.1093054884792463e-012))*x+(-7.6975463040677512e-014))*x+(1.7141843500212417e-013))*x+(1.0233554744350689e-011))*x+(-1.2884457389894521e-010))*x+(2.1279896594839083e-009))*x+(-5.2182480308448257e-008))*x+(1.6283595047398257e-006))*x+(-5.9248286439520241e-005))*x+(0.0032566922609316134));
		wts[3] = (((((((((((((1.5128639082225465e-013))*x+(1.0362081563168127e-014))*x+(-1.0508260928077105e-013))*x+(-5.5881225572799541e-015))*x+(-3.3838672604720938e-015))*x+(3.394853842486611e-013))*x+(-3.4339791571645164e-012))*x+(3.8569076318134548e-011))*x+(-6.8578220530596799e-010))*x+(1.9340354711573913e-008))*x+(-6.9330234108023627e-007))*x+(3.8064645072628953e-005));
		break;
	case 28:
		rts[0] = (((((((((((((1.1937117960769683e-011))*x+(-4.3579954459952808e-013))*x+(-8.2351903074595612e-012))*x+(1.6105635343895603e-013))*x+(1.9190575054987371e-012))*x+(7.6203487964221478e-012))*x+(-2.6059301938552437e-010))*x+(7.7938568099344963e-009))*x+(-2.2406156214375045e-007))*x+(6.3709322454550662e-006))*x+(-0.00018072068212873454))*x+(0.0051244859489002524));
		rts[1] = (((((((((((((4.0017766878008842e-011))*x+(-6.9727927135924493e-012))*x+(-2.4707939398164552e-011))*x+(3.4863963567962246e-012))*x+(3.0458598606249633e-012))*x+(9.7729232114337122e-011))*x+(-3.1268131787480038e-009))*x+(8.915092560476029e-008))*x+(-2.4527982039705227e-006))*x+(6.6800439469184362e-005))*x+(-0.0018151167974579361))*x+(0.049302282670286537));
		rts[2] = (((((((((((((2.1464074961841106e-010))*x+(-1.152026622245709e-011))*x+(-1.3649999649108699e-010))*x+(5.2295945351943374e-012))*x+(1.1870800638765409e-011))*x+(6.1590081183264067e-010))*x+(-1.6933696815139378e-008))*x+(4.3219984598626599e-007))*x+(-1.0737995113918597e-005))*x+(0.00026453002273454929))*x+(-0.0065030611366931343))*x+(0.15980742022046168));
		rts[3] = (((((((((((((7.4214767664670944e-010))*x+(-2.6678511252005894e-011))*x+(-4.671771118106941e-010))*x+(2.319211489520967e-011))*x+(-1.7973889043787494e-010))*x+(6.3199176262666388e-009))*x+(-1.3320832081831213e-007))*x+(2.7149296594567809e-006))*x+(-5.44942873526022e-005))*x+(0.0010874334211101362))*x+(-0.021661830482971604))*x+(0.43134176255680001));
		wts[0] = (((((((((((((7.3972235744198159e-011))*x+(-1.152026622245709e-011))*x+(-4.0245140553452075e-011))*x+(6.0254023992456496e-012))*x+(5.8548721426632247e-012))*x+(3.4961071075182794e-011))*x+(-1.4758686125067773e-009))*x+(5.0284046852292853e-008))*x+(-1.6659806173306238e-006))*x+(5.7152468798736068e-005))*x+(-0.0021726406697183199))*x+(0.12384409755250285));
		wts[1] = (((((((((((((1.9402553637822468e-011))*x+(5.7601331112285452e-012))*x+(-8.2991391536779702e-012))*x+(-2.8611187493273365e-012))*x+(-1.1344999014302934e-012))*x+(2.8418156716725207e-011))*x+(-6.1279529598815919e-010))*x+(1.6880186877917442e-008))*x+(-5.2965952438791908e-007))*x+(1.7988127873638789e-005))*x+(-0.00068294001777066617))*x+(0.038925003098696245));
		wts[2] = (((((((((((((5.1159076974727213e-012))*x+(8.8107299234252423e-013))*x+(-3.479290929438624e-012))*x+(-4.6777396770873259e-013))*x+(3.943512183468556e-013))*x+(5.9405443527301332e-012))*x+(-8.1969718050226931e-011))*x+(1.6121966030698449e-009))*x+(-4.4779791839288e-008))*x+(1.4834297305216064e-006))*x+(-5.6140190794907205e-005))*x+(0.0031990221601859254));
		wts[3] = (((((((((((((-6.6613381477509392e-014))*x+(1.5395092608135503e-014))*x+(4.7647071473496304e-014))*x+(-8.1416355139178141e-015))*x+(-2.8592868813367048e-014))*x+(1.8282597658014763e-013))*x+(-1.9221507342968383e-012))*x+(2.5571866239110227e-011))*x+(-5.5999653644239723e-010))*x+(1.7484606093441251e-008))*x+(-6.5654002421545936e-007))*x+(3.7390032751871825e-005));
		break;
	case 29:
		rts[0] = (((((((((((((8.2612435411040971e-012))*x+(0))*x+(-5.5848659030743867e-012))*x+(-4.736951571734001e-015))*x+(1.1954881529163684e-012))*x+(6.6041986694168981e-012))*x+(-2.1773514472892921e-010))*x+(6.6015098202735576e-009))*x+(-1.9534213439055073e-007))*x+(5.7430185122405346e-006))*x+(-0.00016862108395669572))*x+(0.0049499196784260017));
		rts[1] = (((((((((((((5.6691836410512523e-011))*x+(6.0632980118195212e-013))*x+(-3.4428164023362719e-011))*x+(-7.3896444519050419e-013))*x+(4.9453774408902973e-012))*x+(8.3301661864728274e-011))*x+(-2.5830451111374941e-009))*x+(7.4916791141059009e-008))*x+(-2.1255692571007603e-006))*x+(5.994711468754188e-005))*x+(-0.0016885327671223248))*x+(0.047551599634688142));
		rts[2] = (((((((((((((1.7098500393331051e-010))*x+(3.637978807091713e-012))*x+(-1.0633508888228486e-010))*x+(-2.4253192047278085e-012))*x+(6.7075234255753458e-012))*x+(4.9606304249512811e-010))*x+(-1.3606795394120278e-008))*x+(3.5616268749076124e-007))*x+(-9.1668102166209114e-006))*x+(0.00023474879114974515))*x+(-0.0060045673613766696))*x+(0.15355856697833511));
		rts[3] = (((((((((((((6.378589508434136e-010))*x+(-1.0913936421275139e-011))*x+(-4.0699887904338533e-010))*x+(1.3945585427184899e-011))*x+(-1.1349735965874666e-010))*x+(4.6337665556469192e-009))*x+(-1.006109631163099e-007))*x+(2.134633045732433e-006))*x+(-4.4849399457924648e-005))*x+(0.00093899734570721905))*x+(-0.01964021674022105))*x+(0.41071545898793016));
		wts[0] = (((((((((((((1.3339255626002947e-010))*x+(-7.2759576141834259e-012))*x+(-7.9429203954835728e-011))*x+(4.0169349328304333e-012))*x+(1.5755100927587286e-011))*x+(3.245759216952137e-011))*x+(-1.2686930025059455e-009))*x+(4.3432718162724392e-008))*x+(-1.4788950342496201e-006))*x+(5.2442005323505292e-005))*x+(-0.0020631397035466713))*x+(0.12172699221480204));
		wts[1] = (((((((((((((4.2139921182145671e-011))*x+(0))*x+(-2.5409008230781179e-011))*x+(-4.1685173831259209e-013))*x+(4.1969390925563248e-012))*x+(1.9364658025248598e-011))*x+(-4.7439704016956808e-010))*x+(1.4184598680818302e-008))*x+(-4.6776071717380407e-007))*x+(1.6494688749998005e-005))*x+(-0.00064848812747333681))*x+(0.038259537842950025));
		wts[2] = (((((((((((((3.5432397756570327e-012))*x+(-1.4495071809506044e-012))*x+(-2.393344781618604e-012))*x+(9.0357351230826077e-013))*x+(3.5852802208561719e-013))*x+(3.2216081654231252e-012))*x+(-5.4887571339830757e-011))*x+(1.276556457763256e-009))*x+(-3.9047181507543175e-008))*x+(1.3580237085146669e-006))*x+(-5.3301599183037357e-005))*x+(0.0031443221550695333));
		wts[3] = (((((((((((((-4.3224683092072759e-014))*x+(-6.8093678843676263e-015))*x+(3.0494125743037629e-014))*x+(4.6259292692714853e-015))*x+(-1.5799861419196759e-014))*x+(9.5907078575171083e-014))*x+(-1.1169664730174369e-012))*x+(1.8178648112284382e-011))*x+(-4.7382972342296405e-010))*x+(1.5941218456229809e-008))*x+(-6.2315714997051279e-007))*x+(3.6750441151591398e-005));
		break;
	case 30:
		rts[0] = (((((((((((((1.2240282861360658e-011))*x+(-1.2505552149377763e-012))*x+(-7.9746579710141905e-012))*x+(7.0106883261663222e-013))*x+(1.7269149073702768e-012))*x+(5.431803155412732e-012))*x+(-1.8131889508351168e-010))*x+(5.6073222546674612e-009))*x+(-1.7098525785924168e-007))*x+(5.194521074282134e-006))*x+(-0.00015769571673032688))*x+(0.0047868526612073617));
		rts[1] = (((((((((((((4.2443086082736649e-011))*x+(-7.5791225147744013e-013))*x+(-2.6147972675971684e-011))*x+(-1.3263464400855207e-013))*x+(3.5906092913743724e-012))*x+(6.8837972359384964e-011))*x+(-2.1287567264494101e-009))*x+(6.3175880600970429e-008))*x+(-1.8501404779140229e-006))*x+(5.3995283738494465e-005))*x+(-0.0015747280074285702))*x+(0.045920960828217804));
		rts[2] = (((((((((((((1.8311159995694953e-010))*x+(2.2434202643732228e-011))*x+(-1.0997306768937656e-010))*x+(-1.5234036254696545e-011))*x+(8.6496735699862841e-012))*x+(3.9764576816499658e-010))*x+(-1.0948677520161708e-008))*x+(2.9503562644824416e-007))*x+(-7.8688388288061795e-006))*x+(0.00020925639353638889))*x+(-0.0055612107199630341))*x+(0.1477799246354603));
		rts[3] = (((((((((((((4.9961575617392851e-010))*x+(1.2126596023639042e-012))*x+(-3.0649971449747676e-010))*x+(3.3348139065007371e-012))*x+(-8.3787199400831014e-011))*x+(3.4164552668395722e-009))*x+(-7.6655994737014524e-008))*x+(1.6945418644572403e-006))*x+(-3.7230902928545952e-005))*x+(0.00081631637420899927))*x+(-0.017888708286150499))*x+(0.39197142866259699));
		wts[0] = (((((((((((((2.4374458007514477e-010))*x+(1.5158245029548803e-012))*x+(-1.5893419913481921e-010))*x+(-1.7053025658242402e-012))*x+(3.6465053199208342e-011))*x+(2.9912664937607282e-011))*x+(-1.0833428968718786e-009))*x+(3.7574964621237918e-008))*x+(-1.3171924289253252e-006))*x+(4.8253729459347507e-005))*x+(-0.0019625247887153467))*x+(0.11971485781949241));
		wts[1] = (((((((((((((7.2759576141834259e-012))*x+(7.73070496506989e-012))*x+(-4.5095778962907689e-012))*x+(-5.4190725980636971e-012))*x+(4.0264088359739145e-014))*x+(1.4993043843484579e-011))*x+(-3.7700198518564316e-010))*x+(1.2070544489854266e-008))*x+(-4.1541125533894885e-007))*x+(1.5172042019014065e-005))*x+(-0.00061684755535251832))*x+(0.03762709037232452));
		wts[2] = (((((((((((((1.5726679218156883e-012))*x+(-2.7474319116057206e-013))*x+(-9.3910064909626568e-013))*x+(2.4040029226550053e-013))*x+(5.8915835173441624e-014))*x+(1.9808229131020503e-012))*x+(-3.8853360343852707e-011))*x+(1.0458120249431011e-009))*x+(-3.4428995423993934e-008))*x+(1.248039498777358e-006))*x+(-5.0697842425304312e-005))*x+(0.0030923407573078738));
		wts[3] = (((((((((((((4.2632564145606011e-014))*x+(-1.8059627867235879e-014))*x+(-2.8717768903637385e-014))*x+(1.1971904948874604e-014))*x+(2.9605947323337513e-015))*x+(4.9428054242165828e-014))*x+(-6.8665906294285151e-013))*x+(1.3781306535768735e-011))*x+(-4.1062533657609118e-010))*x+(1.4618911291686304e-008))*x+(-5.926285510805655e-007))*x+(3.6142768540056147e-005));
		break;
	case 31:
		rts[0] = (((((((((((((4.5853691214385127e-012))*x+(0))*x+(-3.0150696754086917e-012))*x+(-2.8421709430404007e-014))*x+(5.3971641970444273e-013))*x+(4.6222285258560679e-012))*x+(-1.5076109805001181e-010))*x+(4.7801100485263719e-009))*x+(-1.5026109380887612e-007))*x+(4.7134782571334882e-006))*x+(-0.00014779807441645703))*x+(0.0046341859118862877));
		rts[1] = (((((((((((((3.9108272176235914e-011))*x+(2.4253192047278085e-012))*x+(-2.4537409141582127e-011))*x+(-1.8758328224066645e-012))*x+(3.6711374680938515e-012))*x+(5.6580518048576778e-011))*x+(-1.7557964711774805e-009))*x+(5.3498204681072061e-008))*x+(-1.6174133494056828e-006))*x+(4.8803624325753171e-005))*x+(-0.0014720454008224667))*x+(0.044398439078372202));
		rts[2] = (((((((((((((2.0615213240186373e-010))*x+(4.2443086082736646e-012))*x+(-1.3521154566357532e-010))*x+(-2.8042753304665281e-012))*x+(2.1306808169659533e-011))*x+(3.1261748745237123e-010))*x+(-8.8427244785786261e-009))*x+(2.4577396207092761e-007))*x+(-6.7907283663274729e-006))*x+(0.00018731626349604197))*x+(-0.0051651767672677654))*x+(0.14242038594007111));
		rts[3] = (((((((((((((4.3898277605573333e-010))*x+(-6.063298011819521e-012))*x+(-2.7633480688867468e-010))*x+(4.0927261579781763e-012))*x+(-4.5815795601811247e-011))*x+(2.5351454269184615e-009))*x+(-5.8951628171636607e-008))*x+(1.3577473527703887e-006))*x+(-3.1155784081415831e-005))*x+(0.00071407269844446042))*x+(-0.016361353828889678))*x+(0.37486342701214126));
		wts[0] = (((((((((((((1.6674069532503683e-010))*x+(-5.1538033100465928e-012))*x+(-1.0811618267325683e-010))*x+(3.4485007442223524e-012))*x+(2.3855288115252428e-011))*x+(2.4202269817881945e-011))*x+(-9.190495771823255e-010))*x+(3.2594470381989517e-008))*x+(-1.1771249604960086e-006))*x+(4.4517231625920695e-005))*x+(-0.0018698238342678263))*x+(0.11779930609171686));
		wts[1] = (((((((((((((7.3365905943016203e-011))*x+(2.2737367544323206e-012))*x+(-4.9226400733459734e-011))*x+(-1.4968766966679443e-012))*x+(1.1468159755168015e-011))*x+(1.0460965427228073e-011))*x+(-3.0787742725616829e-010))*x+(1.0370164208832003e-008))*x+(-3.7064646882245533e-007))*x+(1.399465410553922e-005))*x+(-0.00058770322990475286))*x+(0.037025011154415137));
		wts[2] = (((((((((((((4.6043169277254492e-012))*x+(-1.3737159558028602e-012))*x+(-2.7628270042138561e-012))*x+(9.1896860491639611e-013))*x+(4.7191880033399991e-013))*x+(1.074584865534689e-012))*x+(-2.9064505432015626e-011))*x+(8.7805883397518159e-010))*x+(-3.0597588211664826e-008))*x+(1.1506670116900584e-006))*x+(-4.8301049993493968e-005))*x+(0.0030428575342719361));
		wts[3] = (((((((((((((2.0724163126336254e-014))*x+(-7.2534570942176889e-015))*x+(-3.9597954544963906e-015))*x+(4.4408920985006254e-015))*x+(-4.8664775912736023e-015))*x+(2.7920374345846713e-014))*x+(-4.4962370053987699e-013))*x+(1.0998584638530207e-011))*x+(-3.6145598252229454e-010))*x+(1.3463560364586038e-008))*x+(-5.6457062529735549e-007))*x+(3.556436141815229e-005));
		break;
	case 32:
		rts[0] = (((((((((((((6.1011936243933933e-012))*x+(2.2737367544323206e-013))*x+(-3.4034997042908795e-012))*x+(-4.5001039931473016e-014))*x+(4.9708385555883662e-013))*x+(3.7710575403101148e-012))*x+(-1.2564792724785906e-010))*x+(4.0913568088996044e-009))*x+(-1.3255995405120807e-007))*x+(4.2899350341813608e-006))*x+(-0.00013880350751771002))*x+(0.0044909556885171752));
		rts[1] = (((((((((((((7.3062741042425231e-011))*x+(3.0316490059097605e-012))*x+(-4.6289490758984656e-011))*x+(-2.1032064978498961e-012))*x+(8.9149428580033893e-012))*x+(4.6056195894076758e-011))*x+(-1.4525460093987401e-009))*x+(4.5507071000372434e-008))*x+(-1.4199084170709215e-006))*x+(4.4255627511466389e-005))*x+(-0.0013790848508764967))*x+(0.042973631685870026));
		rts[2] = (((((((((((((8.7311491370201111e-011))*x+(3.637978807091713e-012))*x+(-5.0173791047806545e-011))*x+(-2.5011104298755527e-012))*x+(9.0002079862946239e-013))*x+(2.475246674293885e-010))*x+(-7.1720579105279585e-009))*x+(2.0590847989628475e-007))*x+(-5.890140541457237e-006))*x+(0.00016833479298887047))*x+(-0.0048099757271575479))*x+(0.13743597194397325));
		rts[3] = (((((((((((((3.8562575355172157e-010))*x+(8.4886172165473291e-012))*x+(-2.4207717312189442e-010))*x+(-3.0316490059097597e-012))*x+(-2.5238477974198759e-011))*x+(1.8973243716876214e-009))*x+(-4.5763058527844194e-008))*x+(1.097577781550285e-006))*x+(-2.6267078277168267e-005))*x+(0.00062819825583743105))*x+(-0.015021525034493759))*x+(0.35918629133038438));
		wts[0] = (((((((((((((1.4733814168721437e-010))*x+(-7.8822874153653775e-012))*x+(-9.2957937643708036e-011))*x+(5.722237498654673e-012))*x+(2.0084674664152164e-011))*x+(1.9632295789051568e-011))*x+(-7.8035400363773988e-010))*x+(2.8366105612557625e-008))*x+(-1.0554348493970374e-006))*x+(4.1172618195371248e-005))*x+(-0.0017841948064459942))*x+(0.11597285406607676));
		wts[1] = (((((((((((((4.1533591380963721e-011))*x+(-3.9411437076826888e-012))*x+(-2.5787964356519901e-011))*x+(1.8379372098327922e-012))*x+(5.2461738656954058e-012))*x+(7.5163579064489259e-012))*x+(-2.540840871034788e-010))*x+(8.9753681524011118e-009))*x+(-3.3204359088656593e-007))*x+(1.2942012590791417e-005))*x+(-0.00056078585585054002))*x+(0.036450942005351261));
		wts[2] = (((((((((((((1.7053025658242404e-012))*x+(-2.4632148173016805e-013))*x+(-8.6923061341318929e-013))*x+(1.0539717247108152e-013))*x+(7.8751819880077787e-014))*x+(8.5198514909734513e-013))*x+(-2.2683753024092351e-011))*x+(7.49834999647092e-010))*x+(-2.7352378087601898e-008))*x+(1.0638700521147769e-006))*x+(-4.6088134482564485e-005))*x+(0.0029956774039307174));
		wts[3] = (((((((((((((1.3618735768735253e-014))*x+(-2.3684757858670005e-015))*x+(-5.5881225572799541e-015))*x+(4.9960036108132044e-016))*x+(-9.9457479289336927e-016))*x+(1.688579831515824e-014))*x+(-3.1765634682841737e-013))*x+(9.1080771397189508e-012))*x+(-3.2146247154177883e-010))*x+(1.2441067171577335e-008))*x+(-5.3868597256443434e-007))*x+(3.5012903472027588e-005));
		break;
	case 33:
		rts[0] = (((((((((((((7.7686005776437615e-012))*x+(-4.7369515717340006e-013))*x+(-5.1893304468345978e-012))*x+(1.91846538655227e-013))*x+(1.1481186371990284e-012))*x+(3.0869381125360933e-012))*x+(-1.0515474602179607e-010))*x+(3.5164367806483909e-009))*x+(-1.1737865402393354e-007))*x+(3.91560169138583e-006))*x+(-0.00013060555801143613))*x+(0.0043563135254954845));
		rts[1] = (((((((((((((4.2139921182145671e-011))*x+(0))*x+(-2.5787964356519901e-011))*x+(-1.0042337332076081e-012))*x+(4.1779912862693891e-012))*x+(3.7485866262917021e-011))*x+(-1.2053939328164156e-009))*x+(3.8886862322821493e-008))*x+(-1.2515310206841674e-006))*x+(4.025508420406794e-005))*x+(-0.0012946582868190693))*x+(0.041637426653771972));
		rts[2] = (((((((((((((1.2611659864584604e-010))*x+(-9.0949470177292824e-012))*x+(-7.3820653293902667e-011))*x+(6.1390892369672656e-012))*x+(8.1001871876651421e-012))*x+(1.9453949562375783e-010))*x+(-5.8511104109963217e-009))*x+(1.7348178005249792e-007))*x+(-5.1335605071312074e-006))*x+(0.00015183164285340056))*x+(-0.0044901873613582667))*x+(0.13278863984505154));
		rts[3] = (((((((((((((2.352559628585974e-010))*x+(6.063298011819521e-012))*x+(-1.1990171818373102e-010))*x+(1.2126596023639049e-012))*x+(-3.9638810752270118e-011))*x+(1.4303935813586575e-009))*x+(-3.5851239606661998e-008))*x+(8.9471327235912657e-007))*x+(-2.2298984585685428e-005))*x+(0.00055555179452746817))*x+(-0.013839757383289018))*x+(0.34476775111391794));
		wts[0] = (((((((((((((1.3096723705530167e-010))*x+(1.2126596023639042e-012))*x+(-7.7155467200403408e-011))*x+(-3.2969182939268649e-012))*x+(1.4618232550371126e-011))*x+(1.9075703979372822e-011))*x+(-6.631690752101348e-010))*x+(2.4772791817895268e-008))*x+(-9.4935084615777043e-007))*x+(3.8169030806574814e-005))*x+(-0.0017049061801016549))*x+(0.11422880405101959));
		wts[1] = (((((((((((((5.2750692702829838e-011))*x+(5.1538033100465928e-012))*x+(-3.1225984760870538e-011))*x+(-2.5579538487363603e-012))*x+(6.1746163737552706e-012))*x+(6.5002817943119827e-012))*x+(-2.1290613716473672e-010))*x+(7.8144200739889876e-009))*x+(-2.98532593488258e-007))*x+(1.1997308388453363e-005))*x+(-0.0005358632835110004))*x+(0.035902774847711871));
		wts[2] = (((((((((((((7.5222790959135929e-012))*x+(3.7895612573872008e-014))*x+(-4.6410283024063874e-012))*x+(-8.1712414612411521e-014))*x+(9.7048295325900337e-013))*x+(6.4156087849672373e-013))*x+(-1.8414811342459814e-011))*x+(6.4793466888109675e-010))*x+(-2.4564063391280717e-008))*x+(9.8609715846904411e-007))*x+(-4.4039560705379075e-005))*x+(0.0029506265150950847));
		wts[3] = (((((((((((((1.4388490399142029e-013))*x+(1.6283271027835629e-015))*x+(-9.4479979395600822e-014))*x+(-2.4239869370982583e-015))*x+(2.1348663577687905e-014))*x+(1.1114373310583401e-014))*x+(-2.4104922340580554e-013))*x+(7.7322548682155315e-012))*x+(-2.8791223155396879e-010))*x+(1.1528377616877724e-008))*x+(-5.147332898041937e-007))*x+(3.4486345910061345e-005));
		break;
	case 34:
		rts[0] = (((((((((((((-2.2737367544323206e-012))*x+(-2.2358411418584483e-012))*x+(1.5821418249591563e-012))*x+(1.2718714970105791e-012))*x+(-4.5533946983293084e-013))*x+(2.2986057501839241e-012))*x+(-8.8117180219171574e-011))*x+(3.0348860461752261e-009))*x+(-1.0430415490573589e-007))*x+(3.5835587638930835e-006))*x+(-0.00012311293199847726))*x+(0.0042295096049393202));
		rts[1] = (((((((((((((4.0320931778599814e-011))*x+(-4.6990559591601287e-012))*x+(-2.3324749539218221e-011))*x+(2.6716406864579763e-012))*x+(3.5527136788005005e-012))*x+(2.9563906878138368e-011))*x+(-1.0049795810355513e-009))*x+(3.3379979447190067e-008))*x+(-1.1073308579939711e-006))*x+(3.6722294923044921e-005))*x+(-0.00121775297442639))*x+(0.040381809637959343));
		rts[2] = (((((((((((((1.8432425955931345e-010))*x+(-6.063298011819521e-012))*x+(-1.1853747613107163e-010))*x+(3.5621875819439684e-012))*x+(2.1903664067698017e-011))*x+(1.5540517021387737e-010))*x+(-4.8018679403109364e-009))*x+(1.4695760105117492e-007))*x+(-4.4944315091092566e-006))*x+(0.00013741615893730907))*x+(-0.0042012589491469497))*x+(0.12844531838725998));
		rts[3] = (((((((((((((5.2386894822120667e-010))*x+(-6.184563972055912e-011))*x+(-3.3166240124652785e-010))*x+(4.0017766878008842e-011))*x+(3.1718627724330872e-011))*x+(1.0816876283570309e-009))*x+(-2.8346815857579106e-008))*x+(7.3508608563107214e-007))*x+(-1.9051888207795759e-005))*x+(0.0004936849429100405))*x+(-0.012792142944519014))*x+(0.33146210677911769));
		wts[0] = (((((((((((((1.1944697083284456e-010))*x+(-4.850638409455617e-012))*x+(-7.3328010330442326e-011))*x+(2.2737367544323206e-013))*x+(1.507297990125759e-011))*x+(1.56035184772918e-011))*x+(-5.6605875542459206e-010))*x+(2.1712675509396224e-008))*x+(-8.5654128431644772e-007))*x+(3.5463251225590721e-005))*x+(-0.0016313202866512495))*x+(0.11256114167897255));
		wts[1] = (((((((((((((5.305385760342081e-011))*x+(1.8947806286936004e-011))*x+(-3.4769224536527567e-011))*x+(-1.152026622245709e-011))*x+(7.969921019442456e-012))*x+(7.3286562004189672e-012))*x+(-1.8033670852920142e-010))*x+(6.8373939103120538e-009))*x+(-2.6928319612577284e-007))*x+(1.1146560892033124e-005))*x+(-0.00051273403346088374))*x+(0.035378617947943246));
		wts[2] = (((((((((((((-1.6863547595373043e-012))*x+(8.1475567033824815e-013))*x+(1.2920035411904487e-012))*x+(-4.9501143924620306e-013))*x+(-3.9287092098068871e-013))*x+(5.569618840202868e-013))*x+(-1.5115367291151927e-011))*x+(5.6458412944770942e-010))*x+(-2.2144267845051097e-008))*x+(9.1611793096921018e-007))*x+(-4.2138554991249811e-005))*x+(0.0029075491176768233));
		wts[3] = (((((((((((((-2.1908401019269754e-014))*x+(6.0692192012841888e-015))*x+(1.6912397408456549e-014))*x+(-4.8664775912736023e-015))*x+(-5.6852670719346553e-015))*x+(8.1445267197111077e-015))*x+(-1.8790510235751806e-013))*x+(6.6718319960181357e-012))*x+(-2.5918702247555313e-010))*x+(1.0708787337399585e-008))*x+(-4.9251047920891385e-007))*x+(3.398286058867169e-005));
		break;
	case 35:
		rts[0] = (((((((((((((8.9812601800076663e-012))*x+(-1.1937117960769683e-012))*x+(-5.5967082820037222e-012))*x+(7.460698725481052e-013))*x+(1.1374604961626271e-012))*x+(1.9271251261443467e-012))*x+(-7.4398422607776141e-011))*x+(2.6298761686878907e-009))*x+(-9.2997767677076764e-008))*x+(3.288010658664073e-006))*x+(-0.00011624701346009847))*x+(0.004109878876738117));
		rts[1] = (((((((((((((5.0931703299283981e-011))*x+(1.0610771520684161e-012))*x+(-3.1908105787200235e-011))*x+(-6.44225413755824e-013))*x+(6.1817218011128716e-012))*x+(2.4674188618215944e-011))*x+(-8.421284410549863e-010))*x+(2.8778168958965011e-008))*x+(-9.832862767715036e-007))*x+(3.3590968191658792e-005))*x+(-0.0011475017064363155))*x+(0.039199704032056401));
		rts[2] = (((((((((((((1.5885840790967146e-010))*x+(-1.3339255626002947e-011))*x+(-9.3602163057463856e-011))*x+(6.9727927135924493e-012))*x+(1.437191106864096e-011))*x+(1.2389023140713104e-010))*x+(-3.961257100115744e-009))*x+(1.2513677116743338e-007))*x+(-3.9516406298845119e-006))*x+(0.00012476885591524342))*x+(-0.003939345190068169))*x+(0.12437712347486715));
		rts[3] = (((((((((((((4.0745362639427185e-010))*x+(-3.637978807091713e-012))*x+(-2.4586673437928158e-010))*x+(1.0610771520684163e-012))*x+(1.9194127768666177e-011))*x+(8.385588519862115e-010))*x+(-2.259768313213802e-008))*x+(6.0837913610593353e-007))*x+(-1.6374523882145553e-005))*x+(0.00044067190473212614))*x+(-0.011859123823145527))*x+(0.31914530468410535));
		wts[0] = (((((((((((((1.4612548208485046e-010))*x+(-3.0316490059097606e-013))*x+(-9.5913795424470053e-011))*x+(1.0989727646422882e-012))*x+(2.1988929195989233e-011))*x+(1.187198487665834e-011))*x+(-4.8558446152924262e-010))*x+(1.9098424619556909e-008))*x+(-7.7505437468909178e-007))*x+(3.3018470869260644e-005))*x+(-0.0015628792944440387))*x+(0.1109644492647225));
		wts[1] = (((((((((((((8.4886172165473291e-012))*x+(5.6085506609330569e-012))*x+(-3.4485007442223524e-012))*x+(-4.2632564145606003e-012))*x+(7.1054273576007999e-015))*x+(5.1461057637425256e-012))*x+(-1.5279614610600825e-010))*x+(6.0086529085623397e-009))*x+(-2.4363487301689207e-007))*x+(1.0378012128620568e-005))*x+(-0.00049122228019514956))*x+(0.034876767854969702));
		wts[2] = (((((((((((((2.4442670110147446e-012))*x+(1.3831898589463283e-012))*x+(-1.718329182646509e-012))*x+(-8.1830838401704865e-013))*x+(4.2721381987576024e-013))*x+(5.1758597408024798e-013))*x+(-1.2805335495672901e-011))*x+(4.9503123822347561e-010))*x+(-2.0029001205542723e-008))*x+(8.529275258333085e-007))*x+(-4.0370566764937487e-005))*x+(0.0028663050862170452));
		wts[3] = (((((((((((((6.5725203057809267e-014))*x+(1.2878587085651816e-014))*x+(-4.5482136575477248e-014))*x+(-7.7530574552990093e-015))*x+(1.093107086328852e-014))*x+(6.4375588193499303e-015))*x+(-1.5548398795324953e-013))*x+(5.8191319240082544e-012))*x+(-2.3426152130511608e-010))*x+(9.9694662697536276e-009))*x+(-4.7184468261542006e-007))*x+(3.3500806199559356e-005));
		break;
	case 36:
		rts[0] = (((((((((((((2.4632148173016804e-012))*x+(-5.6843418860808015e-013))*x+(-1.2955562548692492e-012))*x+(3.3158661002138007e-013))*x+(1.4506914188435377e-013))*x+(1.6558606337942667e-012))*x+(-6.2891886143390252e-011))*x+(2.2878049639925751e-009))*x+(-8.3181452194385413e-008))*x+(3.0240837074468432e-006))*x+(-0.00010993982535329957))*x+(0.0039968294337632462));
		rts[1] = (((((((((((((5.4872847006966666e-011))*x+(-4.850638409455617e-012))*x+(-3.4807120149101437e-011))*x+(3.0695446184836324e-012))*x+(7.0699002208129968e-012))*x+(1.9396632448357799e-011))*x+(-7.0885364245043547e-010))*x+(2.4914973047647965e-008))*x+(-8.7612218476843895e-007))*x+(3.080571651383849e-005))*x+(-0.0010831585815717858))*x+(0.038084837967994174));
		rts[2] = (((((((((((((1.4309383307894069e-010))*x+(1.8189894035458565e-012))*x+(-8.9585228124633419e-011))*x+(-2.6526928801710406e-012))*x+(1.6200374375330284e-011))*x+(1.0177577299449088e-010))*x+(-3.2875160371759193e-009))*x+(1.0708239687555003e-007))*x+(-3.4883245253469752e-006))*x+(0.00011362695014726272))*x+(-0.0037011809298498318))*x+(0.12055871679797654));
		rts[3] = (((((((((((((3.2741809263825417e-010))*x+(1.5764574830730755e-011))*x+(-1.9478344862970215e-010))*x+(-1.2126596023639042e-011))*x+(1.5271931867270424e-011))*x+(6.534198367565598e-010))*x+(-1.8160491184933864e-008))*x+(5.0696900366631326e-007))*x+(-1.4151210924665904e-005))*x+(0.00039498461844143329))*x+(-0.01102457821844738))*x+(0.30771106483516314));
		wts[0] = (((((((((((((1.7462298274040222e-010))*x+(-1.2429760924230019e-011))*x+(-1.13990002622207e-010))*x+(7.8443918027915061e-012))*x+(2.6223763901119433e-011))*x+(8.6603317110226872e-012))*x+(-4.1787136713840784e-010))*x+(1.6856726237080011e-008))*x+(-7.0325800227699631e-007))*x+(3.0803242812178312e-005))*x+(-0.001499093467587619))*x+(0.1094338320137056));
		wts[1] = (((((((((((((6.6696278130014735e-012))*x+(1.0459189070388675e-011))*x+(-3.6000831945178407e-012))*x+(-7.4654356770527865e-012))*x+(5.3527552760594201e-013))*x+(5.2467659846418729e-012))*x+(-1.3101149794655004e-010))*x+(5.3006776005541188e-009))*x+(-2.2105203006013891e-007))*x+(9.6816893236257671e-006))*x+(-0.00047117386652263031))*x+(0.03439568581183277));
		wts[2] = (((((((((((((3.1832314562052488e-012))*x+(-5.6843418860808015e-014))*x+(-2.1126804009933644e-012))*x+(3.5527136788005009e-014))*x+(5.0833411554170504e-013))*x+(2.7822188997106423e-013))*x+(-1.0908884906513094e-011))*x+(4.3620338822473548e-010))*x+(-1.816967735296382e-008))*x+(7.9568830432836851e-007))*x+(-3.8722880279940886e-005))*x+(0.0028267679006052111));
		wts[3] = (((((((((((((2.8717768903637378e-014))*x+(6.6613381477509392e-015))*x+(-1.8485213360008853e-014))*x+(-3.9412917374193057e-015))*x+(4.4316402399620829e-015))*x+(4.505076867111768e-015))*x+(-1.2979468483794349e-013))*x+(5.1132076003823634e-012))*x+(-2.1243818880762602e-010))*x+(9.3001219546224794e-009))*x+(-4.5258600189328693e-007))*x+(3.3038702391187731e-005));
		break;
	case 37:
		rts[0] = (((((((((((((7.920183027939249e-012))*x+(-3.7895612573872007e-013))*x+(-5.0188001902521738e-012))*x+(2.4868995751603501e-013))*x+(1.0877225046594199e-012))*x+(1.3670546176551093e-012))*x+(-5.3566641862919554e-011))*x+(1.9976672815946728e-009))*x+(-7.4626236126404399e-008))*x+(2.787662161749087e-006))*x+(-0.00010413235551886169))*x+(0.0038898327372538367));
		rts[1] = (((((((((((((2.1524707941959299e-011))*x+(-1.2126596023639042e-012))*x+(-1.2638186793386314e-011))*x+(8.905468954859921e-013))*x+(1.9682033780554775e-012))*x+(1.6311692737266029e-011))*x+(-5.9887243312554495e-010))*x+(2.1656548110371432e-008))*x+(-7.8316168120503194e-007))*x+(2.8320047290530947e-005))*x+(-0.0010240792797945512))*x+(0.037031633206987102));
		rts[2] = (((((((((((((1.3703053506712118e-010))*x+(-7.8822874153653775e-012))*x+(-8.3597721337961645e-011))*x+(4.3200998334214083e-012))*x+(1.4987714772966378e-011))*x+(8.0833710095854856e-011))*x+(-2.7428231537858969e-009))*x+(9.2061890851387787e-008))*x+(-3.0909424027873258e-006))*x+(0.00010377306082802924))*x+(-0.0034839795193116604))*x+(0.11696777838804447));
		rts[3] = (((((((((((((3.5894724229971564e-010))*x+(-2.7891170854369797e-011))*x+(-2.2343253173554936e-010))*x+(1.6522487082208194e-011))*x+(2.9994377352219694e-011))*x+(5.0509640914242471e-010))*x+(-1.4707307371963907e-008))*x+(4.2516977494244651e-007))*x+(-1.2292683715831034e-005))*x+(0.00035540050555984038))*x+(-0.010275121783241262))*x+(0.29706780946316186));
		wts[0] = (((((((((((((9.0343140376110867e-011))*x+(1.8189894035458565e-012))*x+(-5.2106467289074005e-011))*x+(-3.2211270687791207e-012))*x+(9.5212726591853393e-012))*x+(9.9878623890011422e-012))*x+(-3.5866791018671995e-010))*x+(1.4927084161323972e-008))*x+(-6.3978569676363206e-007))*x+(2.8790605634293476e-005))*x+(-0.0014395313458233909))*x+(0.10796485498226042));
		wts[1] = (((((((((((((5.5782341708739594e-011))*x+(2.2737367544323206e-012))*x+(-3.5659771432013557e-011))*x+(-1.8379372098327926e-012))*x+(7.808864666003501e-012))*x+(3.3093527918026662e-012))*x+(-1.1342467705806787e-010))*x+(4.6929126510756678e-009))*x+(-2.0109460359870232e-007))*x+(9.0490769715211479e-006))*x+(-0.00045245307591549173))*x+(0.033933977755754449));
		wts[2] = (((((((((((((8.0149220593739301e-012))*x+(5.6843418860808015e-013))*x+(-5.3065699982350152e-012))*x+(-3.8250883941752062e-013))*x+(1.2316074086508404e-012))*x+(3.1752378504279477e-013))*x+(-9.4250857118893789e-012))*x+(3.859318790470449e-010))*x+(-1.6527964091968272e-008))*x+(7.4369207069801169e-007))*x+(-3.7184320504112265e-005))*x+(0.0027888229645779174));
		wts[3] = (((((((((((((1.9539925233402755e-014))*x+(-2.9605947323337506e-016))*x+(-1.1472304587793285e-014))*x+(-5.3660779523549239e-016))*x+(1.9405773284593883e-015))*x+(3.2427764177593113e-015))*x+(-1.0993723292829215e-013))*x+(4.5174442890131656e-012))*x+(-1.9320882371393007e-010))*x+(8.6922467793393976e-009))*x+(-4.3460324465051172e-007))*x+(3.2595209060604747e-005));
		break;
	case 38:
		rts[0] = (((((((((((((2.0084674664152163e-012))*x+(1.0042337332076081e-012))*x+(-6.5606779268515904e-013))*x+(-5.8738199489501599e-013))*x+(-8.7929663550312448e-014))*x+(1.304808113407792e-012))*x+(-4.5597664533048032e-011))*x+(1.7505189612669152e-009))*x+(-6.7142905481436713e-008))*x+(2.5752554608333626e-006))*x+(-9.8773178261244549e-005))*x+(0.0037884153632486484));
		rts[1] = (((((((((((((3.8805107275644936e-011))*x+(7.8822874153653775e-012))*x+(-2.3874235921539366e-011))*x+(-4.964325247177233e-012))*x+(4.665897298157991e-012))*x+(1.4760341097523149e-011))*x+(-5.0882142943464714e-010))*x+(1.8895785528864433e-008))*x+(-7.022072640953484e-007))*x+(2.6094753070073549e-005))*x+(-0.00096970494160376669))*x+(0.036035111886705315));
		rts[2] = (((((((((((((1.6855968472858268e-010))*x+(0))*x+(-1.0936673788819461e-010))*x+(-4.5474735088646412e-013))*x+(2.3163693185779266e-011))*x+(6.6748384597303811e-011))*x+(-2.3015050606052983e-009))*x+(7.9498095513959769e-008))*x+(-2.7485589691456092e-006))*x+(9.5026364769971547e-005))*x+(-0.0032853512117700595))*x+(0.11358457038674964));
		rts[3] = (((((((((((((3.6137256150444347e-010))*x+(-2.1827872842550278e-011))*x+(-2.2085563008052603e-010))*x+(1.3642420526593924e-011))*x+(3.2722861457538472e-011))*x+(3.9810288399166893e-010))*x+(-1.1994740016045094e-008))*x+(3.5870178294317157e-007))*x+(-1.0729457279275618e-005))*x+(0.00032093370811673661))*x+(-0.0095995687314002313))*x+(0.28713620645903842));
		wts[0] = (((((((((((((1.594647377108534e-010))*x+(9.701276818911234e-012))*x+(-1.009918075093689e-010))*x+(-6.4422541375582414e-012))*x+(2.2263672387149804e-011))*x+(8.9102059064316563e-012))*x+(-3.1197074553309295e-010))*x+(1.3260494036160251e-008))*x+(-5.8349003857297933e-007))*x+(2.6957357859254866e-005))*x+(-0.0013838115221152345))*x+(0.10655348903406531));
		wts[1] = (((((((((((((5.2144362901647881e-011))*x+(-1.5612992380435266e-011))*x+(-3.2741809263825417e-011))*x+(9.4360075308941289e-012))*x+(7.0296361324532573e-012))*x+(3.5704772471945075e-013))*x+(-9.808420742274393e-011))*x+(4.1686288495175932e-009))*x+(-1.833971099614769e-007))*x+(8.4728636488030449e-006))*x+(-0.00043493998150495941))*x+(0.033490377245123187));
		wts[2] = (((((((((((((7.4654356770527849e-012))*x+(-1.6200374375330284e-012))*x+(-4.4882616142179659e-012))*x+(1.0255500152804113e-012))*x+(9.1038288019262836e-013))*x+(-3.8080649744642895e-014))*x+(-8.1010661142263026e-012))*x+(3.4271551800172751e-010))*x+(-1.5072826480578651e-008))*x+(6.9633410154891604e-007))*x+(-3.5745021689083795e-005))*x+(0.0027523661850354618));
		wts[3] = (((((((((((((1.1723955140041653e-013))*x+(-9.3258734068513149e-015))*x+(-7.4236912913268796e-014))*x+(5.3845816694320092e-015))*x+(1.6523819349837748e-014))*x+(1.1454957353033515e-015))*x+(-9.5890309581569966e-014))*x+(4.0084700605088246e-012))*x+(-1.7618285828727501e-010))*x+(8.1386680854569284e-009))*x+(-4.1778084015883324e-007))*x+(3.2169109264354071e-005));
		break;
	case 39:
		rts[0] = (((((((((((((4.2822042208475369e-012))*x+(-1.1937117960769683e-012))*x+(-2.6455874528134396e-012))*x+(7.1054273576010019e-013))*x+(5.3438734918624198e-013))*x+(8.4576790015944425e-013))*x+(-3.9151339577732827e-011))*x+(1.5391810511318955e-009))*x+(-6.0574380195248717e-008))*x+(2.3838907965258514e-006))*x+(-9.3817315177735446e-005))*x+(0.0036921520035990752));
		rts[1] = (((((((((((((3.5167128468553223e-011))*x+(-5.9117155615240335e-012))*x+(-2.2206828968288996e-011))*x+(3.6758744196655852e-012))*x+(4.5190517994342372e-012))*x+(1.0573468027056757e-011))*x+(-4.339633837465347e-010))*x+(1.6546790456336186e-008))*x+(-6.3144670477595832e-007))*x+(2.4096620085130301e-005))*x+(-0.00091954893626969053))*x+(0.035090817891681815));
		rts[2] = (((((((((((((9.0949470177292824e-011))*x+(-7.2759576141834259e-012))*x+(-5.3887561080045998e-011))*x+(3.6758744196655852e-012))*x+(9.0665253082988784e-012))*x+(5.3901771934761194e-011))*x+(-1.9384733818128552e-009))*x+(6.8936013638184093e-008))*x+(-2.4522926049634166e-006))*x+(8.7235643434731738e-005))*x+(-0.0031032372766223761))*x+(0.11039157424432243));
		rts[3] = (((((((((((((2.0857745160659153e-010))*x+(-2.3040532444914181e-011))*x+(-1.2005330063402653e-010))*x+(1.2429760924230019e-011))*x+(1.1842378929335005e-011))*x+(3.1645204974968988e-010))*x+(-9.8456212072051114e-009))*x+(3.0431860468619715e-007))*x+(-9.4069912922230704e-006))*x+(0.0002907833771678322))*x+(-0.0089885125218978242))*x+(0.27784718907673422));
		wts[0] = (((((((((((((1.7583564234276611e-010))*x+(-1.4248750327775875e-011))*x+(-1.0618350643198937e-010))*x+(8.9812601800076663e-012))*x+(2.1458390619955026e-011))*x+(4.1957548546633916e-012))*x+(-2.707899090144868e-010))*x+(1.1815920834360819e-008))*x+(-5.3340518522497027e-007))*x+(2.5283459243523782e-005))*x+(-0.0013315957406785431))*x+(0.10519606433763101));
		wts[1] = (((((((((((((1.6370904631912708e-011))*x+(2.4253192047278085e-012))*x+(-5.7980287238024175e-012))*x+(-1.6484591469634322e-012))*x+(-4.5948430245819825e-013))*x+(2.3305801732931286e-012))*x+(-8.432114266080741e-011))*x+(3.7139753494841443e-009))*x+(-1.6765361709099774e-007))*x+(7.9467418781786758e-006))*x+(-0.00041852824560130393))*x+(0.033063730803391839));
		wts[2] = (((((((((((((5.3432813729159534e-012))*x+(8.8107299234252423e-013))*x+(-3.1761260288476478e-012))*x+(-5.7909232964448165e-013))*x+(6.3386333219265611e-013))*x+(2.9098945475425353e-013))*x+(-7.0128625129228794e-012))*x+(3.0527081325744848e-010))*x+(-1.3778653209714498e-008))*x+(6.5309427639678372e-007))*x+(-3.4396240219885298e-005))*x+(0.0027173027594723114));
		wts[3] = (((((((((((((1.1339077824838265e-013))*x+(-2.6645352591003757e-015))*x+(-7.4995565313429324e-014))*x+(2.3499720687899144e-015))*x+(1.7832957333041577e-014))*x+(1.1772989990295932e-015))*x+(-8.3473664901541803e-014))*x+(3.5694989354341971e-012))*x+(-1.610485563945151e-010))*x+(7.6332595098728088e-009))*x+(-4.0201647757065719e-007))*x+(3.1759294825631158e-005));
		break;
	case 40:
		rts[0] = (((((((((((((7.0485839387401938e-012))*x+(1.4116115683767323e-012))*x+(-4.6280016855841195e-012))*x+(-8.2896652505345015e-013))*x+(1.0581165573360825e-012))*x+(1.0010881013045037e-012))*x+(-3.3747134716340575e-011))*x+(1.3576809815285527e-009))*x+(-5.4789753122184516e-008))*x+(2.2110259845279797e-006))*x+(-8.9225289798813406e-005))*x+(0.0036006595058676238));
		rts[1] = (((((((((((((2.3040532444914181e-011))*x+(2.7284841053187847e-012))*x+(-1.4210854715202002e-011))*x+(-1.7431981783981125e-012))*x+(2.7734851452502572e-012))*x+(9.8848336923159276e-012))*x+(-3.7150475288664592e-010))*x+(1.4539316935587483e-008))*x+(-5.6937832645006137e-007))*x+(2.2297388950806574e-005))*x+(-0.00087318595104758699))*x+(0.034194750253011781));
		rts[2] = (((((((((((((1.13990002622207e-010))*x+(6.9727927135924493e-012))*x+(-6.9121597334742533e-011))*x+(-5.3432813729159526e-012))*x+(1.2742399727964461e-011))*x+(4.6361729270453601e-011))*x+(-1.6418297832387907e-009))*x+(6.0013279531053357e-008))*x+(-2.1948881329854801e-006))*x+(8.0273790057608374e-005))*x+(-0.0029358564959503551))*x+(0.10737318736974366));
		rts[3] = (((((((((((((2.9831426218152046e-010))*x+(3.637978807091713e-012))*x+(-1.7992836850074431e-010))*x+(-3.3348139065007367e-012))*x+(2.7985909885804481e-011))*x+(2.5601802159750753e-010))*x+(-8.135217536657061e-009))*x+(2.5953418199738582e-007))*x+(-8.282135529354603e-006))*x+(0.00026429443940676845))*x+(-0.0084339968483181336))*x+(0.26914034772329104));
		wts[0] = (((((((((((((1.7462298274040222e-010))*x+(3.0316490059097606e-013))*x+(-1.0686562745831907e-010))*x+(-3.4106051316484809e-013))*x+(2.2557363384597316e-011))*x+(5.4699948274598374e-012))*x+(-2.3655803242187779e-010))*x+(1.0558509474141904e-008))*x+(-4.8871419881339295e-007))*x+(2.3751536766133952e-005))*x+(-0.0012825830843833257))*x+(0.10388923020363088));
		wts[1] = (((((((((((((6.1542474819968135e-011))*x+(-1.0610771520684162e-011))*x+(-3.8217725280749918e-011))*x+(5.6843418860808015e-012))*x+(8.1665045096694176e-012))*x+(6.6554169582862711e-013))*x+(-7.4463916514370482e-011))*x+(3.3187891694079022e-009))*x+(-1.5360624494124381e-007))*x+(7.4652472294526682e-006))*x+(-0.00040312327834069622))*x+(0.032652985277359596));
		wts[2] = (((((((((((((4.0927261579781771e-012))*x+(-9.8528592692067219e-013))*x+(-2.4679517688734145e-012))*x+(5.5540757178581158e-013))*x+(5.0922229396140517e-013))*x+(2.6423307986078726e-014))*x+(-6.1084470814876105e-012))*x+(2.7277771708078546e-010))*x+(-1.2624052638891362e-008))*x+(6.135227146357562e-007))*x+(-3.3130200378975995e-005))*x+(0.002683546133349893));
		wts[3] = (((((((((((((3.1678363635971131e-014))*x+(-7.4014868308343759e-015))*x+(-2.133478578988009e-014))*x+(5.6436337085112111e-015))*x+(5.2689334377002216e-015))*x+(-5.7824115865892255e-018))*x+(-7.1596013261528592e-014))*x+(3.1888555742746548e-012))*x+(-1.4755023168537521e-010))*x+(7.1707417538174316e-009))*x+(-3.8721922370633869e-007))*x+(3.1364754048600666e-005));
		break;
	case 41:
		rts[0] = (((((((((((((1.3263464400855203e-012))*x+(6.1580370432542009e-013))*x+(-6.0869827696781909e-013))*x+(-4.5711582667233109e-013))*x+(2.6645352591003732e-014))*x+(8.250807444672621e-013))*x+(-2.9035394459124099e-011))*x+(1.2012821709594943e-009))*x+(-4.967942947471659e-008))*x+(2.0544785406541831e-006))*x+(-8.4962339673975081e-005))*x+(0.0035135917771617446));
		rts[1] = (((((((((((((4.9112713895738125e-011))*x+(3.9411437076826888e-012))*x+(-3.1074402310575046e-011))*x+(-3.0127011996228244e-012))*x+(6.624626773070001e-012))*x+(8.7609919319220353e-012))*x+(-3.1973357295100868e-010))*x+(1.281710663529149e-008))*x+(-5.1475201239455548e-007))*x+(2.0672914805369699e-005))*x+(-0.00083024295176988461))*x+(0.033343306489925485));
		rts[2] = (((((((((((((1.0065074699620405e-010))*x+(-2.1221543041368323e-012))*x+(-5.9799276641570032e-011))*x+(1.2505552149377761e-012))*x+(1.1008675452709818e-011))*x+(3.6866509844912798e-011))*x+(-1.3965892146453975e-009))*x+(5.2441377018652702e-008))*x+(-1.9703868203528136e-006))*x+(7.4033445852980662e-005))*x+(-0.0027816614698765651))*x+(0.10451546819197524));
		rts[3] = (((((((((((((2.6678511252005893e-010))*x+(-3.637978807091713e-012))*x+(-1.634058814185361e-010))*x+(1.6674069532503686e-012))*x+(2.8118544529813029e-011))*x+(2.05256848554806e-010))*x+(-6.7611587439841969e-009))*x+(2.2243005422713696e-007))*x+(-7.3204952206011118e-006))*x+(0.00024092757274516799))*x+(-0.0079292554275315185))*x+(0.26096261482750782));
		wts[0] = (((((((((((((1.0125707679738601e-010))*x+(-1.1823431123048067e-011))*x+(-5.5820237321313464e-011))*x+(6.1390892369672656e-012))*x+(9.2275816617378317e-012))*x+(3.4710012641880894e-012))*x+(-2.0548170572472674e-010))*x+(9.4610759227009567e-009))*x+(-4.4872423946018536e-007))*x+(2.2346476212191841e-005))*x+(-0.0012365050615266815))*x+(0.10262992027086801));
		wts[1] = (((((((((((((5.184119800105691e-011))*x+(-2.5769016550232964e-012))*x+(-3.1889157980913296e-011))*x+(2.5579538487363603e-012))*x+(6.6625223856438733e-012))*x+(5.9507954119908401e-013))*x+(-6.5020951585855372e-011))*x+(2.973805868222712e-009))*x+(-1.4103684447634249e-007))*x+(7.0236274495941164e-006))*x+(-0.00038864068681906684))*x+(0.032257176886580766));
		wts[2] = (((((((((((((1.6484591469634324e-012))*x+(-7.9580786405131221e-013))*x+(-8.6330942394852173e-013))*x+(4.4764192352886312e-013))*x+(1.1220654035544916e-013))*x+(3.2270482582437867e-014))*x+(-5.2969619431427377e-012))*x+(2.4440605095321644e-010))*x+(-1.1590992466473568e-008))*x+(5.7722850516720337e-007))*x+(-3.1939965562937927e-005))*x+(0.0026510170984687638));
		wts[3] = (((((((((((((7.6087284620977386e-014))*x+(-5.1810407815840636e-015))*x+(-5.0496643903367535e-014))*x+(2.1279274638648831e-015))*x+(1.1816936318354008e-014))*x+(1.2206670859290134e-015))*x+(-6.3177689353192485e-014))*x+(2.8567321396176051e-012))*x+(-1.3547438637938363e-010))*x+(6.7465364893983903e-009))*x+(-3.7330798187458892e-007))*x+(3.0984561135633314e-005));
		break;
	case 42:
		rts[0] = (((((((((((((2.3116323670061925e-012))*x+(1.9516240475544082e-012))*x+(-1.2813454001540472e-012))*x+(-1.2150280781497711e-012))*x+(1.9865590653959469e-013))*x+(8.5835042777186266e-013))*x+(-2.5175074987634119e-011))*x+(1.0660015740497166e-009))*x+(-4.5151247616304992e-008))*x+(1.9123677461680443e-006))*x+(-8.0997756833037563e-005))*x+(0.0034306354095341657));
		rts[1] = (((((((((((((2.6678511252005894e-011))*x+(5.1538033100465928e-012))*x+(-1.5196140642122675e-011))*x+(-3.6190310008047764e-012))*x+(2.5129528088048874e-012))*x+(7.5850437042390695e-012))*x+(-2.7547164549446279e-010))*x+(1.1334004549704938e-008))*x+(-4.6652237571202332e-007))*x+(1.9202485683688281e-005))*x+(-0.00079039165882626859))*x+(0.032533234206740556));
		rts[2] = (((((((((((((1.673470251262188e-010))*x+(6.063298011819521e-012))*x+(-1.07775122160092e-010))*x+(-4.0169349328304325e-012))*x+(2.3684757858670007e-011))*x+(3.184652541676769e-011))*x+(-1.1944963536810367e-009))*x+(4.5987111600235643e-008))*x+(-1.773868587388409e-006))*x+(6.8423513639688974e-005))*x+(-0.0026393027355900269))*x+(0.10180592086295491));
		rts[3] = (((((((((((((3.3711936945716537e-010))*x+(-2.5465851649641991e-011))*x+(-2.0903219895747799e-010))*x+(1.5158245029548805e-011))*x+(3.9240906820244462e-011))*x+(1.6341061837010781e-010))*x+(-5.6509161794338061e-009))*x+(1.9151282989090154e-007))*x+(-6.4944599788008261e-006))*x+(0.00022023603789191512))*x+(-0.0074685046495696315))*x+(0.25326718234843537));
		wts[0] = (((((((((((((1.5036979069312412e-010))*x+(1.3945585427184899e-011))*x+(-9.8528592692067221e-011))*x+(-9.81496365663285e-012))*x+(2.2708945834892799e-011))*x+(6.3261988240507581e-012))*x+(-1.8219203923308669e-010))*x+(8.4994710528955401e-009))*x+(-4.1284460516877175e-007))*x+(2.1055083843729557e-005))*x+(-0.0011931214370478037))*x+(0.10141532222161627));
		wts[1] = (((((((((((((7.2153246340652303e-011))*x+(-1.9250971187526979e-011))*x+(-4.6914768366453544e-011))*x+(1.1804483316761129e-011))*x+(1.084998757505673e-011))*x+(-1.2748320917429128e-012))*x+(-5.7643371557484592e-011))*x+(2.6717427529613738e-009))*x+(-1.2975953545916555e-007))*x+(6.6177348685900195e-006))*x+(-0.00037500496181063625))*x+(0.03187542170096197));
		wts[2] = (((((((((((((6.9917405198793858e-012))*x+(-6.7264712318622811e-013))*x+(-4.574710980402112e-012))*x+(3.9435121834685555e-013))*x+(1.0755840662568517e-012))*x+(2.3203661214665772e-014))*x+(-4.7614736227904091e-012))*x+(2.1956635121167523e-010))*x+(-1.0664149755675959e-008))*x+(5.4387061705528481e-007))*x+(-3.0819329750198769e-005))*x+(0.002619643009632697));
		wts[3] = (((((((((((((8.7041485130612273e-014))*x+(2.3684757858670005e-015))*x+(-5.5622173533720343e-014))*x+(-2.201942332173227e-015))*x+(1.2869335227113273e-014))*x+(1.8920050711320377e-015))*x+(-5.5712234594181474e-014))*x+(2.5661971101339125e-012))*x+(-1.2464099134854197e-010))*x+(6.3566536177624214e-009))*x+(-3.602102071906618e-007))*x+(3.0617867011903673e-005));
		break;
	case 43:
		rts[0] = (((((((((((((-1.9326762412674725e-012))*x+(2.1789977229976404e-013))*x+(1.7739883636143834e-012))*x+(-1.9895196601282803e-013))*x+(-5.9744801698495097e-013))*x+(5.6477045262681713e-013))*x+(-2.1795944678733765e-011))*x+(9.4861841992699425e-010))*x+(-4.1127427575250265e-008))*x+(1.7830670960328602e-006))*x+(-7.730433335637918e-005))*x+(0.0033515059106365205));
		rts[1] = (((((((((((((3.698611787209908e-011))*x+(-2.5769016550232964e-012))*x+(-2.3457384183226772e-011))*x+(1.3642420526593922e-012))*x+(5.0685381817553808e-012))*x+(5.3959799591514939e-012))*x+(-2.388905369817469e-010))*x+(1.0052248441046647e-008))*x+(-4.2381123689187261e-007))*x+(1.7868266601913745e-005))*x+(-0.00075334225595164307))*x+(0.031761589576493422));
		rts[2] = (((((((((((((1.6128372711439926e-010))*x+(-9.701276818911234e-012))*x+(-1.0557717663080742e-010))*x+(5.4948638232114409e-012))*x+(2.3826866405822024e-011))*x+(2.4778993671740562e-011))*x+(-1.0248664139567154e-009))*x+(4.0463224474744188e-008))*x+(-1.6012505649753983e-006))*x+(6.3366356184442932e-005))*x+(-0.0025075991465121957))*x+(0.099233312597464762));
		rts[3] = (((((((((((((2.8861298536260921e-010))*x+(-1.8189894035458565e-011))*x+(-1.8326318240724504e-010))*x+(1.0459189070388675e-011))*x+(3.6645057358934231e-011))*x+(1.3382361885305727e-010))*x+(-4.7473462198392253e-009))*x+(1.6561139718855125e-007))*x+(-5.7817172689119305e-006))*x+(0.00020184765779727534))*x+(-0.007046777174763247))*x+(0.24601260530363581));
		wts[0] = (((((((((((((1.3399888606121141e-010))*x+(-2.4253192047278085e-012))*x+(-8.6060936155263322e-011))*x+(6.0632980118195202e-013))*x+(1.9535188281831019e-011))*x+(3.4248159863636825e-012))*x+(-1.6027549657830301e-010))*x+(7.65511920519657e-009))*x+(-3.8057085554229114e-007))*x+(1.9865804710065639e-005))*x+(-0.0011522166817854701))*x+(0.10024285134724907));
		wts[1] = (((((((((((((8.2157688060154513e-011))*x+(-2.7284841053187847e-012))*x+(-5.5157064101270706e-011))*x+(1.4779288903810084e-012))*x+(1.3128461281060783e-011))*x+(7.6146496515624063e-013))*x+(-5.1091945489171537e-011))*x+(2.4060951749523456e-009))*x+(-1.1961564027699692e-007))*x+(6.243937357000573e-006))*x+(-0.00036214836039032231))*x+(0.031506907330603087));
		wts[2] = (((((((((((((3.7895612573872007e-013))*x+(5.6843418860808015e-014))*x+(2.0842586915629607e-013))*x+(-9.4739031434680016e-014))*x+(-1.9273471707492718e-013))*x+(1.2360483007493409e-013))*x+(-4.0531652108673671e-012))*x+(1.9773628105272204e-010))*x+(-9.8304822442052409e-009))*x+(5.1315047802993886e-007))*x+(-2.9762725399657172e-005))*x+(0.0025893571013540406));
		wts[3] = (((((((((((((-4.4408920985006262e-015))*x+(1.8207657603852567e-014))*x+(8.3081689676115876e-015))*x+(-1.2175445836722551e-014))*x+(-3.4786988104921566e-015))*x+(3.8817328980774351e-015))*x+(-4.731378772567426e-014))*x+(2.3109318278424773e-012))*x+(-1.1489694911006141e-010))*x+(5.9976016534387384e-009))*x+(-3.4786082291027641e-007))*x+(3.026389133034975e-005));
		break;
	case 44:
		rts[0] = (((((((((((((3.2969182939268649e-012))*x+(-3.0316490059097606e-013))*x+(-1.7929361699013195e-012))*x+(1.3263464400855202e-013))*x+(2.8244073746463987e-013))*x+(4.119667570042414e-013))*x+(-1.9090867775517495e-011))*x+(8.4640510341256925e-010))*x+(-3.7542024148550415e-008))*x+(1.6651651116335088e-006))*x+(-7.3857893382954536e-005))*x+(0.0032759444441918602));
		rts[1] = (((((((((((((3.0316490059097604e-011))*x+(7.5791225147744013e-013))*x+(-1.8341476485754051e-011))*x+(-4.7369515717340006e-013))*x+(3.6048201460895744e-012))*x+(4.9033369956911583e-012))*x+(-2.0741216151994496e-010))*x+(8.940438759689565e-009))*x+(-3.8587800828733998e-007))*x+(1.665484405818235e-005))*x+(-0.00071883810670080386))*x+(0.031025701595219168));
		rts[2] = (((((((((((((8.4886172165473298e-011))*x+(-3.637978807091713e-012))*x+(-5.0780120848988489e-011))*x+(1.7431981783981125e-012))*x+(9.5591682717592123e-012))*x+(2.1477338426241961e-011))*x+(-8.8101378044787749e-010))*x+(3.5716511526118211e-008))*x+(-1.4491281583965214e-006))*x+(5.8795532514440328e-005))*x+(-0.0023855132953775381))*x+(0.096787518022343588));
		rts[3] = (((((((((((((3.2499277343352634e-010))*x+(1.2126596023639042e-012))*x+(-2.0918378140777349e-010))*x+(-1.5158245029548803e-012))*x+(4.4356814517717183e-011))*x+(1.1210943284822861e-010))*x+(-4.0088086924091239e-009))*x+(1.438017657543848e-007))*x+(-5.1641224445564404e-006))*x+(0.00018545069504603368))*x+(-0.0066597874962086396))*x+(0.23916205506887822));
		wts[0] = (((((((((((((6.6696278130014733e-011))*x+(1.3642420526593924e-011))*x+(-4.039672300374756e-011))*x+(-8.2612435411040987e-012))*x+(8.3086130568214376e-012))*x+(4.5936587866890477e-012))*x+(-1.4045564711295808e-010))*x+(6.9107734349908388e-009))*x+(-3.5146976719765039e-007))*x+(1.8768487640546023e-005))*x+(-0.001113596936913258))*x+(0.099110127399282127));
		wts[1] = (((((((((((((2.7588005953778822e-011))*x+(-9.0949470177292824e-013))*x+(-1.6389852438199643e-011))*x+(-1.3263464400855197e-013))*x+(3.2542857297812584e-012))*x+(1.1344999014302932e-012))*x+(-4.4177920581015919e-011))*x+(2.1721001293902495e-009))*x+(-1.1046899970242514e-007))*x+(5.8990441720307976e-006))*x+(-0.00035000995122955322))*x+(0.031150885649197414));
		wts[2] = (((((((((((((7.5222790959135929e-012))*x+(-5.6843418860808015e-013))*x+(-4.7878738011301412e-012))*x+(3.1737575530617807e-013))*x+(1.0779525420427185e-012))*x+(8.7337544603845606e-015))*x+(-3.713293561524722e-012))*x+(1.7852269662554929e-010))*x+(-9.0787616744437503e-009))*x+(4.848058291883477e-007))*x+(-2.8765144869439239e-005))*x+(0.0025600978896869733));
		wts[3] = (((((((((((((1.2049620560598365e-013))*x+(-7.6975463040677515e-015))*x+(-7.510658761589184e-014))*x+(4.3298697960381097e-015))*x+(1.6276332133931721e-014))*x+(1.5034270125132262e-017))*x+(-4.3630969786175498e-014))*x+(2.0865582843708022e-012))*x+(-1.0611086332789221e-010))*x+(5.6663145555617741e-009))*x+(-3.3620129877932077e-007))*x+(2.9921915476531385e-005));
		break;
	case 45:
		rts[0] = (((((((((((((9.8528592692067215e-012))*x+(7.5791225147744016e-014))*x+(-6.6364691519993349e-012))*x+(-8.6449366184145518e-014))*x+(1.5978329770405251e-012))*x+(4.0042043754813978e-013))*x+(-1.6860161415147936e-011))*x+(7.5711495406416418e-010))*x+(-3.4338947773234388e-008))*x+(1.5574328986802757e-006))*x+(-7.0636896509315277e-005))*x+(0.0032037150016399484));
		rts[1] = (((((((((((((3.2741809263825417e-011))*x+(-2.1221543041368323e-012))*x+(-1.9743614150987316e-011))*x+(1.6674069532503682e-012))*x+(3.9387752318968223e-012))*x+(3.6249521902694446e-012))*x+(-1.8085251814644227e-010))*x+(7.97306361673596e-009))*x+(-3.5209539428482373e-007))*x+(1.554885102177106e-005))*x+(-0.0006866512984952972))*x+(0.03032314119256229));
		rts[2] = (((((((((((((8.9736810574928911e-011))*x+(-7.8822874153653775e-012))*x+(-5.4418099656080202e-011))*x+(4.8127427968817447e-012))*x+(1.076235397097965e-011))*x+(1.7278030857899768e-011))*x+(-7.6151766374247621e-010))*x+(3.1622722218571653e-008))*x+(-1.3146491463222885e-006))*x+(5.4653958699607541e-005))*x+(-0.0022721310237405964))*x+(0.094459385988704098));
		rts[3] = (((((((((((((3.3226873104770977e-010))*x+(-2.2434202643732228e-011))*x+(-2.1236701286397874e-010))*x+(1.2581343374525505e-011))*x+(4.5493682894933344e-011))*x+(8.9644440019280111e-011))*x+(-3.4005124642059546e-009))*x+(1.253499618177519e-007))*x+(-4.6268323766751607e-006))*x+(0.0001707827046518266))*x+(-0.0063038226402473913))*x+(0.23268269405111064));
		wts[0] = (((((((((((((1.4673181188603241e-010))*x+(-8.4886172165473291e-012))*x+(-9.2086338554508971e-011))*x+(6.1011936243933925e-012))*x+(1.9980461729574014e-011))*x+(9.3791641120333225e-013))*x+(-1.2541878646743498e-010))*x+(6.2533957271663594e-009))*x+(-3.2516822355092379e-007))*x+(1.7754188032200375e-005))*x+(-0.00107708740931938))*x+(0.098014954254185563));
		wts[1] = (((((((((((((2.5162686749051012e-011))*x+(3.0316490059097606e-013))*x+(-1.5631940186722204e-011))*x+(-3.1263880373444408e-013))*x+(3.2827074392116629e-012))*x+(8.4554585555451922e-013))*x+(-3.9137804108690943e-011))*x+(1.9654319653265398e-009))*x+(-1.0220226943913335e-007))*x+(5.5802439041704082e-006))*x+(-0.00033853479567818364))*x+(0.030806666402233288));
		wts[2] = (((((((((((((7.787548383930698e-012))*x+(5.0211686660380406e-013))*x+(-4.9962996702864375e-012))*x+(-3.7421917416698603e-013))*x+(1.1091868164688399e-012))*x+(1.6294373258081879e-013))*x+(-3.2920749459819376e-012))*x+(1.6151582386362642e-010))*x+(-8.3993696185201868e-009))*x+(4.5860560771463985e-007))*x+(-2.7822073060103783e-005))*x+(0.002531808646859863));
		wts[3] = (((((((((((((6.2468548852242137e-014))*x+(3.4046839421838131e-015))*x+(-3.3140157285060923e-014))*x+(-2.0539125955565392e-015))*x+(4.9381794949473106e-015))*x+(1.1489651822553051e-015))*x+(-3.736543771152659e-014))*x+(1.8878728152519711e-012))*x+(-9.8170269868795283e-011))*x+(5.360091368375636e-009))*x+(-3.2517886237775436e-007))*x+(2.9591276426534571e-005));
		break;
	case 46:
		rts[0] = (((((((((((((2.4632148173016804e-012))*x+(4.5474735088646412e-013))*x+(-1.1534477077172292e-012))*x+(-3.1027032794857706e-013))*x+(1.0125233984581423e-013))*x+(3.9005835598497168e-013))*x+(-1.4630380240632235e-011))*x+(6.788953010872234e-010))*x+(-3.1470323003217796e-008))*x+(1.4587971771210886e-006))*x+(-6.7622100409879261e-005))*x+(0.0031346019398612712));
		rts[1] = (((((((((((((4.6687394691010312e-011))*x+(-2.3495279795800643e-012))*x+(-2.9179621681881443e-011))*x+(1.2031856992204362e-012))*x+(6.2598815020464826e-012))*x+(3.3013591860253655e-012))*x+(-1.5839833148826679e-010))*x+(7.1285233641897134e-009))*x+(-3.2193014627239042e-007))*x+(1.4538656880508601e-005))*x+(-0.00065657886942965696))*x+(0.029651694446154633));
		rts[2] = (((((((((((((1.3399888606121141e-010))*x+(3.637978807091713e-012))*x+(-8.7425178207922714e-011))*x+(-2.1979455292845764e-012))*x+(1.9838353182421997e-011))*x+(1.5977737651458785e-011))*x+(-6.6148405271822708e-010))*x+(2.8079078913852602e-008))*x+(-1.1954139742994159e-006))*x+(5.0892406002978063e-005))*x+(-0.0021666442597636057))*x+(0.09224062515435244));
		rts[3] = (((((((((((((3.6743585951626301e-010))*x+(1.2126596023639042e-011))*x+(-2.4351720639970154e-010))*x+(-8.8675733422860487e-012))*x+(5.5839185127600409e-011))*x+(7.8633396090784416e-011))*x+(-2.8985794505350291e-009))*x+(1.0966701680104052e-007))*x+(-4.1576363331204585e-006))*x+(0.00015762167568026766))*x+(-0.0059756527741231672))*x+(0.2265451493263814));
		wts[0] = (((((((((((((1.2247861983875433e-010))*x+(-4.850638409455617e-012))*x+(-7.3593279618459435e-011))*x+(3.6000831945178407e-012))*x+(1.4712971581805807e-011))*x+(1.2316074086508402e-012))*x+(-1.1080410663074265e-010))*x+(5.6705535082339038e-009))*x+(-3.0134410805571216e-007))*x+(1.6815002063852447e-005))*x+(-0.0010425301289666577))*x+(0.096955301996619128));
		wts[1] = (((((((((((((4.2139921182145671e-011))*x+(-7.5791225147744013e-013))*x+(-3.0335437865384542e-011))*x+(6.3475151061235603e-013))*x+(7.9865003499435261e-012))*x+(4.577079456187979e-013))*x+(-3.5424626195397949e-011))*x+(1.782289279124901e-009))*x+(-9.4714157974906663e-008))*x+(5.2850523101106534e-006))*x+(-0.00032767324276883943))*x+(0.030473611575505658));
		wts[2] = (((((((((((((-6.2527760746888816e-013))*x+(3.979039320256561e-013))*x+(5.3882824128474261e-013))*x+(-3.043491384839096e-013))*x+(-1.8030021919912542e-013))*x+(1.3256062914024369e-013))*x+(-2.8085080557479119e-012))*x+(1.4646566367145414e-010))*x+(-7.7839743004825181e-009))*x+(4.3434563964332012e-007))*x+(-2.6929429453016831e-005))*x+(0.0025044369384296704));
		wts[3] = (((((((((((((-4.9737991503207013e-014))*x+(-1.4728958793360409e-014))*x+(4.2558549277297665e-014))*x+(8.4469468456897322e-015))*x+(-1.3540094971157639e-014))*x+(-1.03765375921346e-015))*x+(-3.1238900355390342e-014))*x+(1.7120936106918931e-012))*x+(-9.0977651284191108e-011))*x+(5.0765455929104679e-009))*x+(-3.1474582105516928e-007))*x+(2.9271361336582378e-005));
		break;
	case 47:
		rts[0] = (((((((((((((3.1453358436313766e-012))*x+(3.7895612573872007e-013))*x+(-2.1766292472117734e-012))*x+(-2.3092638912203251e-013))*x+(5.3379523023977526e-013))*x+(3.204843797751285e-013))*x+(-1.2942767228333688e-011))*x+(6.1018035069082543e-010))*x+(-2.8895077977889039e-008))*x+(1.3683177717462719e-006))*x+(-6.4796272788206392e-005))*x+(0.0030684078308735202));
		rts[1] = (((((((((((((2.9103830456733704e-011))*x+(3.1074402310575047e-012))*x+(-1.8796223836640518e-011))*x+(-2.0368891758456203e-012))*x+(4.1258848189803148e-012))*x+(3.4766263941795237e-012))*x+(-1.3877373324551931e-010))*x+(6.3890669421695634e-009))*x+(-2.9492727782187695e-007))*x+(1.3614109859992386e-005))*x+(-0.00062843960089113227))*x+(0.029009339277529751));
		rts[2] = (((((((((((((1.1884064103166261e-010))*x+(2.7284841053187847e-012))*x+(-7.7003884750107916e-011))*x+(-2.5769016550232964e-012))*x+(1.7403560074550718e-011))*x+(1.3987033753437571e-011))*x+(-5.7550408882889315e-010))*x+(2.5001488139035168e-008))*x+(-1.089395389490081e-006))*x+(4.7468268139325143e-005))*x+(-0.0020683365806385737))*x+(0.090123705321266831));
		rts[3] = (((((((((((((3.3348139065007365e-010))*x+(3.0316490059097605e-012))*x+(-2.1350388124119488e-010))*x+(-3.4863963567962246e-012))*x+(4.6820029335018866e-011))*x+(6.4780181219248334e-011))*x+(-2.4789980438792254e-009))*x+(9.6281127367111211e-008))*x+(-3.7464360734262847e-006))*x+(0.00014577894611605044))*x+(-0.0056724576828432929))*x+(0.2207230674402626));
		wts[0] = (((((((((((((6.427095892528692e-011))*x+(-4.2443086082736646e-012))*x+(-3.7971403799019747e-011))*x+(1.8947806286936002e-012))*x+(7.0296361324532565e-012))*x+(1.6792493321797031e-012))*x+(-9.7985323558683974e-011))*x+(5.152695455497753e-009))*x+(-2.7971802002424434e-007))*x+(1.5943926492225272e-005))*x+(-0.0010097820114442616))*x+(0.095929291088424073));
		wts[1] = (((((((((((((5.3357022504011788e-011))*x+(-5.6085506609330569e-012))*x+(-3.152914966146151e-011))*x+(3.4011312285050122e-012))*x+(6.2764608325475511e-012))*x+(-1.5809575870662229e-013))*x+(-3.1152562011508663e-011))*x+(1.6195929042339683e-009))*x+(-8.7916979381782057e-008))*x+(5.0112682156040287e-006))*x+(-0.0003173803202117057))*x+(0.030151130419275512));
		wts[2] = (((((((((((((8.7159908919905616e-013))*x+(-1.1558161835030962e-012))*x+(1.1368683772161603e-013))*x+(7.1291121154596715e-013))*x+(-2.6127248512845347e-013))*x+(-1.0680345496894006e-013))*x+(-2.4591810069788754e-012))*x+(1.3311276155410684e-010))*x+(-7.225356589077303e-009))*x+(4.1184502269902418e-007))*x+(-2.6083518048742746e-005))*x+(0.0024779342143358288));
		wts[3] = (((((((((((((-1.5987211554602254e-014))*x+(-2.5683159302995286e-014))*x+(1.8947806286936004e-014))*x+(1.6477560057145031e-014))*x+(-7.5148220979315283e-015))*x+(-3.2176229273576476e-015))*x+(-2.8207471081120872e-014))*x+(1.5559988555148099e-012))*x+(-8.4448571173789095e-011))*x+(4.8135628161830944e-009))*x+(-3.0485897654963876e-007))*x+(2.8961602763031429e-005));
		break;
	case 48:
		rts[0] = (((((((((((((2.5390060424494245e-012))*x+(8.8107299234252423e-013))*x+(-1.7029340900383734e-012))*x+(-5.2224891078367364e-013))*x+(3.9050244519482169e-013))*x+(3.4028335704761048e-013))*x+(-1.1402628841139517e-011))*x+(5.496374883007249e-010))*x+(-2.6577949886636785e-008))*x+(1.2851687449188208e-006))*x+(-6.2143944583653907e-005))*x+(0.0030049515783417058));
		rts[1] = (((((((((((((3.5925040720030665e-011))*x+(3.7895612573872007e-013))*x+(-2.2500519965736505e-011))*x+(-2.7474319116057206e-013))*x+(4.8198482242393465e-012))*x+(2.663054961734209e-012))*x+(-1.2212575395409428e-010))*x+(5.7398507058437076e-009))*x+(-2.7069714406367329e-007))*x+(1.2766322237489866e-005))*x+(-0.00060207128108019387))*x+(0.028394225112849308));
		rts[2] = (((((((((((((7.1546916539470346e-011))*x+(-7.8822874153653775e-012))*x+(-4.2973624658770853e-011))*x+(4.3579954459952806e-012))*x+(8.280191347391032e-012))*x+(1.0461557546174541e-011))*x+(-5.0132786810763719e-010))*x+(2.2320123823268052e-008))*x+(-9.9487376683156815e-007))*x+(4.4344544848334833e-005))*x+(-0.0019765710163351853))*x+(0.088101772053989919));
		rts[3] = (((((((((((((2.7163575092951453e-010))*x+(-5.4569682106375694e-012))*x+(-1.7128816883390147e-010))*x+(1.5158245029548807e-012))*x+(3.6133466589186959e-011))*x+(5.3482551720662735e-011))*x+(-2.1281643114434701e-009))*x+(8.4808774225564307e-008))*x+(-3.3848378966361285e-006))*x+(0.00013509350202007647))*x+(-0.005391765975662881))*x+(0.21519273613619233));
		wts[0] = (((((((((((((7.2153246340652303e-011))*x+(9.701276818911234e-012))*x+(-4.7634785005357116e-011))*x+(-6.2906716872627531e-012))*x+(1.0989727646422882e-011))*x+(3.0884924247705685e-012))*x+(-8.8102414252944072e-011))*x+(4.6914350922596286e-009))*x+(-2.600470409286349e-007))*x+(1.5134739880184878e-005))*x+(-0.00097871317878246776))*x+(0.094935178342381119));
		wts[1] = (((((((((((((3.3954468866189317e-011))*x+(-5.3811769854898249e-012))*x+(-1.8076207197736949e-011))*x+(2.8232231367534642e-012))*x+(2.8776980798284058e-012))*x+(3.8783790993572202e-014))*x+(-2.7458183874765986e-011))*x+(1.4746162439275659e-009))*x+(-8.1734306582130031e-008))*x+(4.7569361856988433e-006))*x+(-0.00030761520659857626))*x+(0.029838675039712711));
		wts[2] = (((((((((((((2.5579538487363607e-012))*x+(-4.1685173831259209e-013))*x+(-1.51227178927608e-012))*x+(2.7355895326763857e-013))*x+(3.1027032794857711e-013))*x+(-2.6275278249462034e-014))*x+(-2.2756935225132224e-012))*x+(1.2119526678529741e-010))*x+(-6.7172336764079188e-009))*x+(3.9094305152199738e-007))*x+(-2.5280983986761655e-005))*x+(0.0024522554465830136));
		wts[3] = (((((((((((((6.6613381477509392e-015))*x+(-8.4376949871511897e-015))*x+(-8.7892656116158279e-016))*x+(5.6436337085112127e-015))*x+(-8.0259872821860249e-016))*x+(-8.9916500171464508e-016))*x+(-2.6102709403674762e-014))*x+(1.4165677456277428e-012))*x+(-7.8509714438209294e-011))*x+(4.5692647195259254e-009))*x+(-2.9547911785124463e-007))*x+(2.8661474427541634e-005));
		break;
	case 49:
		rts[0] = (((((((((((((3.6000831945178407e-012))*x+(-1.3263464400855202e-013))*x+(-2.2476835207877835e-012))*x+(6.51330841113425e-014))*x+(4.8168876295070118e-013))*x+(1.9414099957278572e-013))*x+(-1.0094897140433544e-011))*x+(4.9617390751599533e-010))*x+(-2.4488499641867983e-008))*x+(1.2086225238807625e-006))*x+(-5.9651197821550307e-005))*x+(0.0029440667630612279));
		rts[1] = (((((((((((((3.3954468866189317e-011))*x+(7.5791225147744016e-014))*x+(-2.1032064978498962e-011))*x+(-1.4210854715202004e-013))*x+(4.4361551469288916e-012))*x+(2.2840988359954886e-012))*x+(-1.0768349175312626e-010))*x+(5.1681886548138323e-009))*x+(-2.4890501115759633e-007))*x+(1.1987490465540049e-005))*x+(-0.00057732836205080156))*x+(0.027804655077534893));
		rts[2] = (((((((((((((8.9736810574928911e-011))*x+(-3.0316490059097605e-012))*x+(-5.411493475548923e-011))*x+(1.2505552149377761e-012))*x+(1.076235397097965e-011))*x+(9.523641134971209e-012))*x+(-4.3915271419336927e-010))*x+(1.9976375812783921e-008))*x+(-9.1038479055338684e-007))*x+(4.148899987942619e-005))*x+(-0.0018907797057064074))*x+(0.086168572539056659));
		rts[3] = (((((((((((((2.9225096416970092e-010))*x+(-3.637978807091713e-012))*x+(-1.8242947893061984e-010))*x+(1.2126596023639045e-012))*x+(3.8312464312184602e-011))*x+(4.4825772723318856e-011))*x+(-1.8350953349492252e-009))*x+(7.4938342346323836e-008))*x+(-3.0658317541158255e-006))*x+(0.0001254273635451312))*x+(-0.0051314045643814626))*x+(0.20993276156046692));
		wts[0] = (((((((((((((1.1338367282102505e-010))*x+(-4.5474735088646412e-012))*x+(-7.0068987649089338e-011))*x+(2.4253192047278085e-012))*x+(1.4845606225814358e-011))*x+(1.0172603500298767e-012))*x+(-7.9042994372002782e-011))*x+(4.2799149409707598e-009))*x+(-2.4211952386517699e-007))*x+(1.4381901509564568e-005))*x+(-0.00094920549961855936))*x+(0.093971344462233417));
		wts[1] = (((((((((((((3.6076623170326151e-011))*x+(-2.2737367544323206e-013))*x+(-2.2491046062593036e-011))*x+(2.8421709430404007e-014))*x+(4.8340590789545477e-012))*x+(4.7695181137896725e-013))*x+(-2.4869069766471811e-011))*x+(1.345188072043868e-009))*x+(-7.6099563701507528e-008))*x+(4.5203147361489353e-006))*x+(-0.00029834077255193754))*x+(0.029535736482639362));
		wts[2] = (((((((((((((2.9179621681881445e-012))*x+(-3.7895612573872008e-014))*x+(-1.7976731214730533e-012))*x+(1.3026616822268501e-014))*x+(3.7895612573872007e-013))*x+(3.6933419285863537e-014))*x+(-2.0410987714806575e-012))*x+(1.1055290941956267e-010))*x+(-6.254150828587564e-009))*x+(3.7149660354520114e-007))*x+(-2.4518775832176021e-005))*x+(0.002427358807385442));
		wts[3] = (((((((((((((3.4342898895071507e-014))*x+(-2.9605947323337506e-016))*x+(-2.1168252336186317e-014))*x+(5.5511151231257827e-017))*x+(4.4686476741162551e-015))*x+(4.5681051534055917e-016))*x+(-2.3859964929743662e-014))*x+(1.2921171655781252e-012))*x+(-7.3097272231097591e-011))*x+(4.3419784907454693e-009))*x+(-2.8657058035573752e-007))*x+(2.8370487455218731e-005));
		break;
	case 50:
		rts[0] = (((((((((((((3.6190310008047768e-012))*x+(-1.1368683772161603e-013))*x+(-2.2559731860383177e-012))*x+(5.0922229396140515e-014))*x+(4.8316906031686803e-013))*x+(1.7127040526550749e-013))*x+(-8.9547952386581642e-012))*x+(4.4882397798318152e-010))*x+(-2.2600403247648171e-008))*x+(1.1380365023284239e-006))*x+(-5.7305482653742481e-005))*x+(0.0028856001855828289));
		rts[1] = (((((((((((((3.759244767328103e-011))*x+(-7.5791225147744013e-013))*x+(-2.3381592958079029e-011))*x+(3.3158661002138002e-013))*x+(4.9809045776783023e-012))*x+(1.8965569855330009e-012))*x+(-9.5286001311478685e-011))*x+(4.6635072840454468e-009))*x+(-2.292623362820656e-007))*x+(1.1270743952048837e-005))*x+(-0.00055407994689689842))*x+(0.027239070363997486));
		rts[2] = (((((((((((((9.822542779147625e-011))*x+(1.2126596023639042e-012))*x+(-5.9192946840388075e-011))*x+(-1.1747639897900322e-012))*x+(1.1804483316761132e-011))*x+(8.6354627152710821e-012))*x+(-3.8569236693319908e-010))*x+(1.7921852742593572e-008))*x+(-8.3467737493903016e-007))*x+(3.8873460406430034e-005))*x+(-0.0018104550902180382))*x+(0.0843183909958891));
		rts[3] = (((((((((((((2.801243681460619e-010))*x+(-4.850638409455617e-012))*x+(-1.7439560906495899e-010))*x+(1.8189894035458563e-012))*x+(3.6701900777795039e-011))*x+(3.773455622043305e-011))*x+(-1.5878649506362308e-009))*x+(6.6414814388811763e-008))*x+(-2.7835368451486113e-006))*x+(0.00011666183044267697))*x+(-0.0048894564767111171))*x+(0.20492379167815197));
		wts[0] = (((((((((((((1.1884064103166261e-010))*x+(-1.5158245029548803e-012))*x+(-7.4426983095084623e-011))*x+(2.2737367544323196e-013))*x+(1.6153004859612942e-011))*x+(1.4222697094131338e-012))*x+(-7.1114669708549614e-011))*x+(3.9114724792455036e-009))*x+(-2.2575020841575369e-007))*x+(1.3680465096731671e-005))*x+(-0.00092115131631765235))*x+(0.093036282948059587));
		wts[1] = (((((((((((((3.759244767328103e-011))*x+(2.2737367544323206e-013))*x+(-2.3419488570652899e-011))*x+(-3.6000831945178408e-013))*x+(5.0401164723249768e-012))*x+(5.3557158707917552e-013))*x+(-2.2340943909663718e-011))*x+(1.2293916625457275e-009))*x+(-7.0954595809968879e-008))*x+(4.29984921875362e-006))*x+(-0.00028952318065775484))*x+(0.029241841246429402));
		wts[2] = (((((((((((((2.9748055870489525e-012))*x+(-7.5791225147744016e-014))*x+(-1.8604377297985289e-012))*x+(2.9605947323337504e-014))*x+(4.0234482412415668e-013))*x+(3.1234274426121069e-014))*x+(-1.8352958042200385e-012))*x+(1.0103717862364192e-010))*x+(-5.8313177067730497e-009))*x+(3.5337791142014041e-007))*x+(-2.3794112698865064e-005))*x+(0.0024032053825848733));
		wts[3] = (((((((((((((3.4194869158454821e-014))*x+(-2.2204460492503131e-016))*x+(-2.1362541365495719e-014))*x+(-4.6259292692714839e-017))*x+(4.6236163046368501e-015))*x+(4.4495657158805102e-016))*x+(-2.1447072994877175e-014))*x+(1.1808959842971032e-012))*x+(-6.8155282377636478e-011))*x+(4.1302108171276636e-009))*x+(-2.7810086163502e-007))*x+(2.8088187025129795e-005));
		break;
	case 51:
		rts[0] = (((((((((((((3.2969182939268649e-012))*x+(1.8947806286936004e-014))*x+(-2.0439946032032217e-012))*x+(-3.0790185216271006e-014))*x+(4.3224683092072758e-013))*x+(1.6616337935223175e-013))*x+(-7.9573292399714985e-012))*x+(4.0679300668718566e-010))*x+(-2.089081841255095e-008))*x+(1.0728416849177637e-006))*x+(-5.5095459093917078e-005))*x+(0.0028294105791114702));
		rts[1] = (((((((((((((3.4257633766780295e-011))*x+(3.0316490059097606e-013))*x+(-2.1505760135672365e-011))*x+(-3.1263880373444408e-013))*x+(4.6516864434427889e-012))*x+(1.7763568394002505e-012))*x+(-8.4472058977288115e-011))*x+(4.2168102343254077e-009))*x+(-2.1151965675740106e-007))*x+(1.0610017488916582e-005))*x+(-0.00053220805499828506))*x+(0.02669603646924364));
		rts[2] = (((((((((((((8.1854523159563541e-011))*x+(-3.0316490059097606e-013))*x+(-4.9908521759789437e-011))*x+(-3.4106051316484804e-013))*x+(1.019391978237157e-011))*x+(7.3576700287958374e-012))*x+(-3.3956467267633644e-010))*x+(1.6115778489478316e-008))*x+(-7.6667864433906574e-007))*x+(3.6473231845463951e-005))*x+(-0.0017351423896646849))*x+(0.082545992233865634));
		rts[3] = (((((((((((((2.1827872842550278e-010))*x+(-6.6696278130014735e-012))*x+(-1.3339255626002947e-010))*x+(3.2590226813529926e-012))*x+(2.7133258602892361e-011))*x+(3.1593098507679919e-011))*x+(-1.37783355095659e-009))*x+(5.9028619917948312e-008))*x+(-2.5329982065169787e-006))*x+(0.00010869441102043242))*x+(-0.0046642254697743012))*x+(0.20014827836207502));
		wts[0] = (((((((((((((1.0732037480920553e-010))*x+(-1.5158245029548803e-012))*x+(-6.6355217616849885e-011))*x+(2.2737367544323196e-013))*x+(1.4059272264906515e-011))*x+(1.2659503075459118e-012))*x+(-6.3742936854775196e-011))*x+(3.5811189569301405e-009))*x+(-2.1077674880465302e-007))*x+(1.3026004836746059e-005))*x+(-0.00089445233193820241))*x+(0.092128590189633569));
		wts[1] = (((((((((((((3.4257633766780295e-011))*x+(-5.3053857603420807e-013))*x+(-2.1316282072803006e-011))*x+(1.8000415972589199e-013))*x+(4.5687897909374442e-012))*x+(3.5260683262094972e-013))*x+(-2.0055882880380217e-011))*x+(1.1255730051710582e-009))*x+(-6.6248348848385596e-008))*x+(4.0941485774393296e-006))*x+(-0.00028113153561432904))*x+(0.028956548168273581));
		wts[2] = (((((((((((((2.7095362990318486e-012))*x+(0))*x+(-1.6828020458585036e-012))*x+(-1.5395092608135503e-014))*x+(3.5823196261238378e-013))*x+(3.6341300339396789e-014))*x+(-1.6462525787019897e-012))*x+(9.2503134781670341e-011))*x+(-5.4445405808211294e-009))*x+(3.3647265287207784e-007))*x+(-2.3104455492697387e-005))*x+(0.0023797589157478365));
		wts[3] = (((((((((((((3.4194869158454821e-014))*x+(-7.4014868308343765e-017))*x+(-2.1547578536266581e-014))*x+(-1.1102230246251564e-016))*x+(4.7184478546569153e-015))*x+(4.039014493232665e-016))*x+(-1.9310616473922071e-014))*x+(1.0811605155707411e-012))*x+(-6.3634704635924608e-011))*x+(3.9326255138724625e-009))*x+(-2.7004028523555407e-007))*x+(2.7814149379255007e-005));
		break;
	case 52:
		rts[0] = (((((((((((((3.3916573253615448e-012))*x+(-1.3263464400855202e-013))*x+(-2.1280754936014997e-012))*x+(6.8685797790143001e-014))*x+(4.612606592975983e-013))*x+(1.2338278547000906e-013))*x+(-7.0961153619819576e-012))*x+(3.6940141686277645e-010))*x+(-1.9339869063566641e-008))*x+(1.0125330346860116e-006))*x+(-5.3010859704781596e-005))*x+(0.0027753674699078188));
		rts[1] = (((((((((((((3.1225984760870532e-011))*x+(-6.0632980118195212e-013))*x+(-1.9307814606387787e-011))*x+(2.8421709430404007e-013))*x+(4.0761468274771078e-012))*x+(1.4210854715202004e-012))*x+(-7.5015919402214123e-011))*x+(3.8205086501837586e-009))*x+(-1.9546064016865797e-007))*x+(9.9999432208175404e-006))*x+(-0.00051160612223504929))*x+(0.026174231046466226));
		rts[2] = (((((((((((((1.0853303441156943e-010))*x+(-7.5791225147744009e-012))*x+(-6.8553163146134453e-011))*x+(4.16851738312592e-012))*x+(1.4987714772966378e-011))*x+(5.3894666507403599e-012))*x+(-3.003575166360406e-010))*x+(1.4523861964950886e-008))*x+(-7.0546557169130309e-007))*x+(3.4266606963674152e-005))*x+(-0.0016644331507603769))*x+(0.080846572181422105));
		rts[3] = (((((((((((((2.2312936683495838e-010))*x+(-1.5764574830730755e-011))*x+(-1.3733369996771216e-010))*x+(8.4128259913995846e-012))*x+(2.8194335754960775e-011))*x+(2.5840070823808976e-011))*x+(-1.2003032641890361e-009))*x+(5.2606589306947171e-008))*x+(-2.3100237765601625e-006))*x+(0.00010143629761307411))*x+(-0.0044542062187862552))*x+(0.19559027198940596));
		wts[0] = (((((((((((((9.943808739384015e-011))*x+(-4.850638409455617e-012))*x+(-6.1694057270263628e-011))*x+(2.6905884927449124e-012))*x+(1.3111881950559713e-011))*x+(4.7843210874513409e-013))*x+(-5.7380470745253355e-011))*x+(3.2843067524860694e-009))*x+(-1.9705635460424512e-007))*x+(1.2414551918841591e-005))*x+(-0.00086901863433728782))*x+(0.091246956605421883));
		wts[1] = (((((((((((((3.213547946264346e-011))*x+(-1.2126596023639042e-012))*x+(-2.0008883439004418e-011))*x+(6.2527760746888816e-013))*x+(4.2798357450616696e-012))*x+(2.0487315547749549e-013))*x+(-1.8053410618297978e-011))*x+(1.0322711574417553e-009))*x+(-6.1935949730029805e-008))*x+(3.9019653931826603e-006))*x+(-0.00027313757751552001))*x+(0.028679445639129851));
		wts[2] = (((((((((((((2.7663797178926566e-012))*x+(-4.7369515717340008e-014))*x+(-1.7076710416101071e-012))*x+(1.6579330501069002e-014))*x+(3.6060043839825074e-013))*x+(2.5202062658991053e-014))*x+(-1.4836927982505206e-012))*x+(8.4835088028552746e-011))*x+(-5.0901312441629463e-009))*x+(3.2067831015137119e-007))*x+(-2.2447481707451255e-005))*x+(0.0023569855792826642));
		wts[3] = (((((((((((((3.2714571792287942e-014))*x+(-1.1102230246251565e-015))*x+(-2.0381844360410163e-014))*x+(6.106226635438361e-016))*x+(4.3761290887308251e-015))*x+(1.8474805019152996e-016))*x+(-1.7367943021262544e-014))*x+(9.9154759200757249e-013))*x+(-5.9492440679856869e-011))*x+(3.7480243738590919e-009))*x+(-2.6236170616595935e-007))*x+(2.7547979147424062e-005));
		break;
	case 53:
		rts[0] = (((((((((((((3.9411437076826888e-012))*x+(9.4739031434680016e-014))*x+(-2.4916365267320844e-012))*x+(-7.4606987254810507e-014))*x+(5.4771002548174386e-013))*x+(1.3855583347321954e-013))*x+(-6.3476261284260244e-012))*x+(3.3605453605053032e-010))*x+(-1.7930214660233368e-008))*x+(9.5666124081487014e-007))*x+(-5.1042370130300809e-005))*x+(0.0027233501658448776));
		rts[1] = (((((((((((((3.4560798667371273e-011))*x+(2.2737367544323206e-013))*x+(-2.1752081617402535e-011))*x+(-2.1789977229976404e-013))*x+(4.7487939506633365e-012))*x+(1.3396691163810222e-012))*x+(-6.6910033069689234e-011))*x+(3.4680523267975141e-009))*x+(-1.8089714179381211e-007))*x+(9.4357588722344954e-006))*x+(-0.00049217770052560486))*x+(0.025672433154066865));
		rts[2] = (((((((((((((1.0550138540565968e-010))*x+(-9.0949470177292824e-013))*x+(-6.6772069355162486e-011))*x+(3.7895612573872077e-014))*x+(1.4627706453514595e-011))*x+(5.4652578758881037e-012))*x+(-2.6590729618192194e-010))*x+(1.31168135612351e-008))*x+(-6.5024160246969953e-007))*x+(3.2234452645094058e-005))*x+(-0.0015979596974057876))*x+(0.079215714402846485));
		rts[3] = (((((((((((((2.4253192047278083e-010))*x+(4.2443086082736646e-012))*x+(-1.5006662579253313e-010))*x+(-3.4106051316484801e-012))*x+(3.152914966146151e-011))*x+(2.4255560523063952e-011))*x+(-1.0493034589368713e-009))*x+(4.7004767189662289e-008))*x+(-2.1110531824852785e-006))*x+(9.4810281654765044e-005))*x+(-0.0042580590995939891))*x+(0.1912352434795829));
		wts[0] = (((((((((((((1.176279814292987e-010))*x+(2.1221543041368323e-012))*x+(-7.4502774320232363e-011))*x+(-1.7810937909719842e-012))*x+(1.6465643663347386e-011))*x+(1.3891110484109959e-012))*x+(-5.2226371375733528e-011))*x+(3.0168568384188652e-009))*x+(-1.8446319170288086e-007))*x+(1.1842539792227455e-005))*x+(-0.00084476783827647109))*x+(0.090390158695561107));
		wts[1] = (((((((((((((3.5318710918848709e-011))*x+(2.2737367544323206e-013))*x+(-2.2311041902867143e-011))*x+(-2.8421709430404007e-013))*x+(4.9098503041022915e-012))*x+(3.7688370942608646e-013))*x+(-1.6389445356423948e-011))*x+(9.4822072416178571e-010))*x+(-5.7977847469729373e-008))*x+(3.7221786766625702e-006))*x+(-0.00026551541220497168))*x+(0.028410149105922385));
		wts[2] = (((((((((((((2.8421709430404007e-012))*x+(-1.8947806286936004e-014))*x+(-1.7976731214730535e-012))*x+(1.1842378929334993e-015))*x+(3.958315157130225e-013))*x+(2.5091040356528535e-014))*x+(-1.3460806543482324e-012))*x+(7.7929015092810986e-011))*x+(-4.7648393882114099e-009))*x+(3.0590275606716166e-007))*x+(-2.1821063263179519e-005))*x+(0.0023348537691595707));
		wts[3] = (((((((((((((3.1234274426121069e-014))*x+(1.0362081563168126e-015))*x+(-1.9475162223632953e-014))*x+(-7.7715611723760938e-016))*x+(4.1980308118638732e-015))*x+(4.6895357967239672e-016))*x+(-1.5682153203337247e-014))*x+(9.1080261099366978e-013))*x+(-5.5690498317033346e-011))*x+(3.5753306344653009e-009))*x+(-2.5504025185065946e-007))*x+(2.7289306948016157e-005));
		break;
	case 54:
		rts[0] = (((((((((((((3.4106051316484809e-012))*x+(0))*x+(-2.1505760135672367e-012))*x+(-1.3026616822268503e-014))*x+(4.6984638402136625e-013))*x+(1.1006010917450718e-013))*x+(-5.6759411985278039e-012))*x+(3.0625926794591862e-010))*x+(-1.6646686801004746e-008))*x+(9.0482567393987629e-007))*x+(-4.9181524869174879e-005))*x+(0.0026732468566134063));
		rts[1] = (((((((((((((3.4560798667371273e-011))*x+(-2.1979455292845764e-012))*x+(-2.1827872842550278e-011))*x+(1.2316074086508402e-012))*x+(4.779584135879607e-012))*x+(8.8255328970869117e-013))*x+(-5.9752351215062533e-011))*x+(3.1539344839496644e-009))*x+(-1.6766511439410733e-007))*x+(8.9132295122360435e-006))*x+(-0.00047383532696220555))*x+(0.025189513718081959));
		rts[2] = (((((((((((((8.3067182761927441e-011))*x+(-3.9411437076826888e-012))*x+(-5.1272763812448829e-011))*x+(2.0463630789890881e-012))*x+(1.0729195309977513e-011))*x+(4.3047047408132731e-012))*x+(-2.3558917779572158e-010))*x+(1.1870315545318514e-008))*x+(-6.00317121725776e-007))*x+(3.0359860662988271e-005))*x+(-0.0015353903413729351))*x+(0.077649351773919212));
		rts[3] = (((((((((((((2.255546860396862e-010))*x+(4.2443086082736646e-012))*x+(-1.4021376652332643e-010))*x+(-3.7895612573872005e-012))*x+(2.950173438875936e-011))*x+(2.1100750776289107e-011))*x+(-9.1954828936498712e-010))*x+(4.2103845447153766e-008))*x+(-1.9330512737540198e-006))*x+(8.8749024011486322e-005))*x+(-0.0040745887733220189))*x+(0.18706992958944835));
		wts[0] = (((((((((((((1.1702165162811676e-010))*x+(-2.1221543041368323e-012))*x+(-7.3631175231033311e-011))*x+(7.9580786405131201e-013))*x+(1.6058265828178264e-011))*x+(7.5199106201277266e-013))*x+(-4.7231700032549874e-011))*x+(2.7756755412629746e-009))*x+(-1.7288615118219811e-007))*x+(1.130675682814904e-005))*x+(-0.00082162432936581638))*x+(0.089557051900862022));
		wts[1] = (((((((((((((3.698611787209908e-011))*x+(-6.0632980118195212e-013))*x+(-2.319211489520967e-011))*x+(1.8947806286936003e-013))*x+(5.0472218996825778e-012))*x+(2.5697962276656955e-013))*x+(-1.4846790463707293e-011))*x+(8.7240792367992981e-010))*x+(-5.4339115734824979e-008))*x+(3.5537789958711707e-006))*x+(-0.00025824127364303345))*x+(0.02814829882708534));
		wts[2] = (((((((((((((2.8990143619012088e-012))*x+(-8.5265128291212022e-014))*x+(-1.822542117224657e-012))*x+(3.6711374680938512e-014))*x+(3.9879211044535623e-013))*x+(1.6320278461989798e-014))*x+(-1.2192145441384619e-012))*x+(7.1698309326665807e-011))*x+(-4.4657945388534848e-009))*x+(2.9206303182972734e-007))*x+(-2.1223246976637373e-005))*x+(0.0023133339204527326));
		wts[3] = (((((((((((((3.6415315207705135e-014))*x+(-6.6613381477509392e-016))*x+(-2.2926105458509483e-014))*x+(2.4980018054066022e-016))*x+(5.0260721510634694e-015))*x+(2.2464669013899652e-016))*x+(-1.4282918019599873e-014))*x+(8.3799283340004372e-013))*x+(-5.2195318303112991e-011))*x+(3.4135746868679247e-009))*x+(-2.4805309387211322e-007))*x+(2.7037787232052474e-005));
		break;
	case 55:
		rts[0] = (((((((((((((3.5621875819439688e-012))*x+(1.8947806286936004e-014))*x+(-2.2311041902867142e-012))*x+(-2.7237471537470505e-014))*x+(4.8376117926333484e-013))*x+(1.0147438445073931e-013))*x+(-5.092981592014211e-012))*x+(2.7957700969120458e-010))*x+(-1.5475981786592739e-008))*x+(8.5666834304659373e-007))*x+(-4.742061610757488e-005))*x+(0.0026249538114577553));
		rts[1] = (((((((((((((3.0771237409984068e-011))*x+(-2.2737367544323206e-013))*x+(-1.895728019007947e-011))*x+(0))*x+(3.9979871265434968e-012))*x+(1.0157800526637098e-012))*x+(-5.3382594641012318e-011))*x+(2.8733035580449e-009))*x+(-1.5562111809151269e-007))*x+(8.4285806717203354e-006))*x+(-0.00045649953773332648))*x+(0.024724427051190781));
		rts[2] = (((((((((((((7.9429203954835728e-011))*x+(-1.8189894035458565e-012))*x+(-4.8392697256834552e-011))*x+(7.9580786405131221e-013))*x+(9.9665461069283375e-012))*x+(3.964828465541359e-012))*x+(-2.094927194680925e-010))*x+(1.076324214939935e-008))*x+(-5.5509337236932699e-007))*x+(2.8627851624144867e-005))*x+(-0.0014764252366293636))*x+(0.076143732616203663));
		rts[3] = (((((((((((((2.1100277081131935e-010))*x+(-1.3945585427184899e-011))*x+(-1.280871704996874e-010))*x+(7.9580786405131205e-012))*x+(2.6091129257110879e-011))*x+(1.5620097807792867e-011))*x+(-8.0792557829075418e-010))*x+(3.7803779366167113e-008))*x+(-1.7734212840088877e-006))*x+(8.319361393691048e-005))*x+(-0.0039027259318563166))*x+(0.18308219799525918));
		wts[0] = (((((((((((((9.943808739384015e-011))*x+(-2.1221543041368323e-012))*x+(-6.1239309919377164e-011))*x+(7.9580786405131201e-013))*x+(1.289398217825995e-011))*x+(6.6198898214982671e-013))*x+(-4.2521245783670254e-011))*x+(2.5576105677771466e-009))*x+(-1.6222678300703561e-007))*x+(1.0804305355369137e-005))*x+(-0.00079951859615088683))*x+(0.088746564172749051));
		wts[1] = (((((((((((((3.3044974164416388e-011))*x+(-6.8212102632969618e-013))*x+(-2.0330996145882331e-011))*x+(2.463214817301681e-013))*x+(4.2845726966334033e-012))*x+(2.1345888020126341e-013))*x+(-1.3385662948432278e-011))*x+(8.0387093278252065e-010))*x+(-5.0988814508564254e-008))*x+(3.39585559490721e-006))*x+(-0.00025129331397799284))*x+(0.027893557851557643));
		wts[2] = (((((((((((((2.4253192047278085e-012))*x+(-7.5791225147744016e-014))*x+(-1.4802973661668753e-012))*x+(3.0790185216271006e-014))*x+(3.0745776295285998e-013))*x+(1.5617137213060531e-014))*x+(-1.0956698511440282e-012))*x+(6.6065310629544654e-011))*x+(-4.1904542555833606e-009))*x+(2.7908428799818669e-007))*x+(-2.0652237308524914e-005))*x+(0.002292398341246418));
		wts[3] = (((((((((((((2.8421709430404007e-014))*x+(-7.4014868308343763e-016))*x+(-1.7282471749998269e-014))*x+(3.05311331771918e-016))*x+(3.5596525727044082e-015))*x+(1.8445892961220048e-016))*x+(-1.2796332280832582e-014))*x+(7.7215895714447902e-013))*x+(-4.8977197731475679e-011))*x+(3.2618817075943862e-009))*x+(-2.4137924632359758e-007))*x+(2.679309634192395e-005));
		break;
	case 56:
		rts[0] = (((((((((((((3.2590226813529926e-012))*x+(-2.8421709430404007e-014))*x+(-2.0558369821325564e-012))*x+(-4.7369515717340002e-015))*x+(4.4941828036826332e-013))*x+(8.7744626379541543e-014))*x+(-4.5758767145779676e-012))*x+(2.5563663685890243e-010))*x+(-1.4406405817133742e-008))*x+(8.1186869308507001e-007))*x+(-4.5752613773933111e-005))*x+(0.0025783746623275778));
		rts[1] = (((((((((((((3.0013325158506632e-011))*x+(2.2737367544323206e-013))*x+(-1.8625693580058094e-011))*x+(-2.7474319116057206e-013))*x+(3.9671969413272263e-012))*x+(9.5716027696350169e-013))*x+(-4.7870226301445954e-011))*x+(2.6221233702846312e-009))*x+(-1.446394112397664e-007))*x+(7.9784409687059157e-006))*x+(-0.00044009800602844238))*x+(0.024276203294224086));
		rts[2] = (((((((((((((9.943808739384015e-011))*x+(-2.1221543041368323e-012))*x+(-6.2755134422332035e-011))*x+(1.0231815394945441e-012))*x+(1.3775055170602475e-011))*x+(3.4023154663979463e-012))*x+(-1.8722860299173283e-010))*x+(9.777807748652851e-009))*x+(-5.1404907852603532e-007))*x+(2.7025123047673866e-005))*x+(-0.0014207927803118264))*x+(0.074695390696326705));
		rts[3] = (((((((((((((2.0372681319713593e-010))*x+(1.2126596023639042e-012))*x+(-1.2429760924230018e-010))*x+(-1.7431981783981123e-012))*x+(2.5446903843355053e-011))*x+(1.5466146881711516e-011))*x+(-7.120597445009479e-010))*x+(3.401968543907212e-008))*x+(-1.6299340024339415e-006))*x+(7.809236359832919e-005))*x+(-0.0037415116820105755))*x+(0.17926092927064322));
		wts[0] = (((((((((((((1.0671404500802358e-010))*x+(-9.0949470177292824e-013))*x+(-6.6847860580310213e-011))*x+(-3.7895612573871976e-014))*x+(1.4514019615792979e-011))*x+(7.8751819880077757e-013))*x+(-3.8852476791362272e-011))*x+(2.3601039641126436e-009))*x+(-1.5239769298365971e-007))*x+(1.0332566002741831e-005))*x+(-0.00077838663869018066))*x+(0.087957690171972941));
		wts[1] = (((((((((((((2.9255412907029189e-011))*x+(-1.5158245029548803e-013))*x+(-1.7915150844297991e-011))*x+(-8.5265128291212022e-014))*x+(3.744560217455728e-012))*x+(2.5994021749890333e-013))*x+(-1.2116715038719878e-011))*x+(7.4179381156132718e-010))*x+(-4.7899479866294246e-008))*x+(3.2475851908913183e-006))*x+(-0.0002446514176584473))*x+(0.027645610195404961));
		wts[2] = (((((((((((((2.8800665556142726e-012))*x+(3.7895612573872008e-014))*x+(-1.7810937909719842e-012))*x+(-3.907985046680551e-014))*x+(3.7836400679225325e-013))*x+(2.8495724298712353e-014))*x+(-1.0023833614998996e-012))*x+(6.096277186766011e-011))*x+(-3.9365606630907078e-009))*x+(2.6689886406383356e-007))*x+(-2.0106381086572658e-005))*x+(0.0022720210627828665));
		wts[3] = (((((((((((((3.0050036533187566e-014))*x+(2.2204460492503131e-016))*x+(-1.8512968935624482e-014))*x+(-3.1456319031046099e-016))*x+(3.9065972678997688e-015))*x+(2.9981804076465813e-016))*x+(-1.1669159562244236e-014))*x+(7.1252397067002771e-013))*x+(-4.6009740186866727e-011))*x+(3.1194608936792186e-009))*x+(-2.3499938725618681e-007))*x+(2.6554930759949525e-005));
		break;
	case 57:
		rts[0] = (((((((((((((2.9748055870489525e-012))*x+(-9.4739031434680016e-014))*x+(-1.836752971939859e-012))*x+(4.6185277824406506e-014))*x+(3.8754185046248791e-013))*x+(6.4540965164875758e-014))*x+(-4.1136769916387079e-012))*x+(2.341161708940831e-010))*x+(-1.3427654945406818e-008))*x+(7.701391163822402e-007))*x+(-4.4171095264540987e-005))*x+(0.002533419762020604));
		rts[1] = (((((((((((((3.0316490059097604e-011))*x+(-1.1368683772161603e-012))*x+(-1.8834119449214388e-011))*x+(6.3475151061235613e-013))*x+(4.0193034086162998e-012))*x+(6.3800816481792322e-013))*x+(-4.3016109193179844e-011))*x+(2.3968636334951534e-009))*x+(-1.3460952251002445e-007))*x+(7.5597927724734004e-006))*x+(-0.00042456478642301752))*x+(0.023843941665190629));
		rts[2] = (((((((((((((8.6705161569019154e-011))*x+(3.0316490059097605e-012))*x+(-5.3015961990846933e-011))*x+(-2.0084674664152163e-012))*x+(1.1003938501138084e-011))*x+(3.5621875819439688e-012))*x+(-1.6698420424177127e-010))*x+(8.8986344219203293e-009))*x+(-4.7672924740245948e-007))*x+(2.5539834383470073e-005))*x+(-0.0013682464794970723))*x+(0.073301118585239231));
		rts[3] = (((((((((((((2.4131926087041694e-010))*x+(-1.2126596023639042e-012))*x+(-1.513550766200448e-010))*x+(1.5158245029548801e-013))*x+(3.2552331200956054e-011))*x+(1.2974510354979429e-011))*x+(-6.3008058030315317e-010))*x+(3.068136559628934e-008))*x+(-1.50066948835977e-006))*x+(7.3399795570213338e-005))*x+(-0.0035900841413040647))*x+(0.17559591334242522));
		wts[0] = (((((((((((((1.0974569401393333e-010))*x+(-9.0949470177292824e-013))*x+(-6.8628954371282206e-011))*x+(3.0316490059097611e-013))*x+(1.4836132322670892e-011))*x+(5.2935433814127464e-013))*x+(-3.5404716195823007e-011))*x+(2.1809714034759505e-009))*x+(-1.4332122212172097e-007))*x+(9.8891666574368858e-006))*x+(-0.00075816944369309165))*x+(0.087189486024701363));
		wts[1] = (((((((((((((3.3196556614711881e-011))*x+(-3.7895612573872007e-013))*x+(-2.062468714332984e-011))*x+(1.4210854715202001e-013))*x+(4.4124703890702222e-012))*x+(1.5898393712632242e-013))*x+(-1.1099232644085077e-011))*x+(6.8549229255883871e-010))*x+(-4.5046689496619496e-008))*x+(3.1082222149552787e-006))*x+(-0.00023829703646631928))*x+(0.02740415919362852));
		wts[2] = (((((((((((((2.7284841053187847e-012))*x+(7.5791225147744016e-014))*x+(-1.6934601868949055e-012))*x+(-5.6843418860808009e-014))*x+(3.6163664655456767e-013))*x+(2.8717768903637378e-014))*x+(-9.1194644428564199e-013))*x+(5.6334871952519919e-011))*x+(-3.7021077557708444e-009))*x+(2.5544548634045633e-007))*x+(-1.9584153947892311e-005))*x+(0.0022521777040076913));
		wts[3] = (((((((((((((3.3158661002138004e-014))*x+(-3.7007434154171881e-016))*x+(-2.0761170560490424e-014))*x+(1.3877787807814454e-016))*x+(4.5033421436357904e-015))*x+(1.5641423341724209e-016))*x+(-1.069500391026601e-014))*x+(6.5844671295195445e-013))*x+(-4.3269497685370639e-011))*x+(2.9855960901191494e-009))*x+(-2.2889570021924909e-007))*x+(2.6323005525209747e-005));
		break;
	case 58:
		rts[0] = (((((((((((((2.4253192047278085e-012))*x+(-4.7369515717340008e-014))*x+(-1.4802973661668753e-012))*x+(1.8947806286936001e-014))*x+(3.0420110874729289e-013))*x+(6.1987452208237898e-014))*x+(-3.7030101207591315e-012))*x+(2.1473181103607666e-010))*x+(-1.2530628906021191e-008))*x+(7.3122106878818403e-007))*x+(-4.2670183525640685e-005))*x+(0.0024900056083208399));
		rts[1] = (((((((((((((2.4101609596982598e-011))*x+(-6.8212102632969618e-013))*x+(-1.4561389131510321e-011))*x+(3.3158661002138012e-013))*x+(2.9558577807620168e-012))*x+(6.2557366694212157e-013))*x+(-3.8612631610609086e-011))*x+(2.1944049910516124e-009))*x+(-1.254341535431025e-007))*x+(7.1699296468226426e-006))*x+(-0.00040983965097636651))*x+(0.023426804416932335));
		rts[2] = (((((((((((((7.9429203954835728e-011))*x+(-2.7284841053187847e-012))*x+(-4.8468488481982299e-011))*x+(1.2505552149377763e-012))*x+(9.9618091553566046e-012))*x+(2.5733489413444959e-012))*x+(-1.4942846959797862e-010))*x+(8.1127133159479091e-009))*x+(-4.4273552885868795e-007))*x+(2.4161422944142065e-005))*x+(-0.0013185622161277816))*x+(0.071957943946476643));
		rts[3] = (((((((((((((1.8553691916167736e-010))*x+(6.6696278130014735e-012))*x+(-1.1421737629765023e-010))*x+(-4.6990559591601287e-012))*x+(2.3646862246096134e-011))*x+(1.2323179513866002e-011))*x+(-5.574163353117001e-010))*x+(2.7728402388997132e-008))*x+(-1.3839691388647009e-006))*x+(6.907578950067031e-005))*x+(-0.0034476668944893492))*x+(0.17207775839381825));
		wts[0] = (((((((((((((1.0368239600211382e-010))*x+(-2.1221543041368323e-012))*x+(-6.4612019438451781e-011))*x+(9.4739031434680011e-013))*x+(1.3907689814611029e-011))*x+(3.7066646048818563e-013))*x+(-3.2233031059073859e-011))*x+(2.0181540882902023e-009))*x+(-1.3492810678935224e-007))*x+(9.4719553564391133e-006))*x+(-0.00073881251772477401))*x+(0.086441064573783408));
		wts[1] = (((((((((((((3.1074402310575046e-011))*x+(-5.3053857603420807e-013))*x+(-1.920360167180964e-011))*x+(2.08425869156296e-013))*x+(4.0643044485477731e-012))*x+(1.4181248767878665e-013))*x+(-1.0090780063383893e-011))*x+(6.3431389770348301e-010))*x+(-4.2408685907898334e-008))*x+(2.9770902928219021e-006))*x+(-0.00023221304280008297))*x+(0.027168926007610308));
		wts[2] = (((((((((((((2.6147972675971687e-012))*x+(-1.1368683772161603e-013))*x+(-1.6176689617471614e-012))*x+(5.921189464667502e-014))*x+(3.4520534579011536e-013))*x+(2.5905203907920298e-015))*x+(-8.3119622296123897e-013))*x+(5.2131183629159729e-011))*x+(-3.4853064236756159e-009))*x+(2.4466856771588469e-007))*x+(-1.9084148281253357e-005))*x+(0.0022328453489060584));
		wts[3] = (((((((((((((2.7681560747320568e-014))*x+(-6.6613381477509392e-016))*x+(-1.7032671569457609e-014))*x+(3.1456319031046104e-016))*x+(3.5874081483200371e-015))*x+(1.0437252913793788e-016))*x+(-9.6661321886496819e-015))*x+(6.0929303413957226e-013))*x+(-4.073557146213622e-011))*x+(2.8596376070774276e-009))*x+(-2.230517333322799e-007))*x+(2.6097052799876377e-005));
		break;
	case 59:
		rts[0] = (((((((((((((3.1453358436313766e-012))*x+(-3.7895612573872008e-014))*x+(-1.9516240475544082e-012))*x+(8.2896652505345011e-015))*x+(4.1551947068304185e-013))*x+(5.8323716226974894e-014))*x+(-3.3578325305446315e-012))*x+(1.9724184322870525e-010))*x+(-1.1707273197755773e-008))*x+(6.9488169977469094e-007))*x+(-4.1244492375359262e-005))*x+(0.0024480543263490258));
		rts[1] = (((((((((((((2.6830093702301383e-011))*x+(-6.8212102632969618e-013))*x+(-1.6550908791638601e-011))*x+(2.8421709430404007e-013))*x+(3.4958702599396929e-012))*x+(5.7465143754598103e-013))*x+(-3.4884428679049506e-011))*x+(2.01212746464563e-009))*x+(-1.1702739836684979e-007))*x+(6.8064195380493813e-006))*x+(-0.00039586750453616149))*x+(0.023024011418120261));
		rts[2] = (((((((((((((8.4886172165473298e-011))*x+(-1.8189894035458565e-012))*x+(-5.2750692702829831e-011))*x+(9.8528592692067219e-013))*x+(1.1254996934439985e-011))*x+(2.2216302871432467e-012))*x+(-1.3426001051660325e-010))*x+(7.4086117981172111e-009))*x+(-4.1171845159097365e-007))*x+(2.2880445867401455e-005))*x+(-0.0012715358532947561))*x+(0.070663108384481893));
		rts[3] = (((((((((((((2.1221543041368324e-010))*x+(-7.8822874153653775e-012))*x+(-1.3225568788281331e-010))*x+(4.0927261579781763e-012))*x+(2.8232231367534645e-011))*x+(9.0167873167956714e-012))*x+(-4.9560799908476828e-010))*x+(2.5110247806973497e-008))*x+(-1.2783954589553244e-006))*x+(6.5084860056121199e-005))*x+(-0.0033135590213821033))*x+(0.16869781050354585));
		wts[0] = (((((((((((((1.0610771520684162e-010))*x+(-2.4253192047278085e-012))*x+(-6.5824679040815681e-011))*x+(1.0610771520684161e-012))*x+(1.4097167877480388e-011))*x+(3.150072795203111e-013))*x+(-2.9480270076949942e-011))*x+(1.8699456797814187e-009))*x+(-1.2715650124506261e-007))*x+(9.0789765286221798e-006))*x+(-0.0007202654711838402))*x+(0.085711591070861542));
		wts[1] = (((((((((((((3.4712381117666759e-011))*x+(-7.5791225147744016e-014))*x+(-2.1856294551980682e-011))*x+(-8.526512829121201e-014))*x+(4.793794990594809e-012))*x+(1.8977412234259342e-013))*x+(-9.314808184039217e-012))*x+(5.8772657111442561e-010))*x+(-3.9966020375092892e-008))*x+(2.8535747768516917e-006))*x+(-0.00022638359891704267))*x+(0.026939648271118759));
		wts[2] = (((((((((((((2.8611187493273365e-012))*x+(-7.5791225147744016e-014))*x+(-1.8012258351518538e-012))*x+(3.5527136788005009e-014))*x+(3.9464727782008896e-013))*x+(6.5873232794425949e-015))*x+(-7.6556816441808441e-013))*x+(4.8302371361922759e-011))*x+(-3.2845590677265291e-009))*x+(2.3451759432185684e-007))*x+(-1.8605062480900633e-005))*x+(0.0022140024352263104));
		wts[3] = (((((((((((((2.7385501274087194e-014))*x+(-4.4408920985006262e-016))*x+(-1.679212324745549e-014))*x+(1.3877787807814457e-016))*x+(3.5249581031848712e-015))*x+(1.3704315460216776e-016))*x+(-8.8263091858424102e-015))*x+(5.645431315713193e-013))*x+(-3.8389279405912681e-011))*x+(2.7409950469310003e-009))*x+(-2.1745227368603416e-007))*x+(2.5876820568636169e-005));
		break;
	case 60:
		rts[0] = (((((((((((((3.0505968121966967e-012))*x+(6.6317322004276009e-014))*x+(-1.8959648665865339e-012))*x+(-5.4474943074941004e-014))*x+(4.0574950806634048e-013))*x+(6.5540165887038412e-014))*x+(-3.040359630723799e-012))*x+(1.8143296587336264e-010))*x+(-1.095044640641446e-008))*x+(6.6091092237310554e-007))*x+(-3.988907811394045e-005))*x+(0.00240749320237384));
		rts[1] = (((((((((((((2.5465851649641991e-011))*x+(-1.5158245029548803e-013))*x+(-1.5726679218156885e-011))*x+(-5.6843418860808015e-014))*x+(3.3324454307148699e-012))*x+(5.8678987594854937e-013))*x+(-3.1507981409125322e-011))*x+(1.8477166463526373e-009))*x+(-1.0931328268496779e-007))*x+(6.4670728663410171e-006))*x+(-0.00038259786863077742))*x+(0.022634835283836918));
		rts[2] = (((((((((((((6.9121597334742546e-011))*x+(-9.0949470177292824e-013))*x+(-4.1003052804929517e-011))*x+(1.5158245029548806e-013))*x+(8.0433437688043341e-012))*x+(2.2109721461068448e-012))*x+(-1.2033959014464318e-010))*x+(6.7765348887860447e-009))*x+(-3.8337068551201148e-007))*x+(2.168844402036333e-005))*x+(-0.0012269811350478787))*x+(0.069414048536223974));
		rts[3] = (((((((((((((2.0008883439004421e-010))*x+(-5.4569682106375694e-012))*x+(-1.2573764252010733e-010))*x+(2.0463630789890885e-012))*x+(2.7265893246900912e-011))*x+(8.3962466608985161e-012))*x+(-4.4126865124856823e-010))*x+(2.2783008960895281e-008))*x+(-1.1826994229339565e-006))*x+(6.139554409193003e-005))*x+(-0.0031871264562043818))*x+(0.16544808257320437));
		wts[0] = (((((((((((((9.7619097990294293e-011))*x+(0))*x+(-6.0140337154734867e-011))*x+(-6.0632980118195212e-013))*x+(1.2723451921677526e-011))*x+(6.8922645368729718e-013))*x+(-2.6855702846736072e-011))*x+(1.7347815036335608e-009))*x+(-1.1995107863464283e-007))*x+(8.7084501696754746e-006))*x+(-0.0007024816467914324))*x+(0.085000279261764539));
		wts[1] = (((((((((((((2.986174270821114e-011))*x+(-5.3053857603420807e-013))*x+(-1.8294106970036712e-011))*x+(1.7053025658242399e-013))*x+(3.8274568699610727e-012))*x+(1.3115434664238515e-013))*x+(-8.4183400990885567e-012))*x+(5.4526009633330353e-010))*x+(-3.7701318338079208e-008))*x+(2.7371162009785788e-006))*x+(-0.00022079404016464501))*x+(0.026716078859925305));
		wts[2] = (((((((((((((2.4632148173016804e-012))*x+(-9.473903143468002e-015))*x+(-1.5063505998114122e-012))*x+(-4.7369515717340018e-015))*x+(3.1426713083722763e-013))*x+(1.3877787807814455e-014))*x+(-6.917429592097808e-013))*x+(4.4811423090725576e-011))*x+(-3.0984372827863589e-009))*x+(2.2494658702887013e-007))*x+(-1.8145691350100516e-005))*x+(0.0021956286533623835));
		wts[3] = (((((((((((((2.8569739167020693e-014))*x+(1.4802973661668753e-016))*x+(-1.7569279364693102e-014))*x+(-2.4980018054066022e-016))*x+(3.7030563800518239e-015))*x+(2.1452746986246513e-016))*x+(-8.0941113186905334e-015))*x+(5.2374120665388268e-013))*x+(-3.621391849454236e-011))*x+(2.6291310153704955e-009))*x+(-2.1208323518058085e-007))*x+(2.5662071456848725e-005));
		break;
	case 61:
		rts[0] = (((((((((((((2.9369099744750806e-012))*x+(4.7369515717340008e-014))*x+(-1.8320160203681248e-012))*x+(-3.7895612573872001e-014))*x+(3.9479530755670562e-013))*x+(5.4659980245711865e-014))*x+(-2.7577431079469266e-012))*x+(1.6712215407851025e-010))*x+(-1.0253800229904908e-008))*x+(6.2911885850821505e-007))*x+(-3.8599396609238541e-005))*x+(0.0023682542632126359));
		rts[1] = (((((((((((((2.986174270821114e-011))*x+(0))*x+(-1.867306309577543e-011))*x+(-1.3263464400855202e-013))*x+(4.0429881664749692e-012))*x+(5.3053857603420807e-013))*x+(-2.8594053051259984e-011))*x+(1.6991750229067291e-009))*x+(-1.0222443344818737e-007))*x+(6.1499147828066488e-006))*x+(-0.00036998442490800934))*x+(0.022258596991797979));
		rts[2] = (((((((((((((9.7012768189112337e-011))*x+(-1.5158245029548803e-012))*x+(-6.184563972055912e-011))*x+(3.7895612573871996e-013))*x+(1.3803476880032879e-011))*x+(1.9338604791604057e-012))*x+(-1.0909732376755224e-010))*x+(6.2081132827055772e-009))*x+(-3.5742117043824345e-007))*x+(2.057782447217419e-005))*x+(-0.001184727839307044))*x+(0.068208379133362779));
		rts[3] = (((((((((((((1.8553691916167736e-010))*x+(-9.0949470177292824e-012))*x+(-1.1421737629765023e-010))*x+(4.4716822837168974e-012))*x+(2.4025818371834852e-011))*x+(6.7477875139350837e-012))*x+(-3.9340412409198205e-010))*x+(2.0709982765746794e-008))*x+(-1.0957924951315867e-006))*x+(5.7979878597338067e-005))*x+(-0.0030677944790844036))*x+(0.16232119131406439));
		wts[0] = (((((((((((((1.1035202381511529e-010))*x+(0))*x+(-6.9500553460481258e-011))*x+(-4.926429634603361e-013))*x+(1.5252984060983483e-011))*x+(5.9448742225261709e-013))*x+(-2.4938569727813352e-011))*x+(1.6114152974940528e-009))*x+(-1.1326219982269829e-007))*x+(8.3587535045318937e-006))*x+(-0.00068541778718285993))*x+(0.084306387823443435));
		wts[1] = (((((((((((((3.1680732111756996e-011))*x+(-9.8528592692067219e-013))*x+(-1.980993147299159e-011))*x+(4.926429634603361e-013))*x+(4.2845726966334033e-012))*x+(3.7007434154171876e-014))*x+(-7.7791476963777005e-012))*x+(5.0649133035799788e-010))*x+(-3.5598967109788195e-008))*x+(2.6272045185772581e-006))*x+(-0.00021543077050340136))*x+(0.026497984771912689));
		wts[2] = (((((((((((((2.6526928801710406e-012))*x+(-4.7369515717340008e-014))*x+(-1.6531960985351662e-012))*x+(1.7763568394002501e-014))*x+(3.5704772471945029e-013))*x+(8.4006875529970183e-015))*x+(-6.3996955882809437e-013))*x+(4.1624879469163524e-011))*x+(-2.9256580190891351e-009))*x+(2.1591362826247837e-007))*x+(-1.7704917514777301e-005))*x+(0.002177704854316868));
		wts[3] = (((((((((((((3.0050036533187566e-014))*x+(-2.2204460492503131e-016))*x+(-1.8772020974703686e-014))*x+(2.7755575615628914e-017))*x+(4.0615658984203638e-015))*x+(1.338628282295436e-016))*x+(-7.4695385871940499e-015))*x+(4.8649976553081598e-013))*x+(-3.4194510240101877e-011))*x+(2.5235555880219666e-009))*x+(-2.0693155816945442e-007))*x+(2.5452581654836969e-005));
		break;
	case 62:
		rts[0] = (((((((((((((2.9179621681881445e-012))*x+(-1.0421293457814802e-013))*x+(-1.8142524519741223e-012))*x+(5.447494307494101e-014))*x+(3.8976229651173827e-013))*x+(3.0605148045500151e-014))*x+(-2.5055513219740529e-012))*x+(1.541457008332377e-010))*x+(-9.6116825303258839e-009))*x+(5.9933360712340642e-007))*x+(-3.7371265160561489e-005))*x+(0.0023302738961038113));
		rts[1] = (((((((((((((2.9255412907029189e-011))*x+(-2.2737367544323206e-013))*x+(-1.8294106970036712e-011))*x+(4.7369515717340021e-014))*x+(3.9671969413272255e-012))*x+(4.3195077144749427e-013))*x+(-2.5929961881369458e-011))*x+(1.5647372656838836e-009))*x+(-9.570101354207844e-008))*x+(5.8531609990348137e-006))*x+(-0.00035798461039365369))*x+(0.021894661928630942));
		rts[2] = (((((((((((((9.398111918320258e-011))*x+(-6.3664629124104977e-012))*x+(-5.9155051227814199e-011))*x+(3.7895612573872013e-012))*x+(1.2998195112838097e-011))*x+(8.8225723023545766e-013))*x+(-9.8415349943555455e-011))*x+(5.6960378636006218e-009))*x+(-3.3363058773994148e-007))*x+(1.9541758767333918e-005))*x+(-0.0011446201495978383))*x+(0.067043877799460708));
		rts[3] = (((((((((((((2.2676734564205009e-010))*x+(-4.850638409455617e-012))*x+(-1.4392753655556589e-010))*x+(2.3495279795800643e-012))*x+(3.1803892852622084e-011))*x+(6.1675109463976688e-012))*x+(-3.5269476228450003e-010))*x+(1.8859169041244666e-008))*x+(-1.0167234791672954e-006))*x+(5.4812954766873347e-005))*x+(-0.0029550411732839239))*x+(0.15931030124684745));
		wts[0] = (((((((((((((9.398111918320258e-011))*x+(-3.3348139065007367e-012))*x+(-5.7639226724859321e-011))*x+(1.6295113406764963e-012))*x+(1.2107648217352104e-011))*x+(7.9343938826544554e-014))*x+(-2.2567281376950632e-011))*x+(1.4986413591581518e-009))*x+(-1.0704537370398448e-007))*x+(8.0284048438970333e-006))*x+(-0.00066903373692596695))*x+(0.083629217115739313));
		wts[1] = (((((((((((((3.0619654959688582e-011))*x+(-1.0610771520684161e-012))*x+(-1.8890962868075196e-011))*x+(5.4001247917767604e-013))*x+(4.000355602329364e-012))*x+(1.4802973661668771e-014))*x+(-7.1121627106170609e-012))*x+(4.7103276834548069e-010))*x+(-3.3644979066660419e-008))*x+(2.5233740264136531e-006))*x+(-0.00021028116884907355))*x+(0.026285146106136741));
		wts[2] = (((((((((((((2.5579538487363607e-012))*x+(-6.6317322004276009e-014))*x+(-1.5927999659955578e-012))*x+(3.3158661002138004e-014))*x+(3.4165263211131486e-013))*x+(2.9976021664879227e-015))*x+(-5.8613761992158209e-013))*x+(3.8711219415195806e-011))*x+(-2.7650718598462572e-009))*x+(2.0738044472567882e-007))*x+(-1.7281703726372906e-005))*x+(0.0021602129657964297));
		wts[3] = (((((((((((((3.0050036533187566e-014))*x+(-1.4062824978585316e-015))*x+(-1.8623991238086998e-014))*x+(7.3089682454489469e-016))*x+(3.9875510301120203e-015))*x+(-2.3418766925686896e-017))*x+(-6.8540008738016134e-015))*x+(4.5245184190680543e-013))*x+(-3.231760964118564e-011))*x+(2.423821434139201e-009))*x+(-2.0198511949787323e-007))*x+(2.524813993722716e-005));
		break;
	case 63:
		rts[0] = (((((((((((((2.9937533933358886e-012))*x+(-1.8947806286936004e-014))*x+(-1.8426741614045263e-012))*x+(7.1054273576010011e-015))*x+(3.8857805861880469e-013))*x+(3.4564943499996538e-014))*x+(-2.2788622840626731e-012))*x+(1.4235809753238016e-010))*x+(-9.0190510297396189e-009))*x+(5.7139928931731337e-007))*x+(-3.6200828542484376e-005))*x+(0.002293492504579117));
		rts[1] = (((((((((((((2.5465851649641991e-011))*x+(-2.2737367544323206e-013))*x+(-1.5802470443304628e-011))*x+(5.6843418860808015e-014))*x+(3.3750779948604759e-012))*x+(3.8221277994428721e-013))*x+(-2.3495723885010495e-011))*x+(1.4428609788434224e-009))*x+(-8.9689756251528266e-008))*x+(5.5751966727887268e-006))*x+(-0.00034655925795730517))*x+(0.021542436317781691));
		rts[2] = (((((((((((((7.8822874153653772e-011))*x+(-1.8189894035458565e-012))*x+(-4.8354801644260682e-011))*x+(6.0632980118195223e-013))*x+(1.0103917702508625e-011))*x+(1.4684549872375401e-012))*x+(-8.8664483162877631e-011))*x+(5.2336786756275915e-009))*x+(-3.1178691963414568e-007))*x+(1.8574094617251898e-005))*x+(-0.0011065152164918153))*x+(0.065918471378369675));
		rts[3] = (((((((((((((1.8917489796876907e-010))*x+(-1.8189894035458565e-012))*x+(-1.1762798142929873e-010))*x+(6.0632980118195223e-013))*x+(2.5143738942764081e-011))*x+(5.6772364587232005e-012))*x+(-3.1541939430705191e-010))*x+(1.7203341270051926e-008))*x+(-9.4465933275778013e-007))*x+(5.1872535759546944e-005))*x+(-0.002848391708766699))*x+(0.15640907482048147));
		wts[0] = (((((((((((((1.0186340659856796e-010))*x+(-3.0316490059097606e-013))*x+(-6.3209881773218513e-011))*x+(-2.2737367544323206e-013))*x+(1.3500311979441904e-011))*x+(4.2987835513486056e-013))*x+(-2.090712788079448e-011))*x+(1.3952973591339437e-009))*x+(-1.0126046001701637e-007))*x+(7.7160493117354543e-006))*x+(-0.00065329217492631614))*x+(0.08296810621562567));
		wts[1] = (((((((((((((3.3196556614711881e-011))*x+(-8.3370347662518418e-013))*x+(-2.0852060818773072e-011))*x+(4.0737783516912407e-013))*x+(4.5593158877939759e-012))*x+(2.8125649957170649e-014))*x+(-6.6174843382782448e-012))*x+(4.3855952203131205e-010))*x+(-3.1826744876136307e-008))*x+(2.4251988777722333e-006))*x+(-0.00020533350496599592))*x+(0.026077355130671834));
		wts[2] = (((((((((((((2.6526928801710406e-012))*x+(-4.7369515717340008e-014))*x+(-1.6484591469634322e-012))*x+(1.53950926081355e-014))*x+(3.5379107051388315e-013))*x+(7.6605388699135801e-015))*x+(-5.4088215388029915e-013))*x+(3.6041850060009033e-011))*x+(-2.6156427371248903e-009))*x+(1.9931203881787837e-007))*x+(-1.6875085949639367e-005))*x+(0.002143135915603812));
		wts[3] = (((((((((((((3.2418512319054571e-014))*x+(-5.1810407815840632e-016))*x+(-2.0511370379949767e-014))*x+(1.9428902930940235e-016))*x+(4.5264717899821489e-015))*x+(7.950815931560365e-017))*x+(-6.3747835135630204e-015))*x+(4.2125110546788652e-013))*x+(-3.057110970577159e-011))*x+(2.3295195089205439e-009))*x+(-1.9723265171322314e-007))*x+(2.5048546767569793e-005));
		break;
	case 64:
		rts[0] = (((((((((((((2.6337450738841044e-012))*x+(-9.4739031434680016e-014))*x+(-1.6378010059270307e-012))*x+(4.7369515717340008e-014))*x+(3.50090327098466e-013))*x+(2.4868995751603503e-014))*x+(-2.0748079180658388e-012))*x+(1.3163622044250664e-010))*x+(-8.4713985811756439e-009))*x+(5.4517433278715454e-007))*x+(-3.5084528713063007e-005))*x+(0.0022578541964201238));
		rts[1] = (((((((((((((2.5465851649641991e-011))*x+(-7.5791225147744016e-014))*x+(-1.5878261668452371e-011))*x+(-7.5791225147744016e-014))*x+(3.4177105590060819e-012))*x+(3.8043642310488691e-013))*x+(-2.138481984085653e-011))*x+(1.3321957241056264e-009))*x+(-8.4143151594477203e-008))*x+(5.3145579293282143e-006))*x+(-0.00033567227630473291))*x+(0.021201363986753534));
		rts[2] = (((((((((((((7.8822874153653772e-011))*x+(6.0632980118195212e-013))*x+(-4.9719043696920075e-011))*x+(-6.8212102632969618e-013))*x+(1.0823934341412192e-011))*x+(1.5395092608135503e-012))*x+(-8.0435806163829199e-011))*x+(4.8156777824696438e-009))*x+(-2.9170202666313938e-007))*x+(1.7669279036532554e-005))*x+(-0.001070281883892426))*x+(0.064830223616845511));
		rts[3] = (((((((((((((1.964508555829525e-010))*x+(-7.2759576141834259e-012))*x+(-1.265713459967325e-010))*x+(3.3348139065007371e-012))*x+(2.8592239686986431e-011))*x+(4.6280016855841195e-012))*x+(-2.8381978249096085e-010))*x+(1.5718953250143383e-008))*x+(-8.7886825280344039e-007))*x+(4.9138728216084157e-005))*x+(-0.002747413334959719))*x+(0.15361162788374594));
		wts[0] = (((((((((((((1.0307606620093186e-010))*x+(-1.2126596023639042e-012))*x+(-6.5256244852207588e-011))*x+(3.0316490059097601e-013))*x+(1.4381384971784426e-011))*x+(3.1263880373444408e-013))*x+(-1.9421797503582638e-011))*x+(1.3005602520858399e-009))*x+(-9.5871359906407605e-008))*x+(7.4204462073105644e-006))*x+(-0.00063815837368508613))*x+(0.082322430205346867));
		wts[1] = (((((((((((((2.9710160257915654e-011))*x+(-7.5791225147744016e-014))*x+(-1.8644641386345029e-011))*x+(-4.7369515717340008e-014))*x+(4.0477251180467038e-012))*x+(1.151671350877829e-013))*x+(-6.0526398707831195e-012))*x+(4.0877401463745855e-010))*x+(-3.0132924479694033e-008))*x+(2.3322891143500815e-006))*x+(-0.00020057686380049386))*x+(0.025874415430256877));
		wts[2] = (((((((((((((2.4442670110147446e-012))*x+(-1.8947806286936004e-014))*x+(-1.5027978861326119e-012))*x+(0))*x+(3.1663560662309465e-013))*x+(9.6959477483930333e-015))*x+(-4.9467374640954631e-013))*x+(3.3594460546737537e-011))*x+(-2.4764381543682101e-009))*x+(1.9167636218248713e-007))*x+(-1.6484167144094792e-005))*x+(0.0021264575615881614));
		wts[3] = (((((((((((((2.7829590483937256e-014))*x+(-2.2204460492503131e-016))*x+(-1.7282471749998269e-014))*x+(2.7755575615628914e-017))*x+(3.6961174861479167e-015))*x+(9.9168358710007456e-017))*x+(-5.7886276790449411e-015))*x+(3.9264753919308426e-013))*x+(-2.8944116499179592e-011))*x+(2.2402752374108849e-009))*x+(-1.9266367038462536e-007))*x+(2.4853613479612922e-005));
		break;
	case 65:
		rts[0] = (((((((((((((2.5390060424494245e-012))*x+(0))*x+(-1.6058265828178264e-012))*x+(-1.1842378929335002e-014))*x+(3.5305092183079978e-013))*x+(3.404683942183813e-014))*x+(-1.8960388814548423e-012))*x+(1.2186785377140316e-010))*x+(-7.9646900458020982e-009))*x+(5.2052996306686805e-007))*x+(-3.4019077741329e-005))*x+(0.0022233065002623884));
		rts[1] = (((((((((((((2.2585785094027717e-011))*x+(-7.5791225147744016e-014))*x+(-1.4428754487501765e-011))*x+(-1.4210854715202004e-013))*x+(3.2140216414215193e-012))*x+(3.8280489889075392e-013))*x+(-1.9484895178815503e-011))*x+(1.2315578556965079e-009))*x+(-7.9018761693638861e-008))*x+(5.069915648145175e-006))*x+(-0.00032529036460701347))*x+(0.020870923436657737));
		rts[2] = (((((((((((((7.9429203954835728e-011))*x+(-3.0316490059097606e-013))*x+(-5.0060104210084923e-011))*x+(-3.0316490059097606e-013))*x+(1.0970779840135947e-011))*x+(1.3701632421240597e-012))*x+(-7.3036539779044077e-011))*x+(4.4371142315924317e-009))*x+(-2.7320870409538084e-007))*x+(1.6822291346293983e-005))*x+(-0.0010357995589328004))*x+(0.063777324047432915));
		rts[3] = (((((((((((((1.7341032313803831e-010))*x+(5.4569682106375694e-012))*x+(-1.0906357298760362e-010))*x+(-4.2443086082736654e-012))*x+(2.3675283955526535e-011))*x+(5.6014452335754559e-012))*x+(-2.5482579009879675e-010))*x+(1.4385504639354469e-008))*x+(-8.1870635809666581e-007))*x+(4.659369910304615e-005))*x+(-0.002651710983886764))*x+(0.15091248985141287));
		wts[0] = (((((((((((((9.7619097990294293e-011))*x+(-1.2126596023639042e-012))*x+(-6.1504579207394259e-011))*x+(4.1685173831259204e-013))*x+(1.3452942463724561e-011))*x+(2.2974215122909903e-013))*x+(-1.7851350027816199e-011))*x+(1.2135732418983025e-009))*x+(-9.0845485217760924e-008))*x+(7.1404578146453774e-006))*x+(-0.00062359998236014881))*x+(0.081691597689157208));
		wts[1] = (((((((((((((3.2287061912938952e-011))*x+(-3.7895612573872007e-013))*x+(-2.0492052499321289e-011))*x+(9.4739031434679991e-014))*x+(4.5332626541494392e-012))*x+(9.1482377229112886e-014))*x+(-5.6466313106776998e-012))*x+(3.814300357044923e-010))*x+(-2.8553258898481964e-008))*x+(2.2442871451614404e-006))*x+(-0.00019600107729623702))*x+(0.025676141125792223));
		wts[2] = (((((((((((((2.5200582361624884e-012))*x+(-1.1368683772161603e-013))*x+(-1.5927999659955578e-012))*x+(5.4474943074941016e-014))*x+(3.50090327098466e-013))*x+(-1.4062824978585337e-015))*x+(-4.6166311514402492e-013))*x+(3.1348021400923181e-011))*x+(-2.3466151837075082e-009))*x+(1.844440266736529e-007))*x+(-1.6108111660314034e-005))*x+(0.0021101626275003196));
		wts[3] = (((((((((((((3.1678363635971131e-014))*x+(-2.9605947323337506e-016))*x+(-2.0150547896946591e-014))*x+(4.6259292692714839e-017))*x+(4.4825254619240695e-015))*x+(9.8300996972019077e-017))*x+(-5.4400205405184342e-015))*x+(3.6638068158049525e-013))*x+(-2.7426769997732487e-011))*x+(2.1557451372864315e-009))*x+(-1.8826840860766382e-007))*x+(2.4663161527591579e-005));
		break;
	case 66:
		rts[0] = (((((((((((((2.3116323670061925e-012))*x+(0))*x+(-1.4400332778071363e-012))*x+(-1.3026616822268503e-014))*x+(3.0923411979226023e-013))*x+(3.2122452845821194e-014))*x+(-1.7285432344730603e-012))*x+(1.1295715751646895e-010))*x+(-7.4953071058786458e-009))*x+(4.9734887391968119e-007))*x+(-3.3001433568984634e-005))*x+(0.0021898001078251494));
		rts[1] = (((((((((((((2.319211489520967e-011))*x+(-9.0949470177292824e-013))*x+(-1.4504545712649511e-011))*x+(4.7369515717340016e-013))*x+(3.124019561558574e-012))*x+(1.9125441970876028e-013))*x+(-1.7759016479601538e-011))*x+(1.1399294101247885e-009))*x+(-7.4278601864171304e-008))*x+(4.8400612089397055e-006))*x+(-0.00031538275754820224))*x+(0.020550625181599121));
		rts[2] = (((((((((((((8.9736810574928911e-011))*x+(-9.0949470177292824e-013))*x+(-5.7752913562580937e-011))*x+(3.0316490059097611e-013))*x+(1.3045564628555438e-011))*x+(1.0551559626037486e-012))*x+(-6.6637658354314525e-011))*x+(4.0937324641276973e-009))*x+(-2.5615797002072799e-007))*x+(1.6028584570388731e-005))*x+(-0.0010029572072746222))*x+(0.062758077937348111));
		rts[3] = (((((((((((((1.8674957876404125e-010))*x+(-1.8189894035458565e-012))*x+(-1.1793114632988969e-010))*x+(3.0316490059097611e-013))*x+(2.5759542647089497e-011))*x+(4.0950946337640435e-012))*x+(-2.299458401466836e-010))*x+(1.3185714742292019e-008))*x+(-7.6360534225402188e-007))*x+(4.4221430988727877e-005))*x+(-0.0025609234001300048))*x+(0.14830656799743952));
		wts[0] = (((((((((((((9.822542779147625e-011))*x+(-1.2126596023639042e-012))*x+(-6.184563972055912e-011))*x+(2.6526928801710404e-013))*x+(1.3514522834157106e-011))*x+(2.8658557008990704e-013))*x+(-1.652367132010113e-011))*x+(1.1335729392195997e-009))*x+(-8.6153341775456e-008))*x+(6.8750394486375805e-006))*x+(-0.00060958683094930921))*x+(0.081075048516231374));
		wts[1] = (((((((((((((3.0619654959688582e-011))*x+(-3.0316490059097606e-013))*x+(-1.9118336543518428e-011))*x+(4.7369515717339996e-014))*x+(4.1211478674085811e-012))*x+(9.5923269327613525e-014))*x+(-5.1728251312018374e-012))*x+(3.5628803611113352e-010))*x+(-2.7078494469849147e-008))*x+(2.1608646191736041e-006))*x+(-0.00019159666284693203))*x+(0.025482356158637195));
		wts[2] = (((((((((((((2.3116323670061925e-012))*x+(-3.7895612573872008e-014))*x+(-1.4542441325223383e-012))*x+(8.2896652505345011e-015))*x+(3.1663560662309465e-013))*x+(7.9195909089927844e-015))*x+(-4.2360559504572848e-013))*x+(2.9280980418100455e-011))*x+(-2.2254133703649331e-009))*x+(1.7758804722109214e-007))*x+(-1.5746140181759793e-005))*x+(0.0020942366441736751));
		wts[3] = (((((((((((((3.0642155479654321e-014))*x+(-2.9605947323337506e-016))*x+(-1.9364139921170438e-014))*x+(4.6259292692714839e-017))*x+(4.2581678923644022e-015))*x+(9.1362103068111849e-017))*x+(-5.0085442159416198e-015))*x+(3.4223202975229111e-013))*x+(-2.6010186804482537e-011))*x+(2.0756138112643309e-009))*x+(-1.8403775788549535e-007))*x+(2.4477021798761282e-005));
		break;
	case 67:
		rts[0] = (((((((((((((2.3116323670061925e-012))*x+(-5.6843418860808015e-014))*x+(-1.4163485199484662e-012))*x+(2.0132044179869506e-014))*x+(2.9679962191645848e-013))*x+(2.2796579438969879e-014))*x+(-1.5802729495343706e-012))*x+(1.0481773319674184e-010))*x+(-7.0599978831825663e-009))*x+(4.7552405325138508e-007))*x+(-3.202877827223557e-005))*x+(0.0021572886391033764));
		rts[1] = (((((((((((((2.5769016550232966e-011))*x+(-4.5474735088646412e-013))*x+(-1.6200374375330281e-011))*x+(1.5158245029548806e-013))*x+(3.5313973967276975e-012))*x+(2.4395300594430103e-013))*x+(-1.627431522877032e-011))*x+(1.0563382020952379e-009))*x+(-6.9888607294917485e-008))*x+(4.6238939408379158e-006))*x+(-0.00030592099714078574))*x+(0.020240009329347292));
		rts[2] = (((((((((((((6.851526753356059e-011))*x+(-2.1221543041368323e-012))*x+(-4.2935729046196983e-011))*x+(1.0231815394945441e-012))*x+(9.2891620321703759e-012))*x+(8.0172905351597968e-013))*x+(-6.028762674266848e-011))*x+(3.7817424747288442e-009))*x+(-2.4041690439384017e-007))*x+(1.5284034108169659e-005))*x+(-0.00097165245815045436))*x+(0.061770897185982131));
		rts[3] = (((((((((((((1.8432425955931345e-010))*x+(6.6696278130014735e-012))*x+(-1.1702165162811676e-010))*x+(-5.0022208597511053e-012))*x+(2.5806912162806836e-011))*x+(4.8245851758110803e-012))*x+(-2.0775559050889569e-010))*x+(1.2103842372823692e-008))*x+(-7.1306286164585231e-007))*x+(4.2007510028354192e-005))*x+(-0.0024747197266598298))*x+(0.14578911538482406));
		wts[0] = (((((((((((((9.1555799978474767e-011))*x+(1.5158245029548803e-012))*x+(-5.7108688148825117e-011))*x+(-1.4779288903810082e-012))*x+(1.2320811038080137e-011))*x+(6.6198898214982661e-013))*x+(-1.5187406887662291e-011))*x+(1.0598980952162642e-009))*x+(-8.1768249458417458e-008))*x+(6.6232305947165147e-006))*x+(-0.00059609075325805301))*x+(0.080472251689816213));
		wts[1] = (((((((((((((2.8649083105847239e-011))*x+(-2.2737367544323206e-013))*x+(-1.7915150844297994e-011))*x+(-9.4739031434679941e-015))*x+(3.8771948614642797e-012))*x+(1.0154839931904763e-013))*x+(-4.77518025121526e-012))*x+(3.3314280963499715e-010))*x+(-2.5700233156900065e-008))*x+(2.0817196411590058e-006))*x+(-0.00018735476765518997))*x+(0.025292893633444485));
		wts[2] = (((((((((((((2.5200582361624884e-012))*x+(-9.473903143468002e-015))*x+(-1.5785891112803558e-012))*x+(-8.2896652505345027e-015))*x+(3.4268884026763164e-013))*x+(1.0473103865630643e-014))*x+(-3.9466115560789683e-013))*x+(2.7378682654344285e-011))*x+(-2.1121425375474528e-009))*x+(1.7108361285483067e-007))*x+(-1.5397525151972745e-005))*x+(0.0020786658955158142));
		wts[3] = (((((((((((((2.7829590483937256e-014))*x+(7.4014868308343765e-017))*x+(-1.7356486618306612e-014))*x+(-1.9428902930940239e-016))*x+(3.7354378849367241e-015))*x+(1.3848875749881509e-016))*x+(-4.5837176646893835e-015))*x+(3.1999609125671347e-013))*x+(-2.4686303430046172e-011))*x+(1.9995912748368234e-009))*x+(-1.7996321468270545e-007))*x+(2.4295033982159074e-005));
		break;
	case 68:
		rts[0] = (((((((((((((2.0842586915629604e-012))*x+(-8.5265128291212022e-014))*x+(-1.3002932064409833e-012))*x+(3.907985046680551e-014))*x+(2.8007226167877281e-013))*x+(1.6172248725373113e-014))*x+(-1.4483506986332864e-012))*x+(9.7371985474659084e-011))*x+(-6.6558367515373576e-009))*x+(4.5495774448816559e-007))*x+(-3.1098498533154557e-005))*x+(0.0021257284281706573));
		rts[1] = (((((((((((((2.1676290392254789e-011))*x+(-1.2884508275116482e-012))*x+(-1.3651894429737389e-011))*x+(7.1054273576010008e-013))*x+(2.9819110144065531e-012))*x+(8.5561187764445381e-014))*x+(-1.4852230556527957e-011))*x+(9.8001654939376205e-010))*x+(-6.5818197130899467e-008))*x+(4.420410032493262e-006))*x+(-0.00029687872814464759))*x+(0.019938643378145316));
		rts[2] = (((((((((((((6.6696278130014733e-011))*x+(0))*x+(-4.2291503632441163e-011))*x+(-2.8421709430404007e-013))*x+(9.3081098384573124e-012))*x+(9.7818049956307119e-013))*x+(-5.4990086558367083e-011))*x+(3.4978238083738233e-009))*x+(-2.2586658308491417e-007))*x+(1.4584892655285692e-005))*x+(-0.00094179080566354995))*x+(0.060814292068189946));
		rts[3] = (((((((((((((1.4794447148839632e-010))*x+(-1.2126596023639042e-012))*x+(-9.276845958083868e-011))*x+(4.5474735088646407e-013))*x+(1.9980461729574017e-011))*x+(3.0648076669118987e-012))*x+(-1.8741393622197694e-010))*x+(1.112699680542543e-008))*x+(-6.6663377754997788e-007))*x+(3.9938941697792441e-005))*x+(-0.0023927964862074332))*x+(0.14335570200722078));
		wts[0] = (((((((((((((9.398111918320258e-011))*x+(-2.7284841053187847e-012))*x+(-5.9079260002666459e-011))*x+(1.3263464400855205e-012))*x+(1.2879771323544747e-011))*x+(-1.7763568394002505e-014))*x+(-1.415593568291721e-011))*x+(9.9208922558583867e-010))*x+(-7.7665989408245054e-008))*x+(6.3841470071499913e-006))*x+(-0.0005830854266052082))*x+(0.079882703444886891));
		wts[1] = (((((((((((((2.9406995357324675e-011))*x+(-6.8212102632969618e-013))*x+(-1.8663589192631964e-011))*x+(3.0316490059097611e-013))*x+(4.1211478674085803e-012))*x+(2.042810365310288e-014))*x+(-4.4616902764952702e-012))*x+(3.1181683161444579e-010))*x+(-2.4410868590396539e-008))*x+(2.0065742887855061e-006))*x+(-0.00018326711835012192))*x+(0.025107595213956259));
		wts[2] = (((((((((((((2.3495279795800643e-012))*x+(-7.5791225147744016e-014))*x+(-1.4826658419527423e-012))*x+(3.6711374680938505e-014))*x+(3.2418512319054571e-013))*x+(-5.9211894646674963e-016))*x+(-3.6485629332598058e-013))*x+(2.5626413028649136e-011))*x+(-2.0061778280289207e-009))*x+(1.6490788288097782e-007))*x+(-1.5061586633965531e-005))*x+(0.0020634373688527409));
		wts[3] = (((((((((((((2.5313084961453569e-014))*x+(-8.8817841970012523e-016))*x+(-1.5811426242369937e-014))*x+(4.2558549277297669e-016))*x+(3.4093098714530851e-015))*x+(-5.7824115865893734e-018))*x+(-4.2250274459587622e-015))*x+(2.9951656028056234e-013))*x+(-2.344780940184742e-011))*x+(1.9274105699591988e-009))*x+(-1.7603683203094675e-007))*x+(2.4117045988236771e-005));
		break;
	case 69:
		rts[0] = (((((((((((((2.4063713984408724e-012))*x+(-3.7895612573872008e-014))*x+(-1.5099033134902127e-012))*x+(1.0658141036401501e-014))*x+(3.2818192607919622e-013))*x+(1.9835984706636129e-014))*x+(-1.3341226271871656e-012))*x+(9.0551219300571972e-011))*x+(-6.2801870761089451e-009))*x+(4.3556052588498517e-007))*x+(-3.0208168067791464e-005))*x+(0.0020950783275126609));
		rts[1] = (((((((((((((2.1979455292845764e-011))*x+(-4.5474735088646412e-013))*x+(-1.3727685654885134e-011))*x+(1.8947806286936006e-013))*x+(2.9475681155114821e-012))*x+(1.8000415972589201e-013))*x+(-1.3600935192907098e-011))*x+(9.1019517848659837e-010))*x+(-6.203985195250375e-008))*x+(4.228692738653117e-006))*x+(-0.0002882315143405123))*x+(0.019646120207458612));
		rts[2] = (((((((((((((7.2759576141834259e-011))*x+(-2.2737367544323206e-012))*x+(-4.6005273664680622e-011))*x+(1.0989727646422884e-012))*x+(1.0122865508795561e-011))*x+(5.9863225487788441e-013))*x+(-5.0298432086037792e-011))*x+(3.2391478388404944e-009))*x+(-2.1240054548510301e-007))*x+(1.3927750543376673e-005))*x+(-0.00091328489468887083))*x+(0.059886863733077715));
		rts[3] = (((((((((((((1.6370904631912708e-010))*x+(-5.4569682106375694e-012))*x+(-1.0315185742607962e-010))*x+(2.5769016550232968e-012))*x+(2.2566837287740782e-011))*x+(2.4087398742267396e-012))*x+(-1.7015455711089089e-010))*x+(1.024313345254768e-008))*x+(-6.2392276498994071e-007))*x+(3.8003990435806851e-005))*x+(-0.0023148749066486266))*x+(0.1410021887732156));
		wts[0] = (((((((((((((9.1555799978474767e-011))*x+(1.2126596023639042e-012))*x+(-5.6805523248234139e-011))*x+(-1.2126596023639042e-012))*x+(1.2131332975210777e-011))*x+(5.4238095496354311e-013))*x+(-1.3049857490917324e-011))*x+(9.2939729986104191e-010))*x+(-7.3824598388153945e-008))*x+(6.1569736693375026e-006))*x+(-0.00057054622646400262))*x+(0.079305925478488165));
		wts[1] = (((((((((((((2.7284841053187847e-011))*x+(-4.5474735088646412e-013))*x+(-1.6977234433094662e-011))*x+(1.7053025658242404e-013))*x+(3.6356103313058457e-012))*x+(4.4408920985006262e-014))*x+(-4.0876931469332094e-012))*x+(2.9212639714633798e-010))*x+(-2.3203498058140443e-008))*x+(1.935172395788979e-006))*x+(-0.0001793259753006734))*x+(0.024926310566790309));
		wts[2] = (((((((((((((2.2926845607192563e-012))*x+(-5.6843418860808015e-014))*x+(-1.4246381851990007e-012))*x+(2.7237471537470508e-014))*x+(3.0346096006420942e-013))*x+(1.4802973661668701e-016))*x+(-3.3575457229299371e-013))*x+(2.4008485014862892e-011))*x+(-1.9069515379393125e-009))*x+(1.5903980457414313e-007))*x+(-1.4737688555516748e-005))*x+(0.0020485387092171277));
		wts[3] = (((((((((((((2.7681560747320568e-014))*x+(-2.2204460492503131e-016))*x+(-1.7328731042690983e-014))*x+(4.6259292692714864e-017))*x+(3.7516286373791745e-015))*x+(6.1004442238517712e-017))*x+(-3.9555670660236979e-015))*x+(2.8060102707829399e-013))*x+(-2.2288068225779563e-011))*x+(1.8588256368128866e-009))*x+(-1.722511756445845e-007))*x+(2.3942913414590999e-005));
		break;
	default:
		double fr = 1/X;
		double fw = sqrt(fr);
		for(unsigned int i = 0 ; i < 4 ; i++){
			double DUM = fr*hermite_roots[4][i]*hermite_roots[4][i];
			rts[i] = DUM/(1.0-DUM);
			wts[i] = fw*hermite_weights[4][i];
		}
		break;
	}
}

void __Root5(double X, double rts[] , double wts[]){
	int n = int(X);
	double x = X - double(n) - 0.5;

	switch(n){
	case 0:
		rts[0] = (((((((((((((-3.8956689725940422e-011))*x+(-4.1685173831259208e-012))*x+(2.8033279401521817e-011))*x+(5.3622291792028891e-012))*x+(-5.2073308628071871e-011))*x+(1.0605167114855854e-009))*x+(-2.2874770781259692e-008))*x+(4.5373774615331541e-007))*x+(-8.3119184002995276e-006))*x+(0.00013861599400079419))*x+(-0.0020135755249476171))*x+(0.021623416790520412));
		rts[1] = (((((((((((((1.2369127944111824e-010))*x+(-1.4551915228366852e-011))*x+(-7.624597249863048e-011))*x+(8.2612435411040987e-012))*x+(2.0935431166435592e-010))*x+(-3.8984069306025049e-009))*x+(1.2128457053487788e-008))*x+(1.5529497610818528e-006))*x+(-5.7661465413638702e-005))*x+(0.0012862667110753825))*x+(-0.020695590699350626))*x+(0.22059502581238014));
		rts[2] = (((((((((((((1.3969838619232178e-009))*x+(1.4551915228366852e-011))*x+(-8.6583895608782768e-010))*x+(-3.1832314562052488e-011))*x+(-2.7118100357862807e-010))*x+(4.8630492225735598e-009))*x+(1.4627272548750622e-007))*x+(-2.4197214069469433e-006))*x+(-8.1704195414644687e-005))*x+(0.0039143099330253657))*x+(-0.077677668832856636))*x+(0.81751855491933156));
		rts[3] = (((((((((((((5.8401686449845629e-009))*x+(5.7237533231576277e-010))*x+(-3.7919865765919285e-009))*x+(-3.7956245553990198e-010))*x+(1.5803986267807582e-009))*x+(2.8016226375863573e-010))*x+(-2.4897584675424394e-007))*x+(-4.9663612221214253e-006))*x+(-1.005708348985242e-005))*x+(0.010113130664629081))*x+(-0.27307510159820225))*x+(2.834463593224176));
		rts[4] = (((((((((((((2.2196521361668904e-008))*x+(-1.2417634328206379e-008))*x+(-1.4891459917028742e-008))*x+(6.9267116487026206e-009))*x+(2.7078688920785981e-009))*x+(-1.0152992520791788e-008))*x+(-9.021012677597657e-009))*x+(3.0516778224409791e-006))*x+(0.00011192641756233948))*x+(0.046127104675484532))*x+(-1.7077825489961249))*x+(17.549776725175182));
		wts[0] = (((((((((((((8.2460852960745485e-011))*x+(-3.152914966146151e-011))*x+(-4.6081064889828362e-011))*x+(1.4491282248248655e-010))*x+(-2.0292532099119849e-009))*x+(3.1710252793952038e-008))*x+(-4.7888312100970621e-007))*x+(6.9778839926944621e-006))*x+(-9.7981546957652072e-005))*x+(0.0013332200224442181))*x+(-0.018276406738487228))*x+(0.28604001705176957));
		wts[1] = (((((((((((((5.3357022504011787e-010))*x+(5.5782341708739594e-011))*x+(-1.0216657149915893e-009))*x+(8.5894195459938292e-009))*x+(-1.0400159074682354e-007))*x+(1.1768886641524052e-006))*x+(-1.2324262120462967e-005))*x+(0.00011812605648664486))*x+(-0.0010182402952803036))*x+(0.0076675389156068965))*x+(-0.047679392911484465))*x+(0.24337507083998033));
		wts[2] = (((((((((((((3.5409660389026004e-010))*x+(7.5912491107980407e-010))*x+(-9.6636843712379524e-009))*x+(1.0459113279163526e-007))*x+(-1.0694765061695457e-006))*x+(9.9322094987049549e-006))*x+(-8.2637825097246306e-005))*x+(0.00060468175279855996))*x+(-0.0037854539001140144))*x+(0.019386889866341888))*x+(-0.074559141042040075))*x+(0.17644634877521811));
		wts[3] = (((((((((((((6.9121597334742546e-011))*x+(3.3645240667586523e-009))*x+(-3.8527787182829343e-008))*x+(3.9125734474509954e-007))*x+(-3.6035988936570598e-006))*x+(2.9546143980023011e-005))*x+(-0.00021193013055024559))*x+(0.0012985601965593099))*x+(-0.0065628935772157511))*x+(0.025858254277567095))*x+(-0.071477369550248776))*x+(0.1063394648615807));
		wts[4] = (((((((((((((-3.0073958138624824e-010))*x+(4.0948483122823136e-009))*x+(-4.401961935703487e-008))*x+(4.2923962458492798e-007))*x+(-3.7415800354286452e-006))*x+(2.8701499404112006e-005))*x+(-0.00018997009650600913))*x+(0.0010559670777211907))*x+(-0.004739101415787002))*x+(0.016129365330997597))*x+(-0.037101421937262104))*x+(0.04342349036359977));
		break;
	case 1:
		rts[0] = (((((((((((((1.3490838076298434e-011))*x+(1.5916157281026244e-012))*x+(-8.9338906642903258e-012))*x+(-2.1789977229976409e-013))*x+(-3.1218879333512937e-011))*x+(7.9118430325782652e-010))*x+(-1.7358347537133056e-008))*x+(3.538292865738294e-007))*x+(-6.7059670095815736e-006))*x+(0.00011618893907750991))*x+(-0.0017595726498534075))*x+(0.019740577221766899));
		rts[1] = (((((((((((((4.5232203168173629e-010))*x+(2.4859521848460037e-011))*x+(-2.9854163585696364e-010))*x+(-2.0615213240186371e-011))*x+(2.4078872229438275e-010))*x+(-2.601867758282121e-009))*x+(-7.3038644761898768e-009))*x+(1.5617973305737107e-006))*x+(-5.1399619213983914e-005))*x+(0.0011226668829031246))*x+(-0.01828979126236998))*x+(0.20112960173366148));
		rts[2] = (((((((((((((1.1156468341747918e-009))*x+(-5.5782341708739594e-011))*x+(-6.6756911110132922e-010))*x+(3.6076623170326151e-011))*x+(-3.4985229528198641e-010))*x+(1.481405812834661e-009))*x+(1.6540311520429893e-007))*x+(-1.6320117464848254e-006))*x+(-8.9839566964252285e-005))*x+(0.0036562048865242569))*x+(-0.070103083135698421))*x+(0.74367122278041753));
		rts[3] = (((((((((((((3.8611081739266711e-009))*x+(-2.9103830456733704e-010))*x+(-2.3974280338734388e-009))*x+(1.940255363782247e-010))*x+(1.4363952990000446e-009))*x+(5.9180062332112957e-009))*x+(-2.3130723529144837e-007))*x+(-6.1812102861343492e-006))*x+(-3.2381338411546772e-005))*x+(0.010050690784495645))*x+(-0.25290011512103605))*x+(2.5714863508777959));
		rts[4] = (((((((((((((-4.2996058861414589e-008))*x+(1.0399768749872843e-008))*x+(3.1597058599193886e-008))*x+(-6.5774656832218162e-009))*x+(-9.7679730970412493e-009))*x+(-1.4663479911784327e-008))*x+(-8.0901410607718078e-008))*x+(2.842890808096854e-006))*x+(0.00012383702268200145))*x+(0.046480954919781915))*x+(-1.615180456850644))*x+(15.888236240428212));
		wts[0] = (((((((((((((-1.2126596023639042e-011))*x+(-4.1230426480372742e-011))*x+(2.0463630789890885e-011))*x+(9.5648526136452944e-011))*x+(-1.2627954977991369e-009))*x+(2.0457567491879061e-008))*x+(-3.2508398994934845e-007))*x+(4.9959711834191012e-006))*x+(-7.4289258683912771e-005))*x+(0.0010767901351683336))*x+(-0.015878217221781187))*x+(0.26900537758861742));
		wts[1] = (((((((((((((6.7060076010723902e-010))*x+(3.637978807091713e-011))*x+(-7.6965989137534052e-010))*x+(4.3239651859039441e-009))*x+(-5.432023423660818e-008))*x+(6.4184810829222739e-007))*x+(-7.0404472548209664e-006))*x+(7.1042085109477654e-005))*x+(-0.00064865311375034141))*x+(0.0052140180636534765))*x+(-0.034981757061917258))*x+(0.20245185912807101));
		wts[2] = (((((((((((((-1.4309383307894069e-010))*x+(3.2256745422879851e-010))*x+(-4.0217855712398878e-009))*x+(4.7082418556480356e-008))*x+(-4.9409189273319488e-007))*x+(4.7248825012502485e-006))*x+(-4.065905524678707e-005))*x+(0.00030932589001005561))*x+(-0.0020267421245864963))*x+(0.010961385708323203))*x+(-0.045083319263395878))*x+(0.1180196462203801));
		wts[3] = (((((((((((((-3.8198777474462986e-011))*x+(1.4439744215148189e-009))*x+(-1.5815771803318057e-008))*x+(1.6286401205434231e-007))*x+(-1.520607658752245e-006))*x+(1.2662847087341333e-005))*x+(-9.2500893505024592e-005))*x+(0.0005791680767095464))*x+(-0.0030040997282752462))*x+(0.012218864027332155))*x+(-0.03516008384418913))*x+(0.055270384658285474));
		wts[4] = (((((((((((((-9.170738242877026e-011))*x+(1.6172331622025618e-009))*x+(-1.7475988064082532e-008))*x+(1.7098307125706924e-007))*x+(-1.497667833897746e-006))*x+(1.1552397772026286e-005))*x+(-7.6952867572181255e-005))*x+(0.0004309418804004187))*x+(-0.0019510796129613771))*x+(0.0067107129894486391))*x+(-0.015636884506019317))*x+(0.018603678244980697));
		break;
	case 2:
		rts[0] = (((((((((((((3.5318710918848709e-011))*x+(5.3053857603420807e-013))*x+(-2.3883709824682832e-011))*x+(1.0326554426380123e-012))*x+(-1.8716879897813975e-011))*x+(5.8966431737417214e-010))*x+(-1.3247251406944825e-008))*x+(2.7781926340934382e-007))*x+(-5.4495123922975357e-006))*x+(9.8031629675794874e-005))*x+(-0.0015459796245751232))*x+(0.018090824773893836));
		rts[1] = (((((((((((((2.4616989927987254e-010))*x+(0))*x+(-1.5650887993009138e-010))*x+(-4.1685173831259208e-012))*x+(1.6838915447200026e-010))*x+(-1.5368755157396661e-009))*x+(-1.9593926185261047e-008))*x+(1.4919029561373993e-006))*x+(-4.5271773194151731e-005))*x+(0.00097773022385660969))*x+(-0.016192460121292229))*x+(0.18391262979635145));
		rts[2] = (((((((((((((9.4102385143438961e-010))*x+(-3.637978807091713e-011))*x+(-5.6206772569566955e-010))*x+(3.7289282772690058e-011))*x+(-2.9437311847383779e-010))*x+(-1.6925791139025628e-009))*x+(1.645306587268654e-007))*x+(-7.991704542575917e-007))*x+(-9.4700383258021021e-005))*x+(0.0033785605254876465))*x+(-0.063065887474595794))*x+(0.6771330393727385));
		rts[3] = (((((((((((((2.2312936683495837e-009))*x+(-6.4028427004814148e-010))*x+(-1.2017456659426291e-009))*x+(3.0680287939806783e-010))*x+(1.1530876993977772e-009))*x+(1.2622876965906471e-008))*x+(-1.7553725702631101e-007))*x+(-7.2150590237166999e-006))*x+(-5.92667279339191e-005))*x+(0.0099142559110993265))*x+(-0.23292171644949422))*x+(2.32859813961554));
		rts[4] = (((((((((((((4.2142346501350403e-008))*x+(-2.2506962219874063e-009))*x+(-2.8487799378732841e-008))*x+(9.4587448984384537e-010))*x+(5.0107094769676532e-009))*x+(-2.7534952096175402e-008))*x+(-2.1068503504769373e-007))*x+(2.1417636920280829e-006))*x+(0.00013401925192250511))*x+(0.046868434933167905))*x+(-1.5218361793015394))*x+(14.319663319243986));
		wts[0] = (((((((((((((4.1230426480372745e-010))*x+(4.9719043696920075e-011))*x+(-2.7921487344428892e-010))*x+(1.2884508275116481e-011))*x+(-7.1876608368863038e-010))*x+(1.347792988326546e-008))*x+(-2.2491582877629901e-007))*x+(3.6383901124518534e-006))*x+(-5.718695887790836e-005))*x+(0.00088092991327291337))*x+(-0.013929031703677404))*x+(0.25413435140899027));
		wts[1] = (((((((((((((4.5232203168173629e-010))*x+(8.4886172165473291e-012))*x+(-4.6406967157963658e-010))*x+(2.2321273718262087e-009))*x+(-2.9095720795642894e-008))*x+(3.5896979492614867e-007))*x+(-4.1257110240759216e-006))*x+(4.3829096981677175e-005))*x+(-0.00042373949328483596))*x+(0.0036325020811138198))*x+(-0.02624721209993313))*x+(0.17210006011083523));
		wts[2] = (((((((((((((9.0343140376110867e-011))*x+(1.5340143969903389e-010))*x+(-1.904898757250824e-009))*x+(2.1584772487888888e-008))*x+(-2.3289704624100219e-007))*x+(2.2981487409386623e-006))*x+(-2.049458162423079e-005))*x+(0.00016245008004330447))*x+(-0.00111649745340367))*x+(0.0063922054982929744))*x+(-0.02818153249888045))*x+(0.082143911457749366));
		wts[3] = (((((((((((((-1.2126596023639042e-012))*x+(5.82986103836447e-010))*x+(-6.5762909192320267e-009))*x+(6.8539842838314741e-008))*x+(-6.4943033114180549e-007))*x+(5.5023005636201106e-006))*x+(-4.1016633184269111e-005))*x+(0.00026305949657675259))*x+(-0.0014044533677108892))*x+(0.0059186243849941814))*x+(-0.01781398038974645))*x+(0.029823022934111404));
		wts[4] = (((((((((((((-1.5385618704992034e-011))*x+(6.321746089573328e-010))*x+(-6.9694531627343776e-009))*x+(6.8396957431104966e-008))*x+(-6.0228701907287052e-007))*x+(4.674617057591016e-006))*x+(-3.1362431380299587e-005))*x+(0.00017711345789332236))*x+(-0.00080992894771859123))*x+(0.0028196566496349663))*x+(-0.0066696379400198571))*x+(0.0080906258734619145));
		break;
	case 3:
		rts[0] = (((((((((((((6.3664629124104977e-012))*x+(2.2737367544323206e-012))*x+(-9.4739031434680052e-013))*x+(-4.0737783516912417e-013))*x+(-1.9178732676058036e-011))*x+(4.4139033169206715e-010))*x+(-1.0175882803054035e-008))*x+(2.1963298935112616e-007))*x+(-4.4597177592577602e-006))*x+(8.3225896595225584e-005))*x+(-0.0013652164849911163))*x+(0.016637692405277536));
		rts[1] = (((((((((((((1.6007106751203537e-010))*x+(0))*x+(-9.3677954282611609e-011))*x+(-3.1832314562052488e-012))*x+(1.1253102153811292e-010))*x+(-7.4037605675888086e-010))*x+(-2.6285351376979332e-008))*x+(1.3752246719178629e-006))*x+(-3.952640719403118e-005))*x+(0.0008506500294604239))*x+(-0.0143669536602271))*x+(0.16865409902976253));
		rts[2] = (((((((((((((1.2999710937341054e-009))*x+(-1.3096723705530167e-010))*x+(-8.5249970046182467e-010))*x+(9.9134922493249178e-011))*x+(-6.0708771343342934e-011))*x+(-4.0644370831917813e-009))*x+(1.4680278089448012e-007))*x+(-1.4851342674167729e-008))*x+(-9.6298733296566283e-005))*x+(0.003091276346861719))*x+(-0.056595254403881433))*x+(0.6173503753302797));
		rts[3] = (((((((((((((3.9193158348401385e-009))*x+(-9.7012768189112337e-011))*x+(-2.6266206987202168e-009))*x+(-3.637978807091713e-012))*x+(1.3736401645777125e-009))*x+(1.8779246602207422e-008))*x+(-8.0474298632301127e-008))*x+(-7.8702680070819042e-006))*x+(-8.9596173305395155e-005))*x+(0.0096916198409141181))*x+(-0.21330066008319276))*x+(2.1055240353740419));
		rts[4] = (((((((((((((-4.2918448646863297e-008))*x+(1.0865430037180581e-009))*x+(2.9176590032875535e-008))*x+(-1.1399000262220698e-009))*x+(-9.6624717116355896e-009))*x+(-4.3405937807013587e-008))*x+(-4.2027369318020646e-007))*x+(6.0538404037894589e-007))*x+(0.00013986449086781741))*x+(0.047280788687492255))*x+(-1.4276899133884957))*x+(12.844831496451961));
		wts[0] = (((((((((((((1.6492170592149097e-010))*x+(-3.637978807091713e-011))*x+(-8.7008326469610126e-011))*x+(5.3508604954307274e-011))*x+(-4.9254822442890145e-010))*x+(9.0283075830181279e-009))*x+(-1.5837332156820594e-007))*x+(2.6912348947879155e-006))*x+(-4.4638274350787079e-005))*x+(0.00072913701333465752))*x+(-0.012325228077037457))*x+(0.24103248886843237));
		wts[1] = (((((((((((((5.347828846424818e-010))*x+(1.6977234433094658e-011))*x+(-4.5315573515836149e-010))*x+(1.1680943619770308e-009))*x+(-1.5918885765131563e-008))*x+(2.0571597284894475e-007))*x+(-2.4773774311981356e-006))*x+(2.7702132471792613e-005))*x+(-0.00028340906944251953))*x+(0.0025878302653722742))*x+(-0.02009677241172669))*x+(0.14910164587311994));
		wts[2] = (((((((((((((8.6098831767837198e-011))*x+(5.305385760342081e-011))*x+(-8.9956605127857381e-010))*x+(1.0102667147293685e-008))*x+(-1.1211928570749781e-007))*x+(1.1435878957873531e-006))*x+(-1.0587927118462423e-005))*x+(8.7603785795901473e-005))*x+(-0.00063276188792473398))*x+(0.0038425930453538509))*x+(-0.018186970461192196))*x+(0.059382127622405835));
		wts[3] = (((((((((((((-2.1221543041368323e-012))*x+(2.4472986600206542e-010))*x+(-2.7612448623888972e-009))*x+(2.9176277394071803e-008))*x+(-2.8103882480460623e-007))*x+(2.4270326000793334e-006))*x+(-1.8502348099487993e-005))*x+(0.00012186000337362685))*x+(-0.00067171583801342116))*x+(0.0029440581870189748))*x+(-0.0093139744826841245))*x+(0.016750171814461253));
		wts[4] = (((((((((((((-1.3869794202037156e-011))*x+(2.5409008230781183e-010))*x+(-2.7809647917820257e-009))*x+(2.7481668496420752e-008))*x+(-2.4346530717404369e-007))*x+(1.9027475226529589e-006))*x+(-1.2869059215843878e-005))*x+(7.3370830159717265e-005))*x+(-0.00033937219378244474))*x+(0.001198088339728106))*x+(-0.0028841476786932892))*x+(0.0035806010232045833));
		break;
	case 4:
		rts[0] = (((((((((((((4.6081064889828362e-011))*x+(-4.6232647340123849e-012))*x+(-3.213547946264346e-011))*x+(2.8705926524708043e-012))*x+(-5.1774880679052639e-012))*x+(3.3182138518365412e-010))*x+(-7.8739579301156937e-009))*x+(1.7478204950016618e-007))*x+(-3.6747204827843514e-006))*x+(7.1069035749330572e-005))*x+(-0.0012113136682102396))*x+(0.01535145197971087));
		rts[1] = (((((((((((((4.5596001048882801e-010))*x+(2.2434202643732228e-011))*x+(-3.0301331814068056e-010))*x+(-1.781093790971984e-011))*x+(1.3626314891250027e-010))*x+(-1.8608877401978435e-010))*x+(-2.8969460312093059e-008))*x+(1.2357351642696321e-006))*x+(-3.4300060819836269e-005))*x+(0.00074005009050160742))*x+(-0.012778867154314835))*x+(0.15509961728295474));
		rts[2] = (((((((((((((8.1005661437908805e-010))*x+(1.3581787546475727e-010))*x+(-4.9628094226742781e-010))*x+(-7.3669070843607174e-011))*x+(7.9580786405131221e-012))*x+(-5.2745576795132365e-009))*x+(1.1820309116690926e-007))*x+(6.5085416167676158e-007))*x+(-9.4978849320452127e-005))*x+(0.0028036936378217359))*x+(-0.050700949157473238))*x+(0.56375022622117932));
		rts[3] = (((((((((((((9.5072512825330092e-010))*x+(-1.5522042910257974e-010))*x+(-4.6202330850064754e-010))*x+(8.4886172165473259e-012))*x+(3.3636145720568789e-010))*x+(2.247422041061024e-008))*x+(4.5015255523139786e-008))*x+(-7.9680747120391953e-006))*x+(-0.0001214824365313542))*x+(0.0093751015987750819))*x+(-0.19421797453312117))*x+(1.9018174677569866));
		rts[4] = (((((((((((((-2.8715779383977251e-009))*x+(-6.28642737865448e-009))*x+(2.9831426218152046e-009))*x+(3.8417056202888489e-009))*x+(-3.9302297712614136e-009))*x+(-6.4195470865039767e-008))*x+(-7.4161348114406189e-007))*x+(-2.2519704240645901e-006))*x+(0.00013710578811417423))*x+(0.047699091703633435))*x+(-1.332708707081788))*x+(11.464562374270256));
		wts[0] = (((((((((((((4.5474735088646412e-010))*x+(-7.0334256937106446e-011))*x+(-2.9172042559366673e-010))*x+(5.5630759258444102e-011))*x+(-2.6310923810039333e-010))*x+(6.1613813310638453e-009))*x+(-1.1338133247088914e-007))*x+(2.0190061326511941e-006))*x+(-3.5292588084416085e-005))*x+(0.00060991152120763248))*x+(-0.01099084491478251))*x+(0.22939430094819349));
		wts[1] = (((((((((((((-2.5102053768932819e-010))*x+(4.8506384094556168e-011))*x+(1.3831898589463284e-010))*x+(6.0867932916153212e-010))*x+(-9.0470469634359071e-009))*x+(1.2068811372500932e-007))*x+(-1.5225578762212422e-006))*x+(1.7913632637996575e-005))*x+(-0.0001937607719779133))*x+(0.0018818218440856775))*x+(-0.015671786474891664))*x+(0.13133471022340812));
		wts[2] = (((((((((((((6.6696278130014733e-011))*x+(1.9705718538413443e-011))*x+(-4.3087311496492475e-010))*x+(4.820359815009093e-009))*x+(-5.5158433080274939e-008))*x+(5.8243200484753288e-007))*x+(-5.607376933151424e-006))*x+(4.8506280692528485e-005))*x+(-0.00036877709779575829))*x+(0.002379104959865925))*x+(-0.012096444120762981))*x+(0.044483044949748592));
		wts[3] = (((((((((((((8.2612435411040971e-012))*x+(9.2957937643708036e-011))*x+(-1.1759150690219637e-009))*x+(1.2584531342933284e-008))*x+(-1.233721024599769e-007))*x+(1.0880964370999873e-006))*x+(-8.5022731137196478e-006))*x+(5.7657729208941223e-005))*x+(-0.00032916632255935654))*x+(0.0015062786174489602))*x+(-0.005033271569250551))*x+(0.0098140699772273597));
		wts[4] = (((((((((((((-6.8022624570100252e-012))*x+(1.0088759457479075e-010))*x+(-1.1154798566318884e-009))*x+(1.109856739844872e-008))*x+(-9.8981378056824568e-008))*x+(7.7958970053545085e-007))*x+(-5.3209016919788148e-006))*x+(3.0666341703312429e-005))*x+(-0.00014371280171952391))*x+(0.00051561445421005993))*x+(-0.0012670401472273927))*x+(0.0016173554819381548));
		break;
	case 5:
		rts[0] = (((((((((((((4.9719043696920075e-011))*x+(1.7810937909719844e-012))*x+(-3.3442878096442044e-011))*x+(-7.5791225147744013e-013))*x+(-1.5430619744923514e-012))*x+(2.5330863332821235e-010))*x+(-6.1311778617086539e-009))*x+(1.3997084800469276e-007))*x+(-3.0481148399300975e-006))*x+(6.1019554369050197e-005))*x+(-0.0010795380910892764))*x+(0.014207699855131335));
		rts[1] = (((((((((((((2.304053244491418e-010))*x+(3.8198777474462986e-011))*x+(-1.4097167877480388e-010))*x+(-2.9028039231585957e-011))*x+(7.0324783033962974e-011))*x+(1.7940019840049595e-010))*x+(-2.8935370247988128e-008))*x+(1.0900939531784577e-006))*x+(-2.964847494050608e-005))*x+(0.00064427310764269175))*x+(-0.011396869740764202))*x+(0.14302770680260882));
		rts[2] = (((((((((((((6.3058299322923018e-010))*x+(-1.6977234433094658e-011))*x+(-3.7531814693162835e-010))*x+(1.9402553637822465e-011))*x+(1.1937117960769683e-010))*x+(-5.4604072374786475e-009))*x+(8.5436234087410412e-008))*x+(1.160389757615121e-006))*x+(-9.1301575257052292e-005))*x+(0.0025237633879830654))*x+(-0.045375336254016803))*x+(0.51575875554525918));
		rts[3] = (((((((((((((1.2029583255449929e-009))*x+(-2.5223319729169208e-010))*x+(-8.0763129517436017e-010))*x+(1.0853303441156942e-010))*x+(-1.079267046103875e-010))*x+(2.2390016359471094e-008))*x+(1.818221922652204e-007))*x+(-7.4008236528773823e-006))*x+(-0.00015244898288753936))*x+(0.0089636372017833903))*x+(-0.17586372955478952))*x+(1.7168452120217041));
		rts[4] = (((((((((((((1.1098260680834452e-008))*x+(-3.4924596548080444e-010))*x+(-7.6300542180736849e-009))*x+(1.5522042910257977e-010))*x+(1.0913936421275118e-010))*x+(-8.0292466009268524e-008))*x+(-1.1770962184224723e-006))*x+(-7.0058343339951534e-006))*x+(0.00011931651092448684))*x+(0.048088470306395813))*x+(-1.2369123231137433))*x+(10.179686804691228));
		wts[0] = (((((((((((((2.9225096416970092e-010))*x+(-2.4253192047278085e-012))*x+(-1.6696806900048006e-010))*x+(1.2732925824820994e-011))*x+(-1.8748854320923178e-010))*x+(4.2891012223359813e-009))*x+(-8.2393935526188969e-008))*x+(1.5342680702209084e-006))*x+(-2.823754804206121e-005))*x+(0.00051510011923154109))*x+(-0.0098693556493823532))*x+(0.21897998645304512));
		wts[1] = (((((((((((((8.7311491370201111e-011))*x+(-9.0949470177292824e-012))*x+(-7.624597249863048e-011))*x+(3.5841670372368145e-010))*x+(-5.1615624367210931e-009))*x+(7.2399162813023083e-008))*x+(-9.5661929281713266e-007))*x+(1.1835724600099221e-005))*x+(-0.00013520087577134632))*x+(0.0013944333285032251))*x+(-0.012424717557623529))*x+(0.11736748816962821));
		wts[2] = (((((((((((((5.1538033100465931e-011))*x+(8.6401996668428183e-012))*x+(-2.2017350905419636e-010))*x+(2.347633198951371e-009))*x+(-2.7736649125624051e-008))*x+(3.0366082093280511e-007))*x+(-3.0442185074974759e-006))*x+(2.756853785309173e-005))*x+(-0.00022086780581156984))*x+(0.0015154375851449433))*x+(-0.0082754335380199745))*x+(0.034440359314294199));
		wts[3] = (((((((((((((7.503331289626658e-012))*x+(4.5891586826959e-011))*x+(-5.0809016253576067e-010))*x+(5.4959770068307989e-009))*x+(-5.5002294866805336e-008))*x+(4.9643191113446505e-007))*x+(-3.9852350996090928e-006))*x+(2.7901880723583496e-005))*x+(-0.00016549704120156933))*x+(0.00079374822409621591))*x+(-0.0028143377277469904))*x+(0.0060080423881578122));
		wts[4] = (((((((((((((-2.7569058147491887e-012))*x+(4.0524620696184378e-011))*x+(-4.5021941730283288e-010))*x+(4.5070211266799252e-009))*x+(-4.049707214015541e-008))*x+(3.2175709876088488e-007))*x+(-2.218817190117091e-006))*x+(1.2946543943362364e-005))*x+(-6.1590242469168399e-005))*x+(0.00022515507431838805))*x+(-0.00056682443623674395))*x+(0.00074825311250386001));
		break;
	case 6:
		rts[0] = (((((((((((((-2.8118544529813029e-011))*x+(1.0231815394945443e-012))*x+(1.8005152924160939e-011))*x+(-7.1054273576010019e-013))*x+(-1.0962490174885412e-011))*x+(1.9691700122355843e-010))*x+(-4.7905629278292379e-009))*x+(1.128081877355136e-007))*x+(-2.5447857864811792e-006))*x+(5.2657337923105521e-005))*x+(-0.0009661126405820957))*x+(0.013186267287955102));
		rts[1] = (((((((((((((2.6678511252005894e-011))*x+(-1.3339255626002947e-011))*x+(-1.4855080128957827e-011))*x+(5.0022208597511053e-012))*x+(2.8393287720973603e-011))*x+(4.0392933442490175e-010))*x+(-2.7146979183119886e-008))*x+(9.4931586917349853e-007))*x+(-2.5572648855498589e-005))*x+(0.00056158231620680643))*x+(-0.010193051929765254))*x+(0.13224652306778686));
		rts[2] = (((((((((((((7.7610214551289869e-010))*x+(-5.3357022504011788e-011))*x+(-5.2386894822120667e-010))*x+(3.8047195024167494e-011))*x+(2.6420821086503565e-010))*x+(-4.8055047348801346e-009))*x+(5.4321091624842666e-008))*x+(1.5081629989310839e-006))*x+(-8.5912515694452907e-005))*x+(0.0022575948132971626))*x+(-0.040596677782328464))*x+(0.47281712153263333));
		rts[3] = (((((((((((((3.3760443329811096e-009))*x+(-2.5708383570114768e-010))*x+(-2.1561087730030217e-009))*x+(9.1555799978474741e-011))*x+(-3.5288394428789616e-010))*x+(1.8306025140191196e-008))*x+(3.0602227714856173e-007))*x+(-6.1707564379768582e-006))*x+(-0.00017979983917311887))*x+(0.0084640318347345058))*x+(-0.15842236429397463))*x+(1.5497854737589845));
		rts[4] = (((((((((((((1.3038516044616699e-008))*x+(-3.2596290111541748e-009))*x+(-6.7423873891433086e-009))*x+(2.5417345265547433e-009))*x+(1.9966440352921682e-009))*x+(-8.4641821255596967e-008))*x+(-1.6804424755415917e-006))*x+(-1.4139140906384757e-005))*x+(7.786898944080653e-005))*x+(0.048391379886602692))*x+(-1.1404118335530371))*x+(8.9909740037455386));
		wts[0] = (((((((((((((1.1156468341747919e-010))*x+(1.8796223836640515e-011))*x+(-5.6691836410512523e-011))*x+(-4.6990559591601271e-012))*x+(-1.3653789210366083e-010))*x+(3.0512623538925254e-009))*x+(-6.0633504735581781e-008))*x+(1.1797940796161772e-006))*x+(-2.2845603381134911e-005))*x+(0.00043882924815888402))*x+(-0.0089181186399500244))*x+(0.20959894933385359));
		wts[1] = (((((((((((((3.637978807091713e-010))*x+(1.6977234433094658e-011))*x+(-2.5162686749051016e-010))*x+(1.8985701899509877e-010))*x+(-2.9838626384541081e-009))*x+(4.4363891523365354e-008))*x+(-6.1375408459222547e-007))*x+(7.9795504680883287e-006))*x+(-9.6139307904049176e-005))*x+(0.0010512653082111836))*x+(-0.0099984929121255898))*x+(0.10621294972820997));
		wts[2] = (((((((((((((8.7008326469610126e-011))*x+(-1.2732925824820995e-011))*x+(-1.438327975241312e-010))*x+(1.1776251085393596e-009))*x+(-1.4256696564037458e-008))*x+(1.6206188035994273e-007))*x+(-1.6938146358835835e-006))*x+(1.6074737116215467e-005))*x+(-0.00013581639526095982))*x+(0.00099183506119516563))*x+(-0.0058104637474753742))*x+(0.027484297964768315));
		wts[3] = (((((((((((((-1.4400332778071363e-011))*x+(2.2585785094027717e-011))*x+(-2.088095622336065e-010))*x+(2.4359441871032077e-009))*x+(-2.4935703576052976e-008))*x+(2.3076476759105918e-007))*x+(-1.9077265940858901e-006))*x+(1.3826623510515557e-005))*x+(-8.5468019643858862e-005))*x+(0.00043124506065139035))*x+(-0.0016290176308247075))*x+(0.0038463189527563517));
		wts[4] = (((((((((((((-2.8895404587577406e-013))*x+(1.6304587309908431e-011))*x+(-1.8308643490172472e-010))*x+(1.8415352206109976e-009))*x+(-1.6686175663416236e-008))*x+(1.3388656309546809e-007))*x+(-9.341230345870366e-007))*x+(5.5277696834448338e-006))*x+(-2.6755516576902833e-005))*x+(9.9963015931957568e-005))*x+(-0.00025891348316880471))*x+(0.00035600658945644299));
		break;
	case 7:
		rts[0] = (((((((((((((8.033869865660865e-012))*x+(6.3664629124104977e-012))*x+(-3.8179829668176045e-012))*x+(-4.0879892064064433e-012))*x+(-4.4326024332500911e-012))*x+(1.5769785477459664e-010))*x+(-3.7377630990320654e-009))*x+(9.1585721229137107e-008))*x+(-2.1377507470448265e-006))*x+(4.5654735648145699e-005))*x+(-0.00086800390932367344))*x+(0.012270375406916662));
		rts[1] = (((((((((((((2.6193447411060333e-010))*x+(1.7583564234276612e-011))*x+(-1.7280399333685637e-010))*x+(-1.2505552149377762e-011))*x+(5.5649707064731047e-011))*x+(5.489582122208958e-010))*x+(-2.425797399988975e-008))*x+(8.2046049539504407e-007))*x+(-2.2037930256901817e-005))*x+(0.00049029537298571802))*x+(-0.0091429411157780693))*x+(0.12259040340369058));
		rts[2] = (((((((((((((5.6752469390630722e-010))*x+(-1.6977234433094658e-011))*x+(-3.446984919719398e-010))*x+(5.9117155615240319e-012))*x+(2.4491934406493477e-010))*x+(-3.6859830743196653e-009))*x+(2.8743183833057625e-008))*x+(1.713072903678873e-006))*x+(-7.9427359810220935e-005))*x+(0.0020093806496848479))*x+(-0.036332949167827047))*x+(0.43439368388844313));
		rts[3] = (((((((((((((2.7939677238464355e-009))*x+(-9.2162129779656724e-011))*x+(-1.8165640843411286e-009))*x+(7.2759576141834259e-012))*x+(-7.5791225147744013e-010))*x+(1.1064742011512863e-008))*x+(3.9544962267730927e-007))*x+(-4.3985962771368268e-006))*x+(-0.00020108799679263709))*x+(0.0078909242553991295))*x+(-0.14205674916272143))*x+(1.3996414942068423));
		rts[4] = (((((((((((((-4.5013924439748125e-009))*x+(8.149072527885437e-010))*x+(4.0939388175805407e-009))*x+(1.2611659864584601e-010))*x+(3.9805551447595154e-009))*x+(-6.2430899561149986e-008))*x+(-2.1357488246091334e-006))*x+(-2.3733950039665313e-005))*x+(2.8870968951840341e-006))*x+(0.048522119527765639))*x+(-1.0434609198523022))*x+(7.8990155167670757));
		wts[0] = (((((((((((((2.5223319729169208e-010))*x+(5.5176011907557644e-011))*x+(-1.4976346089194217e-010))*x+(-3.1453358436313764e-011))*x+(-6.6127843941406666e-011))*x+(2.2338255689646758e-009))*x+(-4.4981443162820746e-008))*x+(9.1781201394525159e-007))*x+(-1.8676423796678183e-005))*x+(0.00037680777909453639))*x+(-0.0081045636013900198))*x+(0.20109793641149665));
		wts[1] = (((((((((((((-1.8189894035458565e-011))*x+(-4.5474735088646412e-011))*x+(5.532759435785314e-012))*x+(1.42411712052611e-010))*x+(-1.8287285759773415e-009))*x+(2.7714882833151929e-008))*x+(-4.0172663210806075e-007))*x+(5.4822729561957812e-006))*x+(-6.956762455169925e-005))*x+(0.00080519392180386496))*x+(-0.0081552843878580934))*x+(0.097176990126811386));
		wts[2] = (((((((((((((2.2737367544323206e-011))*x+(6.8970014884447055e-012))*x+(-5.7355009630555287e-011))*x+(5.9006310948461749e-010))*x+(-7.5010220257354376e-009))*x+(8.8516570961871821e-008))*x+(-9.6556218405948369e-007))*x+(9.6088460968350251e-006))*x+(-8.5655178759372328e-005))*x+(0.00066605719434614677))*x+(-0.0041775318390213229))*x+(0.022544382685242684));
		wts[3] = (((((((((((((-8.2991391536779702e-012))*x+(7.778074480787229e-012))*x+(-9.0738675832350652e-011))*x+(1.0991515845641213e-009))*x+(-1.150580105265438e-008))*x+(1.0941511456123247e-007))*x+(-9.3368693438825956e-007))*x+(7.0233847868500501e-006))*x+(-4.5375974888596626e-005))*x+(0.0002417225113881395))*x+(-0.00097593594344694084))*x+(0.0025752053278964974));
		wts[4] = (((((((((((((-1.9421501444109404e-013))*x+(6.5902838741749292e-012))*x+(-7.4643994688964696e-011))*x+(7.5759902055475925e-010))*x+(-6.929529986858066e-009))*x+(5.6222275719256899e-008))*x+(-3.9750011568764898e-007))*x+(2.3903912622057675e-006))*x+(-1.1802395000078137e-005))*x+(4.5225403104612185e-005))*x+(-0.00012111378215039366))*x+(0.00017501312673122394));
		break;
	case 8:
		rts[0] = (((((((((((((1.2884508275116483e-011))*x+(-1.0876040808701266e-011))*x+(-8.7823082139948367e-012))*x+(6.4990975564190486e-012))*x+(-1.6354325301411637e-012))*x+(1.2597611842579681e-010))*x+(-2.8899663033025531e-009))*x+(7.5090151781716699e-008))*x+(-1.8058111444900953e-006))*x+(3.9755873982990839e-005))*x+(-0.00078275912832518951))*x+(0.011445976482537881));
		rts[1] = (((((((((((((1.6674069532503683e-010))*x+(6.9727927135924493e-012))*x+(-1.0902567737502976e-010))*x+(-6.5180453627059852e-012))*x+(2.9350151938463867e-011))*x+(6.1508960887598129e-010))*x+(-2.0739383395825449e-008))*x+(7.0781476191328341e-007))*x+(-1.89872525334552e-005))*x+(0.00042887027801912875))*x+(-0.0082253002158175093))*x+(0.11391651649725283));
		rts[2] = (((((((((((((5.1174235219756759e-010))*x+(7.2759576141834259e-012))*x+(-3.2756967508854962e-010))*x+(-1.3794002976889411e-011))*x+(2.3158008843893185e-010))*x+(-2.4974061337464564e-009))*x+(1.0230248056094144e-008))*x+(1.8075620881556158e-006))*x+(-7.2355251336012991e-005))*x+(0.0017816128390237458))*x+(-0.032545494816317522))*x+(0.39999242631940635));
		rts[3] = (((((((((((((1.6686196128527322e-009))*x+(-2.7648638933897018e-010))*x+(-1.0065074699620404e-009))*x+(1.4794447148839632e-010))*x+(-1.0700205166358501e-009))*x+(2.2660628928861111e-009))*x+(4.3583645492617507e-007))*x+(-2.2982058543637622e-006))*x+(-0.00021454895922505082))*x+(0.0072653640175566192))*x+(-0.12689372366995921))*x+(1.2652705880532389));
		rts[4] = (((((((((((((1.6919026772181191e-008))*x+(1.0089327891667683e-009))*x+(-1.1728843674063681e-008))*x+(-1.5764574830730749e-010))*x+(1.31258275359869e-008))*x+(-7.6346016915825512e-009))*x+(-2.3641986217626254e-006))*x+(-3.5120536343432221e-005))*x+(-0.00011443629979387045))*x+(0.048366209712252584))*x+(-0.94651396769315688))*x+(6.9040536771056322));
		wts[0] = (((((((((((((1.7826096154749393e-010))*x+(-3.698611787209908e-011))*x+(-1.0951832033849011e-010))*x+(2.4859521848460037e-011))*x+(-4.2746250983327627e-011))*x+(1.6672387914695719e-009))*x+(-3.3394969456423951e-008))*x+(7.2325996539982884e-007))*x+(-1.5413554229163719e-005))*x+(0.00032586708996983527))*x+(-0.0074035182410873293))*x+(0.19335237913310116));
		wts[1] = (((((((((((((5.9420320515831307e-011))*x+(2.0008883439004421e-011))*x+(-3.7365073997837797e-011))*x+(5.6274984672199935e-011))*x+(-1.1120656987865609e-009))*x+(1.7638922618819681e-008))*x+(-2.6811809809383175e-007))*x+(3.8327619904521271e-006))*x+(-5.1159417540025391e-005))*x+(0.00062574785786774034))*x+(-0.0067335245605626278))*x+(0.089762438584803705));
		wts[2] = (((((((((((((-9.3981119183202574e-012))*x+(-1.3642420526593924e-012))*x+(-1.3206620981994396e-011))*x+(3.0919030299022171e-010))*x+(-4.0373440886772487e-009))*x+(4.945129639111201e-008))*x+(-5.6371017002436008e-007))*x+(5.8826685850702871e-006))*x+(-5.5337897311033557e-005))*x+(0.00045827441329752278))*x+(-0.0030682924686390935))*x+(0.018955977709724493));
		wts[3] = (((((((((((((-5.3811769854898249e-012))*x+(3.808509063674137e-012))*x+(-3.9551177148193041e-011))*x+(5.0365045467515301e-010))*x+(-5.4094821955175113e-009))*x+(5.2968379164279135e-008))*x+(-4.6765169034457266e-007))*x+(3.6597866823797247e-006))*x+(-2.4779350359254576e-005))*x+(0.00013982528873183843))*x+(-0.00060460978331285282))*x+(0.0018018045394726928));
		wts[4] = (((((((((((((1.1842378929335002e-015))*x+(2.6497322854387067e-012))*x+(-3.0730159158072937e-011))*x+(3.1405870496807137e-010))*x+(-2.9029837885404439e-009))*x+(2.3851046482744238e-008))*x+(-1.7119222278389604e-007))*x+(1.0485728813370077e-006))*x+(-5.2970349056694738e-006))*x+(2.0902180914651337e-005))*x+(-5.820181838914647e-005))*x+(8.936522579841963e-005));
		break;
	case 9:
		rts[0] = (((((((((((((1.2505552149377763e-011))*x+(-1.0231815394945443e-011))*x+(-7.2712206626116922e-012))*x+(6.6364691519993357e-012))*x+(-1.9172811486593365e-012))*x+(1.0144981151446093e-010))*x+(-2.2002602887797687e-009))*x+(6.2426031973335697e-008))*x+(-1.5319282526000027e-006))*x+(3.4761916906592368e-005))*x+(-0.00070837816399821677))*x+(0.010701239740993894));
		rts[1] = (((((((((((((1.2308494963993627e-010))*x+(-3.5167128468553223e-011))*x+(-7.7193362812977271e-011))*x+(2.2017350905419637e-011))*x+(9.4170597246071923e-012))*x+(5.9938543017779001e-010))*x+(-1.7041477414399726e-008))*x+(6.1339384653062256e-007))*x+(-1.635101123205011e-005))*x+(0.0003759572995997717))*x+(-0.007421790140788284))*x+(0.10610178700149493));
		rts[2] = (((((((((((((3.1529149661461509e-010))*x+(-7.7610214551289872e-011))*x+(-2.0099832909181711e-010))*x+(3.8047195024167494e-011))*x+(1.5283300551042581e-010))*x+(-1.5647098431751754e-009))*x+(-1.7571899491031216e-009))*x+(1.8264010464008607e-006))*x+(-6.5067402826709142e-005))*x+(0.0015754604948511701))*x+(-0.029192067396389781))*x+(0.36915800454235437));
		rts[3] = (((((((((((((2.1245796233415604e-009))*x+(2.4253192047278084e-011))*x+(-1.3551471056416631e-009))*x+(5.4569682106375694e-012))*x+(-8.1634728606635077e-010))*x+(-6.2237290876510087e-009))*x+(4.2347851329319986e-007))*x+(-1.2845184234796153e-007))*x+(-0.00021938153295097959))*x+(0.0066122942461922882))*x+(-0.11301365120027212))*x+(1.1454258181088268));
		rts[4] = (((((((((((((6.7520886659622192e-009))*x+(-9.7012768189112332e-010))*x+(-3.8465562586983042e-009))*x+(6.4513490845759692e-010))*x+(1.3943160107980171e-008))*x+(7.5916280669237806e-008))*x+(-2.1704232911664194e-006))*x+(-4.6666463750473966e-005))*x+(-0.00027832904614299991))*x+(0.047788649742048626))*x+(-0.85027713015671913))*x+(6.0057540013044433));
		wts[0] = (((((((((((((1.2247861983875433e-010))*x+(-3.213547946264346e-011))*x+(-6.4801497501321137e-011))*x+(2.2964741219766435e-011))*x+(-3.8464046762480094e-011))*x+(1.2764497607046601e-009))*x+(-2.4591940039897505e-008))*x+(5.7926993542641481e-007))*x+(-1.2823145912610467e-005))*x+(0.00028365583559959256))*x+(-0.0067952890555642602))*x+(0.18626000590341646));
		wts[1] = (((((((((((((1.0246973639974991e-010))*x+(1.4248750327775875e-011))*x+(-7.0447943774828062e-011))*x+(2.9028039231585957e-011))*x+(-6.7948728125581204e-010))*x+(1.1416350531590069e-008))*x+(-1.8244091289550587e-007))*x+(2.721866917188009e-006))*x+(-3.8192466996702278e-005))*x+(0.00049282783147655085))*x+(-0.005621418136554362))*x+(0.083607083691460499));
		wts[2] = (((((((((((((3.4712381117666759e-011))*x+(7.806496190217633e-012))*x+(-3.3111291486420669e-011))*x+(1.5814786517391136e-010))*x+(-2.2111497817907848e-009))*x+(2.8244876955814863e-008))*x+(-3.3694465132831175e-007))*x+(3.6837185387976015e-006))*x+(-3.6580966726024643e-005))*x+(0.00032258455820972801))*x+(-0.0022967744678723321))*x+(0.0162959864191877));
		wts[3] = (((((((((((((-2.1789977229976404e-013))*x+(1.7621459846850485e-012))*x+(-1.9636440621676833e-011))*x+(2.3488707275494863e-010))*x+(-2.5932319995073763e-009))*x+(2.6203032484535999e-008))*x+(-2.398939972803974e-007))*x+(1.9572180750826447e-006))*x+(-1.392169885399688e-005))*x+(8.3463077145329537e-005))*x+(-0.00038671274584206069))*x+(0.001315480852996266));
		wts[4] = (((((((((((((-7.6975463040677512e-014))*x+(1.1235457009206584e-012))*x+(-1.2660687313352051e-011))*x+(1.3125582102683589e-010))*x+(-1.228072019077153e-009))*x+(1.0234113860761266e-008))*x+(-7.472512861088354e-008))*x+(4.674032781606651e-007))*x+(-2.4239421238331622e-006))*x+(9.8951959867642552e-006))*x+(-2.8825183915763088e-005))*x+(4.7667168053694065e-005));
		break;
	case 10:
		rts[0] = (((((((((((((2.3343697345505156e-011))*x+(-1.1368683772161603e-012))*x+(-1.4741393291236211e-011))*x+(4.7369515717340016e-013))*x+(-4.0027240781152337e-013))*x+(7.8831163818904302e-011))*x+(-1.6540230666587754e-009))*x+(5.2851202192449869e-008))*x+(-1.3022849925982865e-006))*x+(3.052015971024187e-005))*x+(-0.00064321081789999682))*x+(0.01002615189099372));
		rts[1] = (((((((((((((1.837179297581315e-010))*x+(8.4886172165473291e-012))*x+(-1.1993961379630491e-010))*x+(-6.8212102632969602e-012))*x+(8.0433437688043341e-012))*x+(5.125665817710493e-010))*x+(-1.3648989938275236e-008))*x+(5.3691108270470522e-007))*x+(-1.405607339661589e-005))*x+(0.00033042310777814388))*x+(-0.0067165566345340237))*x+(0.099040200098633846));
		rts[2] = (((((((((((((3.4682064627607662e-010))*x+(2.3040532444914181e-011))*x+(-2.0994169365925089e-010))*x+(-2.2888949994618692e-011))*x+(8.1134506520659956e-011))*x+(-1.0406656277458142e-009))*x+(-9.3087416293731914e-009))*x+(1.797473068757919e-006))*x+(-5.7807149385191707e-005))*x+(0.0013911778498033782))*x+(-0.026229060425646537))*x+(0.34147815342905968));
		rts[3] = (((((((((((((1.8917489796876907e-009))*x+(-2.2312936683495838e-010))*x+(-1.3224052963778377e-009))*x+(1.6855968472858268e-010))*x+(-5.0674013133781648e-010))*x+(-1.3215526450949254e-008))*x+(3.6420837782695042e-007))*x+(1.858369034361355e-006))*x+(-0.0002158225935754802))*x+(0.0059574977456636384))*x+(-0.10044564860287934))*x+(1.0388053673507207));
		rts[4] = (((((((((((((8.8475644588470459e-009))*x+(-2.4641243120034533e-009))*x+(-5.6073380013306933e-009))*x+(1.0404619388282297e-009))*x+(1.3732157337168852e-008))*x+(1.6879243958101142e-007))*x+(-1.4327832786875661e-006))*x+(-5.5908283011755579e-005))*x+(-0.00048470894582663959))*x+(0.046653381543174589))*x+(-0.75573178584679557))*x+(5.2029384443709823));
		wts[0] = (((((((((((((3.4682064627607662e-010))*x+(-2.2434202643732228e-011))*x+(-2.1812714597520725e-010))*x+(1.1671848672752578e-011))*x+(6.290671687262745e-012))*x+(9.7047111088007431e-010))*x+(-1.7858439467962246e-008))*x+(4.7392555509636236e-007))*x+(-1.0727977349097213e-005))*x+(0.000248434340587883))*x+(-0.0062642453417413981))*x+(0.17973610544979846));
		wts[1] = (((((((((((((-5.0325373498102025e-011))*x+(1.0307606620093186e-011))*x+(3.8918794113366552e-011))*x+(1.7659355459424358e-011))*x+(-4.4887826788908569e-010))*x+(7.5211990709552375e-009))*x+(-1.2654233202032589e-007))*x+(1.9591079188548597e-006))*x+(-2.8923375524338619e-005))*x+(0.00039291489027741078))*x+(-0.004740300687531924))*x+(0.078442851103171479));
		wts[2] = (((((((((((((3.1225984760870532e-011))*x+(-4.0169349328304325e-012))*x+(-2.8895404587577403e-011))*x+(9.1082104821301372e-011))*x+(-1.2353259156346514e-009))*x+(1.6487184654560377e-008))*x+(-2.061393216864123e-007))*x+(2.3552294379965608e-006))*x+(-2.4719953658098686e-005))*x+(0.00023195583802321346))*x+(-0.001748142938051082))*x+(0.014288588497392138));
		wts[3] = (((((((((((((-2.4726887204451486e-012))*x+(7.4843834833397216e-013))*x+(-7.1699683227658771e-012))*x+(1.1170027865622008e-010))*x+(-1.2695030212247123e-009))*x+(1.3255053351220644e-008))*x+(-1.2611108466537011e-007))*x+(1.0742915311778845e-006))*x+(-8.0467934889156111e-006))*x+(5.1386872154575603e-005))*x+(-0.00025478150301780041))*x+(0.0010000506360844188));
		wts[4] = (((((((((((((-3.6711374680938505e-014))*x+(4.5978036193143146e-013))*x+(-5.2779262441996853e-012))*x+(5.538421573210902e-011))*x+(-5.2517665216633692e-010))*x+(4.4473612454779908e-009))*x+(-3.3110434104546838e-008))*x+(2.1210739725921235e-007))*x+(-1.1334730185134502e-006))*x+(4.8115254051190117e-006))*x+(-1.4756876273849647e-005))*x+(2.6715041825411289e-005));
		break;
	case 11:
		rts[0] = (((((((((((((9.5496943686157465e-012))*x+(-2.9179621681881445e-012))*x+(-5.0780120848988499e-012))*x+(1.2173965539356382e-012))*x+(-3.1992186677598511e-012))*x+(5.1996777254241052e-011))*x+(-1.2591715818170237e-009))*x+(4.5635898153021743e-008))*x+(-1.1059690324550602e-006))*x+(2.6914980580761257e-005))*x+(-0.00058587376974408563))*x+(0.009412210220487353));
		rts[1] = (((((((((((((7.9429203954835728e-011))*x+(-1.6977234433094658e-011))*x+(-4.7483202555061624e-011))*x+(8.1475567033824811e-012))*x+(-2.120259523508139e-011))*x+(3.3109870400949148e-010))*x+(-1.1075262040805001e-008))*x+(4.7555693782896919e-007))*x+(-1.2035436838429373e-005))*x+(0.00029134710693682708))*x+(-0.0060957963076400511))*x+(0.092640534253479206));
		rts[2] = (((((((((((((4.4140809526046115e-010))*x+(-4.850638409455617e-012))*x+(-2.7739588404074306e-010))*x+(-5.1538033100465936e-012))*x+(3.4522903054797397e-011))*x+(-1.0124760289424255e-009))*x+(-1.5252487865306346e-008))*x+(1.7360195829022966e-006))*x+(-5.0730335929024165e-005))*x+(0.0012284330891424815))*x+(-0.023612988872931114))*x+(0.31658425085742969));
		rts[3] = (((((((((((((1.7074247201283772e-009))*x+(2.27980005244414e-010))*x+(-1.114434174572428e-009))*x+(-9.8831757592658193e-011))*x+(-2.4427511865117901e-010))*x+(-1.7882427982840454e-008))*x+(2.6969219391048677e-007))*x+(3.4550932355159598e-006))*x+(-0.00020503771191708134))*x+(0.0053246081885516272))*x+(-0.08916895092290876))*x+(0.94410360251770331));
		rts[4] = (((((((((((((6.4416478077570592e-009))*x+(-1.1641532182693481e-010))*x+(-4.2346073314547539e-009))*x+(-1.0065074699620404e-009))*x+(7.9647482683261241e-009))*x+(2.4015556239949848e-007))*x+(-1.856988660620118e-007))*x+(-6.0132937600580284e-005))*x+(-0.00071887639557507055))*x+(0.044852264043803672))*x+(-0.66410884775696988))*x+(4.4933181712880206));
		wts[0] = (((((((((((((2.5587117609878379e-010))*x+(-3.2741809263825417e-011))*x+(-1.7136396005904922e-010))*x+(1.8341476485754054e-011))*x+(-6.6317322004275802e-013))*x+(6.8145785310965335e-010))*x+(-1.2887473310740914e-008))*x+(3.9779855972218076e-007))*x+(-8.99281413607733e-006))*x+(0.00021892913682371637))*x+(-0.0057977486174839174))*x+(0.1737100234733959));
		wts[1] = (((((((((((((1.5764574830730755e-011))*x+(1.3945585427184899e-011))*x+(-8.033869865660865e-012))*x+(6.4422541375582406e-012))*x+(-2.7381948560408392e-010))*x+(5.0721785290382595e-009))*x+(-8.9342539292639841e-008))*x+(1.4254941544204294e-006))*x+(-2.2215984324817455e-005))*x+(0.00031673824581685917))*x+(-0.0040339950736927701))*x+(0.074068381600854674));
		wts[2] = (((((((((((((3.9108272176235914e-011))*x+(6.7833146507230895e-012))*x+(-2.8630135299560305e-011))*x+(4.5095778962907687e-011))*x+(-7.0147147350022954e-010))*x+(9.8498094125432073e-009))*x+(-1.2898738899203011e-007))*x+(1.533921703341286e-006))*x+(-1.7069619846242962e-005))*x+(0.00017008949193419941))*x+(-0.0013499100045901956))*x+(0.012749845863598263));
		wts[3] = (((((((((((((1.4210854715202004e-013))*x+(-9.2370555648813024e-014))*x+(-4.3763511333357501e-012))*x+(5.4426093261857503e-011))*x+(-6.3391077572324162e-010))*x+(6.8609909512999199e-009))*x+(-6.7965441952662811e-008))*x+(6.0495258136575292e-007))*x+(-4.7844834572568764e-006))*x+(3.2606136517281575e-005))*x+(-0.00017241006281662808))*x+(0.00078956948148881849));
		wts[4] = (((((((((((((5.3290705182007514e-015))*x+(1.9465910365094411e-013))*x+(-2.2341017924532025e-012))*x+(2.3610021345395655e-011))*x+(-2.2730381928533677e-010))*x+(1.9601025906534897e-009))*x+(-1.4917979982830704e-008))*x+(9.8181689002337674e-008))*x+(-5.4287408642951626e-007))*x+(2.4097076136576791e-006))*x+(-7.8279593908357027e-006))*x+(1.5819187615994123e-005));
		break;
	case 12:
		rts[0] = (((((((((((((1.2808717049968738e-011))*x+(6.442254137558241e-013))*x+(-8.4080890398278517e-012))*x+(-5.4474943074941008e-013))*x+(-2.2464992828948502e-012))*x+(2.3174795416025518e-011))*x+(-1.0334736955108781e-009))*x+(3.9977757752366706e-008))*x+(-9.3511818274073322e-007))*x+(2.3858993277494842e-005))*x+(-0.00053518518365287533))*x+(0.0088521898870971994));
		rts[1] = (((((((((((((1.1641532182693481e-010))*x+(-4.2443086082736646e-012))*x+(-7.6397554948925972e-011))*x+(1.8189894035458561e-012))*x+(-1.748882520284193e-011))*x+(9.5475627404084662e-011))*x+(-9.7745799602459247e-009))*x+(4.2403397149115563e-007))*x+(-1.0238430223778277e-005))*x+(0.00025798770972694968))*x+(-0.0055473597765174814))*x+(0.086824514399193198));
		rts[2] = (((((((((((((3.7834979593753815e-010))*x+(1.2126596023639042e-011))*x+(-2.3252747875327864e-010))*x+(-9.7012768189112324e-012))*x+(-8.4696694102603942e-012))*x+(-1.3311307611729715e-009))*x+(-2.2174848623990329e-008))*x+(1.6432903914657495e-006))*x+(-4.3960214614428374e-005))*x+(0.0010864898275777892))*x+(-0.021301452165351162))*x+(0.29415068446541981));
		rts[3] = (((((((((((((1.5958600367108979e-009))*x+(4.1230426480372742e-011))*x+(-1.0474347315418222e-009))*x+(1.6674069532503687e-011))*x+(1.3657578771623472e-010))*x+(-2.0067744799234785e-008))*x+(1.5435140573079781e-007))*x+(4.5207469968981205e-006))*x+(-0.00018889333757547239))*x+(0.0047326448743483605))*x+(-0.079119789335037508))*x+(0.86005792851451979));
		rts[4] = (((((((((((((3.3760443329811096e-009))*x+(6.0147916277249647e-010))*x+(-1.9572325982153416e-009))*x+(-1.6710449320574601e-009))*x+(-1.6828683631805079e-009))*x+(2.5871842505390913e-007))*x+(1.3423837401660419e-006))*x+(-5.7287768849316002e-005))*x+(-0.00095627510441609331))*x+(0.042336701037593315))*x+(-0.57680092713348852))*x+(3.873282638733814));
		wts[0] = (((((((((((((2.1221543041368324e-010))*x+(9.701276818911234e-012))*x+(-1.2892087397631258e-010))*x+(-8.1854523159563541e-012))*x+(-1.570773141186995e-011))*x+(3.9347014535451308e-010))*x+(-9.6529726434368951e-009))*x+(3.421971719319572e-007))*x+(-7.5182117939924052e-006))*x+(0.00019421805152157004))*x+(-0.005385338191407108))*x+(0.16812259673680852));
		wts[1] = (((((((((((((-9.701276818911234e-012))*x+(-3.0316490059097605e-012))*x+(2.1524707941959299e-011))*x+(1.2998195112838097e-011))*x+(-1.8240105722118946e-010))*x+(3.5323376816146874e-009))*x+(-6.3889935712306098e-008))*x+(1.0462368090398875e-006))*x+(-1.7314820793072155e-005))*x+(0.0002578205315853973))*x+(-0.003461882653381989))*x+(0.0703302497508205));
		wts[2] = (((((((((((((6.4422541375582414e-012))*x+(7.9580786405131221e-013))*x+(-4.8837970704577547e-012))*x+(2.7085889087175019e-011))*x+(-4.0831338310454152e-010))*x+(6.0420828340568278e-009))*x+(-8.23540057814931e-008))*x+(1.0150378105255875e-006))*x+(-1.2049076164992224e-005))*x+(0.00012692844245023281))*x+(-0.0010553946193090961))*x+(0.011554369853701327));
		wts[3] = (((((((((((((-3.7895612573872008e-014))*x+(2.1316282072803006e-014))*x+(-1.9279392896957384e-012))*x+(2.6857035114365619e-011))*x+(-3.2339353417398792e-010))*x+(3.6372201824471282e-009))*x+(-3.7548481171545411e-008))*x+(3.4916426248805349e-007))*x+(-2.9265867079169422e-006))*x+(2.129372567194003e-005))*x+(-0.00011943413062086606))*x+(0.00064552433615838658));
		wts[4] = (((((((((((((-1.3322676295501878e-015))*x+(7.7345537382219235e-014))*x+(-9.4834325577627011e-013))*x+(1.018433485692564e-011))*x+(-9.9698433536632436e-011))*x+(8.774886005892083e-010))*x+(-6.8465589368694665e-009))*x+(4.6446085769380939e-008))*x+(-2.6692453825736959e-007))*x+(1.2462127626480261e-006))*x+(-4.3086894435156142e-006))*x+(9.9430798243292021e-006));
		break;
	case 13:
		rts[0] = (((((((((((((-1.6674069532503684e-012))*x+(-2.1979455292845764e-012))*x+(1.8947806286936002e-012))*x+(1.7479351299698463e-012))*x+(-3.964236346594892e-012))*x+(-4.1442405063207843e-012))*x+(-9.7840913149127552e-010))*x+(3.5015530937728315e-008))*x+(-7.8522199427102002e-007))*x+(2.1283431816010445e-005))*x+(-0.00049011769766758135))*x+(0.0083399675419129297));
		rts[1] = (((((((((((((4.6081064889828362e-011))*x+(-1.2429760924230019e-011))*x+(-2.4859521848460034e-011))*x+(9.3223206931725144e-012))*x+(-2.3741601277530815e-011))*x+(-1.3542352424641041e-010))*x+(-9.9142010157038385e-009))*x+(3.7539488687935807e-007))*x+(-8.6393285577690548e-006))*x+(0.00022971959469933931))*x+(-0.0050604520477616037))*x+(0.081525318223777066));
		rts[2] = (((((((((((((2.8618766615788138e-010))*x+(-2.4253192047278085e-012))*x+(-1.861432489628593e-010))*x+(7.2759576141834259e-012))*x+(8.5833562479820102e-012))*x+(-1.6960086668404983e-009))*x+(-3.134405091032022e-008))*x+(1.5104401468827668e-006))*x+(-3.7637444433746836e-005))*x+(0.00096422600231989752))*x+(-0.019253899252513241))*x+(0.27389338164125154));
		rts[3] = (((((((((((((1.0137834275762239e-009))*x+(-7.7610214551289872e-011))*x+(-6.411937647499143e-010))*x+(1.0580455030625065e-010))*x+(4.7809104823196924e-010))*x+(-1.9330438287094392e-008))*x+(3.4597347801460871e-008))*x+(4.9913372421883651e-006))*x+(-0.00016966903333156166))*x+(0.0041943311016456875))*x+(-0.070202445547573614))*x+(0.78548654570380638));
		rts[4] = (((((((((((((4.6760154267152148e-009))*x+(8.052059759696324e-010))*x+(-3.0352869847168522e-009))*x+(-1.4964219493170579e-009))*x+(-1.0562265136589607e-008))*x+(2.1096885423806572e-007))*x+(2.783269257141304e-006))*x+(-4.6853506664964087e-005))*x+(-0.001166970044446991))*x+(0.039141375026617187))*x+(-0.49521726188808951))*x+(3.337806447511154));
		wts[0] = (((((((((((((1.7098500393331051e-010))*x+(-2.7284841053187847e-011))*x+(-1.0724458358405779e-010))*x+(1.9402553637822468e-011))*x+(-1.4419280584358298e-011))*x+(1.0007047042866664e-010))*x+(-8.1808127679513145e-009))*x+(2.9834347170520914e-007))*x+(-6.2395798573292947e-006))*x+(0.00017362507410006073))*x+(-0.0050181341370234443))*x+(0.16292429128054556));
		wts[1] = (((((((((((((1.3339255626002947e-010))*x+(1.7886729134867587e-011))*x+(-9.7770680440589786e-011))*x+(-5.7601331112285436e-012))*x+(-8.3872464529122226e-011))*x+(2.5697595162910147e-009))*x+(-4.5811709388961689e-008))*x+(7.7439066300163018e-007))*x+(-1.3703630970270572e-005))*x+(0.00021156421948625526))*x+(-0.0029943004936475374))*x+(0.067109858523992094));
		wts[2] = (((((((((((((1.3263464400855202e-011))*x+(2.7663797178926566e-012))*x+(-8.4365107492582557e-012))*x+(1.3708737848598199e-011))*x+(-2.3874235921539361e-010))*x+(3.82808436801459e-009))*x+(-5.3332741315840572e-008))*x+(6.8132860125968964e-007))*x+(-8.7045167847417376e-006))*x+(9.6130663111082648e-005))*x+(-0.00083400298444196244))*x+(0.010614792943729115));
		wts[3] = (((((((((((((1.6579330501069003e-013))*x+(-5.2106467289074012e-014))*x+(-1.1495989345651954e-012))*x+(1.3607485508752385e-011))*x+(-1.683109577636325e-010))*x+(1.9778128764376861e-009))*x+(-2.1241340854063113e-008))*x+(2.0630754789021286e-007))*x+(-1.8426429615781667e-006))*x+(1.4281916933179227e-005))*x+(-8.4397767546320594e-005))*x+(0.00054477229904620111));
		wts[4] = (((((((((((((-7.4755016991427202e-015))*x+(3.5675166524621695e-014))*x+(-4.0320062103897197e-013))*x+(4.4467022656628306e-012))*x+(-4.4373375344501177e-011))*x+(3.9968225893268384e-010))*x+(-3.2064659320177494e-009))*x+(2.249488527308191e-008))*x+(-1.3504592721758757e-007))*x+(6.6697311699835869e-007))*x+(-2.4608452497902292e-006))*x+(6.6540652338805881e-006));
		break;
	case 14:
		rts[0] = (((((((((((((-3.7137700322394567e-012))*x+(-2.9937533933358886e-012))*x+(3.652189661806915e-012))*x+(2.4158453015843406e-012))*x+(-2.3897920679398035e-012))*x+(-2.0430324099152131e-011))*x+(-1.0568686481526866e-009))*x+(2.996745242696737e-008))*x+(-6.5512280533637035e-007))*x+(1.9127954531004156e-005))*x+(-0.00044977137436286407))*x+(0.0078703820842326872));
		rts[1] = (((((((((((((4.4262075486282505e-011))*x+(-2.4556356947869062e-011))*x+(-2.209314213056738e-011))*x+(1.849305893604954e-011))*x+(-2.9084882650446778e-012))*x+(-2.6256093595596514e-010))*x+(-1.1170968890657681e-008))*x+(3.2299982940150091e-007))*x+(-7.2404193558565453e-006))*x+(0.00020595230426510847))*x+(-0.0046254798165445846))*x+(0.076686311763229445));
		rts[2] = (((((((((((((2.7406107013424236e-010))*x+(-2.7891170854369797e-011))*x+(-1.6022264996233085e-010))*x+(2.9406995357324675e-011))*x+(7.6378607142639027e-011))*x+(-1.6901490577462632e-009))*x+(-4.1776018496382975e-008))*x+(1.3276459422210487e-006))*x+(-3.194378631821148e-005))*x+(0.00086003695129738267))*x+(-0.017432484880816817))*x+(0.25556754832324113));
		rts[3] = (((((((((((((1.0186340659856796e-009))*x+(-4.850638409455617e-012))*x+(-6.1785006740440928e-010))*x+(5.3660187404602766e-011))*x+(9.4026593918291224e-010))*x+(-1.5273845595705399e-008))*x+(-7.0861074637681057e-008))*x+(4.8906094699911282e-006))*x+(-0.00014972881430426929))*x+(0.0037153370814352695))*x+(-0.062302765130821953))*x+(0.71931376924731238));
		rts[4] = (((((((((((((5.5685328940550481e-009))*x+(6.1118043959140778e-010))*x+(-3.5324774216860529e-009))*x+(-7.7125150710344315e-010))*x+(-1.620962090479831e-008))*x+(1.0893522054781593e-007))*x+(3.7626126688413324e-006))*x+(-3.0231951280749549e-005))*x+(-0.0013227799239053555))*x+(0.035390077092755913))*x+(-0.4206077406399456))*x+(2.8805197190708021));
		wts[0] = (((((((((((((1.964508555829525e-010))*x+(-3.213547946264346e-011))*x+(-1.2520710394407311e-010))*x+(2.1448916716811553e-011))*x+(4.9927469566076395e-012))*x+(-1.2100305942415918e-010))*x+(-8.2723149811651329e-009))*x+(2.5778042426575592e-007))*x+(-5.1271642427611983e-006))*x+(0.00015661540870201549))*x+(-0.0046884498796663831))*x+(0.15807383286967019));
		wts[1] = (((((((((((((7.5184895346562059e-011))*x+(2.2131037743141253e-011))*x+(-4.6232647340123848e-011))*x+(-1.1823431123048067e-011))*x+(-6.7141551577757738e-011))*x+(1.9332292803634723e-009))*x+(-3.2433196276807998e-008))*x+(5.8037307804070792e-007))*x+(-1.1016358048528593e-005))*x+(0.00017467793679719346))*x+(-0.0026093997499922355))*x+(0.064314149663768944));
		wts[2] = (((((((((((((2.5086895523903269e-011))*x+(3.2211270687791207e-012))*x+(-1.7664092410996087e-011))*x+(6.3285672998366262e-012))*x+(-1.421713117603455e-010))*x+(2.5089860559527701e-009))*x+(-3.4650880220699059e-008))*x+(4.6465210721639377e-007))*x+(-6.4435837728062115e-006))*x+(7.3624533884177168e-005))*x+(-0.00066537515572841384))*x+(0.009868847703804794));
		wts[3] = (((((((((((((1.0468662973532141e-012))*x+(5.2106467289074012e-014))*x+(-1.2893390059313483e-012))*x+(6.8940408937123712e-012))*x+(-8.9473613703224445e-011))*x+(1.1052649536343513e-009))*x+(-1.2265301497828748e-008))*x+(1.2470724705324066e-007))*x+(-1.1954826922246462e-006))*x+(9.8058968030386856e-006))*x+(-6.0632050896002519e-005))*x+(0.00047300069372864664));
		wts[4] = (((((((((((((-6.7723604502134549e-015))*x+(1.4303373300587431e-014))*x+(-1.7311846400858144e-013))*x+(1.9693321047971799e-012))*x+(-2.0067518248974754e-011))*x+(1.8557414654431226e-010))*x+(-1.534820982411261e-009))*x+(1.1171251337078171e-008))*x+(-7.0471822312864391e-008))*x+(3.699146959723143e-007))*x+(-1.4559698652356966e-006))*x+(4.7447949753980199e-006));
		break;
	case 15:
		rts[0] = (((((((((((((2.5011104298755527e-012))*x+(-5.3053857603420807e-013))*x+(-1.1037097162140224e-012))*x+(6.442254137558241e-013))*x+(1.82194999827819e-012))*x+(-1.7938243483210197e-011))*x+(-1.1806887874795298e-009))*x+(2.4367978005794082e-008))*x+(-5.462425271285839e-007))*x+(1.7331506980577949e-005))*x+(-0.00041336637408265702))*x+(0.0074391124312399737));
		rts[1] = (((((((((((((9.276845958083868e-011))*x+(-6.9727927135924493e-012))*x+(-5.6502358347643167e-011))*x+(7.3517488393311688e-012))*x+(3.4977650405683861e-011))*x+(-1.9885604274350044e-010))*x+(-1.2648672183720086e-008))*x+(2.6329978686234762e-007))*x+(-6.0653243769045089e-006))*x+(0.00018605341902109182))*x+(-0.0042340618918580743))*x+(0.072259855398456183));
		rts[2] = (((((((((((((2.5223319729169208e-010))*x+(2.5465851649641991e-011))*x+(-1.5643308870494366e-010))*x+(-4.3200998334214091e-012))*x+(1.8417267710901794e-010))*x+(-9.9073815817973809e-010))*x+(-5.0190389326113895e-008))*x+(1.0960085094306273e-006))*x+(-2.7082331162109341e-005))*x+(0.00077172975843651603))*x+(-0.015803150318555743))*x+(0.23896444085129923));
		rts[3] = (((((((((((((9.0706938256820036e-010))*x+(-1.0671404500802358e-010))*x+(-5.7995445483053721e-010))*x+(9.0343140376110867e-011))*x+(1.287086585458989e-009))*x+(-8.2418030918537007e-009))*x+(-1.4259423034938359e-007))*x+(4.339338100104821e-006))*x+(-0.00013114896003470672))*x+(0.0032945752353083315))*x+(-0.055302154754754619))*x+(0.66058141773432788));
		rts[4] = (((((((((((((4.7342230876286822e-009))*x+(2.6193447411060333e-010))*x+(-2.8473247463504472e-009))*x+(1.673470251262188e-010))*x+(-1.6587970700735845e-008))*x+(-1.4333522813103627e-008))*x+(4.0466941868544373e-006))*x+(-1.0398622668124819e-005))*x+(-0.0014045146846359084))*x+(0.031279239758829437))*x+(-0.35389750903688361))*x+(2.4939528978566869));
		wts[0] = (((((((((((((2.1827872842550278e-010))*x+(-1.5158245029548802e-011))*x+(-1.393042718215535e-010))*x+(1.250555214937776e-011))*x+(3.2182848978360809e-011))*x+(-1.9887854326346616e-010))*x+(-9.3026712259340148e-009))*x+(2.1405689872485328e-007))*x+(-4.1817438475681241e-006))*x+(0.00014269572942908942))*x+(-0.0043896116276600254))*x+(0.15353712060702707));
		wts[1] = (((((((((((((7.3365905943016203e-011))*x+(-3.3348139065007367e-012))*x+(-4.702845520417516e-011))*x+(4.5853691214385127e-012))*x+(-5.2944907717270936e-011))*x+(1.4459817047433414e-009))*x+(-2.2345934732233747e-008))*x+(4.4463244538069563e-007))*x+(-8.9831448753796561e-006))*x+(0.00014481418336019514))*x+(-0.002290922557216071))*x+(0.061868961289126376));
		wts[2] = (((((((((((((2.5693225325085223e-011))*x+(-1.5537201155287523e-012))*x+(-1.610089839232387e-011))*x+(5.5327594357853132e-012))*x+(-9.3391960831468168e-011))*x+(1.6764579354363225e-009))*x+(-2.2267359234273698e-008))*x+(3.2442812338458654e-007))*x+(-4.8860049469169609e-006))*x+(5.6769961699454939e-005))*x+(-0.00053575739384942821))*x+(0.0092710858699105742));
		wts[3] = (((((((((((((0))*x+(3.6711374680938505e-014))*x+(-3.0494125743037631e-013))*x+(3.5478286974921498e-012))*x+(-4.9269662423985964e-011))*x+(6.3433310918773833e-010))*x+(-7.1868486370418871e-009))*x+(7.7246548602661697e-008))*x+(-7.9999252070693755e-007))*x+(6.8599114207232091e-006))*x+(-4.4163148011408851e-005))*x+(0.00042109252091772202));
		wts[4] = (((((((((((((-1.2582527612418439e-015))*x+(6.346774957440478e-015))*x+(-7.8247593589727174e-014))*x+(8.845008059310543e-013))*x+(-9.2376395884515485e-012))*x+(8.8012919362857406e-011))*x+(-7.5155283719826347e-010))*x+(5.6967293558109746e-009))*x+(-3.8028868399109074e-008))*x+(2.125901122654429e-007))*x+(-8.8955776495346128e-007))*x+(3.5980717275312471e-006));
		break;
	case 16:
		rts[0] = (((((((((((((9.0570514051554093e-012))*x+(-9.4739031434680016e-014))*x+(-6.7477875139350845e-012))*x+(2.7237471537470504e-013))*x+(5.898688944701764e-012))*x+(3.102777294354079e-012))*x+(-1.2332298053123007e-009))*x+(1.8280749608523547e-008))*x+(-4.6085524605237832e-007))*x+(1.5826958167383141e-005))*x+(-0.00038025061166589317))*x+(0.0070425544930870238));
		rts[1] = (((((((((((((1.2187229003757238e-010))*x+(-3.0316490059097606e-013))*x+(-8.3484034500240042e-011))*x+(2.0463630789890885e-012))*x+(6.6071000522545845e-011))*x+(5.2687928094504358e-011))*x+(-1.316350184410453e-008))*x+(1.9814461345764772e-007))*x+(-5.1415539739178371e-006))*x+(0.00016930838335187101))*x+(-0.0038791620639213454))*x+(0.068206032081962409));
		rts[2] = (((((((((((((3.6015990190207958e-010))*x+(3.3348139065007367e-011))*x+(-2.3427067693167675e-010))*x+(-1.7583564234276612e-011))*x+(2.6733459890238009e-010))*x+(3.2849101216925187e-010))*x+(-5.2425561669622311e-008))*x+(8.3617063998768027e-007))*x+(-2.3214175555933782e-005))*x+(0.00069654550135307214))*x+(-0.014336809519321456))*x+(0.22390698294890385));
		rts[3] = (((((((((((((8.246085296074549e-010))*x+(-9.701276818911234e-012))*x+(-5.0446639458338416e-010))*x+(-2.9103830456733704e-011))*x+(1.2537005507814076e-009))*x+(1.1770377265444645e-010))*x+(-1.6691072820170424e-007))*x+(3.5446353455389117e-006))*x+(-0.00011534048456522208))*x+(0.0029256399772841961))*x+(-0.049089847832883636))*x+(0.60844687895966176));
		rts[4] = (((((((((((((1.8044374883174896e-009))*x+(-2.9103830456733704e-010))*x+(-9.8346693751712654e-010))*x+(9.8710491632421805e-010))*x+(-1.2185713179254282e-008))*x+(-1.2025626953497218e-007))*x+(3.6258120180339879e-006))*x+(9.0486264809896949e-006))*x+(-0.0014065073894640179))*x+(0.027043206134772291))*x+(-0.29557413776714109))*x+(2.1699237308374606));
		wts[0] = (((((((((((((2.6678511252005893e-010))*x+(3.0316490059097604e-011))*x+(-1.8053469830192626e-010))*x+(-1.6067739731321727e-011))*x+(7.0950060641431862e-011))*x+(-8.9623123737207295e-011))*x+(-1.0265621241956067e-008))*x+(1.6489369218201472e-007))*x+(-3.4222109269362493e-006))*x+(0.00013133901174785154))*x+(-0.0041159568172826049))*x+(0.14928622752959822));
		wts[1] = (((((((((((((5.2144362901647881e-011))*x+(-1.5158245029548803e-012))*x+(-2.7663797178926565e-011))*x+(1.5347723092418162e-012))*x+(-5.5678128774161444e-011))*x+(1.0161554560757697e-009))*x+(-1.4966910969841742e-008))*x+(3.5242953814555256e-007))*x+(-7.4013136669252395e-006))*x+(0.00012032948300921367))*x+(-0.0020265685774305091))*x+(0.059714293442021157));
		wts[2] = (((((((((((((1.4097167877480388e-011))*x+(-1.9326762412674725e-012))*x+(-8.4412477008299902e-012))*x+(3.5716614850874367e-012))*x+(-6.9351339485971637e-011))*x+(1.0987813621928428e-009))*x+(-1.4029422179540063e-008))*x+(2.3512697444605377e-007))*x+(-3.7805946695330475e-006))*x+(4.3859075797674521e-005))*x+(-0.00043567969278550975))*x+(0.0087875161778981428));
		wts[3] = (((((((((((((5.7080266439394712e-013))*x+(-7.3422749361877011e-014))*x+(-4.9604764740251994e-013))*x+(1.9202417433916703e-012))*x+(-2.8265241998800168e-011))*x+(3.7042742021912523e-010))*x+(-4.2453216087210786e-009))*x+(4.9321968187872781e-008))*x+(-5.5173385948793698e-007))*x+(4.8601156027053005e-006))*x+(-3.2566763515759683e-005))*x+(0.0003830599398650386));
		wts[4] = (((((((((((((3.3306690738754696e-015))*x+(2.2574534834044848e-015))*x+(-3.6577222732129634e-014))*x+(4.0353600091099412e-013))*x+(-4.343075667619563e-012))*x+(4.2700179908132054e-011))*x+(-3.763661154469802e-010))*x+(2.9891082170024606e-009))*x+(-2.1276878788322298e-008))*x+(1.2631677191486493e-007))*x+(-5.5896514752362048e-007))*x+(2.8880999704075525e-006));
		break;
	case 17:
		rts[0] = (((((((((((((8.033869865660865e-012))*x+(-7.2001663890356815e-013))*x+(-4.6611603465862564e-012))*x+(3.0553337637684308e-013))*x+(5.1105786269545206e-012))*x+(3.3482698095591936e-011))*x+(-1.1238148189818276e-009))*x+(1.2312038888406818e-008))*x+(-3.9985142276146207e-007))*x+(1.4541882282850225e-005))*x+(-0.00034991225497643864))*x+(0.0066776870393880031));
		rts[1] = (((((((((((((4.7293724492192268e-011))*x+(4.850638409455617e-012))*x+(-2.5238477974198759e-011))*x+(-5.5327594357853132e-012))*x+(4.8771653382573277e-011))*x+(3.8649735264092061e-010))*x+(-1.1846019572677353e-008))*x+(1.3478715965575816e-007))*x+(-4.4778824400126807e-006))*x+(0.00015494275438510119))*x+(-0.0035552425428042678))*x+(0.06449122193015884));
		rts[2] = (((((((((((((2.3161798405150572e-010))*x+(1.2126596023639042e-011))*x+(-1.4165379980113355e-010))*x+(-1.8568850161197283e-011))*x+(2.0977116340266849e-010))*x+(1.7687208734666153e-009))*x+(-4.603768003856127e-008))*x+(5.8639512564203266e-007))*x+(-2.0379721176540702e-005))*x+(0.00063140516133652913))*x+(-0.013010275014517316))*x+(0.21024428904469308));
		rts[3] = (((((((((((((8.343098064263661e-010))*x+(-1.9402553637822468e-011))*x+(-5.2932591643184423e-010))*x+(-5.8813990714649364e-011))*x+(8.3609090021733812e-010))*x+(6.8797779325298807e-009))*x+(-1.4438546003248118e-007))*x+(2.7494105244348548e-006))*x+(-0.00010279045154752234))*x+(0.0025992422137334583))*x+(-0.043571236830388535))*x+(0.56217070958502902));
		rts[4] = (((((((((((((2.5611370801925659e-009))*x+(-9.7012768189112337e-011))*x+(-1.6273891863723595e-009))*x+(9.8467959711949037e-010))*x+(-4.6285701197727267e-009))*x+(-1.8150338595053958e-007))*x+(2.6945999043922102e-006))*x+(2.5003214612221804e-005))*x+(-0.0013368430375505129))*x+(0.022912195186332102))*x+(-0.24565372506147559))*x+(1.8999988345304748));
		wts[0] = (((((((((((((2.3283064365386963e-010))*x+(4.850638409455617e-012))*x+(-1.4976346089194217e-010))*x+(-3.865352482534945e-012))*x+(7.2039559502930687e-011))*x+(1.4730498302621223e-010))*x+(-1.014822122632116e-008))*x+(1.1327347356389812e-007))*x+(-2.8660546440573142e-006))*x+(0.00012195835490989386))*x+(-0.0038629375115379386))*x+(0.14529834208152256));
		wts[1] = (((((((((((((3.0316490059097605e-012))*x+(1.3794002976889411e-011))*x+(-1.0989727646422882e-012))*x+(-7.2191141953226179e-012))*x+(-5.3248072617861908e-011))*x+(6.1798092569157837e-010))*x+(-1.0091517399501981e-008))*x+(2.9078611407662436e-007))*x+(-6.1230003833937872e-006))*x+(0.00010010445449634466))*x+(-0.0018067729850267948))*x+(0.057800991453663186));
		wts[2] = (((((((((((((1.1141310096718371e-011))*x+(7.5791225147744016e-014))*x+(-7.1764816311770119e-012))*x+(1.9800457569848122e-012))*x+(-5.2292984757211038e-011))*x+(6.6379020798497846e-010))*x+(-8.7996995801198352e-009))*x+(1.791418536104909e-007))*x+(-2.9607539681839505e-006))*x+(3.3802820614254235e-005))*x+(-0.00035842684785728998))*x+(0.0083921370942853148));
		wts[3] = (((((((((((((7.9580786405131221e-013))*x+(4.3816802038539507e-014))*x+(-6.3415939166588942e-013))*x+(1.0240697179142444e-012))*x+(-1.6934638876383208e-011))*x+(2.1522488883688831e-010))*x+(-2.5274839235422948e-009))*x+(3.2776170927224326e-008))*x+(-3.9038766166665329e-007))*x+(3.46340204598809e-006))*x+(-2.4323634513774843e-005))*x+(0.00035484697858522308));
		wts[4] = (((((((((((((7.7345537382219228e-015))*x+(1.267504619780387e-015))*x+(-2.1105802291051149e-014))*x+(1.8733278817073537e-013))*x+(-2.0936050925309444e-012))*x+(2.1162982499246807e-011))*x+(-1.9256639814806072e-010))*x+(1.6201243676751134e-009))*x+(-1.2362161411952575e-008))*x+(7.7216568455908685e-008))*x+(-3.5985890159067057e-007))*x+(2.4368261860100204e-006));
		break;
	case 18:
		rts[0] = (((((((((((((-3.6758744196655844e-012))*x+(-1.8568850161197284e-012))*x+(3.5029756872972935e-012))*x+(8.9528384705772613e-013))*x+(1.1404210908949606e-012))*x+(5.7391869034972842e-011))*x+(-8.4289159911025513e-010))*x+(7.3341791528847011e-009))*x+(-3.610292789255759e-007))*x+(1.3405551330029561e-005))*x+(-0.00032198418531475772))*x+(0.006341928041223471));
		rts[1] = (((((((((((((5.9420320515831307e-011))*x+(-3.637978807091713e-012))*x+(-3.5242919693700969e-011))*x+(-4.9264296346033599e-013))*x+(2.8838561168716595e-011))*x+(6.3055930847137154e-010))*x+(-8.7132301374026594e-009))*x+(8.2769290384495278e-008))*x+(-4.0480191856132981e-006))*x+(0.00014220604476496607))*x+(-0.003258308149116883))*x+(0.061086567629255725));
		rts[2] = (((((((((((((2.2191670723259449e-010))*x+(-1.8189894035458565e-012))*x+(-1.3013353357867649e-010))*x+(-1.7053025658242404e-011))*x+(8.9528384705772623e-011))*x+(2.662126519226149e-009))*x+(-3.2338546359274759e-008))*x+(3.8820834872647459e-007))*x+(-1.8453482988178834e-005))*x+(0.00057335399455106051))*x+(-0.011806476674887051))*x+(0.19784558176666023));
		rts[3] = (((((((((((((6.3058299322923018e-010))*x+(4.6081064889828362e-011))*x+(-4.0563463699072594e-010))*x+(-1.1550582712516189e-010))*x+(1.5961632016114891e-010))*x+(9.669605560702621e-009))*x+(-9.244520290015619e-008))*x+(2.1504289347736476e-006))*x+(-9.3078106857398993e-005))*x+(0.0023060397467006273))*x+(-0.038670802275675084))*x+(0.52109853707757814));
		rts[4] = (((((((((((((3.2693302879730859e-009))*x+(7.2759576141834259e-011))*x+(-2.1458011663829284e-009))*x+(6.5665517468005419e-010))*x+(2.3936384726160514e-009))*x+(-1.9120903971270309e-007))*x+(1.552114239207943e-006))*x+(3.564400212259973e-005))*x+(-0.0012136363710507263))*x+(0.019075830562583034))*x+(-0.20372749421590458))*x+(1.6759479739130232));
		wts[0] = (((((((((((((8.3673512563109398e-011))*x+(-1.3945585427184899e-011))*x+(-3.9638810752270125e-011))*x+(7.5033312896266563e-012))*x+(3.4030260091337063e-011))*x+(3.9457148659494123e-010))*x+(-8.4846266309076165e-009))*x+(6.6065644214556102e-008))*x+(-2.5101542375227655e-006))*x+(0.00011394137679575829))*x+(-0.0036272154519115148))*x+(0.1415546001831523));
		wts[1] = (((((((((((((1.0974569401393333e-010))*x+(7.8822874153653775e-012))*x+(-7.3024845429851354e-011))*x+(-3.0316490059097605e-012))*x+(-2.1553129651389707e-011))*x+(2.8934247590465623e-010))*x+(-7.4316501101160757e-009))*x+(2.4780531493462377e-007))*x+(-5.0502358038551068e-006))*x+(8.3387416216227736e-005))*x+(-0.0016238170554180188))*x+(0.056088481181638589));
		wts[2] = (((((((((((((3.812298624931524e-011))*x+(4.926429634603361e-013))*x+(-2.5915862048956719e-011))*x+(1.8142524519741223e-012))*x+(-3.118039160199259e-011))*x+(3.4259158473067442e-010))*x+(-5.8388180401713896e-009))*x+(1.433513924601707e-007))*x+(-2.3206838926451605e-006))*x+(2.5916293436942819e-005))*x+(-0.00029902727801002206))*x+(0.0080647232671897072));
		wts[3] = (((((((((((((7.2001663890356815e-013))*x+(8.2896652505345011e-015))*x+(-4.506025182611968e-013))*x+(6.7679195581149533e-013))*x+(-1.0317228552973271e-011))*x+(1.2077329414328375e-010))*x+(-1.5427574033092619e-009))*x+(2.283586038378619e-008))*x+(-2.8079704964221553e-007))*x+(2.4665183165035361e-006))*x+(-1.8448346444053323e-005))*x+(0.00033362680628704891));
		wts[4] = (((((((((((((3.6452322641859301e-015))*x+(9.6219328800846894e-016))*x+(-9.243763162321745e-015))*x+(8.9549895276874736e-014))*x+(-1.0371045746730239e-012))*x+(1.0649737674483146e-011))*x+(-1.0079400152246484e-010))*x+(9.1278289213094638e-010))*x+(-7.4480837622092613e-009))*x+(4.8203349505327992e-008))*x+(-2.3688090080541448e-007))*x+(2.1432684903718921e-006));
		break;
	case 19:
		rts[0] = (((((((((((((1.5878261668452371e-011))*x+(3.1074402310575047e-012))*x+(-1.0906830993917538e-011))*x+(-2.1600499167107046e-012))*x+(2.1280754936015001e-012))*x+(6.3972234916794449e-011))*x+(-4.6905822744432624e-010))*x+(4.0397838037738625e-009))*x+(-3.3890864564907469e-007))*x+(1.2358941744530087e-005))*x+(-0.00029623068966546414))*x+(0.0060329949287117627));
		rts[1] = (((((((((((((5.3357022504011788e-011))*x+(-3.4863963567962246e-012))*x+(-3.1756523336904742e-011))*x+(-1.5347723092418164e-012))*x+(-3.4153420832202154e-012))*x+(6.7348497149547859e-010))*x+(-4.6837316247660957e-009))*x+(4.9173477808158353e-008))*x+(-3.7908876153736064e-006))*x+(0.00013048130134737238))*x+(-0.0029857486918004432))*x+(0.057966492211840491));
		rts[2] = (((((((((((((2.801243681460619e-010))*x+(3.8805107275644936e-011))*x+(-1.6863547595373044e-010))*x+(-4.039672300374756e-011))*x+(-3.2514435588382185e-011))*x+(2.6422336911006519e-009))*x+(-1.5977571562094301e-008))*x+(2.6750143137614185e-007))*x+(-1.7169489719137673e-005))*x+(0.00052004022648866044))*x+(-0.010713721700926474))*x+(0.18659436418395309));
		rts[3] = (((((((((((((3.686485191186269e-010))*x+(-1.2126596023639041e-010))*x+(-2.0433314299831784e-010))*x+(3.0619654959688569e-011))*x+(-4.1302428144263104e-010))*x+(8.1352595771022607e-009))*x+(-3.7182798469833259e-008))*x+(1.8302432209793551e-006))*x+(-8.5209464317337322e-005))*x+(0.0020389277991139649))*x+(-0.03432975975513692))*x+(0.48464276408428641));
		rts[4] = (((((((((((((2.8327728311220803e-009))*x+(-2.1827872842550278e-010))*x+(-1.8602198300262289e-009))*x+(4.7839421313256025e-010))*x+(6.6934262576978645e-009))*x+(-1.6080220651322935e-007))*x+(4.8076611847136519e-007))*x+(4.0649385044370469e-005))*x+(-0.001059258890132142))*x+(0.015661497772590478))*x+(-0.16906753391106061))*x+(1.4901196814224844));
		wts[0] = (((((((((((((1.4188117347657681e-010))*x+(2.3040532444914181e-011))*x+(-8.5265128291212022e-011))*x+(-1.6749860757651426e-011))*x+(2.4130031306413002e-011))*x+(5.3283599754649903e-010))*x+(-5.6239644052880067e-009))*x+(3.046127794448239e-008))*x+(-2.3218978784285875e-006))*x+(0.00010672896971980482))*x+(-0.0034066387526212336))*x+(0.13803887395873846));
		wts[1] = (((((((((((((3.5773458269735173e-011))*x+(8.7917821171383058e-012))*x+(-1.8379372098327924e-011))*x+(-3.9411437076826888e-012))*x+(-1.6910917111090384e-011))*x+(8.4742879380428336e-011))*x+(-6.3859387407679451e-009))*x+(2.1377844102351179e-007))*x+(-4.1287843529173394e-006))*x+(6.96528101101999e-005))*x+(-0.0014712373842039356))*x+(0.054543241933505883));
		wts[2] = (((((((((((((-5.6085506609330569e-012))*x+(-5.4190725980636971e-012))*x+(3.6853483228090527e-012))*x+(5.3432813729159534e-012))*x+(-2.1350624971698075e-011))*x+(1.3947791070260487e-010))*x+(-4.4503998634463455e-009))*x+(1.1813541693032428e-007))*x+(-1.8000028975372524e-006))*x+(1.9760378155718576e-005))*x+(-0.00025361071855028587))*x+(0.0077894294190691826));
		wts[3] = (((((((((((((2.5816386065950303e-013))*x+(2.3211062701496604e-013))*x+(-1.3485509005780233e-013))*x+(3.1130653610489384e-013))*x+(-5.9091250411332412e-012))*x+(6.4650904999889264e-011))*x+(-1.0022057379590237e-009))*x+(1.6613390518606847e-008))*x+(-2.027942464764221e-007))*x+(1.7473258927647101e-006))*x+(-1.4273414289021439e-005))*x+(0.00031738558523938598));
		wts[4] = (((((((((((((2.4609943712524301e-015))*x+(2.55351295663786e-015))*x+(-4.7427339833205906e-015))*x+(4.3449040661632424e-014))*x+(-5.2108245380636886e-013))*x+(5.4014887181097474e-012))*x+(-5.4432315836938576e-011))*x+(5.3773522499582819e-010))*x+(-4.6237221551856826e-009))*x+(3.0468093488762163e-008))*x+(-1.5961399658524598e-007))*x+(1.9479645395825478e-006));
		break;
	case 20:
		rts[0] = (((((((((((((1.6825651982799172e-011))*x+(2.8421709430404007e-013))*x+(-1.0478136876675611e-011))*x+(-4.8316906031686813e-013))*x+(-5.3290705182007514e-013))*x+(5.0769240663347162e-011))*x+(-1.1830888121030131e-010))*x+(2.6054552496971675e-009))*x+(-3.2620511348363518e-007))*x+(1.1362698824781033e-005))*x+(-0.00027251534205364347))*x+(0.005748787905841682));
		rts[1] = (((((((((((((9.276845958083868e-011))*x+(-5.0022208597511053e-012))*x+(-5.5441281195574753e-011))*x+(4.3579954459952838e-013))*x+(-2.0927852043920815e-011))*x+(5.1760018493496308e-010))*x+(-1.0299786209107726e-009))*x+(3.5287553249811289e-008))*x+(-3.6280821548995146e-006))*x+(0.00011936665306064992))*x+(-0.0027359815273341882))*x+(0.055107479084580517));
		rts[2] = (((((((((((((2.2191670723259449e-010))*x+(3.0316490059097605e-012))*x+(-1.3922848059640577e-010))*x+(-4.9264296346033608e-012))*x+(-1.1495634074284072e-010))*x+(1.8430791707639098e-009))*x+(-2.2663314188283339e-009))*x+(2.2391015175315943e-007))*x+(-1.6209607928937185e-005))*x+(0.00047001476908493467))*x+(-0.0097241443481224064))*x+(0.17638376730178104));
		rts[3] = (((((((((((((5.8207660913467407e-010))*x+(-9.701276818911234e-012))*x+(-3.5045862508316833e-010))*x+(3.7895612573872005e-012))*x+(-5.3842086344957352e-010))*x+(4.2174216711525032e-009))*x+(4.8543806011972868e-010))*x+(1.7484626830821524e-006))*x+(-7.8115031756513048e-005))*x+(0.001794020835235314))*x+(-0.030500352031150202))*x+(0.45226852338775286));
		rts[4] = (((((((((((((1.1059455573558807e-009))*x+(3.637978807091713e-010))*x+(-7.2638310181597865e-010))*x+(-2.1160910061250129e-010))*x+(7.7905800329366067e-009))*x+(-1.1036932316225527e-007))*x+(-3.37490097498024e-007))*x+(4.0880971603485243e-005))*x+(-0.00089483280626042239))*x+(0.012730154048388693))*x+(-0.14075823173636162))*x+(1.3356953623951295));
		wts[0] = (((((((((((((2.5708383570114768e-010))*x+(-2.1827872842550278e-011))*x+(-1.5794891320789853e-010))*x+(9.1707382428770269e-012))*x+(1.8265685260606304e-011))*x+(4.9324455630994635e-010))*x+(-2.4699424727714359e-009))*x+(1.0326758707416653e-008))*x+(-2.2456077735840312e-006))*x+(9.9897827883536447e-005))*x+(-0.0032000495702684678))*x+(0.13473666765063053));
		wts[1] = (((((((((((((1.1065518871570626e-010))*x+(3.0316490059097605e-012))*x+(-8.2290322704163061e-011))*x+(6.442254137558243e-013))*x+(2.0174676744015109e-011))*x+(1.1525003174028823e-011))*x+(-6.1656997285552953e-009))*x+(1.8258301093254659e-007))*x+(-3.3364122994603935e-006))*x+(5.8486175376237792e-005))*x+(-0.0013434945504081752))*x+(0.053137736033809523));
		wts[2] = (((((((((((((1.0307606620093186e-011))*x+(-5.6843418860808015e-013))*x+(-6.821210263296961e-012))*x+(1.7574090331133143e-012))*x+(-4.4633926184663632e-012))*x+(5.07545117045538e-011))*x+(-3.92820243000358e-009))*x+(9.7410804774285723e-008))*x+(-1.3697645092440127e-006))*x+(1.5026407346725376e-005))*x+(-0.00021903896756222545))*x+(0.0075538928824363527));
		wts[3] = (((((((((((((9.6160116906200212e-013))*x+(2.9605947323337504e-014))*x+(-7.2741812573440246e-013))*x+(2.920626703447245e-013))*x+(-2.6955844963557256e-012))*x+(3.4561709975437311e-011))*x+(-7.1530959512104241e-010))*x+(1.2394404069633141e-008))*x+(-1.4525331003752083e-007))*x+(1.2294586310891225e-006))*x+(-1.1325352918538771e-005))*x+(0.00030467237292286335));
		wts[4] = (((((((((((((-8.1416355139178143e-016))*x+(-1.0177044392397268e-015))*x+(-1.3230157710116448e-015))*x+(2.3673193035496826e-014))*x+(-2.5969041731836262e-013))*x+(2.7686913092045407e-012))*x+(-3.0831335784467035e-011))*x+(3.3110673570238759e-010))*x+(-2.9250711012570015e-009))*x+(1.9350230324720237e-008))*x+(-1.106411079307097e-007))*x+(1.8146831388573498e-006));
		break;
	case 21:
		rts[0] = (((((((((((((5.6085506609330569e-012))*x+(-1.6295113406764963e-012))*x+(-4.1400956736955168e-012))*x+(9.6870659641960312e-013))*x+(-2.3453831469547976e-012))*x+(2.7576311604586106e-011))*x+(1.1911849284729212e-010))*x+(2.6660891827567923e-009))*x+(-3.1605826509434332e-007))*x+(1.0399231534357137e-005))*x+(-0.00025075844546743596))*x+(0.0054873115925355882));
		rts[1] = (((((((((((((4.2139921182145671e-011))*x+(-1.3642420526593924e-012))*x+(-2.2832106575757884e-011))*x+(1.0610771520684163e-012))*x+(-3.2997604648699053e-011))*x+(2.6645648650476989e-010))*x+(1.3391365794035437e-009))*x+(3.6696076029703782e-008))*x+(-3.4880672949757123e-006))*x+(0.00010869089326962648))*x+(-0.0025079935929875007))*x+(0.052487270870724384));
		rts[2] = (((((((((((((2.1221543041368324e-010))*x+(-1.152026622245709e-011))*x+(-1.2316074086508402e-010))*x+(9.9286504943544661e-012))*x+(-1.2234598519474579e-010))*x+(7.8128673900816159e-010))*x+(5.611657212985695e-009))*x+(2.3495755889039552e-007))*x+(-1.5305000574727945e-005))*x+(0.00042273127222172691))*x+(-0.0088318492977646629))*x+(0.16711365145546084));
		rts[3] = (((((((((((((2.1827872842550278e-010))*x+(-3.0316490059097604e-011))*x+(-1.2278178473934531e-010))*x+(4.1836756281554692e-011))*x+(-4.4599346438189968e-010))*x+(3.0479914888322429e-010))*x+(1.3539970922238354e-008))*x+(1.7933862235253173e-006))*x+(-7.1052908605132942e-005))*x+(0.0015702220269102432))*x+(-0.02713963808068837))*x+(0.42348582972472287));
		rts[4] = (((((((((((((1.57160684466362e-009))*x+(2.4253192047278084e-011))*x+(-1.0065074699620407e-009))*x+(-2.2191670723259446e-010))*x+(6.9686241962093236e-009))*x+(-5.9069350299978396e-008))*x+(-8.4276498076481709e-007))*x+(3.7801585721789856e-005))*x+(-0.00073662664867146788))*x+(0.010286070060792888))*x+(-0.11782119476284157))*x+(1.2068128926012416));
		wts[0] = (((((((((((((1.5400776950021583e-010))*x+(2.4253192047278085e-012))*x+(-9.6633812063373612e-011))*x+(-5.1538033100465928e-012))*x+(-6.0727719149629917e-012))*x+(3.3971048196690385e-010))*x+(6.9901714046712485e-011))*x+(4.7355899942166007e-009))*x+(-2.2197270553303557e-006))*x+(9.3205336372266981e-005))*x+(-0.0030069589214175652))*x+(0.13163427863748817));
		wts[1] = (((((((((((((9.3677954282611609e-011))*x+(-1.152026622245709e-011))*x+(-6.0235076186169564e-011))*x+(8.1286088970955461e-012))*x+(2.0795217399912264e-011))*x+(3.2651807183962468e-011))*x+(-6.0589167016900083e-009))*x+(1.5197155608011787e-007))*x+(-2.6674685187216829e-006))*x+(4.9510977698979934e-005))*x+(-0.0012358318532344672))*x+(0.051849567677298217));
		wts[2] = (((((((((((((-1.7053025658242404e-012))*x+(2.6716406864579767e-012))*x+(8.6923061341318929e-013))*x+(-1.1202890467150914e-012))*x+(2.0552448631860898e-012))*x+(4.1900038993958326e-011))*x+(-3.679785282040271e-009))*x+(7.8412343534894888e-008))*x+(-1.0185223791285788e-006))*x+(1.1462971368191311e-005))*x+(-0.00019272516990321632))*x+(0.0073486040866115893));
		wts[3] = (((((((((((((1.3666105284452592e-012))*x+(1.2079226507921703e-013))*x+(-8.9543187679434289e-013))*x+(9.0890258282646132e-014))*x+(-9.0118653280531658e-013))*x+(2.128861901577276e-011))*x+(-5.5399666740637199e-010))*x+(9.2541121420967408e-009))*x+(-1.0222305974079674e-007))*x+(8.6137782054055497e-007))*x+(-9.2560050026196539e-006))*x+(0.00029444293639907976));
		wts[4] = (((((((((((((5.2735593669694936e-015))*x+(1.2813824075882014e-015))*x+(-4.2893929149319847e-015))*x+(1.0793449467527692e-014))*x+(-1.2543192757600666e-013))*x+(1.4716655086406683e-012))*x+(-1.8574177257564027e-011))*x+(2.1080989603565253e-010))*x+(-1.8615124148028397e-009))*x+(1.229001078040976e-008))*x+(-7.9530625304396605e-008))*x+(1.7207699961130993e-006));
		break;
	case 22:
		rts[0] = (((((((((((((2.622376390111943e-011))*x+(-1.8947806286936004e-014))*x+(-1.8474111129762602e-011))*x+(4.2632564145606011e-014))*x+(2.0315601053274195e-012))*x+(5.8685648933002686e-012))*x+(2.1674151362560679e-010))*x+(3.5624199793785985e-009))*x+(-3.0376370826340487e-007))*x+(9.4685911392492755e-006))*x+(-0.00023089675385552325))*x+(0.0052466391300113298));
		rts[1] = (((((((((((((7.6094390048334987e-011))*x+(-1.2126596023639042e-012))*x+(-4.9283244152320542e-011))*x+(1.5916157281026244e-012))*x+(-1.6029844118747857e-011))*x+(3.7331915336835664e-011))*x+(2.2154288033722951e-009))*x+(4.6161583444614962e-008))*x+(-3.323802670813595e-006))*x+(9.8463507247810903e-005))*x+(-0.0023009211801580886))*x+(0.050084518369508946));
		rts[2] = (((((((((((((2.0251415359477201e-010))*x+(-1.2126596023639042e-012))*x+(-1.2770821437394866e-010))*x+(7.4275400644789134e-012))*x+(-6.8287893858117358e-011))*x+(-8.2697700539332202e-011))*x+(7.5315898702873093e-009))*x+(2.69997093127472e-007))*x+(-1.429823331968357e-005))*x+(0.00037829094661630719))*x+(-0.0080313301508493657))*x+(0.15868946964079619));
		rts[3] = (((((((((((((4.7778788333137823e-010))*x+(-7.2759576141834259e-012))*x+(-2.7512214728631074e-010))*x+(3.8198777474462986e-011))*x+(-1.5491726420198879e-010))*x+(-2.0725963167933514e-009))*x+(7.3192030214386242e-009))*x+(1.8514918842527095e-006))*x+(-6.375248008487025e-005))*x+(0.0013679546491439654))*x+(-0.024205112699332759))*x+(0.39784716755781879));
		rts[4] = (((((((((((((8.8281619052092231e-010))*x+(9.7012768189112337e-011))*x+(-4.9658410716801871e-010))*x+(-3.1225984760870529e-010))*x+(4.8896708904067046e-009))*x+(-1.8349472460007142e-008))*x+(-1.0681783943293035e-006))*x+(3.2922349288829381e-005))*x+(-0.00059480535801551915))*x+(0.0082938216862561767))*x+(-0.099312250904886323))*x+(1.0985780475504099));
		wts[0] = (((((((((((((1.6249638671676317e-010))*x+(-1.2126596023639042e-012))*x+(-1.0550138540565968e-010))*x+(-5.3053857603420807e-013))*x+(-1.2979247306551153e-012))*x+(1.4876870106187806e-010))*x+(1.52087054061667e-009))*x+(9.2006147885588981e-009))*x+(-2.1942710617025205e-006))*x+(8.6579778274975538e-005))*x+(-0.0028271862931198758))*x+(0.12871831044329762));
		wts[1] = (((((((((((((-1.5764574830730755e-011))*x+(7.4275400644789134e-012))*x+(1.8189894035458565e-011))*x+(-4.1874651894128566e-012))*x+(1.6105635343895614e-012))*x+(9.29976096131213e-011))*x+(-5.6801257031224842e-009))*x+(1.2247781921992382e-007))*x+(-2.1191964732492075e-006))*x+(4.236050325060145e-005))*x+(-0.0011442344457646585))*x+(0.050660725289017682));
		wts[2] = (((((((((((((-6.442254137558241e-013))*x+(-7.9580786405131221e-013))*x+(1.9682033780554775e-012))*x+(4.5474735088646412e-013))*x+(3.23770639928019e-012))*x+(6.694778065252649e-011))*x+(-3.360702595841166e-009))*x+(6.0745361888751376e-008))*x+(-7.4073621269115742e-007))*x+(8.8417637238580541e-006))*x+(-0.00017255927506959888))*x+(0.0071663981425349934));
		wts[3] = (((((((((((((2.5105843330190203e-013))*x+(7.1054273576010019e-014))*x+(-1.9007018181582677e-013))*x+(-5.6251299914341286e-015))*x+(-2.9700316280430644e-013))*x+(1.672184612999672e-011))*x+(-4.4267517198178408e-010))*x+(6.7736788180820327e-009))*x+(-7.0352100034548726e-008))*x+(6.0499329479346315e-007))*x+(-7.8055509427886313e-006))*x+(0.00028595480660501601));
		wts[4] = (((((((((((((3.9135361618036768e-015))*x+(2.0816681711721685e-016))*x+(-2.8617154942030729e-015))*x+(5.1417203827952562e-015))*x+(-6.0712864134263939e-014))*x+(8.4427493569789547e-013))*x+(-1.1852786608375788e-011))*x+(1.3629685603750016e-010))*x+(-1.1784261117758487e-009))*x+(7.8043064210511543e-009))*x+(-5.9776741739973998e-008))*x+(1.6518614609496592e-006));
		break;
	case 23:
		rts[0] = (((((((((((((2.8421709430404007e-012))*x+(3.808509063674137e-012))*x+(-1.5466146881711515e-012))*x+(-2.5224267119483557e-012))*x+(-1.1202890467150912e-012))*x+(-7.8210771192743778e-012))*x+(2.0473138924910947e-010))*x+(4.6531691000328834e-009))*x+(-2.8731004315188841e-007))*x+(8.5808825074238388e-006))*x+(-0.00021285550935617163))*x+(0.0050249109865461022));
		rts[1] = (((((((((((((4.0624096679190792e-011))*x+(2.1221543041368323e-012))*x+(-2.3457384183226772e-011))*x+(-6.2527760746888796e-013))*x+(-8.8154668749969752e-012))*x+(-1.0422359271918442e-010))*x+(1.9628410008465376e-009))*x+(5.696582953499766e-008))*x+(-3.1171087238324184e-006))*x+(8.8791264747760848e-005))*x+(-0.0021137697997561139))*x+(0.047878785283496005));
		rts[2] = (((((((((((((2.3161798405150572e-010))*x+(3.092281986027956e-011))*x+(-1.4665602066088465e-010))*x+(-1.39455854271849e-011))*x+(-4.6706342497297295e-012))*x+(-5.4104750309610005e-010))*x+(5.4355178136233917e-009))*x+(3.0358318673743645e-007))*x+(-1.3147509161944477e-005))*x+(0.00033708851529506051))*x+(-0.0073165264102696623))*x+(0.1510224095626676));
		rts[3] = (((((((((((((4.0017766878008842e-010))*x+(-8.3673512563109398e-011))*x+(-2.6542087046739954e-010))*x+(7.0334256937106446e-011))*x+(6.7984728957526386e-011))*x+(-2.7247845461412603e-009))*x+(-7.7951257300886319e-009))*x+(1.8519080130137884e-006))*x+(-5.6320241876887479e-005))*x+(0.0011878448360969629))*x+(-0.021653031888014675))*x+(0.37494811359511321));
		rts[4] = (((((((((((((1.8335413187742233e-009))*x+(-9.7012768189112337e-011))*x+(-1.1768861440941691e-009))*x+(-1.6795335492740074e-010))*x+(3.0591612206383916e-009))*x+(8.0467543739359809e-009))*x+(-1.0920054928457526e-006))*x+(2.745600128406522e-005))*x+(-0.00047401134871168549))*x+(0.0066960761600676948))*x+(-0.084382753692046106))*x+(1.0069966533334944));
		wts[0] = (((((((((((((1.5764574830730754e-010))*x+(9.701276818911234e-012))*x+(-1.0156024169797698e-010))*x+(-6.1390892369672648e-012))*x+(6.5654148784233257e-012))*x+(-3.7895612573871875e-014))*x+(1.9276621780287919e-009))*x+(1.8208964410367418e-008))*x+(-2.1401186769779792e-006))*x+(8.0069109780311898e-005))*x+(-0.0026605644149742115))*x+(0.1259755205045309));
		wts[1] = (((((((((((((5.3357022504011788e-011))*x+(-1.6522487082208194e-011))*x+(-3.3651303965598338e-011))*x+(1.1596057447604833e-011))*x+(1.1937117960769682e-011))*x+(1.3612163248429471e-010))*x+(-4.9743581106061656e-009))*x+(9.5722917962485582e-008))*x+(-1.6839786077064525e-006))*x+(3.6682519639098798e-005))*x+(-0.0010654089132731716))*x+(0.049556849047127011));
		wts[2] = (((((((((((((1.1292892547013858e-011))*x+(-2.9179621681881445e-012))*x+(-6.6269952488558667e-012))*x+(1.5395092608135501e-012))*x+(3.744560217455728e-012))*x+(9.1510058789860211e-011))*x+(-2.8778664821575242e-009))*x+(4.5085923198554902e-008))*x+(-5.2988090758325957e-007))*x+(6.9515101338574426e-006))*x+(-0.00015687134805211916))*x+(0.0070019973506559195));
		wts[3] = (((((((((((((8.4080890398278519e-013))*x+(1.3974007136615302e-013))*x+(-5.1706787000208954e-013))*x+(-9.1482377229112886e-014))*x+(-7.893685705084863e-014))*x+(1.5110884765690002e-011))*x+(-3.4778975243713684e-010))*x+(4.8014716230726506e-009))*x+(-4.7359780764008999e-008))*x+(4.3039690578205222e-007))*x+(-6.7816411098997637e-006))*x+(0.00027869024427339936));
		wts[4] = (((((((((((((2.1279274638648832e-016))*x+(2.3129646346357426e-017))*x+(-2.318747046222332e-016))*x+(2.2979303645106106e-015))*x+(-3.189607143220622e-014))*x+(5.3272879091288228e-013))*x+(-7.8236228959967619e-012))*x+(8.7877507026764269e-011))*x+(-7.3675886531472595e-010))*x+(4.9797945953582061e-009))*x+(-4.7212807637089401e-008))*x+(1.5988358315685974e-006));
		break;
	case 24:
		rts[0] = (((((((((((((6.7454190381492172e-012))*x+(-9.8528592692067219e-013))*x+(-4.6895820560166612e-012))*x+(6.3238303482648906e-013))*x+(8.7781633813695704e-013))*x+(-1.4262665123017843e-011))*x+(1.3277134947031752e-010))*x+(5.5114495559986186e-009))*x+(-2.6685963095199328e-007))*x+(7.7487669698482944e-006))*x+(-0.00019653609724460856))*x+(0.0048203538979088665));
		rts[1] = (((((((((((((5.1538033100465931e-011))*x+(3.9411437076826888e-012))*x+(-3.156704527403538e-011))*x+(-1.3263464400855201e-012))*x+(4.8032688937382764e-012))*x+(-1.5446606956478112e-010))*x+(1.1421605883299435e-009))*x+(6.4854092022651827e-008))*x+(-2.8720877073007411e-006))*x+(7.9799557249677716e-005))*x+(-0.001945301626927182))*x+(0.045850748452181983));
		rts[2] = (((((((((((((2.27980005244414e-010))*x+(-1.6977234433094658e-011))*x+(-1.4521598738307753e-010))*x+(1.4021376652332642e-011))*x+(3.7497708641846352e-011))*x+(-6.4636177891467617e-010))*x+(1.7158766259702438e-009))*x+(3.2171607777797812e-007))*x+(-1.1890660728634355e-005))*x+(0.00029951308071117044))*x+(-0.0066805538655566729))*x+(0.14403013260383288));
		rts[3] = (((((((((((((2.6921043172478676e-010))*x+(1.9402553637822468e-011))*x+(-1.5112770294460159e-010))*x+(-6.821210263296961e-012))*x+(1.432454155292362e-010))*x+(-2.2099963340830677e-009))*x+(-2.2959094181373985e-008))*x+(1.7737540728054075e-006))*x+(-4.9043510413941206e-005))*x+(0.0010298776196050092))*x+(-0.019438950344439675))*x+(0.35442844773084548));
		rts[4] = (((((((((((((1.3872825851043065e-009))*x+(-6.305829932292302e-011))*x+(-8.7493390310555686e-010))*x+(-1.2975457745293778e-010))*x+(1.4141884700317555e-009))*x+(2.1747249926799363e-008))*x+(-9.9704997798729278e-007))*x+(2.2199408545494254e-005))*x+(-0.00037486061692589467))*x+(0.0054280315994773929))*x+(-0.072308205211225815))*x+(0.92886233909862204));
		wts[0] = (((((((((((((6.5483618527650833e-011))*x+(1.7583564234276612e-011))*x+(-3.8350359924758472e-011))*x+(-1.0269711007519314e-011))*x+(2.2737367544323206e-013))*x+(-8.1605833202047493e-011))*x+(1.6370401330808211e-009))*x+(2.7332496858415802e-008))*x+(-2.0485362538513736e-006))*x+(7.3776962705135438e-005))*x+(-0.0025067641841102517))*x+(0.12339290520223886));
		wts[1] = (((((((((((((1.0307606620093186e-010))*x+(3.0316490059097606e-013))*x+(-6.5862574653389545e-011))*x+(-1.2505552149377761e-012))*x+(1.5404566511278969e-011))*x+(1.5697902237358599e-010))*x+(-4.0719365657082562e-009))*x+(7.3068628777169423e-008))*x+(-1.3479067642596654e-006))*x+(3.2157354067636569e-005))*x+(-0.00099673692416149193))*x+(0.048526529567130758));
		wts[2] = (((((((((((((-3.4863963567962246e-012))*x+(4.2632564145606011e-012))*x+(3.1169141342009725e-012))*x+(-2.9369099744750806e-012))*x+(-1.0527874868178817e-012))*x+(1.0093015312406804e-010))*x+(-2.2916167112067382e-009))*x+(3.2140934571230531e-008))*x+(-3.7640702257174524e-007))*x+(5.6050273535155366e-006))*x+(-0.00014439144939177375))*x+(0.0068515899340344929));
		wts[3] = (((((((((((((8.1001871876651421e-013))*x+(1.0421293457814802e-013))*x+(-5.3024251656097476e-013))*x+(-7.6679403567444141e-014))*x+(-1.4928798937792937e-013))*x+(1.3538753451669548e-011))*x+(-2.6163812204734366e-010))*x+(3.2818454123266041e-009))*x+(-3.1336833758313983e-008))*x+(3.1387083418414586e-007))*x+(-6.0453704696976444e-006))*x+(0.00027229610887821818));
		wts[4] = (((((((((((((2.5997722493305746e-015))*x+(1.4941751539746897e-015))*x+(-1.6832600128561617e-015))*x+(1.4224732503009818e-016))*x+(-1.8908485888147194e-014))*x+(3.6009066460678435e-013))*x+(-5.1893467844060845e-012))*x+(5.5774098345698093e-011))*x+(-4.538317072361138e-010))*x+(3.2259265948171535e-009))*x+(-3.9148113033720495e-008))*x+(1.5559466165246788e-006));
		break;
	case 25:
		rts[0] = (((((((((((((2.1183647428794451e-011))*x+(1.6863547595373043e-012))*x+(-1.4596916268298323e-011))*x+(-9.9002287849240612e-013))*x+(3.9959147102308634e-012))*x+(-1.3469447779357323e-011))*x+(4.6663034547478333e-011))*x+(5.9599688980357018e-009))*x+(-2.4377294242869846e-007))*x+(6.9823698155682098e-006))*x+(-0.00018181651821165166))*x+(0.0046313053379778832));
		rts[1] = (((((((((((((7.3062741042425231e-011))*x+(3.0316490059097606e-013))*x+(-4.9093766089451187e-011))*x+(3.6000831945178408e-013))*x+(1.6129320101754274e-011))*x+(-1.4246026580622129e-010))*x+(2.2706244292199546e-010))*x+(6.8248377319927528e-008))*x+(-2.6043510886429124e-006))*x+(7.1581511491331879e-005))*x+(-0.0017940545799564711))*x+(0.043982440135851703));
		rts[2] = (((((((((((((1.8432425955931345e-010))*x+(-6.063298011819521e-012))*x+(-1.1444474997309345e-010))*x+(2.8042753304665285e-012))*x+(4.9557987343481117e-011))*x+(-5.2504371221099677e-010))*x+(-1.8610908369964816e-009))*x+(3.2106165281930993e-007))*x+(-1.0599119406743776e-005))*x+(0.00026577912567882217))*x+(-0.0061159080294394368))*x+(0.13763752395745099));
		rts[3] = (((((((((((((3.2256745422879851e-010))*x+(2.9103830456733704e-011))*x+(-1.9387395392792919e-010))*x+(-2.2737367544323206e-011))*x+(1.7742725807086873e-010))*x+(-1.2724778268117611e-009))*x+(-3.3506384629807449e-008))*x+(1.6302408477978738e-006))*x+(-4.2217919983230288e-005))*x+(0.00089312946069974863))*x+(-0.017519357820131778))*x+(0.33597208020204067));
		rts[4] = (((((((((((((1.1835557719071705e-009))*x+(1.2126596023639042e-011))*x+(-7.4336033624907328e-010))*x+(-1.088361993121604e-010))*x+(3.7228649792571861e-010))*x+(2.6414937792651472e-008))*x+(-8.4903252191755496e-007))*x+(1.7572798823787629e-005))*x+(-0.00029556406753261655))*x+(0.004427023463991115))*x+(-0.062492773585516345))*x+(0.86162853006055473));
		wts[0] = (((((((((((((2.304053244491418e-010))*x+(9.701276818911234e-012))*x+(-1.4536756983337301e-010))*x+(-4.8885340220294893e-012))*x+(3.2078636043782652e-011))*x+(-1.0652930389672595e-010))*x+(1.0357350532785856e-009))*x+(3.4080234634359385e-008))*x+(-1.9247041662303244e-006))*x+(6.7810343092796391e-005))*x+(-0.0023652388952587313))*x+(0.12095789832460935));
		wts[1] = (((((((((((((3.637978807091713e-012))*x+(-1.0156024169797698e-011))*x+(4.6232647340123849e-012))*x+(5.2674901477682088e-012))*x+(-6.2480391231171471e-012))*x+(1.4640910706020802e-010))*x+(-3.1467847586933808e-009))*x+(5.5047651104089823e-008))*x+(-1.0932161646493019e-006))*x+(2.8513685895036053e-005))*x+(-0.00093619307522006573))*x+(0.047560671244996813));
		wts[2] = (((((((((((((1.9705718538413444e-012))*x+(5.3053857603420807e-013))*x+(-7.2001663890356815e-013))*x+(-4.2869411724192703e-013))*x+(-1.949847690715008e-012))*x+(9.2528651407519646e-011))*x+(-1.7065705145332304e-009))*x+(2.2165166498518588e-008))*x+(-2.6877218988150908e-007))*x+(4.6472303350299678e-006))*x+(-0.00013419291127490451))*x+(0.0067124570542019596));
		wts[3] = (((((((((((((5.139592455331391e-013))*x+(-6.6317322004276009e-014))*x+(-2.7015426932545472e-013))*x+(3.4638958368304878e-014))*x+(-3.1583994678877997e-013))*x+(1.1275517556678475e-011))*x+(-1.8688948710358458e-010))*x+(2.1661811939096181e-009))*x+(-2.0565446688954797e-008))*x+(2.3713195352884189e-007))*x+(-5.4997409048047772e-006))*x+(0.00026653630586914289));
		wts[4] = (((((((((((((7.586524001605236e-016))*x+(6.9388939039072284e-017))*x+(-5.4470317145671733e-016))*x+(4.9555267297070783e-016))*x+(-1.3203414056528471e-014))*x+(2.4813110550622736e-013))*x+(-3.3857383720638581e-012))*x+(3.4614897200298225e-011))*x+(-2.7605286547402664e-010))*x+(2.1522033589847389e-009))*x+(-3.3858572874450433e-008))*x+(1.5196215247824191e-006));
		break;
	case 26:
		rts[0] = (((((((((((((4.5474735088646412e-013))*x+(-2.6905884927449124e-012))*x+(5.9211894646675012e-013))*x+(1.6721439048221021e-012))*x+(1.1812772982011666e-013))*x+(-1.057953724625804e-011))*x+(-2.5394297775704899e-011))*x+(6.00518679227946e-009))*x+(-2.1972149443633127e-007))*x+(6.2870847278706276e-006))*x+(-0.0001685591015330488))*x+(0.0044562334103754398));
		rts[1] = (((((((((((((7.2456411241243274e-011))*x+(-7.1243751638879376e-012))*x+(-4.5038935544046879e-011))*x+(4.2253608019867288e-012))*x+(1.6119846198610805e-011))*x+(-1.0271072881096188e-010))*x+(-5.1221922999407832e-010))*x+(6.7437980755258309e-008))*x+(-2.3317436870923247e-006))*x+(6.4178200253078396e-005))*x+(-0.0016584312954971716))*x+(0.042257431055336261));
		rts[2] = (((((((((((((1.7704830194513002e-010))*x+(-1.7583564234276612e-011))*x+(-1.0641088010743259e-010))*x+(1.1217101321866114e-011))*x+(4.9936943469219835e-011))*x+(-3.3380113488116575e-010))*x+(-4.4400808955439662e-009))*x+(3.0482922674934798e-007))*x+(-9.343035835181663e-006))*x+(0.00023588222360118591))*x+(-0.0056148751523027911))*x+(0.13177711463782132));
		rts[3] = (((((((((((((3.6622319991389907e-010))*x+(7.0334256937106446e-011))*x+(-2.2449360888761777e-010))*x+(-5.1538033100465925e-011))*x+(1.5738047901929045e-010))*x+(-3.7821716129352956e-010))*x+(-3.8411458902487539e-008))*x+(1.4482317330551569e-006))*x+(-3.6052829848901943e-005))*x+(0.00077590579120571479))*x+(-0.015853405926121139))*x+(0.31930522951892937));
		rts[4] = (((((((((((((9.0706938256820036e-010))*x+(1.0913936421275139e-010))*x+(-5.4236200715725614e-010))*x+(-1.1641532182693481e-010))*x+(-2.2252303703377643e-010))*x+(2.5746762351748959e-008))*x+(-6.9073315837423844e-007))*x+(1.3725258032337706e-005))*x+(-0.00023323239286043848))*x+(0.0036376759392800309))*x+(-0.054459213548844435))*x+(0.80328396618067788));
		wts[0] = (((((((((((((2.0493947279949981e-010))*x+(-2.4859521848460037e-011))*x+(-1.3043669847926745e-010))*x+(1.493087135410557e-011))*x+(3.2334431428656288e-011))*x+(-9.7763575013232185e-011))*x+(4.1750099673739283e-010))*x+(3.7695319162385957e-008))*x+(-1.78011863710692e-006))*x+(6.2249500280377651e-005))*x+(-0.0022352514483036756))*x+(0.11865858008014779));
		wts[1] = (((((((((((((7.7610214551289872e-011))*x+(3.7895612573872005e-012))*x+(-5.5176011907557644e-011))*x+(-2.633745073884104e-012))*x+(1.0189182830799837e-011))*x+(1.233804169942232e-010))*x+(-2.3340408124757533e-009))*x+(4.1409507304616483e-008))*x+(-9.016616742870317e-007))*x+(2.5534994738833642e-005))*x+(-0.00088224003571522294))*x+(0.046651950684045318));
		wts[2] = (((((((((((((8.4886172165473291e-012))*x+(1.7053025658242404e-012))*x+(-5.9875067866717773e-012))*x+(-1.3452942463724562e-012))*x+(-1.2706872591176457e-012))*x+(7.567975875607165e-011))*x+(-1.200609241654623e-009))*x+(1.4940736832909824e-008))*x+(-1.9540471535295365e-007))*x+(3.9581806940419909e-006))*x+(-0.0001256240995019334))*x+(0.0065826631500206382));
		wts[3] = (((((((((((((-2.6053233644537005e-013))*x+(-8.5265128291212022e-014))*x+(2.1227464230832993e-013))*x+(5.6991448597424707e-014))*x+(-4.3731684939984916e-013))*x+(8.6655220036628098e-012))*x+(-1.2694283934207756e-010))*x+(1.3881214898601537e-009))*x+(-1.3556756421805616e-008))*x+(1.8672539998386097e-007))*x+(-5.0793779047255035e-006))*x+(0.00026125512168368473));
		wts[4] = (((((((((((((-4.4408920985006262e-016))*x+(-8.3266726846886741e-017))*x+(3.8163916471489756e-016))*x+(4.4408920985006262e-016))*x+(-9.8357375484988304e-015))*x+(1.6827392344126446e-013))*x+(-2.1490735352316239e-012))*x+(2.0977049474808367e-011))*x+(-1.6692584354860334e-010))*x+(1.5013333363841425e-009))*x+(-3.0259394183275754e-008))*x+(1.487670566891158e-006));
		break;
	case 27:
		rts[0] = (((((((((((((5.5706550483591855e-012))*x+(-2.6526928801710406e-012))*x+(-3.730349362740526e-012))*x+(1.4897712693103433e-012))*x+(1.4699352846037073e-012))*x+(-6.4776332446096295e-012))*x+(-7.4760022246896554e-011))*x+(5.7446520225952931e-009))*x+(-1.9613999856863315e-007))*x+(5.6635550557734135e-006))*x+(-0.00015662026067853814))*x+(0.0042937476421004307));
		rts[1] = (((((((((((((6.6999443030605705e-011))*x+(-9.2465294680247699e-012))*x+(-4.2803094402188429e-011))*x+(5.0969598911857848e-012))*x+(1.5551412010002725e-011))*x+(-5.8918795768173966e-011))*x+(-9.8946517645970268e-010))*x+(6.3577799099453117e-008))*x+(-2.0689179560523518e-006))*x+(5.7581090006588821e-005))*x+(-0.0015368034975004395))*x+(0.040660913047485626));
		rts[2] = (((((((((((((2.1464074961841106e-010))*x+(-1.152026622245709e-011))*x+(-1.401379752981787e-010))*x+(6.063298011819521e-012))*x+(5.5318120454709664e-011))*x+(-1.5128639082225467e-010))*x+(-5.8648964203674341e-009))*x+(2.7862431621154349e-007))*x+(-8.1737637704359916e-006))*x+(0.00020963331975279442))*x+(-0.0051699444812146576))*x+(0.12638907876054445));
		rts[3] = (((((((((((((3.2984341184298194e-010))*x+(4.1230426480372742e-011))*x+(-2.0493947279949981e-010))*x+(-3.213547946264346e-011))*x+(1.1440685436051959e-010))*x+(2.5307637467146077e-010))*x+(-3.8695281053454288e-008))*x+(1.253893334052236e-006))*x+(-3.0648151713534112e-005))*x+(0.00067604897549707521))*x+(-0.014404153538919219))*x+(0.30419308609591794));
		rts[4] = (((((((((((((8.8766682893037796e-010))*x+(8.7311491370201111e-011))*x+(-5.3266073033834494e-010))*x+(-6.972792713592449e-011))*x+(-4.4095334790957464e-010))*x+(2.2509880182042249e-008))*x+(-5.4530036545467431e-007))*x+(1.0643368717921929e-005))*x+(-0.00018473777089108207))*x+(0.0030138009462102504))*x+(-0.047831959700114113))*x+(0.75224225607003836));
		wts[0] = (((((((((((((1.7280399333685637e-010))*x+(-1.546140993013978e-011))*x+(-1.104657106528369e-010))*x+(8.7159908919905628e-012))*x+(2.9198569488168381e-011))*x+(-6.9743322228532634e-011))*x+(-7.4026266598063259e-011))*x+(3.8499310554366652e-008))*x+(-1.6269094674133584e-006))*x+(5.7138167256762233e-005))*x+(-0.0021159404674374526))*x+(0.1164838360372758));
		wts[1] = (((((((((((((1.1004885891452432e-010))*x+(1.3794002976889411e-011))*x+(-7.0201622293097898e-011))*x+(-8.0528176719478016e-012))*x+(1.1558161835030964e-011))*x+(9.5639644352255943e-011))*x+(-1.683358267593841e-009))*x+(3.1445581472055999e-008))*x+(-7.5703528018093258e-007))*x+(2.305689852259013e-005))*x+(-0.00083372034726273921))*x+(0.045794383177154188));
		wts[2] = (((((((((((((-3.0316490059097606e-013))*x+(2.5011104298755527e-012))*x+(1.3073986337985843e-012))*x+(-1.6318798164623634e-012))*x+(-3.3845518980039438e-012))*x+(5.6334492626319837e-011))*x+(-8.0681631745941707e-010))*x+(9.9708437617529455e-009))*x+(-1.4623716444265672e-007))*x+(3.4506780321926409e-006))*x+(-0.00011823975898985044))*x+(0.0064608156393526073));
		wts[3] = (((((((((((((3.3158661002138004e-014))*x+(-3.5527136788005009e-014))*x+(-1.7763568394002505e-015))*x+(3.907985046680551e-014))*x+(-3.3463972333909925e-013))*x+(6.1905388223001028e-012))*x+(-8.2482937147076996e-011))*x+(8.7073635743802514e-010))*x+(-9.1130996803344168e-009))*x+(1.5323675968096701e-007))*x+(-4.7416301701041067e-006))*x+(0.00025635018189931069));
		wts[4] = (((((((((((((-2.248201624865942e-015))*x+(-7.6790425869906654e-016))*x+(1.3259069768049396e-015))*x+(7.8640797577615242e-016))*x+(-7.2244004759950774e-015))*x+(1.1026231287967572e-013))*x+(-1.3227288933755595e-012))*x+(1.2442075812018649e-011))*x+(-1.0146165348639093e-010))*x+(1.1072581617656582e-009))*x+(-2.7683397511847228e-008))*x+(1.458764567116657e-006));
		break;
	case 28:
		rts[0] = (((((((((((((1.9137284349805363e-011))*x+(-2.3495279795800643e-012))*x+(-1.2744768203750329e-011))*x+(1.4258224230919341e-012))*x+(3.4227435700510491e-012))*x+(-3.1170621639375891e-012))*x+(-1.0146756583099639e-010))*x+(5.296610400273849e-009))*x+(-1.7401353214682264e-007))*x+(5.1087744810437291e-006))*x+(-0.00014585899876717347))*x+(0.0041426004607909512));
		rts[1] = (((((((((((((5.305385760342081e-011))*x+(-7.2759576141834259e-012))*x+(-3.2798652682686225e-011))*x+(3.7895612573872013e-012))*x+(1.1101046008358631e-011))*x+(-2.331764411186062e-011))*x+(-1.2249064725485444e-009))*x+(5.7957055747219023e-008))*x+(-1.8254573348613912e-006))*x+(5.1745165439413356e-005))*x+(-0.0014275990114117547))*x+(0.039179684258923229));
		rts[2] = (((((((((((((7.3972235744198159e-011))*x+(1.5764574830730755e-011))*x+(-4.1609382606111467e-011))*x+(-1.1141310096718369e-011))*x+(2.2500519965736502e-011))*x+(-1.5011399530825049e-011))*x+(-6.3363604733505481e-009))*x+(2.4779855056777933e-007))*x+(-7.1201365969275621e-006))*x+(0.00018672336071947254))*x+(-0.0047741146921452555))*x+(0.1214208664697029));
		rts[3] = (((((((((((((3.8562575355172157e-010))*x+(-6.427095892528692e-011))*x+(-2.4177400822130341e-010))*x+(3.2893391714120896e-011))*x+(8.7557812851931275e-011))*x+(6.007354613757342e-010))*x+(-3.6006142660009267e-008))*x+(1.0662619616870945e-006))*x+(-2.6012366533619449e-005))*x+(0.00059124601008625488))*x+(-0.013139175991557854))*x+(0.29043554889526263));
		rts[4] = (((((((((((((1.1447506646315255e-009))*x+(-3.3954468866189317e-011))*x+(-7.21532463406523e-010))*x+(2.2131037743141249e-011))*x+(-4.2261187142382067e-010))*x+(1.845965395356567e-008))*x+(-4.2231910413192958e-007))*x+(8.2344988901657708e-006))*x+(-0.00014718704670624305))*x+(0.0025183205625192162))*x+(-0.042318593050616679))*x+(0.70724947955949025));
		wts[0] = (((((((((((((1.5582675890376169e-010))*x+(-6.3664629124104977e-012))*x+(-9.6065377874765532e-011))*x+(3.6758744196655852e-012))*x+(2.3741601277530812e-011))*x+(-4.1712411302796681e-011))*x+(-3.9857317446490015e-010))*x+(3.7259753652800022e-008))*x+(-1.4748500680080341e-006))*x+(5.2486780915568056e-005))*x+(-0.0020063916031282233))*x+(0.11442344519108305));
		wts[1] = (((((((((((((-1.2126596023639042e-012))*x+(1.5309827479844291e-011))*x+(4.6990559591601295e-012))*x+(-1.019391978237157e-011))*x+(-5.7127635955112055e-012))*x+(7.0395245188592526e-011))*x+(-1.198226406984304e-009))*x+(2.4309371182695824e-008))*x+(-6.4632942044691899e-007))*x+(2.095897442261583e-005))*x+(-0.00078975974685133057))*x+(0.044982992546870292));
		wts[2] = (((((((((((((1.4476124003219107e-011))*x+(-2.5579538487363607e-012))*x+(-9.4881139981832039e-012))*x+(1.6318798164623634e-012))*x+(-8.8817841970012523e-015))*x+(3.8403576615072175e-011))*x+(-5.2486224625762168e-010))*x+(6.6849547656714732e-009))*x+(-1.1339544018010295e-007))*x+(3.0645064659359901e-006))*x+(-0.00011174094838034372))*x+(0.0063458895384733835));
		wts[3] = (((((((((((((4.9737991503207013e-014))*x+(1.9303077654816053e-013))*x+(-2.4720966014986821e-014))*x+(-1.0672944010063169e-013))*x+(-2.4957813593573519e-013))*x+(4.1890796387278328e-012))*x+(-5.1653614834464471e-011))*x+(5.4047795174557345e-010))*x+(-6.341967844580217e-009))*x+(1.3038339524329236e-007))*x+(-4.4593904548301291e-006))*x+(0.00025175346952094086));
		wts[4] = (((((((((((((-3.219646771412954e-015))*x+(8.1878948066105295e-016))*x+(2.2227590138849487e-015))*x+(-2.5037842169931917e-016))*x+(-5.3134580069169601e-015))*x+(6.9753212898991197e-014))*x+(-7.903001621901763e-013))*x+(7.2609217064612619e-012))*x+(-6.2940434670807232e-011))*x+(8.6581585993295223e-010))*x+(-2.5729495731841417e-008))*x+(1.4320981891410002e-006));
		break;
	case 29:
		rts[0] = (((((((((((((9.8528592692067215e-012))*x+(1.7242503721111764e-012))*x+(-6.7075234255753449e-012))*x+(-1.0018652574217413e-012))*x+(1.9332683602139391e-012))*x+(-2.6489921367556235e-013))*x+(-1.1062362137437276e-010))*x+(4.7616717513410123e-009))*x+(-1.538817246728626e-007))*x+(4.6174676384897265e-006))*x+(-0.00013614282407137387))*x+(0.0040016814159599652));
		rts[1] = (((((((((((((4.4262075486282505e-011))*x+(3.4863963567962246e-012))*x+(-2.9217517294455313e-011))*x+(-2.2358411418584483e-012))*x+(9.5402204654722774e-012))*x+(1.5010215292932116e-012))*x+(-1.2837368205490898e-009))*x+(5.1629366781824615e-008))*x+(-1.6061886854157324e-006))*x+(4.6604035785068054e-005))*x+(-0.0013293594540030717))*x+(0.03780206166967516));
		rts[2] = (((((((((((((1.5097612049430609e-010))*x+(9.0949470177292824e-012))*x+(-9.6520125225652009e-011))*x+(-6.4422541375582414e-012))*x+(2.9738581967346058e-011))*x+(6.4387014238794408e-011))*x+(-6.1764597880653582e-009))*x+(2.1632151891992635e-007))*x+(-6.1921728018536158e-006))*x+(0.00016678641383361764))*x+(-0.0044210688714211828))*x+(0.11682659646125043));
		rts[3] = (((((((((((((2.6678511252005893e-010))*x+(-1.9402553637822468e-011))*x+(-1.6037423241262633e-010))*x+(7.5791225147744009e-012))*x+(4.2102025569571801e-011))*x+(7.5368689067545347e-010))*x+(-3.1826557981654936e-008))*x+(8.9633268629540897e-007))*x+(-2.209416987179284e-005))*x+(0.00051925620669231632))*x+(-0.01203063217278361))*x+(0.27786263744590806));
		rts[4] = (((((((((((((7.5184895346562064e-010))*x+(8.2460852960745485e-011))*x+(-4.5019987737759943e-010))*x+(-4.1533591380963714e-011))*x+(-4.3261631314332288e-010))*x+(1.4576850541440459e-008))*x+(-3.2343119353110217e-007))*x+(6.3799340779269187e-006))*x+(-0.0001181229114737281))*x+(0.002122208234473769))*x+(-0.037692579851205651))*x+(0.66730985010418042));
		wts[0] = (((((((((((((5.2750692702829838e-011))*x+(3.1832314562052488e-011))*x+(-3.0202803221375994e-011))*x+(-1.8720432611492772e-011))*x+(8.1001871876651421e-012))*x+(-1.5680493940332475e-011))*x+(-5.7496925739049698e-010))*x+(3.4776568143731389e-008))*x+(-1.3304819406108799e-006))*x+(4.828127644429988e-005))*x+(-0.001905695759311657))*x+(0.11246810234400322));
		wts[1] = (((((((((((((-1.546140993013978e-011))*x+(-1.0307606620093186e-011))*x+(1.6238269987904154e-011))*x+(5.3432813729159526e-012))*x+(-8.5880931995537432e-012))*x+(4.6381861314633469e-011))*x+(-8.5560721470775048e-010))*x+(1.9223388510643719e-008))*x+(-5.5983252687796792e-007))*x+(1.9154807538131664e-005))*x+(-0.00074968915649890856))*x+(0.044213568620624907));
		wts[2] = (((((((((((((-3.7895612573872005e-012))*x+(-4.0169349328304325e-012))*x+(3.6474527102351804e-012))*x+(2.3897920679398031e-012))*x+(-2.8101965199311962e-012))*x+(2.4996301325093857e-011))*x+(-3.3401514887287931e-010))*x+(4.5710953725889656e-009))*x+(-9.1200244233905853e-008))*x+(2.7597201587223341e-006))*x+(-0.00010592778771261939))*x+(0.0062371058979991695));
		wts[3] = (((((((((((((5.6369723703634611e-013))*x+(-3.6711374680938505e-014))*x+(-3.4638958368304884e-013))*x+(2.8125649957170627e-014))*x+(-1.0497158697830854e-013))*x+(2.6556766045497211e-012))*x+(-3.1448718629256689e-011))*x+(3.3650025590044785e-010))*x+(-4.6216058923285773e-009))*x+(1.1414126281984319e-007))*x+(-4.2157226216159869e-006))*x+(0.00024741861324122609));
		wts[4] = (((((((((((((2.4517425127138872e-015))*x+(-3.1456319031046099e-016))*x+(-1.7387711640874195e-015))*x+(3.0068540250264653e-016))*x+(-2.6704622309766295e-015))*x+(4.2356164871767036e-014))*x+(-4.6013817801216058e-013))*x+(4.2028818260216612e-012))*x+(-4.0561317849887998e-011))*x+(7.1360767987103198e-010))*x+(-2.4161206980325046e-008))*x+(1.4071781045273939e-006));
		break;
	case 30:
		rts[0] = (((((((((((((9.4739031434680019e-012))*x+(1.0421293457814802e-012))*x+(-6.3190933966931571e-012))*x+(-9.0949470177292814e-013))*x+(1.6321758759355967e-012))*x+(1.2116974090758958e-012))*x+(-1.0870186232618076e-010))*x+(4.2106767147072804e-009))*x+(-1.3594020771672452e-007))*x+(4.1832863932412048e-006))*x+(-0.00012735104046889223))*x+(0.0038700068288319302));
		rts[1] = (((((((((((((5.6388671509921551e-011))*x+(1.8189894035458565e-012))*x+(-3.8843002888218812e-011))*x+(-1.8947806286936002e-012))*x+(1.0932884227562075e-011))*x+(1.5178377073728672e-011))*x+(-1.2324442207519344e-009))*x+(4.5309617095294165e-008))*x+(-1.4123979508266307e-006))*x+(4.2082482121577613e-005))*x+(-0.0012407698226554434))*x+(0.036517750412648625));
		rts[2] = (((((((((((((1.8250527015576759e-010))*x+(-9.3981119183202574e-012))*x+(-1.180448331676113e-010))*x+(4.5095778962907681e-012))*x+(3.0411229090532281e-011))*x+(1.0201854176254224e-010))*x+(-5.6619664512425061e-009))*x+(1.8663829134032045e-007))*x+(-5.3871172851956599e-006))*x+(0.00014944718148741004))*x+(-0.0041052377171795652))*x+(0.11256633204862737));
		rts[3] = (((((((((((((3.7592447673281032e-010))*x+(9.701276818911234e-012))*x+(-2.326790612035741e-010))*x+(-1.0156024169797698e-011))*x+(4.5001039931473003e-011))*x+(7.6865565764213295e-010))*x+(-2.7214448176475042e-008))*x+(7.4872310721711222e-007))*x+(-1.8811764339414044e-005))*x+(0.00045804491869453717))*x+(-0.011054971478746794))*x+(0.26633003258096621));
		rts[4] = (((((((((((((7.6640086869398749e-010))*x+(4.850638409455617e-012))*x+(-4.6262963830182946e-010))*x+(1.212659602363904e-012))*x+(-3.3924152376130218e-010))*x+(1.1213406499640161e-008))*x+(-2.4642437542373347e-007))*x+(4.9637249569893047e-006))*x+(-9.5563829931884684e-005))*x+(0.001803092652223818))*x+(-0.033778545685865143))*x+(0.63162742613900413));
		wts[0] = (((((((((((((1.2611659864584604e-010))*x+(2.1221543041368323e-012))*x+(-8.2006105609859021e-011))*x+(-2.4253192047278081e-012))*x+(2.0188887598730311e-011))*x+(-4.0678571622265728e-012))*x+(-6.4582946398180263e-010))*x+(3.1693407454014277e-008))*x+(-1.1974264130613457e-006))*x+(4.4492504473021367e-005))*x+(-0.0018129885175678809))*x+(0.11060939156443253));
		wts[1] = (((((((((((((4.0927261579781771e-011))*x+(-2.2282620193436742e-011))*x+(-2.5409008230781183e-011))*x+(1.5006662579253316e-011))*x+(3.7469286932415952e-012))*x+(2.8434143928279809e-011))*x+(-6.2210821679305651e-010))*x+(1.556589398118054e-008))*x+(-4.9064543416558549e-007))*x+(1.7582740999923241e-005))*x+(-0.0007129861624151024))*x+(0.043482492850683153));
		wts[2] = (((((((((((((6.5559409752798574e-012))*x+(-6.6317322004276014e-013))*x+(-3.3419193338583373e-012))*x+(4.5711582667233109e-013))*x+(-5.9211894646675022e-013))*x+(1.5980624231322811e-011))*x+(-2.1146022895675759e-010))*x+(3.2303986800356435e-009))*x+(-7.5801281106703075e-008))*x+(2.5105538854974909e-006))*x+(-0.00010066519277637346))*x+(0.0061338508910002395));
		wts[3] = (((((((((((((-7.5080682411983913e-013))*x+(-1.9776772811989454e-013))*x+(5.0433731265305438e-013))*x+(1.4166445794216997e-013))*x+(-2.3817984621625022e-013))*x+(1.5969679282671714e-012))*x+(-1.877204583907351e-011))*x+(2.1350457975651455e-010))*x+(-3.5426320957711657e-009))*x+(1.0201739221281239e-007))*x+(-4.0001013538928254e-006))*x+(0.00024331271782299818));
		wts[4] = (((((((((((((4.5334106838860555e-016))*x+(-7.4940054162198066e-016))*x+(-5.7303698823100524e-016))*x+(6.7538567331363686e-016))*x+(-1.6949693963190053e-015))*x+(2.4788800930911996e-014))*x+(-2.6231163192440863e-013))*x+(2.4404571607207029e-012))*x+(-2.7603014532971147e-011))*x+(6.1311493612186663e-010))*x+(-2.2840930738918655e-008))*x+(1.3836937261233971e-006));
		break;
	case 31:
		rts[0] = (((((((((((((4.0169349328304325e-012))*x+(7.7686005776437617e-013))*x+(-2.1363651588520343e-012))*x+(-5.068538181755381e-013))*x+(4.1270690568732477e-013))*x+(1.7406076580073202e-012))*x+(-1.0055350996296396e-010))*x+(3.686241867306705e-009))*x+(-1.2015975662503972e-007))*x+(3.7996612424730349e-006))*x+(-0.00011937598171226534))*x+(0.0037467072377678988));
		rts[1] = (((((((((((((3.1832314562052488e-011))*x+(1.5158245029548803e-012))*x+(-2.0596265433899436e-011))*x+(-9.2844250805986418e-013))*x+(5.2911749056268791e-012))*x+(2.0866271673488271e-011))*x+(-1.1229187209712184e-009))*x+(3.9409784620877034e-008))*x+(-1.2431416786575407e-006))*x+(3.8105075537614434e-005))*x+(-0.0011606668748372995))*x+(0.035317694768190272));
		rts[2] = (((((((((((((1.303609072541197e-010))*x+(-9.701276818911234e-012))*x+(-7.9467099567409592e-011))*x+(5.6464462735069292e-012))*x+(1.6844599789086107e-011))*x+(1.1420790239450677e-010))*x+(-4.9954350285948603e-009))*x+(1.5997350259292869e-007))*x+(-4.6950061505142884e-006))*x+(0.00013435066713253971))*x+(-0.003821785812802602))*x+(0.10860533548024248));
		rts[3] = (((((((((((((3.2014213502407074e-010))*x+(-1.2126596023639042e-011))*x+(-2.0372681319713593e-010))*x+(5.6085506609330569e-012))*x+(3.3916573253615453e-011))*x+(7.0199727512469212e-010))*x+(-2.2784639952533325e-008))*x+(6.2390634703035619e-007))*x+(-1.6073895690915663e-005))*x+(0.00040584121342690516))*x+(-0.010192453541498215))*x+(0.25571501652933726));
		rts[4] = (((((((((((((9.1192002097765601e-010))*x+(-1.9402553637822468e-011))*x+(-5.8571458794176568e-010))*x+(2.1221543041368324e-011))*x+(-2.100174848843987e-010))*x+(8.497390050858181e-009))*x+(-1.8762647376509753e-007))*x+(3.8854196399521852e-006))*x+(-7.796343694455031e-005))*x+(0.0015438787026886096))*x+(-0.030440364742177296))*x+(0.59956113737086336));
		wts[0] = (((((((((((((1.1641532182693481e-010))*x+(-5.4569682106375694e-012))*x+(-7.1546916539470359e-011))*x+(2.9179621681881449e-012))*x+(1.5973000699887052e-011))*x+(3.1950738351345836e-012))*x+(-6.4579334472606809e-010))*x+(2.8450267327192098e-008))*x+(-1.0771391873998226e-006))*x+(4.1083903561361934e-005))*x+(-0.0017274722531060852))*x+(0.10883972917093042));
		wts[1] = (((((((((((((3.7895612573872008e-011))*x+(-1.2126596023639042e-011))*x+(-2.1733133811115597e-011))*x+(7.4275400644789134e-012))*x+(2.6053233644537004e-012))*x+(2.023625711444765e-011))*x+(-4.6232269864295478e-010))*x+(1.2881902359633081e-008))*x+(-4.3401587115447316e-007))*x+(1.6198427617621545e-005))*x+(-0.00067923328210878762))*x+(0.042786613758108473));
		wts[2] = (((((((((((((1.777304229714597e-011))*x+(-7.3896444519050419e-013))*x+(-1.1678954100110179e-011))*x+(3.979039320256561e-013))*x+(2.0647187663295577e-012))*x+(9.8373901617302782e-012))*x+(-1.3522006662528935e-010))*x+(2.379853212645481e-009))*x+(-6.470784979888121e-008))*x+(2.3006376284447649e-006))*x+(-9.5859535284217591e-005))*x+(0.0060356234848084698));
		wts[3] = (((((((((((((6.1580370432542012e-014))*x+(-1.0776564825694852e-013))*x+(2.2500519965736508e-014))*x+(6.7353530160592826e-014))*x+(-1.0164091790443307e-013))*x+(9.5700762129761553e-013))*x+(-1.1130029768195252e-011))*x+(1.4035039681374131e-010))*x+(-2.8476255688683846e-009))*x+(9.2504829011839557e-008))*x+(-3.8059253686571434e-006))*x+(0.00023941128746625181));
		wts[4] = (((((((((((((-6.5688195623655089e-016))*x+(-4.9497443181204892e-016))*x+(7.8929918156944723e-016))*x+(3.5966600068585797e-016))*x+(-1.476105117766598e-015))*x+(1.4219004301531852e-014))*x+(-1.4729370112559598e-013))*x+(1.4429806068741388e-012))*x+(-2.0026817205822507e-011))*x+(5.4266234801223752e-010))*x+(-2.1688922531912135e-008))*x+(1.3614405085898401e-006));
		break;
	case 32:
		rts[0] = (((((((((((((7.1243751638879376e-012))*x+(1.2600291180812442e-012))*x+(-4.2964150755627389e-012))*x+(-9.7225931009840362e-013))*x+(9.0505380967442751e-013))*x+(2.1426934300923981e-012))*x+(-8.9911393145551217e-011))*x+(3.2096943112606504e-009))*x+(-1.0638569378681091e-007))*x+(3.4603197045838213e-006))*x+(-0.00011212288600549684))*x+(0.0036310143449425985));
		rts[1] = (((((((((((((5.305385760342081e-011))*x+(3.637978807091713e-012))*x+(-3.3518669321589791e-011))*x+(-3.0505968121966967e-012))*x+(7.4512248223375829e-012))*x+(2.3173167088922732e-011))*x+(-9.9211180012067278e-010))*x+(3.4121186246830838e-008))*x+(-1.0962984651335939e-006))*x+(3.460120452075665e-005))*x+(-0.0010880339944731013))*x+(0.034193928135719406));
		rts[2] = (((((((((((((1.673470251262188e-010))*x+(2.1221543041368323e-012))*x+(-1.051982205050687e-010))*x+(-1.591615728102624e-012))*x+(2.2026824808563106e-011))*x+(1.1269799908101655e-010))*x+(-4.3073953293060185e-009))*x+(1.3673256852679097e-007))*x+(-4.1027440395025039e-006))*x+(0.0001211772809280818))*x+(-0.0035665538807009012))*x+(0.10491336042324138));
		rts[3] = (((((((((((((3.0801553900043166e-010))*x+(-1.9402553637822468e-011))*x+(-1.9266129432556528e-010))*x+(1.4400332778071363e-011))*x+(2.76827449852135e-011))*x+(6.0573294528391364e-010))*x+(-1.8838757516922062e-008))*x+(5.2010207281701537e-007))*x+(-1.3792457480084805e-005))*x+(0.00036114544109918284))*x+(-0.0094266069482314575))*x+(0.24591293212193396));
		rts[4] = (((((((((((((3.0559021979570389e-010))*x+(7.0334256937106446e-011))*x+(-1.4279066817834973e-010))*x+(-3.3954468866189317e-011))*x+(-2.4825415797143552e-010))*x+(6.4039700949554872e-009))*x+(-1.4321192646586192e-007))*x+(3.063605268730877e-006))*x+(-6.413929337386233e-005))*x+(0.0013315453696054838))*x+(-0.027571845355352505))*x+(0.57059039386720578));
		wts[0] = (((((((((((((1.2308494963993627e-010))*x+(6.6696278130014735e-012))*x+(-7.5829120760317879e-011))*x+(-5.7980287238024175e-012))*x+(1.6190900472186815e-011))*x+(9.9499667764272691e-012))*x+(-6.0762402516919179e-010))*x+(2.5311552261560639e-008))*x+(-9.6967944032688713e-007))*x+(3.8016816203069917e-005))*x+(-0.0016484252567924441))*x+(0.1071522914924895));
		wts[1] = (((((((((((((5.3357022504011788e-011))*x+(-1.6674069532503683e-011))*x+(-3.5621875819439687e-011))*x+(1.1709744285326449e-011))*x+(7.6928093524960169e-012))*x+(1.2004619520666893e-011))*x+(-3.5458273354530923e-010))*x+(1.0859338909578279e-008))*x+(-3.8671445634630425e-007))*x+(1.4969351432974251e-005))*x+(-0.00064808913571845483))*x+(0.042123157327961243));
		wts[2] = (((((((((((((4.4337866711430252e-012))*x+(-1.3452942463724562e-012))*x+(-3.2756020118540619e-012))*x+(7.7212310619264203e-013))*x+(4.1389114358025836e-013))*x+(5.8663444472510191e-012))*x+(-8.8298488890951405e-011))*x+(1.8316775781309263e-009))*x+(-5.6362374404803066e-008))*x+(2.1195785174675176e-006))*x+(-9.1443484138211615e-005))*x+(0.0059420021334351675));
		wts[3] = (((((((((((((7.6501767883504113e-013))*x+(1.3737159558028603e-013))*x+(-5.3838415207489254e-013))*x+(-9.7403566693780392e-014))*x+(9.2259533346350509e-014))*x+(5.8978747811503729e-013))*x+(-6.6568827996234719e-012))*x+(9.6912393041104217e-011))*x+(-2.3805516533358917e-009))*x+(8.4705795141825968e-008))*x+(-3.628947536717615e-006))*x+(0.00023569514941437829));
		wts[4] = (((((((((((((3.8950324447265903e-015))*x+(-9.0668213677721111e-016))*x+(-2.8975664460399267e-015))*x+(5.5048558304330675e-016))*x+(1.0336060711028472e-016))*x+(7.8942205781566236e-015))*x+(-8.2369262687330165e-014))*x+(8.8457655100532957e-013))*x+(-1.5479591067283224e-011))*x+(4.8995801483482649e-010))*x+(-2.0658565014788769e-008))*x+(1.3402755304072569e-006));
		break;
	case 33:
		rts[0] = (((((((((((((9.2465294680247699e-012))*x+(2.1221543041368323e-012))*x+(-5.9685589803848416e-012))*x+(-1.3476627221583231e-012))*x+(1.3571366253017914e-012))*x+(2.1550169056657369e-012))*x+(-7.8698936256671459e-011))*x+(2.7887461599244525e-009))*x+(-9.4407502764422738e-008))*x+(3.1595508390361059e-006))*x+(-0.00010550900267614692))*x+(0.003522248514714815));
		rts[1] = (((((((((((((4.8809548995147147e-011))*x+(6.063298011819521e-012))*x+(-3.0032272964793564e-011))*x+(-3.9979871265434968e-012))*x+(6.1082990517509935e-012))*x+(2.2345384801762215e-011))*x+(-8.59874763984673e-010))*x+(2.9496635282436994e-008))*x+(-9.6928287707705608e-007))*x+(3.1507456513401207e-005))*x+(-0.0010219888191900623))*x+(0.033139432199427499));
		rts[2] = (((((((((((((1.0732037480920553e-010))*x+(3.0316490059097606e-013))*x+(-6.3323568610940129e-011))*x+(-2.6526928801710404e-013))*x+(1.0838145196127394e-011))*x+(1.0179590503867075e-010))*x+(-3.6614919984856438e-009))*x+(1.1684473314825064e-007))*x+(-3.5966648173901827e-006))*x+(0.00010964804999678833))*x+(-0.0033359814818409569))*x+(0.10146401361778647));
		rts[3] = (((((((((((((3.1529149661461509e-010))*x+(-2.3646862246096134e-011))*x+(-1.8917489796876905e-010))*x+(1.4476124003219107e-011))*x+(2.3817392502678558e-011))*x+(5.0827253517127236e-010))*x+(-1.5476355012348599e-008))*x+(4.3457586655174885e-007))*x+(-1.1888704900468264e-005))*x+(0.00032270917404654076))*x+(-0.0087437036492273301))*x+(0.23683418001919762));
		rts[4] = (((((((((((((7.1304384618997574e-010))*x+(-4.850638409455617e-012))*x+(-4.411049303598702e-010))*x+(5.7601331112285452e-012))*x+(-1.0394766529013091e-010))*x+(4.8006540964706793e-009))*x+(-1.098668806302309e-007))*x+(2.4349068693159852e-006))*x+(-5.3197781008392418e-005))*x+(0.0011561676607025895))*x+(-0.025089597532863082))*x+(0.54428888112253715));
		wts[0] = (((((((((((((1.7522931254158417e-010))*x+(-1.5158245029548803e-012))*x+(-1.0606981959426774e-010))*x+(3.7895612573871996e-013))*x+(2.2301567999723674e-011))*x+(1.0081417182542888e-011))*x+(-5.5230501653606246e-010))*x+(2.2415279262351835e-008))*x+(-8.7431895724280717e-007))*x+(3.5253715793007179e-005))*x+(-0.0015752023956504817))*x+(0.10554093808641291));
		wts[1] = (((((((((((((1.3339255626002947e-011))*x+(-2.7284841053187847e-012))*x+(-4.8506384094556162e-012))*x+(2.1600499167107046e-012))*x+(-7.2949054204703633e-013))*x+(9.7818049956307115e-012))*x+(-2.7843298037547959e-010))*x+(9.28925677120181e-009))*x+(-3.4654289014316808e-007))*x+(1.3871033061746417e-005))*x+(-0.00061926882455248691))*x+(0.041489661348664893));
		wts[2] = (((((((((((((1.360452491402005e-011))*x+(2.0842586915629605e-013))*x+(-8.3678249514681121e-012))*x+(-1.8710958708349304e-013))*x+(1.4595732030405391e-012))*x+(3.7031859060713633e-012))*x+(-6.0021423016938996e-011))*x+(1.4672602854925998e-009))*x+(-4.9811488983877987e-008))*x+(1.960680946640145e-006))*x+(-8.7366495427835411e-005))*x+(0.0058526236144897346));
		wts[3] = (((((((((((((-1.5395092608135502e-013))*x+(3.1974423109204508e-014))*x+(1.1294668903853258e-013))*x+(-2.8273679693787319e-014))*x+(-5.5326114060486965e-014))*x+(3.3208158445319214e-013))*x+(-4.0447940136134611e-012))*x+(7.0788033999328676e-011))*x+(-2.0494445853571604e-009))*x+(7.8086806689277508e-008))*x+(-3.466320059818306e-006))*x+(0.00023214861791565435));
		wts[4] = (((((((((((((1.0454600148553557e-015))*x+(9.2518585385429703e-017))*x+(-6.0773145775054139e-016))*x+(-2.9490299091605714e-017))*x+(-2.5977484052752686e-016))*x+(4.4021138007980608e-015))*x+(-4.6189824697267373e-014))*x+(5.7236599809399919e-013))*x+(-1.2625540165849752e-011))*x+(4.4811073024812788e-010))*x+(-1.9721917329646247e-008))*x+(1.3200922534606756e-006));
		break;
	case 34:
		rts[0] = (((((((((((((1.3396099044863755e-011))*x+(7.4843834833397216e-013))*x+(-8.7834924518877707e-012))*x+(-4.961956771391366e-013))*x+(2.0348167595329865e-012))*x+(1.8176941433504603e-012))*x+(-6.8069434348376007e-011))*x+(2.4230614598108598e-009))*x+(-8.4001657246699405e-008))*x+(2.8923027059831077e-006))*x+(-9.9462350267841604e-005))*x+(0.0034198073674118552));
		rts[1] = (((((((((((((1.6977234433094658e-011))*x+(3.9411437076826888e-012))*x+(-1.0269711007519314e-011))*x+(-2.4063713984408724e-012))*x+(1.7313557994687772e-012))*x+(1.9773220098310656e-011))*x+(-7.3706537169944874e-010))*x+(2.551132127770472e-008))*x+(-8.5947087670919708e-007))*x+(2.8768310170915187e-005))*x+(-0.00096176793809592211))*x+(0.032148010212379251));
		rts[2] = (((((((((((((1.8978122776995102e-010))*x+(-2.6678511252005894e-011))*x+(-1.2031856992204362e-010))*x+(1.6105635343895603e-011))*x+(2.4783730623312291e-011))*x+(8.5033017664197048e-011))*x+(-3.0919019936940608e-009))*x+(1.0000340289195719e-007))*x+(-3.1639209988332247e-006))*x+(9.9524006044145657e-005))*x+(-0.0031270257024734777))*x+(0.098234196805218596));
		rts[3] = (((((((((((((2.3889394166568912e-010))*x+(2.1221543041368324e-011))*x+(-1.5211298887152222e-010))*x+(-1.5385618704992034e-011))*x+(2.1846820648837209e-011))*x+(4.243195424654308e-010))*x+(-1.2687787709353415e-008))*x+(3.644067687602614e-007))*x+(-1.0295385904931138e-005))*x+(0.00028950316053132547))*x+(-0.0081322875095133172))*x+(0.22840171643863949));
		rts[4] = (((((((((((((6.4028427004814148e-010))*x+(1.6977234433094658e-011))*x+(-3.9593336017181474e-010))*x+(-8.1854523159563525e-012))*x+(-6.3020403710349144e-011))*x+(3.6097939452398955e-009))*x+(-8.4826863163319402e-008))*x+(1.9511860725647994e-006))*x+(-4.4467267205601978e-005))*x+(0.0010101532132172908))*x+(-0.022927637751036112))*x+(0.52030458312616323));
		wts[0] = (((((((((((((1.1459633242338896e-010))*x+(1.2126596023639042e-012))*x+(-6.6809964967736349e-011))*x+(-1.7053025658242402e-012))*x+(1.271397801853406e-011))*x+(1.0800249583553523e-011))*x+(-4.9000285310777747e-010))*x+(1.9815680059783365e-008))*x+(-7.8995914666128242e-007))*x+(3.2759898177914242e-005))*x+(-0.0015072309513859006))*x+(0.10400013696250951));
		wts[1] = (((((((((((((6.1542474819968135e-011))*x+(-1.6977234433094658e-011))*x+(-3.6550318327499547e-011))*x+(1.0023389525789144e-011))*x+(6.6317322004276004e-012))*x+(5.6026294714683892e-012))*x+(-2.2566741068411983e-010))*x+(8.0366664434450286e-009))*x+(-3.1198026448816152e-007))*x+(1.2884499571759004e-005))*x+(-0.00059253056434982378))*x+(0.040883926034776065));
		wts[2] = (((((((((((((-1.5158245029548803e-013))*x+(2.3874235921539366e-012))*x+(5.0211686660380417e-013))*x+(-1.5205614545266144e-012))*x+(-4.4349709090359585e-013))*x+(2.5906684205286483e-012))*x+(-4.2569651507543917e-011))*x+(1.2143976195015207e-009))*x+(-4.4476752639651299e-008))*x+(1.8195007310348869e-006))*x+(-8.3588978261663123e-005))*x+(0.0057671693992862481));
		wts[3] = (((((((((((((4.961956771391366e-013))*x+(-1.1487107561454951e-013))*x+(-2.9613348810168339e-013))*x+(7.209048173232681e-014))*x+(4.3539246282383218e-014))*x+(1.6929513346752856e-013))*x+(-2.5679825742715621e-012))*x+(5.4603747449514601e-011))*x+(-1.8011215890226192e-009))*x+(7.232707571813959e-008))*x+(-3.3160300933872807e-006))*x+(0.00022875840225790284));
		wts[4] = (((((((((((((2.55351295663786e-015))*x+(-6.5225602696727947e-016))*x+(-1.5450603759366761e-015))*x+(3.8742157630148693e-016))*x+(1.1058862159352145e-016))*x+(2.3176086339412221e-015))*x+(-2.6465447310515995e-014))*x+(3.9579932620227224e-013))*x+(-1.0721918921442658e-011))*x+(4.1326511961217848e-010))*x+(-1.8861490028549672e-008))*x+(1.3008063515448435e-006));
		break;
	case 35:
		rts[0] = (((((((((((((5.892767755237097e-012))*x+(-1.3073986337985843e-012))*x+(-3.4307371758283503e-012))*x+(8.8225723023545776e-013))*x+(6.3652786745175628e-013))*x+(1.2948901210544741e-012))*x+(-5.8288406508862524e-011))*x+(2.1083290761373754e-009))*x+(-7.4954942627369431e-008))*x+(2.6541824555880466e-006))*x+(-9.392038686222377e-005))*x+(0.0033231556750677386));
		rts[1] = (((((((((((((4.2139921182145671e-011))*x+(-6.6696278130014735e-012))*x+(-2.4840574042173102e-011))*x+(4.0358827391173691e-012))*x+(4.5451050330787739e-012))*x+(1.5924446946276778e-011))*x+(-6.2892572631293798e-010))*x+(2.2103947931266056e-008))*x+(-7.6442104094317132e-007))*x+(2.6335878523816209e-005))*x+(-0.00090671125625164082))*x+(0.031214175906955716));
		rts[2] = (((((((((((((1.13990002622207e-010))*x+(1.0610771520684162e-011))*x+(-7.1395334089174854e-011))*x+(-8.1096610908086096e-012))*x+(1.3756107364315538e-011))*x+(7.7222968760300617e-011))*x+(-2.6009884616466175e-009))*x+(8.5813666543070141e-008))*x+(-2.7931033018679936e-006))*x+(9.0602651916141252e-005))*x+(-0.0029370843717502087))*x+(0.095203628187811778));
		rts[3] = (((((((((((((3.3105607144534588e-010))*x+(2.1827872842550278e-011))*x+(-1.9637506435780477e-010))*x+(-1.2202387248786787e-011))*x+(2.8649083105847243e-011))*x+(3.4396900142989273e-010))*x+(-1.040828845333408e-008))*x+(3.0687816909846788e-007))*x+(-8.9566111983555939e-006))*x+(0.00026068265422289166))*x+(-0.0075827707026399245))*x+(0.22054898883452118));
		rts[4] = (((((((((((((5.1416767140229536e-010))*x+(3.3954468866189317e-011))*x+(-3.140788370122512e-010))*x+(-1.7583564234276608e-011))*x+(-4.3314685171935707e-011))*x+(2.7246566484488235e-009))*x+(-6.5980183687012556e-008))*x+(1.5764097346012325e-006))*x+(-3.7443438379044139e-005))*x+(0.00088766148878205442))*x+(-0.021033331828931669))*x+(0.49834450115208634));
		wts[0] = (((((((((((((1.0428872580329576e-010))*x+(-2.1221543041368324e-011))*x+(-6.1390892369672656e-011))*x+(1.2581343374525506e-011))*x+(1.1993961379630491e-011))*x+(7.0651632692412623e-012))*x+(-4.3047461891395261e-010))*x+(1.7520493204396342e-008))*x+(-7.1538641229403532e-007))*x+(3.050417496150426e-005))*x+(-0.0014440041546611275))*x+(0.10252489528685323));
		wts[1] = (((((((((((((-4.5474735088646412e-011))*x+(1.0610771520684161e-012))*x+(3.2476539975808315e-011))*x+(-1.6105635343895602e-012))*x+(-9.1328426303031539e-012))*x+(6.3185012777466901e-012))*x+(-1.8485376192719136e-010))*x+(7.0129254255609421e-009))*x+(-2.8194648942399719e-007))*x+(1.1994632118393632e-005))*x+(-0.00056766644305932847))*x+(0.040303975808242569));
		wts[2] = (((((((((((((7.5791225147744013e-013))*x+(-2.1411021104237684e-012))*x+(-1.7053025658242404e-013))*x+(1.6958286626807722e-012))*x+(-2.08425869156296e-013))*x+(9.5723429183180997e-013))*x+(-3.1815994283590492e-011))*x+(1.0303017975813824e-009))*x+(-4.0005261240279762e-008))*x+(1.6929614942241241e-006))*x+(-8.0078749997559203e-005))*x+(0.0056853566189087948));
		wts[3] = (((((((((((((5.281701002483411e-013))*x+(-9.9475983006414026e-014))*x+(-4.2144066014770942e-013))*x+(5.2328511893999049e-014))*x+(1.122620515066804e-013))*x+(9.854154529402119e-014))*x+(-1.7272115450846688e-012))*x+(4.4104999166738601e-011))*x+(-1.6051189608865789e-009))*x+(6.7228172896382582e-008))*x+(-3.1765727047895303e-006))*x+(0.00022551295032788169));
		wts[4] = (((((((((((((3.3954320836452703e-015))*x+(4.6259292692714852e-017))*x+(-2.406061461179831e-015))*x+(-4.8572257327350592e-017))*x+(4.9627547441903153e-016))*x+(1.3149565348628358e-015))*x+(-1.5786532508738762e-014))*x+(2.9310277259384415e-013))*x+(-9.3618711030522898e-012))*x+(3.8324157783950006e-010))*x+(-1.806566158344022e-008))*x+(1.2823477762653181e-006));
		break;
	case 36:
		rts[0] = (((((((((((((1.0307606620093186e-011))*x+(-5.6843418860808015e-013))*x+(-7.0580578418836613e-012))*x+(4.452734477429961e-013))*x+(1.7473430110233796e-012))*x+(1.179056852151916e-012))*x+(-5.0052073596873463e-011))*x+(1.8386008734013377e-009))*x+(-6.7075115966116122e-008))*x+(2.4414069690788243e-006))*x+(-8.8828735947769018e-005))*x+(0.0032318165672582319));
		rts[1] = (((((((((((((4.638422979041934e-011))*x+(-6.2148804621150094e-012))*x+(-3.0373333477958418e-011))*x+(4.1116739642651128e-012))*x+(6.7691037960078883e-012))*x+(1.3404980829060756e-011))*x+(-5.3588104324357267e-010))*x+(1.9200727008339413e-008))*x+(-6.8196764630342377e-007))*x+(2.4169197438942323e-005))*x+(-0.00085624739140782811))*x+(0.030333057599924742));
		rts[2] = (((((((((((((1.2247861983875433e-010))*x+(3.0316490059097606e-013))*x+(-7.6018598823187248e-011))*x+(-1.2126596023639042e-012))*x+(1.4656128162944999e-011))*x+(6.3369753888764535e-011))*x+(-2.1883706698607361e-009))*x+(7.387786486271844e-008))*x+(-2.474406974743252e-006))*x+(8.2713316229337156e-005))*x+(-0.0027639276830550064))*x+(0.092354436652115263));
		rts[3] = (((((((((((((2.1464074961841106e-010))*x+(2.3040532444914181e-011))*x+(-1.3301360013429075e-010))*x+(-1.4021376652332643e-011))*x+(1.9800457569848127e-011))*x+(2.7933329723358235e-010))*x+(-8.5603337751649633e-009))*x+(2.5963242400450776e-007))*x+(-7.8266661791744526e-006))*x+(0.00023555495103686855))*x+(-0.0070870977622845954))*x+(0.2132182409792899));
		rts[4] = (((((((((((((6.4028427004814148e-010))*x+(-7.0334256937106446e-011))*x+(-3.8441309394935769e-010))*x+(4.6081064889828362e-011))*x+(-3.637978807091713e-012))*x+(2.0540843100510151e-009))*x+(-5.1728908564048951e-008))*x+(1.2838035902499694e-006))*x+(-3.1746732384559571e-005))*x+(0.00078416851211352912))*x+(-0.01936434781047075))*x+(0.47816290042384357));
		wts[0] = (((((((((((((2.1827872842550278e-010))*x+(-1.9099388737231493e-011))*x+(-1.3627262281564376e-010))*x+(1.2316074086508403e-011))*x+(2.9160673875594512e-011))*x+(5.8584248563420244e-012))*x+(-3.7738819476847613e-010))*x+(1.5511578540146804e-008))*x+(-6.4941421218378537e-007))*x+(2.8458982402987384e-005))*x+(-0.0013850739742497647))*x+(0.1011106970208812));
		wts[1] = (((((((((((((4.5474735088646412e-012))*x+(8.033869865660865e-012))*x+(3.8464046762480085e-012))*x+(-6.0632980118195202e-012))*x+(-3.4390268410788849e-012))*x+(5.9430978656867718e-012))*x+(-1.5545897902313754e-010))*x+(6.1606049891101585e-009))*x+(-2.5564855742991422e-007))*x+(1.118909136128138e-005))*x+(-0.00054449586358474927))*x+(0.039748028883333439));
		wts[2] = (((((((((((((1.3377151238576818e-011))*x+(-8.3370347662518418e-013))*x+(-8.5904616753396112e-012))*x+(5.4001247917767614e-013))*x+(1.8776091792460647e-012))*x+(8.0913054034681409e-013))*x+(-2.5071768735192752e-011))*x+(8.8957354445658621e-010))*x+(-3.6177201711770635e-008))*x+(1.5788282519101082e-006))*x+(-7.6808873118707624e-005))*x+(0.0056069318248795153));
		wts[3] = (((((((((((((6.406727000770236e-013))*x+(-5.9211894646675007e-014))*x+(-3.6052642352994247e-013))*x+(3.5009032709846594e-014))*x+(6.1080770071460679e-014))*x+(5.6251299914341261e-014))*x+(-1.2182595788649368e-012))*x+(3.6896079941284299e-011))*x+(-1.4439450575072104e-009))*x+(6.2661763476482856e-008))*x+(-3.0467632733490482e-006))*x+(0.0002224020431677623));
		wts[4] = (((((((((((((4.9034850254277741e-016))*x+(5.1810407815840632e-016))*x+(-2.9316826744008035e-016))*x+(-3.5850951836854007e-016))*x+(1.83591567874212e-017))*x+(7.9898472097698437e-016))*x+(-9.898388622786811e-015))*x+(2.3053536709101658e-013))*x+(-8.3242390456699691e-012))*x+(3.5677467763440429e-010))*x+(-1.7326163181376318e-008))*x+(1.2646562729614569e-006));
		break;
	case 37:
		rts[0] = (((((((((((((6.3285672998366254e-012))*x+(-1.5252984060983483e-012))*x+(-4.3319422123507439e-012))*x+(9.012050365223937e-013))*x+(1.0516032489249481e-012))*x+(9.1944970156040021e-013))*x+(-4.2784544425818652e-011))*x+(1.6077825228573892e-009))*x+(-6.0194378161936471e-008))*x+(2.2507334318549715e-006))*x+(-8.4140034720005751e-005))*x+(0.0031453639531578126));
		rts[1] = (((((((((((((5.0780120848988489e-011))*x+(-4.9264296346033608e-012))*x+(-3.3888151544185043e-011))*x+(3.1169141342009721e-012))*x+(7.778074480787229e-012))*x+(1.1443586818889646e-011))*x+(-4.566734768118863e-010))*x+(1.6728687805371102e-008))*x+(-6.1024125994763024e-007))*x+(2.2233354890653874e-005))*x+(-0.00080988068905153471))*x+(0.029500316117772762));
		rts[2] = (((((((((((((9.1555799978474767e-011))*x+(-8.1854523159563541e-012))*x+(-5.9306633678109691e-011))*x+(4.0169349328304333e-012))*x+(1.1946591863913151e-011))*x+(5.1655272651866348e-011))*x+(-1.8440791116347553e-009))*x+(6.3829687757532825e-008))*x+(-2.1995649205630578e-006))*x+(7.5712401265919549e-005))*x+(-0.0026056393292854235))*x+(0.089670819630414719));
		rts[3] = (((((((((((((3.3954468866189319e-010))*x+(1.5158245029548802e-011))*x+(-2.1191226551309225e-010))*x+(-8.8675733422860487e-012))*x+(3.9240906820244462e-011))*x+(2.2491756605328797e-010))*x+(-7.0690534907195497e-009))*x+(2.2070764268041404e-007))*x+(-6.8684717451361621e-006))*x+(0.00021355114229394215))*x+(-0.0066384705175787703))*x+(0.20635912284457955));
		rts[4] = (((((((((((((8.052059759696324e-010))*x+(1.0913936421275139e-011))*x+(-5.1598666080584122e-010))*x+(-5.3053857603420819e-012))*x+(5.646446273506929e-011))*x+(1.5776085623050069e-009))*x+(-4.0888638845141629e-008))*x+(1.0535158600314767e-006))*x+(-2.7090146575610891e-005))*x+(0.00069614323676664425))*x+(-0.017886362550141376))*x+(0.45955220845811462));
		wts[0] = (((((((((((((1.7280399333685637e-010))*x+(-8.7917821171383058e-012))*x+(-1.1834799806820229e-010))*x+(3.979039320256561e-012))*x+(2.8885930684433941e-011))*x+(7.0971376923504676e-012))*x+(-3.2945749831962229e-010))*x+(1.3760528864518543e-008))*x+(-5.909512543478267e-007))*x+(2.6600184215903412e-005))*x+(-0.001330044030988459))*x+(0.099753447759627106));
		wts[1] = (((((((((((((5.2144362901647881e-011))*x+(3.3348139065007367e-012))*x+(-2.849750065555175e-011))*x+(-2.6337450738841044e-012))*x+(4.7795841358796078e-012))*x+(4.2253608019867288e-012))*x+(-1.3297155968909158e-010))*x+(5.4406300205774496e-009))*x+(-2.3248453282868434e-007))*x+(1.0457611414262564e-005))*x+(-0.000522860738912593))*x+(0.039214472471428181));
		wts[2] = (((((((((((((1.0800249583553523e-011))*x+(1.0610771520684161e-012))*x+(-5.9282948920251028e-012))*x+(-5.5896028546461198e-013))*x+(1.0148918742440096e-012))*x+(7.4814228886073875e-013))*x+(-2.0226089321913793e-011))*x+(7.7761397321296489e-010))*x+(-3.2850712773299644e-008))*x+(1.4753981705540227e-006))*x+(-7.3756309157989007e-005))*x+(0.0055316664683635495));
		wts[3] = (((((((((((((-3.2092846898497857e-013))*x+(1.7763568394002505e-015))*x+(2.4165854502674239e-013))*x+(-2.4424906541753444e-015))*x+(-7.0647191800314119e-014))*x+(4.1136076026996683e-014))*x+(-9.0439259090950109e-013))*x+(3.1635637107637241e-011))*x+(-1.3073822552803955e-009))*x+(5.8540020788359246e-008))*x+(-2.9256297208551884e-006))*x+(0.0002194165334530337));
		wts[4] = (((((((((((((-5.1440333474298914e-015))*x+(4.163336342344337e-017))*x+(3.853399081303147e-015))*x+(-4.105512226478443e-017))*x+(-1.1025613292729255e-015))*x+(4.1443628043258407e-016))*x+(-6.5235721917004481e-015))*x+(1.8995344260565894e-013))*x+(-7.4885925713196788e-012))*x+(3.3309587359156696e-010))*x+(-1.663670992489283e-008))*x+(1.2476787815299992e-006));
		break;
	case 38:
		rts[0] = (((((((((((((7.2380620016095536e-012))*x+(-1.3263464400855202e-013))*x+(-4.673002725515592e-012))*x+(7.1054273576009892e-015))*x+(1.0444978215673471e-012))*x+(9.5072098342067558e-013))*x+(-3.6672840690125476e-011))*x+(1.4100932366201135e-009))*x+(-5.4168809763531958e-008))*x+(2.0793862230795873e-006))*x+(-7.9812926833899587e-005))*x+(0.0030634160236641529));
		rts[1] = (((((((((((((3.6682952971508101e-011))*x+(-9.0949470177292824e-013))*x+(-2.29457934134795e-011))*x+(2.6526928801710409e-013))*x+(4.8174797484534785e-012))*x+(1.0204577923407971e-011))*x+(-3.8947874555124901e-010))*x+(1.4621295581681201e-008))*x+(-5.4765278814187613e-007))*x+(2.049862010699658e-005))*x+(-0.00076717999716097705))*x+(0.028712074826932804));
		rts[2] = (((((((((((((9.0343140376110867e-011))*x+(-1.2126596023639042e-011))*x+(-5.1500137487892055e-011))*x+(7.1243751638879368e-012))*x+(8.3844042819691806e-012))*x+(4.1836756281554699e-011))*x+(-1.5577668044386428e-009))*x+(5.5351858208041442e-008))*x+(-1.9616780140748373e-006))*x+(6.94790103093849e-005))*x+(-0.0024605668136015624))*x+(0.087138755175076354));
		rts[3] = (((((((((((((2.7406107013424236e-010))*x+(-2.2434202643732228e-011))*x+(-1.6355746386883158e-010))*x+(1.3642420526593922e-011))*x+(2.7114310796605423e-011))*x+(1.7782753047868027e-010))*x+(-5.8605369446240729e-009))*x+(1.8850633024906452e-007))*x+(-6.0520538435933817e-006))*x+(0.000194202534015947))*x+(-0.0062311248493639657))*x+(0.19992754885678027));
		rts[4] = (((((((((((((6.9849193096160889e-010))*x+(-1.2126596023639042e-011))*x+(-4.3595112704982358e-010))*x+(7.1243751638879368e-012))*x+(4.9756939309493958e-011))*x+(1.2122332767224482e-009))*x+(-3.2572555615691577e-008))*x+(8.7081704691627227e-007))*x+(-2.3255318780298257e-005))*x+(0.00062080755553336098))*x+(-0.016571327788741288))*x+(0.44233591315421183));
		wts[0] = (((((((((((((1.2672292844702798e-010))*x+(2.0008883439004421e-011))*x+(-8.0907132845216737e-011))*x+(-1.4021376652332643e-011))*x+(1.824673745431937e-011))*x+(9.9404928732838016e-012))*x+(-2.8592491337538678e-010))*x+(1.2236342309771922e-008))*x+(-5.3902736371624904e-007))*x+(2.490673936460704e-005))*x+(-0.0012785630623454766))*x+(0.098449426402999543));
		wts[1] = (((((((((((((7.2759576141834259e-012))*x+(1.5158245029548803e-012))*x+(-1.0989727646422888e-012))*x+(-9.0949470177292814e-013))*x+(-1.134499901430293e-012))*x+(3.020990864873359e-012))*x+(-1.1356500924838049e-010))*x+(4.82571138604726e-009))*x+(-2.1198304348916486e-007))*x+(9.7915247717951966e-006))*x+(-0.00050262185035061043))*x+(0.038701842170751614));
		wts[2] = (((((((((((((1.2126596023639042e-011))*x+(4.926429634603361e-013))*x+(-7.7686005776437615e-012))*x+(-4.7843210874513409e-013))*x+(1.7035262089848402e-012))*x+(6.4200496770657389e-013))*x+(-1.6929827909943164e-011))*x+(6.8566147204407447e-010))*x+(-2.9929735648193117e-008))*x+(1.3813193418341779e-006))*x+(-7.0901051571494556e-005))*x+(0.0054593534647433819));
		wts[3] = (((((((((((((3.7066646048818558e-013))*x+(3.0790185216271006e-014))*x+(-2.6934010577406293e-013))*x+(-2.4868995751603503e-014))*x+(6.9351931604918108e-014))*x+(3.2825594094750464e-014))*x+(-7.2955096824811595e-013))*x+(2.7581902040108019e-011))*x+(-1.1892620457756681e-009))*x+(5.479910124403433e-008))*x+(-2.8123496268061784e-006))*x+(0.00021654816713099728));
		wts[4] = (((((((((((((2.0354088784794535e-015))*x+(-1.3877787807814457e-016))*x+(-1.6514567491299204e-015))*x+(3.1803263726241468e-017))*x+(4.6056908287184228e-016))*x+(2.4119884330560854e-016))*x+(-4.8743290220060187e-015))*x+(1.6167581235020564e-013))*x+(-6.7883678612450944e-012))*x+(3.1170863653883689e-010))*x+(-1.5992255217847696e-008))*x+(1.2313678625593658e-006));
		break;
	case 39:
		rts[0] = (((((((((((((5.6843418860808015e-012))*x+(7.4843834833397216e-013))*x+(-3.5290289209418311e-012))*x+(-4.7843210874513409e-013))*x+(7.5406347832540632e-013))*x+(8.9472873554541366e-013))*x+(-3.1487923379813765e-011))*x+(1.2404833225435989e-009))*x+(-4.8876216249040441e-008))*x+(1.9249882055344101e-006))*x+(-7.5811197844941516e-005))*x+(0.0029856296886777191));
		rts[1] = (((((((((((((2.2282620193436742e-011))*x+(-6.0632980118195212e-013))*x+(-1.2628712890242848e-011))*x+(1.1368683772161603e-013))*x+(2.0226783211304187e-012))*x+(8.6105937195194802e-012))*x+(-3.3294267343109136e-010))*x+(1.2820761859562897e-008))*x+(-4.9286222724107909e-007))*x+(1.8939647274507365e-005))*x+(-0.00072776911571750661))*x+(0.027964860039320343));
		rts[2] = (((((((((((((1.5522042910257974e-010))*x+(-7.5791225147744009e-012))*x+(-9.8831757592658193e-011))*x+(4.6990559591601279e-012))*x+(2.0984695462781623e-011))*x+(3.4888832563713855e-011))*x+(-1.3221785148213408e-009))*x+(4.8176729420627368e-008))*x+(-1.7550159339130287e-006))*x+(6.3911140721401957e-005))*x+(-0.0023272799541150363))*x+(0.084745759530487921));
		rts[3] = (((((((((((((2.9831426218152046e-010))*x+(-1.8189894035458565e-011))*x+(-1.8841698571729162e-010))*x+(8.1096610908086112e-012))*x+(3.7497708641846358e-011))*x+(1.4579863242640082e-010))*x+(-4.8844418879904578e-009))*x+(1.6174391781476061e-007))*x+(-5.3531816302336095e-006))*x+(0.00017712142572869535))*x+(-0.0058601501629290285))*x+(0.19388475731075541));
		rts[4] = (((((((((((((4.4140809526046115e-010))*x+(-4.8506384094556168e-011))*x+(-2.7011992642655963e-010))*x+(2.743642350348333e-011))*x+(2.3078428057488048e-011))*x+(9.3609742179978618e-010))*x+(-2.6147343845650539e-008))*x+(7.2472910872534147e-007))*x+(-2.0074916849965874e-005))*x+(0.00055595815395759185))*x+(-0.015396151211853424))*x+(0.42636297702437004));
		wts[0] = (((((((((((((8.7311491370201111e-011))*x+(2.2434202643732228e-011))*x+(-5.2599110252534352e-011))*x+(-1.4172959102628129e-011))*x+(1.062024542382763e-011))*x+(8.7799397382089702e-012))*x+(-2.4845251781850186e-010))*x+(1.0909274964869077e-008))*x+(-4.9279578965647874e-007))*x+(2.3360331145907041e-005))*x+(-0.0012303191015870356))*x+(0.097195243011521784));
		wts[1] = (((((((((((((8.0338698656608657e-011))*x+(-1.0156024169797698e-011))*x+(-5.5270750938992322e-011))*x+(6.3096194935496888e-012))*x+(1.3630578147664588e-011))*x+(9.5271938486500107e-013))*x+(-9.9872628685678436e-011))*x+(4.2962647513652046e-009))*x+(-1.9376499634885891e-007))*x+(9.1834320171286597e-006))*x+(-0.00048365599996232338))*x+(0.038208804576745053));
		wts[2] = (((((((((((((1.0724458358405778e-011))*x+(7.2001663890356815e-013))*x+(-7.5056997654125244e-012))*x+(-5.7080266439394712e-013))*x+(1.921425981284604e-012))*x+(5.4386125232971005e-013))*x+(-1.4458277168098258e-011))*x+(6.0839542663041846e-010))*x+(-2.7345761286744666e-008))*x+(1.2954832841414095e-006))*x+(-6.8225540508028002e-005))*x+(0.0053898044721404767));
		wts[3] = (((((((((((((5.0803805606847163e-013))*x+(1.1131836193574902e-013))*x+(-3.4690768776120723e-013))*x+(-5.7435537807274757e-014))*x+(8.2878148788267936e-014))*x+(2.7033930649622559e-014))*x+(-6.0032794707565174e-013))*x+(2.4318086896032057e-011))*x+(-1.0856752607203758e-009))*x+(5.1389954660584158e-008))*x+(-2.7062123428087967e-006))*x+(0.00021378945422865727));
		wts[4] = (((((((((((((4.1818400594214227e-015))*x+(8.3266726846886741e-016))*x+(-2.7107945517930903e-015))*x+(-4.6085820345117178e-016))*x+(6.2001908237204374e-016))*x+(2.2844139774269578e-016))*x+(-3.7717767277511971e-015))*x+(1.4057824096064728e-013))*x+(-6.1856810618072348e-012))*x+(2.9226860649930457e-010))*x+(-1.5388579135201418e-008))*x+(1.2156806846867805e-006));
		break;
	case 40:
		rts[0] = (((((((((((((4.964325247177233e-012))*x+(-9.2844250805986418e-013))*x+(-3.2756020118540619e-012))*x+(5.4711790653527704e-013))*x+(7.460698725481052e-013))*x+(5.5859021112307039e-013))*x+(-2.7138504406683712e-011))*x+(1.0945991983183725e-009))*x+(-4.4213293481804951e-008))*x+(1.7854997728843425e-006))*x+(-7.2103040603793518e-005))*x+(0.0029116958126649737));
		rts[1] = (((((((((((((4.3049415883918599e-011))*x+(1.2126596023639042e-012))*x+(-2.7777484016648181e-011))*x+(-7.4843834833397216e-013))*x+(6.1533000916824668e-012))*x+(7.3671439319393049e-012))*x+(-2.8626478965065871e-010))*x+(1.1277906534582865e-008))*x+(-4.4474338929216073e-007))*x+(1.7534780990956692e-005))*x+(-0.00069131873900396372))*x+(0.027255550204944513));
		rts[2] = (((((((((((((1.255102688446641e-010))*x+(1.0913936421275139e-011))*x+(-8.0528176719478025e-011))*x+(-6.4043585249843699e-012))*x+(1.7346716655689914e-011))*x+(3.1100455544219585e-011))*x+(-1.1251199971695769e-009))*x+(4.2082529165080963e-008))*x+(-1.5748252147433175e-006))*x+(5.8922469824446149e-005))*x+(-0.0022045364061587733))*x+(0.08248068259251165));
		rts[3] = (((((((((((((1.964508555829525e-010))*x+(5.4569682106375694e-012))*x+(-1.1565740957545738e-010))*x+(-4.3958910585691529e-012))*x+(1.9705718538413446e-011))*x+(1.2067620976570953e-010))*x+(-4.0875918945933636e-009))*x+(1.3939558278034761e-007))*x+(-4.752225955602837e-006))*x+(0.00016198564878834124))*x+(-0.0055213434339811103))*x+(0.18819653239749448));
		rts[4] = (((((((((((((4.9719043696920074e-010))*x+(3.759244767328103e-011))*x+(-2.9755634993004299e-010))*x+(-2.6678511252005891e-011))*x+(3.5015546018257737e-011))*x+(7.4243663069258515e-010))*x+(-2.1147971670150884e-008))*x+(6.0702572035609137e-007))*x+(-1.7419728972660011e-005))*x+(0.00049983378483858809))*x+(-0.014341686035166673))*x+(0.41150340854385087));
		wts[0] = (((((((((((((1.0065074699620405e-010))*x+(-6.9727927135924493e-012))*x+(-6.0102441542161003e-011))*x+(4.2443086082736646e-012))*x+(1.1946591863913149e-011))*x+(3.9210116635028198e-012))*x+(-2.171149186362224e-010))*x+(9.7519733029590352e-009))*x+(-4.5152516294407375e-007))*x+(2.1945006934647366e-005))*x+(-0.0011850343936047969))*x+(0.095987802112722273));
		wts[1] = (((((((((((((6.0329815217604235e-011))*x+(7.5791225147744009e-012))*x+(-3.7611395479567968e-011))*x+(-5.3622291792028883e-012))*x+(8.0954502360934076e-012))*x+(3.2886286286763302e-012))*x+(-8.6242938716433556e-011))*x+(3.8370446079719987e-009))*x+(-1.7751988567552926e-007))*x+(8.6269633549027978e-006))*x+(-0.00046585372501641861))*x+(0.037734142443744796));
		wts[2] = (((((((((((((1.1368683772161603e-012))*x+(-2.8421709430404007e-013))*x+(4.6895820560166612e-013))*x+(9.9475983006414026e-014))*x+(-5.1218288869373885e-013))*x+(3.0101846941003408e-013))*x+(-1.2126392482751195e-011))*x+(5.4242468849885483e-010))*x+(-2.5047413864063652e-008))*x+(1.2169594694330769e-006))*x+(-6.5714246606522449e-005))*x+(0.0053228476636875887));
		wts[3] = (((((((((((((5.139592455331391e-013))*x+(5.2106467289074012e-014))*x+(-3.4476125658026524e-013))*x+(-4.1300296516055823e-014))*x+(8.1545881158717748e-014))*x+(2.4730217873525359e-014))*x+(-5.0663350829408904e-013))*x+(2.1602768185413623e-011))*x+(-9.9398580400243447e-010))*x+(4.8273174301101916e-008))*x+(-2.6065950431055793e-006))*x+(0.00021113356990873458));
		wts[4] = (((((((((((((2.5627648151764029e-015))*x+(-5.4123372450476381e-016))*x+(-1.9099305470504646e-015))*x+(3.0704605524789486e-016))*x+(4.9815475818467304e-016))*x+(3.7567605276622729e-017))*x+(-3.0538474129401341e-015))*x+(1.2393828774685464e-013))*x+(-5.6578273657753133e-012))*x+(2.745199625733463e-010))*x+(-1.482205437510787e-008))*x+(1.2005783254850723e-006));
		break;
	case 41:
		rts[0] = (((((((((((((5.4190725980636971e-012))*x+(-1.1558161835030962e-012))*x+(-3.6356103313058453e-012))*x+(6.8922645368729708e-013))*x+(8.1742020559734852e-013))*x+(4.1914619923015073e-013))*x+(-2.3460057970344415e-011))*x+(9.6872061298528901e-010))*x+(-4.0092817632393169e-008))*x+(1.65916643326437e-006))*x+(-6.8660434023507398e-005))*x+(0.0028413351267141855));
		rts[1] = (((((((((((((5.4418099656080202e-011))*x+(1.0610771520684161e-012))*x+(-3.6086097073469617e-011))*x+(-9.9475983006414006e-013))*x+(8.2849282989627682e-012))*x+(6.3717919829286984e-012))*x+(-2.4679662017727344e-010))*x+(9.9515947334557105e-009))*x+(-4.0235036400521063e-007))*x+(1.6265466012547098e-005))*x+(-0.00065753968190438935))*x+(0.026581332502804363));
		rts[2] = (((((((((((((8.1854523159563541e-011))*x+(1.5158245029548803e-012))*x+(-5.301596199084694e-011))*x+(-1.5916157281026242e-012))*x+(1.136394682058987e-011))*x+(2.5459930460177322e-011))*x+(-9.6071905986150341e-010))*x+(3.6887273531978807e-008))*x+(-1.4171581766142527e-006))*x+(5.4439687385318673e-005))*x+(-0.0020912530552050028))*x+(0.080333534819179764));
		rts[3] = (((((((((((((2.2676734564205009e-010))*x+(9.0949470177292824e-012))*x+(-1.3498417198813209e-010))*x+(-7.9580786405131221e-012))*x+(2.4556356947869062e-011))*x+(1.0008468128338184e-010))*x+(-3.4388832522343664e-009))*x+(1.2064313370530044e-007))*x+(-4.2332285514571719e-006))*x+(0.00014852620840558051))*x+(-0.0052110909674553361))*x+(0.18283255781227861));
		rts[4] = (((((((((((((3.8077511514226592e-010))*x+(-8.4886172165473291e-012))*x+(-2.1812714597520727e-010))*x+(1.9705718538413436e-012))*x+(2.1183647428794451e-011))*x+(5.8002550910411332e-010))*x+(-1.7223201235575893e-008))*x+(5.1150580482328667e-007))*x+(-1.5189194634982844e-005))*x+(0.00045101584186144999))*x+(-0.013391951022974522))*x+(0.39764472315829913));
		wts[0] = (((((((((((((8.7917821171383054e-011))*x+(9.0949470177292824e-013))*x+(-5.1651719938187547e-011))*x+(-2.1979455292845764e-012))*x+(9.8528592692067215e-012))*x+(5.0744593712200486e-012))*x+(-1.8994124791523367e-010))*x+(8.7395923091075165e-009))*x+(-4.1458681540595949e-007))*x+(2.0646850792777987e-005))*x+(-0.0011424610005743058))*x+(0.094824270741267591));
		wts[1] = (((((((((((((2.0615213240186371e-011))*x+(4.5474735088646412e-013))*x+(-1.1671848672752578e-011))*x+(4.1685173831259204e-013))*x+(2.2737367544323206e-012))*x+(1.3683868852846595e-012))*x+(-7.4887947694908988e-011))*x+(3.4374591321532457e-009))*x+(-1.6298882201300677e-007))*x+(8.1165998540415792e-006))*x+(-0.00044911742553579878))*x+(0.037276741915732756));
		wts[2] = (((((((((((((7.3138532267572974e-012))*x+(2.2737367544323206e-013))*x+(-3.957723038183758e-012))*x+(-7.5791225147744028e-014))*x+(6.7027864740036114e-013))*x+(2.3092638912203256e-013))*x+(-1.0649638578404582e-011))*x+(4.854391703427533e-010))*x+(-2.2994382579156571e-008))*x+(1.1449537559981662e-006))*x+(-6.3353359623049819e-005))*x+(0.005258325859626236));
		wts[3] = (((((((((((((2.2500519965736505e-014))*x+(-3.8487731520338756e-014))*x+(-3.4712973236613224e-014))*x+(2.8495724298712347e-014))*x+(1.1842378929335e-014))*x+(2.9351521213527576e-015))*x+(-4.2873199203781931e-013))*x+(1.9297506590372954e-011))*x+(-9.1230311967726544e-010))*x+(4.5416046223996866e-008))*x+(-2.5129466522362929e-006))*x+(0.00020857427517222265));
		wts[4] = (((((((((((((2.794061278639977e-015))*x+(6.476300976980079e-017))*x+(-1.9625504924884276e-015))*x+(-4.0476881106125417e-018))*x+(4.889028996461301e-016))*x+(6.3678807597315286e-017))*x+(-2.5598148817654316e-015))*x+(1.1023662632320593e-013))*x+(-5.190304489266506e-012))*x+(2.5826144238856586e-010))*x+(-1.4289506649998695e-008))*x+(1.1860252542699889e-006));
		break;
	case 42:
		rts[0] = (((((((((((((4.7558993780209367e-012))*x+(2.7474319116057206e-013))*x+(-3.0328332438026942e-012))*x+(-1.7645144604709154e-013))*x+(6.5547567373869242e-013))*x+(5.1481041651868499e-013))*x+(-2.0332527328470462e-011))*x+(8.597529401373668e-010))*x+(-3.6441075190682862e-008))*x+(1.5444745012784264e-006))*x+(-6.5458618441518573e-005))*x+(0.0027742947121739622));
		rts[1] = (((((((((((((1.5309827479844291e-011))*x+(-4.5474735088646412e-013))*x+(-7.0770056481705979e-012))*x+(1.3263464400855204e-013))*x+(3.6474527102351796e-013))*x+(5.1105786269545198e-012))*x+(-2.123600924737919e-010))*x+(8.8077039735641912e-009))*x+(-3.6488747687477935e-007))*x+(1.5115752704267699e-005))*x+(-0.00062617718908571833))*x+(0.02593966564808484));
		rts[2] = (((((((((((((1.2005330063402653e-010))*x+(3.3348139065007367e-012))*x+(-7.5336477796857551e-011))*x+(-3.1074402310575047e-012))*x+(1.5854576910593703e-011))*x+(2.181247774994214e-011))*x+(-8.2421299415121508e-010))*x+(3.2441335395816389e-008))*x+(-1.2787284504045537e-006))*x+(5.0400301195838153e-005))*x+(-0.0019864822587092137))*x+(0.078295340245155109));
		rts[3] = (((((((((((((2.0493947279949981e-010))*x+(-8.4886172165473291e-012))*x+(-1.2179649881242463e-010))*x+(4.3958910585691521e-012))*x+(2.233946361229755e-011))*x+(7.9708684097568026e-011))*x+(-2.9062136401118246e-009))*x+(1.0483396491641391e-007))*x+(-3.7831606449212347e-006))*x+(0.0001365174252811463))*x+(-0.0049262722790865071))*x+(0.17776587712629033));
		rts[4] = (((((((((((((4.3413213764627773e-010))*x+(9.701276818911234e-012))*x+(-2.5966073735617096e-010))*x+(-5.7601331112285452e-012))*x+(3.7554552060707153e-011))*x+(4.6113276160516148e-010))*x+(-1.4123604212083288e-008))*x+(4.3345332774909673e-007))*x+(-1.3304438876630501e-005))*x+(0.0004083533843708409))*x+(-0.01253352365850045))*x+(0.38468909362823039));
		wts[0] = (((((((((((((9.5800108586748437e-011))*x+(-5.1538033100465928e-012))*x+(-5.8435034588910626e-011))*x+(3.2211270687791203e-012))*x+(1.1889748445052341e-011))*x+(2.8765138419354725e-012))*x+(-1.6703586661985051e-010))*x+(7.8525099015773013e-009))*x+(-3.8144099625177691e-007))*x+(1.9453696041666725e-005))*x+(-0.0011023770227982822))*x+(0.093702050559143005));
		wts[1] = (((((((((((((4.0624096679190792e-011))*x+(-4.0927261579781771e-012))*x+(-2.7891170854369797e-011))*x+(1.9895196601282805e-012))*x+(6.9230547220892423e-012))*x+(1.139828971948494e-012))*x+(-6.6224951448627196e-011))*x+(3.0877171190250388e-009))*x+(-1.4995392946803854e-007))*x+(7.6475352227151992e-006))*x+(-0.00043335980635325849))*x+(0.03683558146557752));
		wts[2] = (((((((((((((-8.7159908919905616e-013))*x+(1.3831898589463283e-012))*x+(5.139592455331391e-013))*x+(-8.763360407707902e-013))*x+(-7.4014868308343765e-014))*x+(3.969417387376476e-013))*x+(-9.2781800760851265e-012))*x+(4.3579927629563043e-010))*x+(-2.1154123421134503e-008))*x+(1.0787805931452307e-006))*x+(-6.1130545178528955e-005))*x+(0.0051960949344331342));
		wts[3] = (((((((((((((1.5039821240255452e-013))*x+(7.7567581987144266e-014))*x+(-1.2205051784045887e-013))*x+(-5.0034050976440384e-014))*x+(3.4712973236613224e-014))*x+(1.9653260500499904e-014))*x+(-3.7497753744656731e-013))*x+(1.7305409709400529e-011))*x+(-8.391910026945825e-010))*x+(4.2790794013751682e-008))*x+(-2.424776358544702e-006))*x+(0.00020610585114258433));
		wts[4] = (((((((((((((5.1717889230455204e-015))*x+(6.1524859281310752e-016))*x+(-3.8424124992886277e-015))*x+(-4.3310262783554277e-016))*x+(1.0424242487723963e-015))*x+(1.6058841178131128e-016))*x+(-2.2700008647964787e-015))*x+(9.8635489153512516e-014))*x+(-4.7731391885330306e-012))*x+(2.4332784569388226e-010))*x+(-1.3788125882587123e-008))*x+(1.1719889265506828e-006));
		break;
	case 43:
		rts[0] = (((((((((((((5.3811769854898249e-012))*x+(-7.2949054204703612e-013))*x+(-3.5716614850874367e-012))*x+(4.1093054884792452e-013))*x+(8.5561187764445391e-013))*x+(3.3991328270606869e-013))*x+(-1.772643143382879e-011))*x+(7.6516010657131273e-010))*x+(-3.319564592073794e-008))*x+(1.4401139731457131e-006))*x+(-6.2475652240191084e-005))*x+(0.002710344967102981));
		rts[1] = (((((((((((((2.7284841053187847e-011))*x+(7.5791225147744016e-014))*x+(-1.7242503721111763e-011))*x+(-4.926429634603361e-013))*x+(3.7350863143122605e-012))*x+(4.5886257756440809e-012))*x+(-1.8458568007417853e-010))*x+(7.8177198418553465e-009))*x+(-3.3168364518831872e-007))*x+(1.4071885589602567e-005))*x+(-0.0005970061479795922))*x+(0.02532824792442542));
		rts[2] = (((((((((((((5.5782341708739594e-011))*x+(-3.0316490059097606e-013))*x+(-3.0089116383654372e-011))*x+(-7.2001663890356826e-013))*x+(4.3911541069974191e-012))*x+(1.7930545936906125e-011))*x+(-7.0821659647890556e-010))*x+(2.8622498001359038e-008))*x+(-1.1567915069547277e-006))*x+(4.6750838454692745e-005))*x+(-0.0018893920684688464))*x+(0.076358011198138467));
		rts[3] = (((((((((((((2.0372681319713593e-010))*x+(-1.4551915228366852e-011))*x+(-1.3248306155825654e-010))*x+(7.5791225147744025e-012))*x+(2.8497500655551754e-011))*x+(6.5260981803779331e-011))*x+(-2.4682573022497914e-009))*x+(9.1444463852970629e-008))*x+(-3.391334917631402e-006))*x+(0.00012576906427754403))*x+(-0.0046641816292800524))*x+(0.17297244111962298));
		rts[4] = (((((((((((((4.8021320253610611e-010))*x+(-5.4569682106375694e-011))*x+(-3.155946615152061e-010))*x+(3.152914966146151e-011))*x+(6.1239309919377177e-011))*x+(3.6139624626230216e-010))*x+(-1.1656873984596435e-008))*x+(3.6926013594988183e-007))*x+(-1.1703124557079411e-005))*x+(0.00037090618649417612))*x+(-0.01175506433366573))*x+(0.37255103869419098));
		wts[0] = (((((((((((((7.5184895346562059e-011))*x+(-2.0615213240186371e-011))*x+(-4.5171570188055434e-011))*x+(1.0989727646422882e-011))*x+(8.9907340831511322e-012))*x+(1.2410813117943081e-012))*x+(-1.4694379046886752e-010))*x+(7.0726384748809315e-009))*x+(-3.5162413029402956e-007))*x+(1.8354877984109543e-005))*x+(-0.0010645833538857894))*x+(0.092618753481158875));
		wts[1] = (((((((((((((4.850638409455617e-012))*x+(1.076235397097965e-011))*x+(1.6295113406764963e-012))*x+(-6.8022624570100244e-012))*x+(-2.0818902157770935e-012))*x+(2.6686800917256428e-012))*x+(-5.7097585918578865e-011))*x+(2.7805764357680118e-009))*x+(-1.3823033299479684e-007))*x+(7.2155657387778143e-006))*x+(-0.00041850256591587488))*x+(0.036409722264128308));
		wts[2] = (((((((((((((1.3983481039758772e-011))*x+(-1.5158245029548803e-013))*x+(-9.3862695393909235e-012))*x+(8.7633604077079015e-014))*x+(2.2743288733787872e-012))*x+(1.5291471792503822e-013))*x+(-8.3780112477190479e-012))*x+(3.9237289343555893e-010))*x+(-1.9499631932877924e-008))*x+(1.0178433715573448e-006))*x+(-5.9034748266819617e-005))*x+(0.0051360224424666116));
		wts[3] = (((((((((((((4.1685173831259209e-013))*x+(3.1382304162737754e-014))*x+(-2.8451315377727343e-013))*x+(-2.4424906541753438e-014))*x+(6.8556271770603404e-014))*x+(1.3560911652869359e-014))*x+(-3.3091931972428767e-013))*x+(1.5571953159802345e-011))*x+(-7.7351031974269102e-010))*x+(4.0373474431671481e-008))*x+(-2.3416449227675074e-006))*x+(0.00020372304333076937));
		wts[4] = (((((((((((((4.0893214740359927e-015))*x+(1.7115938296304495e-016))*x+(-2.6564398828791505e-015))*x+(-1.5439038936193581e-016))*x+(6.119237061508186e-016))*x+(8.9464749266262191e-017))*x+(-1.9200723548722558e-015))*x+(8.8654707941880393e-014))*x+(-4.399001615120256e-012))*x+(2.2957960196802033e-010))*x+(-1.3315405459185389e-008))*x+(1.1584394519211884e-006));
		break;
	case 44:
		rts[0] = (((((((((((((4.3200998334214091e-012))*x+(-1.3831898589463283e-012))*x+(-2.7000623958883807e-012))*x+(9.4857455223973375e-013))*x+(6.0159284961021819e-013))*x+(1.153151648243996e-013))*x+(-1.5442924716779768e-011))*x+(6.8279260023729194e-010))*x+(-3.0303541048021243e-008))*x+(1.344947540331265e-006))*x+(-5.9692036404550825e-005))*x+(0.0026492769811077635));
		rts[1] = (((((((((((((3.1680732111756996e-011))*x+(1.4400332778071363e-012))*x+(-1.867306309577543e-011))*x+(-7.4843834833397216e-013))*x+(3.6261364281623774e-012))*x+(3.8076208852544361e-012))*x+(-1.6049284123909044e-010))*x+(6.958267480724107e-009))*x+(-3.021715786315678e-007))*x+(1.3121961887351218e-005))*x+(-0.00056982705254312487))*x+(0.024744989616146674));
		rts[2] = (((((((((((((7.1546916539470346e-011))*x+(3.3348139065007367e-012))*x+(-4.4868405287464455e-011))*x+(-1.8189894035458565e-012))*x+(9.5354835139005429e-012))*x+(1.5126270606439597e-011))*x+(-6.1246948253786582e-010))*x+(2.5330223696329313e-008))*x+(-1.0490465729614169e-006))*x+(4.3445372254050096e-005))*x+(-0.0017992497141350987))*x+(0.07451424110819127));
		rts[3] = (((((((((((((2.3768128206332523e-010))*x+(-3.0316490059097605e-012))*x+(-1.4218433837716776e-010))*x+(-9.0949470177292824e-013))*x+(2.7720640597787373e-011))*x+(5.6177877164979386e-011))*x+(-2.1041538881642432e-009))*x+(8.0054353960671649e-008))*x+(-3.0489426193399298e-006))*x+(0.00011612003199369206))*x+(-0.00442246366864595))*x+(0.16843072626331451));
		rts[4] = (((((((((((((5.9177788595358527e-010))*x+(2.6678511252005894e-011))*x+(-3.6925484891980886e-010))*x+(-2.0008883439004421e-011))*x+(7.086479551314065e-011))*x+(3.0129854167171288e-010))*x+(-9.6763580851681289e-009))*x+(3.1613945239428176e-007))*x+(-1.0335622905236857e-005))*x+(0.00033790114847050595))*x+(-0.011046940419899723))*x+(0.36115553538813899));
		wts[0] = (((((((((((((1.4248750327775875e-010))*x+(-2.4253192047278084e-011))*x+(-9.113894824016218e-011))*x+(1.4855080128957827e-011))*x+(2.0757321787338391e-011))*x+(-4.6895820560166612e-013))*x+(-1.3111985571375348e-010))*x+(6.3853748955011716e-009))*x+(-3.2473732098729313e-007))*x+(1.7341022888898529e-005))*x+(-0.0010289008935257112))*x+(0.091572180310397377));
		wts[1] = (((((((((((((-1.8796223836640515e-011))*x+(5.4569682106375694e-012))*x+(1.493087135410557e-011))*x+(-4.3579954459952806e-012))*x+(-4.5308941783635719e-012))*x+(2.2903160849333895e-012))*x+(-5.0150994468367565e-011))*x+(2.5101081213563244e-009))*x+(-1.2765973037009992e-007))*x+(6.8170011113162978e-006))*x+(-0.00040447528324929463))*x+(0.035998299757972849));
		wts[2] = (((((((((((((9.0570514051554093e-012))*x+(-1.9326762412674725e-012))*x+(-5.2224891078367364e-012))*x+(9.9949678163587419e-013))*x+(9.4383760066799961e-013))*x+(-1.7171449447535788e-014))*x+(-7.2180687353077628e-012))*x+(3.5416691801515299e-010))*x+(-1.8008198829702615e-008))*x+(9.6161981330440227e-007))*x+(-5.7056030642961066e-005))*x+(0.0050779864223316155));
		wts[3] = (((((((((((((3.7895612573872008e-014))*x+(-7.7567581987144266e-014))*x+(-3.8783790993572133e-014))*x+(5.9804013593141761e-014))*x+(1.0195548109474355e-014))*x+(-9.9388090350297863e-015))*x+(-2.8561296846104268e-013))*x+(1.4053725486592079e-011))*x+(-7.1432625960154983e-010))*x+(3.8143239408210952e-008))*x+(-2.2631577945744647e-006))*x+(0.00020142101362725551));
		wts[4] = (((((((((((((3.9782991715734773e-016))*x+(6.476300976980079e-017))*x+(-2.3303118693955105e-016))*x+(-5.7824115865892748e-019))*x+(1.655215316661203e-017))*x+(2.1900883884207186e-017))*x+(-1.619709954266829e-015))*x+(7.9957863789205386e-014))*x+(-4.0621596604695761e-012))*x+(2.1689656083650325e-010))*x+(-1.286909768080393e-008))*x+(1.1453493139012718e-006));
		break;
	case 45:
		rts[0] = (((((((((((((2.5200582361624884e-012))*x+(-9.4739031434680011e-013))*x+(-1.907807245515869e-012))*x+(6.0988251486075252e-013))*x+(5.1721589973870619e-013))*x+(1.5654144647214707e-013))*x+(-1.352052266441935e-011))*x+(6.1080810779638262e-010))*x+(-2.7719616138624042e-008))*x+(1.2579847459614467e-006))*x+(-5.7090395759007953e-005))*x+(0.0025909002564271739));
		rts[1] = (((((((((((((2.849750065555175e-011))*x+(-1.2884508275116482e-012))*x+(-1.7242503721111763e-011))*x+(6.2527760746888806e-013))*x+(3.4034997042908795e-012))*x+(3.0556298232416639e-012))*x+(-1.4000800518942924e-010))*x+(6.2096707405719558e-009))*x+(-2.7586976235801269e-007))*x+(1.225564820331662e-005))*x+(-0.00054446258995817162))*x+(0.024187989155569193));
		rts[2] = (((((((((((((3.8805107275644936e-011))*x+(-6.3664629124104977e-012))*x+(-1.9326762412674725e-011))*x+(3.5242919693700969e-012))*x+(2.1174173525650994e-012))*x+(1.1869616400872474e-011))*x+(-5.2993017381671348e-010))*x+(2.24819628099245e-008))*x+(-9.5355807357607369e-007))*x+(4.04443124825173e-005))*x+(-0.001715407760098846))*x+(0.072757412452811601));
		rts[3] = (((((((((((((2.304053244491418e-010))*x+(-3.0316490059097605e-012))*x+(-1.4294225062864521e-010))*x+(8.3370347662518408e-013))*x+(2.9596473420194038e-011))*x+(4.6140276784475041e-011))*x+(-1.8018315728340895e-009))*x+(7.0324850831582353e-008))*x+(-2.7486877746859166e-006))*x+(0.00010743331127411697))*x+(-0.0041990604024164683))*x+(0.16412141169046474));
		rts[4] = (((((((((((((5.4084618265430129e-010))*x+(2.4253192047278085e-012))*x+(-3.3242031349800527e-010))*x+(-4.5474735088646412e-012))*x+(6.3171986160644636e-011))*x+(2.4149926503014285e-010))*x+(-8.0763999932287334e-009))*x+(2.7192988246345823e-007))*x+(-9.1621448193857091e-006))*x+(0.0003086986782502299))*x+(-0.010400927066144514))*x+(0.35043646725115679));
		wts[0] = (((((((((((((1.0186340659856796e-010))*x+(6.3664629124104977e-012))*x+(-6.7454190381492182e-011))*x+(-4.1685173831259208e-012))*x+(1.5792996540161159e-011))*x+(3.2531014918883252e-012))*x+(-1.1582497923730746e-010))*x+(5.7774645808213636e-009))*x+(-3.0043670847431275e-007))*x+(1.6403869050408505e-005))*x+(-0.00099516814942557136))*x+(0.090560301960986286));
		wts[1] = (((((((((((((7.4275400644789131e-011))*x+(1.5158245029548803e-013))*x+(-4.6062117083541424e-011))*x+(-2.2737367544323203e-013))*x+(9.819700608204583e-012))*x+(1.0249578963339445e-012))*x+(-4.5759322257291992e-011))*x+(2.2712946338524867e-009))*x+(-1.1810626795542382e-007))*x+(6.4485910024544837e-006))*x+(-0.00039121446687034265))*x+(0.035600516276635498));
		wts[2] = (((((((((((((1.7090921270816274e-011))*x+(4.3579954459952808e-013))*x+(-1.1342630538517065e-011))*x+(-3.2684965844964604e-013))*x+(2.6917727306378461e-012))*x+(2.0835185428798769e-013))*x+(-6.6148105511606056e-012))*x+(3.2041472253219183e-010))*x+(-1.6660410613022109e-008))*x+(9.0965061067474712e-007))*x+(-5.5185433968801894e-005))*x+(0.0050218743504355781));
		wts[3] = (((((((((((((3.2448118266377907e-013))*x+(5.2106467289074012e-014))*x+(-2.0383694732117874e-013))*x+(-2.4794980883295161e-014))*x+(4.2891616184685212e-014))*x+(8.7615100360001926e-015))*x+(-2.5510669965367327e-013))*x+(1.2711462669493892e-011))*x+(-6.6085418882714836e-010))*x+(3.6081808870358147e-008))*x+(-2.1889594766779022e-006))*x+(0.00019919529851873183));
		wts[4] = (((((((((((((7.586524001605236e-016))*x+(-4.6259292692714849e-016))*x+(-3.5966600068585797e-016))*x+(2.9895067902666967e-016))*x+(4.2211604582102285e-017))*x+(-3.9537239223304718e-017))*x+(-1.4349189877393047e-015))*x+(7.2312499232197555e-014))*x+(-3.7579597735673096e-012))*x+(2.0517403087569981e-010))*x+(-1.2447179155706012e-008))*x+(1.1326931289831247e-006));
		break;
	case 46:
		rts[0] = (((((((((((((8.1854523159563541e-012))*x+(-3.694822225952521e-013))*x+(-5.2153836804791354e-012))*x+(2.5105843330190208e-013))*x+(1.1661782650662644e-012))*x+(1.9047726359152267e-013))*x+(-1.1915931204716419e-011))*x+(5.4774031144066981e-010))*x+(-2.5405307434167576e-008))*x+(1.1783603920419911e-006))*x+(-5.4655207499877833e-005))*x+(0.0025350407234223707));
		rts[1] = (((((((((((((2.3950027146687109e-011))*x+(-1.6674069532503684e-012))*x+(-1.426769813406281e-011))*x+(1.1179205709292242e-012))*x+(2.7995383788947939e-012))*x+(2.422358609995475e-012))*x+(-1.2250430299805731e-010))*x+(5.5556606722480719e-009))*x+(-2.5236826100653398e-007))*x+(1.1463944971749905e-005))*x+(-0.00052075474462201412))*x+(0.023655512417026986));
		rts[2] = (((((((((((((1.0065074699620405e-010))*x+(-1.8189894035458565e-012))*x+(-6.1011936243933932e-011))*x+(1.2884508275116484e-012))*x+(1.2192913345643319e-011))*x+(1.0274447959091047e-011))*x+(-4.6180629690676745e-010))*x+(2.0009386888138653e-008))*x+(-8.6869067341307127e-007))*x+(3.771341102622635e-005))*x+(-0.0016372924587516981))*x+(0.071081517411253278));
		rts[3] = (((((((((((((1.9160021717349687e-010))*x+(0))*x+(-1.2384286189141372e-010))*x+(-1.6674069532503684e-012))*x+(2.7512214728631076e-011))*x+(3.936880451268128e-011))*x+(-1.5489565186044274e-009))*x+(6.1979996246463984e-008))*x+(-2.4844991469707978e-006))*x+(9.9591871671874277e-005))*x+(-0.0039921672716434044))*x+(0.16002710448205479));
		rts[4] = (((((((((((((2.6678511252005893e-010))*x+(-8.1248193358381585e-011))*x+(-1.6279955161735415e-010))*x+(4.7748471843078726e-011))*x+(2.8459605042977877e-011))*x+(1.8560797343525337e-010))*x+(-6.7745477376017033e-009))*x+(2.3493569697071354e-007))*x+(-8.1505776281520764e-006))*x+(0.00028276656734380995))*x+(-0.0098099673879509918))*x+(0.34033534081046674));
		wts[0] = (((((((((((((1.1823431123048067e-010))*x+(-1.2126596023639042e-012))*x+(-7.6132285660908864e-011))*x+(1.2126596023639042e-012))*x+(1.7015130045668535e-011))*x+(1.5347723092418162e-012))*x+(-1.0291190122302395e-010))*x+(5.2392176523123153e-009))*x+(-2.7842477607712779e-007))*x+(1.5536114928216271e-005))*x+(-0.00096323916927474533))*x+(0.089581242909382366));
		wts[1] = (((((((((((((9.0949470177292824e-012))*x+(2.2737367544323206e-012))*x+(-2.0842586915629608e-012))*x+(-2.1979455292845764e-012))*x+(-7.8633396090784434e-013))*x+(1.4820737230062755e-012))*x+(-3.9604615883111663e-011))*x+(2.0595292878529863e-009))*x+(-1.0945288413573748e-007))*x+(6.1074639192716194e-006))*x+(-0.00037866273782299838))*x+(0.035215634521748938));
		wts[2] = (((((((((((((-6.442254137558241e-013))*x+(1.0231815394945443e-012))*x+(6.8448950211556315e-013))*x+(-8.0765024298064714e-013))*x+(-1.8266869498499241e-013))*x+(3.3913612658883113e-013))*x+(-5.6154432955442717e-012))*x+(2.9051707336099258e-010))*x+(-1.5439680730103263e-008))*x+(8.6153032578632771e-007))*x+(-5.3414863284326979e-005))*x+(0.0049675822208612875));
		wts[3] = (((((((((((((3.3277084791431355e-013))*x+(7.5199106201277261e-014))*x+(-2.0924003270768782e-013))*x+(-4.3742787170231161e-014))*x+(4.4667973024085463e-014))*x+(1.297341863567188e-014))*x+(-2.2681654008686419e-013))*x+(1.1524896488535052e-011))*x+(-6.1242751308983908e-010))*x+(3.4173071983197587e-008))*x+(-2.118728804401467e-006))*x+(0.00019704177246148463));
		wts[4] = (((((((((((((1.4247862149356174e-015))*x+(9.8069700508555481e-016))*x+(-7.5633943552588789e-016))*x+(-6.10622663543836e-016))*x+(1.0271008580679345e-016))*x+(1.5724545508281432e-016))*x+(-1.2671612890924331e-015))*x+(6.5536908763011895e-014))*x+(-3.4825272240779268e-012))*x+(1.9432005857009154e-010))*x+(-1.204782275566579e-008))*x+(1.1204474367977604e-006));
		break;
	case 47:
		rts[0] = (((((((((((((7.7686005776437617e-013))*x+(9.8528592692067219e-013))*x+(8.4080890398278589e-014))*x+(-5.3053857603420807e-013))*x+(-2.19824158875781e-013))*x+(3.1234274426121067e-013))*x+(-1.0339557913556044e-011))*x+(4.9231828798864307e-010))*x+(-2.3327563174249204e-008))*x+(1.1053164787015503e-006))*x+(-5.2372569268225135e-005))*x+(0.0024815390071777806));
		rts[1] = (((((((((((((2.2737367544323206e-011))*x+(3.2590226813529926e-012))*x+(-1.3017142919125035e-011))*x+(-1.9042545318370681e-012))*x+(2.2950530365051236e-012))*x+(2.6766736975029439e-012))*x+(-1.0743443172126868e-010))*x+(4.9825090349860561e-009))*x+(-2.3131688258829866e-007))*x+(1.0738990169635818e-005))*x+(-0.00049856233267793915))*x+(0.023145974685083212));
		rts[2] = (((((((((((((1.2732925824820995e-010))*x+(4.5474735088646412e-012))*x+(-8.0414489881756409e-011))*x+(-3.979039320256561e-012))*x+(1.7574090331133146e-011))*x+(1.0247210487553577e-011))*x+(-4.0363534736798101e-010))*x+(1.7855828667497537e-008))*x+(-7.9305803866539881e-007))*x+(3.5222940457208897e-005))*x+(-0.0015643939137679811))*x+(0.069481089231681212));
		rts[3] = (((((((((((((1.0428872580329576e-010))*x+(-1.9402553637822468e-011))*x+(-5.9875067866717771e-011))*x+(1.0686562745831905e-011))*x+(1.0345502232667057e-011))*x+(3.0577022395542976e-011))*x+(-1.3343441906954467e-009))*x+(5.479583187195658e-008))*x+(-2.2513014986680346e-006))*x+(9.2495351882585869e-005))*x+(-0.0038001966115910448))*x+(0.15613210505440056));
		rts[4] = (((((((((((((5.3114490583539009e-010))*x+(1.4551915228366852e-011))*x+(-3.3242031349800527e-010))*x+(-1.1671848672752578e-011))*x+(6.7984728957526386e-011))*x+(1.6311219042108857e-010))*x+(-5.7166733569147254e-009))*x+(2.0381744884427158e-007))*x+(-7.2748398272463408e-006))*x+(0.00025965954038783173))*x+(-0.0092679789723337531))*x+(0.33080021776508683));
		wts[0] = (((((((((((((1.5279510989785194e-010))*x+(6.3664629124104977e-012))*x+(-9.6709603288521365e-011))*x+(-3.9032480951088173e-012))*x+(2.1609973070250515e-011))*x+(2.6183499812759692e-012))*x+(-9.2214236246945802e-011))*x+(4.7606939131602149e-009))*x+(-2.5844354312187789e-007))*x+(1.473129051949203e-005))*x+(-0.00093298175256600413))*x+(0.088633266569926247));
		wts[1] = (((((((((((((9.398111918320258e-011))*x+(-1.2278178473934531e-011))*x+(-6.2830925647479788e-011))*x+(6.631732200427602e-012))*x+(1.5141665699047732e-011))*x+(-4.8731389294213544e-013))*x+(-3.7048290361478088e-011))*x+(1.8716201921620268e-009))*x+(-1.0159780123678945e-007))*x+(5.7910758359420531e-006))*x+(-0.00036676812483552496))*x+(0.034842971815499793));
		wts[2] = (((((((((((((6.1769848495411371e-012))*x+(-2.3495279795800643e-012))*x+(-3.9245643771816195e-012))*x+(1.423453947306067e-012))*x+(8.8936265759305867e-013))*x+(-2.0590936363381232e-013))*x+(-5.0903263086136495e-012))*x+(2.6403555268098938e-010))*x+(-1.4331605741856509e-008))*x+(8.1689991572308574e-007))*x+(-5.173698697608885e-005))*x+(0.0049150137332482999));
		wts[3] = (((((((((((((1.1534477077172292e-012))*x+(-9.2962674595279766e-014))*x+(-7.7463961171512586e-013))*x+(5.8471745963591574e-014))*x+(1.8599936405886788e-013))*x+(-9.1292714129072758e-015))*x+(-2.1743660113167826e-013))*x+(1.0473651170887315e-011))*x+(-5.6847212928732432e-010))*x+(3.2402774047935292e-008))*x+(-2.0521749315877543e-006))*x+(0.00019495661560805339));
		wts[4] = (((((((((((((3.7747582837255322e-015))*x+(-8.5117098554595328e-016))*x+(-2.6194324487249787e-015))*x+(5.620504062164854e-016))*x+(6.6606153463026152e-016))*x+(-1.0766127572781058e-016))*x+(-1.2044176058688867e-015))*x+(5.9566790157801933e-014))*x+(-3.2325522941463281e-012))*x+(1.8425342740699884e-010))*x+(-1.1669374231203558e-008))*x+(1.1085905158763651e-006));
		break;
	case 48:
		rts[0] = (((((((((((((8.6780952794166897e-012))*x+(1.2695030212247123e-012))*x+(-5.9093470857381663e-012))*x+(-8.4436161766158569e-013))*x+(1.4586850246208389e-012))*x+(3.8694973151602119e-013))*x+(-9.3240322870021454e-012))*x+(4.4348760774859381e-010))*x+(-2.1457930554520201e-008))*x+(1.0381870369340536e-006))*x+(-5.023000036063198e-005))*x+(0.0024302489089771937));
		rts[1] = (((((((((((((2.1524707941959299e-011))*x+(-3.7895612573872007e-013))*x+(-1.2979247306551162e-011))*x+(-4.1685173831259214e-013))*x+(2.6432189770275727e-012))*x+(2.2586377212974181e-012))*x+(-9.4653100172574029e-011))*x+(4.4788848555891523e-009))*x+(-2.1241540748099622e-007))*x+(1.0073895182338467e-005))*x+(-0.00047775889591666459))*x+(0.022657924903171377));
		rts[2] = (((((((((((((7.7003884750107916e-011))*x+(3.9411437076826888e-012))*x+(-4.702845520417516e-011))*x+(-2.2737367544323202e-012))*x+(9.5402204654722774e-012))*x+(8.2174267390655586e-012))*x+(-3.5248885292086618e-010))*x+(1.5974731463567572e-008))*x+(-7.2548032647075844e-007))*x+(3.2947013356548115e-005))*x+(-0.0014962577404663354))*x+(0.067951142663071437));
		rts[3] = (((((((((((((1.7341032313803831e-010))*x+(2.2434202643732228e-011))*x+(-1.0694141868346679e-010))*x+(-1.3869794202037154e-011))*x+(2.1856294551980675e-011))*x+(3.0385175856887749e-011))*x+(-1.1562949116713146e-009))*x+(4.8587558569105717e-008))*x+(-2.0448328799660409e-006))*x+(8.6057355682965048e-005))*x+(-0.003621747108479473))*x+(0.15242220598692161));
		rts[4] = (((((((((((((4.7051192571719481e-010))*x+(-9.701276818911234e-012))*x+(-2.9649527277797455e-010))*x+(4.2443086082736646e-012))*x+(6.1485631401107327e-011))*x+(1.3150724953447932e-010))*x+(-4.8436608797904528e-009))*x+(1.7751748752440713e-007))*x+(-6.5136221343298217e-006))*x+(0.00023900313307778642))*x+(-0.0087696967625000739))*x+(0.32178482175621609));
		wts[0] = (((((((((((((1.7341032313803831e-010))*x+(-5.7601331112285452e-012))*x+(-1.1755219020415095e-010))*x+(2.9937533933358886e-012))*x+(2.8791191652999256e-011))*x+(9.6989083431253675e-013))*x+(-8.3504462603893132e-011))*x+(4.3347854195019409e-009))*x+(-2.4026869358910002e-007))*x+(1.3983647795631769e-005))*x+(-0.00090427590002149208))*x+(0.087714762336556854));
		wts[1] = (((((((((((((3.0316490059097604e-011))*x+(-6.3664629124104977e-012))*x+(-1.7090921270816274e-011))*x+(4.907481828316425e-012))*x+(3.0055957722652234e-012))*x+(-7.2949054204703622e-013))*x+(-3.1771178280829794e-011))*x+(1.7041995962567096e-009))*x+(-9.4453063389140127e-008))*x+(5.4971668883481888e-006))*x+(-0.0003554834538690692))*x+(0.034481895005390582));
		wts[2] = (((((((((((((1.0800249583553523e-011))*x+(-1.6484591469634324e-012))*x+(-6.7335766592198825e-012))*x+(1.0468662973532143e-012))*x+(1.4281908988778014e-012))*x+(-1.5358085173981334e-013))*x+(-4.5765706039683583e-012))*x+(2.4040291054146695e-010))*x+(-1.332373210429875e-008))*x+(7.7544052348229914e-007))*x+(-5.0145150382126268e-005))*x+(0.0048640795736805131));
		wts[3] = (((((((((((((9.5923269327613525e-014))*x+(-2.0605739337042905e-013))*x+(-5.1440333474298924e-014))*x+(1.3063624256422676e-013))*x+(6.4392935428259079e-015))*x+(-2.5877448332304691e-014))*x+(-1.7649336853109432e-013))*x+(9.537623006187582e-012))*x+(-5.2849399337781653e-010))*x+(3.075826119251663e-008))*x+(-1.9890338821246547e-006))*x+(0.00019293628525542681));
		wts[4] = (((((((((((((-1.2490009027033011e-015))*x+(-1.0547118733938987e-015))*x+(8.7372239073365187e-016))*x+(6.5225602696727947e-016))*x+(-2.2602001289081147e-016))*x+(-1.214306433183765e-016))*x+(-9.8080316654827748e-016))*x+(5.4233080157804758e-014))*x+(-3.0052098512077881e-012))*x+(1.7490211321155791e-010))*x+(-1.1310332342937812e-008))*x+(1.0971022209639604e-006));
		break;
	case 49:
		rts[0] = (((((((((((((5.7980287238024175e-012))*x+(-1.3547681495159243e-012))*x+(-3.8345622973186737e-012))*x+(8.869941818071917e-013))*x+(9.0919864229969483e-013))*x+(-4.1781393160060049e-014))*x+(-8.2023369577891945e-012))*x+(4.0040355753223622e-010))*x+(-1.9771917160807395e-008))*x+(9.7638535790983347e-007))*x+(-4.8216270797226847e-005))*x+(0.0023810360722411432));
		rts[1] = (((((((((((((2.1524707941959299e-011))*x+(-7.1243751638879376e-012))*x+(-1.2865560468829546e-011))*x+(4.3390476397083449e-012))*x+(2.6290081223123707e-012))*x+(7.9639998299777903e-013))*x+(-8.3552942342635106e-011))*x+(4.0352656031454144e-009))*x+(-1.9540569136389241e-007))*x+(9.4626071212508528e-006))*x+(-0.00045823089661800511))*x+(0.022190031873461753));
		rts[2] = (((((((((((((3.3348139065007367e-011))*x+(-1.1217101321866114e-011))*x+(-1.7545668621702738e-011))*x+(6.9727927135924485e-012))*x+(2.4868995751603507e-012))*x+(5.1147234595797873e-012))*x+(-3.0869543958071211e-010))*x+(1.4326602126857322e-008))*x+(-6.6494965773415216e-007))*x+(3.0863016148708712e-005))*x+(-0.0014324779691278621))*x+(0.066487122086223052));
		rts[3] = (((((((((((((1.7341032313803831e-010))*x+(-7.8822874153653775e-012))*x+(-1.0512242927992094e-010))*x+(4.2443086082736646e-012))*x+(2.1022591075355493e-011))*x+(2.2616575279243989e-011))*x+(-1.0044389024225589e-009))*x+(4.3205010236135877e-008))*x+(-1.86150001159809e-006))*x+(8.0203236964661751e-005))*x+(-0.0034555781570083967))*x+(0.14888451886130213));
		rts[4] = (((((((((((((3.8320043434699375e-010))*x+(-1.4551915228366852e-011))*x+(-2.3404330325623352e-010))*x+(8.1854523159563541e-012))*x+(4.621369953383691e-011))*x+(1.0770880483808772e-010))*x+(-4.1211241826507221e-009))*x+(1.5518652910865663e-007))*x+(-5.8494147798793242e-006))*x+(0.00022048089712226973))*x+(-0.0083105447160056363))*x+(0.31324778731245562));
		wts[0] = (((((((((((((1.673470251262188e-010))*x+(-1.6674069532503683e-011))*x+(-1.1186784831807017e-010))*x+(1.0876040808701266e-011))*x+(2.6953254443166468e-011))*x+(-1.2114753644709708e-012))*x+(-7.4733700709354408e-011))*x+(3.9546237395882144e-009))*x+(-2.2370469909827048e-007))*x+(1.3288067583175354e-005))*x+(-0.00087701246521043597))*x+(0.086824234071302644));
		wts[1] = (((((((((((((1.8189894035458565e-012))*x+(8.033869865660865e-012))*x+(2.7663797178926562e-012))*x+(-5.7032896923677364e-012))*x+(-2.027415272702152e-012))*x+(1.9391895496786065e-012))*x+(-2.7836547881558239e-011))*x+(1.55437869982696e-009))*x+(-8.7941534341699296e-008))*x+(5.2237245515678503e-006))*x+(-0.00034476581764957741))*x+(0.034131815938372743));
		wts[2] = (((((((((((((1.6484591469634324e-011))*x+(9.0949470177292824e-013))*x+(-1.077893330148072e-011))*x+(-6.0396132539608516e-013))*x+(2.5031828461881864e-012))*x+(2.1212661257171323e-013))*x+(-4.2294778790363799e-012))*x+(2.1927202646191782e-010))*x+(-1.2405186951165251e-008))*x+(7.3686821920893508e-007))*x+(-4.8633300829723403e-005))*x+(0.0048146967760893163));
		wts[3] = (((((((((((((6.8093678843676264e-013))*x+(1.4506914188435377e-013))*x+(-4.5186077102243866e-013))*x+(-9.6219328800846883e-014))*x+(1.0580425424677741e-013))*x+(2.5116482967509527e-014))*x+(-1.6830720844795977e-013))*x+(8.6960858074654669e-012))*x+(-4.9205870019106027e-010))*x+(2.9228268608293731e-008))*x+(-1.929065566601399e-006))*x+(0.00019097749050196443));
		wts[4] = (((((((((((((4.3853809472693683e-015))*x+(9.0205620750793969e-016))*x+(-3.1120939159023919e-015))*x+(-5.874930171974787e-016))*x+(7.9999664300463757e-016))*x+(1.4815622687014418e-016))*x+(-9.88796898815832e-016))*x+(4.9450007077404129e-014))*x+(-2.7980177675601919e-012))*x+(1.6620202664167773e-010))*x+(-1.096933177874754e-008))*x+(1.0859638387590694e-006));
		break;
	case 50:
		rts[0] = (((((((((((((5.2106467289074008e-012))*x+(2.3684757858670003e-013))*x+(-3.4662643126163553e-012))*x+(-1.13686837721616e-013))*x+(8.1194310534253112e-013))*x+(1.5509815654013437e-013))*x+(-7.2668954187449223e-012))*x+(3.6219636086650314e-010))*x+(-1.8248291528029367e-008))*x+(9.1939321279144279e-007))*x+(-4.6321253886240494e-005))*x+(0.0023337768073179682));
		rts[1] = (((((((((((((1.7280399333685637e-011))*x+(6.5180453627059852e-012))*x+(-9.9854939132152757e-012))*x+(-3.8558785793914767e-012))*x+(1.8166209277599896e-012))*x+(2.2879476091475226e-012))*x+(-7.380666448379239e-011))*x+(3.6430950848635267e-009))*x+(-1.800650276523319e-007))*x+(8.8997929477742811e-006))*x+(-0.00043987616528372325))*x+(0.02174107213181195));
		rts[2] = (((((((((((((8.7917821171383054e-011))*x+(-9.0949470177292824e-013))*x+(-5.4380204043506332e-011))*x+(-2.2737367544323206e-013))*x+(1.152026622245709e-011))*x+(5.9626377909201738e-012))*x+(-2.7259986860409902e-010))*x+(1.2878042780310276e-008))*x+(-6.1060226542545659e-007))*x+(2.8951136169024411e-005))*x+(-0.0013726909843104083))*x+(0.065084856207910644));
		rts[3] = (((((((((((((1.5764574830730754e-010))*x+(1.2732925824820995e-011))*x+(-9.4890613884975509e-011))*x+(-8.5644084416950737e-012))*x+(1.8521480645479941e-011))*x+(2.1915506446627355e-011))*x+(-8.7511864421685449e-010))*x+(3.852194030429245e-008))*x+(-1.698260540676048e-006))*x+(7.4868277191081356e-005))*x+(-0.0033005882411357617))*x+(0.14550732466618066));
		rts[4] = (((((((((((((3.0073958138624824e-010))*x+(-1.4551915228366852e-011))*x+(-1.7856412644808489e-010))*x+(7.1243751638879384e-012))*x+(3.2306009719225884e-011))*x+(8.9831549606363595e-011))*x+(-3.5207475453565471e-009))*x+(1.361429831092664e-007))*x+(-5.2677531644877238e-006))*x+(0.000203824179455081))*x+(-0.0078865303706120299))*x+(0.30515202525440788));
		wts[0] = (((((((((((((9.519377878556648e-011))*x+(-3.0316490059097606e-013))*x+(-5.6957105698529631e-011))*x+(1.1747639897900322e-012))*x+(1.1397105481592007e-011))*x+(6.5251507900635874e-013))*x+(-6.5233892361978477e-011))*x+(3.6140869556315156e-009))*x+(-2.0858050750471868e-007))*x+(1.2639979850871209e-005))*x+(-0.00085109197866903232))*x+(0.085960289852645366));
		wts[1] = (((((((((((((2.4253192047278084e-011))*x+(3.0316490059097606e-013))*x+(-1.4097167877480388e-011))*x+(-1.5347723092418162e-012))*x+(2.6290081223123707e-012))*x+(1.1451580424666947e-012))*x+(-2.5479470385410725e-011))*x+(1.4206253210839273e-009))*x+(-8.1995914780197397e-008))*x+(4.9689521964407782e-006))*x+(-0.00033457611321374703))*x+(0.033792187430541118));
		wts[2] = (((((((((((((2.7284841053187847e-012))*x+(-8.905468954859922e-013))*x+(-1.2410813117943085e-012))*x+(7.0343730840249918e-013))*x+(7.5791225147744003e-014))*x+(-1.2412293415309248e-013))*x+(-3.5416114485542494e-012))*x+(2.0043060729631651e-010))*x+(-1.156650111799884e-008))*x+(7.0092954971804939e-007))*x+(-4.7195922340244278e-005))*x+(0.0047667881536534009));
		wts[3] = (((((((((((((1.7763568394002505e-014))*x+(-1.1842378929335002e-015))*x+(1.1472304587793282e-014))*x+(-2.1464311809419696e-015))*x+(-9.9735035045493208e-015))*x+(3.5943470422239435e-015))*x+(-1.397131831522754e-013))*x+(7.9493020962069957e-012))*x+(-4.5879152081523703e-010))*x+(2.7802741465431824e-008))*x+(-1.8720511876552603e-006))*x+(0.00018907716968773322));
		wts[4] = (((((((((((((3.0068540250264655e-015))*x+(5.0885221961986338e-016))*x+(-1.995510238531987e-015))*x+(-2.8449465006019631e-016))*x+(4.8528889240451169e-016))*x+(7.0617701501222514e-017))*x+(-8.5901564001479114e-016))*x+(4.5198744197625741e-014))*x+(-2.6088454264100666e-012))*x+(1.5809597876917012e-010))*x+(-1.0645128345051742e-008))*x+(1.0751579595632864e-006));
		break;
	case 51:
		rts[0] = (((((((((((((1.4968766966679443e-012))*x+(1.1368683772161603e-013))*x+(-1.0267342531733446e-012))*x+(-7.460698725481052e-014))*x+(2.4469315462738445e-013))*x+(1.4566126083082054e-013))*x+(-6.4131339128081777e-012))*x+(3.2829295763351729e-010))*x+(-1.6868642480245832e-008))*x+(8.6675169786466311e-007))*x+(-4.4535798667772874e-005))*x+(0.0022883570534972704));
		rts[1] = (((((((((((((3.1832314562052488e-012))*x+(-4.0169349328304325e-012))*x+(8.5265128291212022e-014))*x+(2.2547889481453841e-012))*x+(-7.460698725481052e-013))*x+(8.7130302972582285e-013))*x+(-6.5188484240271308e-011))*x+(3.2959993623293826e-009))*x+(-1.6620067967478466e-007))*x+(8.3807415069934998e-006))*x+(-0.0004226025616189722))*x+(0.021309919265364755));
		rts[2] = (((((((((((((8.6705161569019154e-011))*x+(3.0316490059097605e-012))*x+(-5.597181977160895e-011))*x+(-2.6147972675971683e-012))*x+(1.270450411539059e-011))*x+(5.6890788376525352e-012))*x+(-2.4086732608452621e-010))*x+(1.1601827202648943e-008))*x+(-5.6169553144802542e-007))*x+(2.719396514806275e-005))*x+(-0.0013165703310316756))*x+(0.063740518369556382));
		rts[3] = (((((((((((((2.1221543041368324e-010))*x+(1.8189894035458565e-012))*x+(-1.2634397232128927e-010))*x+(-9.0949470177292824e-013))*x+(2.50774216207598e-011))*x+(1.7012761569882663e-011))*x+(-7.6569417473137936e-010))*x+(3.4435392019342238e-008))*x+(-1.5525287040962787e-006))*x+(6.9996178598754247e-005))*x+(-0.0031557966329367965))*x+(0.14227994410941674));
		rts[4] = (((((((((((((3.686485191186269e-010))*x+(1.2126596023639042e-011))*x+(-2.2070404763023055e-010))*x+(-9.7012768189112324e-012))*x+(4.221571240729341e-011))*x+(7.8784978541079909e-011))*x+(-3.0222295777093673e-009))*x+(1.1983565547287375e-007))*x+(-4.7566272682135012e-006))*x+(0.00018880390829586111))*x+(-0.0074941577626304323))*x+(0.29746418402310332));
		wts[0] = (((((((((((((6.730260793119669e-011))*x+(6.3664629124104977e-012))*x+(-4.1874651894128569e-011))*x+(-4.9264296346033608e-012))*x+(8.8202038265687098e-012))*x+(2.3815024026892689e-012))*x+(-5.851837533062583e-011))*x+(3.3086358837882317e-009))*x+(-1.9474586542463551e-007))*x+(1.2035295424766185e-005))*x+(-0.00082642361962022119))*x+(0.08512163282406858));
		wts[1] = (((((((((((((7.4881730445971087e-011))*x+(1.5158245029548803e-012))*x+(-4.8639018738564723e-011))*x+(-6.8212102632969608e-013))*x+(1.1233680652367184e-011))*x+(4.346153067065946e-013))*x+(-2.3830493134369135e-011))*x+(1.3007470656134501e-009))*x+(-7.6557277790360396e-008))*x+(4.7312423008029807e-006))*x+(-0.00032487863758587105))*x+(0.033462499669458301));
		wts[2] = (((((((((((((8.9433645674337933e-012))*x+(1.3263464400855202e-013))*x+(-5.1443294069031253e-012))*x+(5.4474943074941023e-014))*x+(9.5094302802560061e-013))*x+(9.5479180117763399e-015))*x+(-3.2602809341142343e-012))*x+(1.8349169406128851e-010))*x+(-1.0799318448754628e-008))*x+(6.6739775054913458e-007))*x+(-4.5827978567766763e-005))*x+(0.0047202817912685505));
		wts[3] = (((((((((((((1.5513516397428853e-013))*x+(-9.5923269327613525e-014))*x+(-1.1760962574195824e-013))*x+(5.6843418860808015e-014))*x+(3.0845696367502264e-014))*x+(-9.1824695995038999e-015))*x+(-1.3041622180335704e-013))*x+(7.278886983893191e-012))*x+(-4.2836061367211456e-010))*x+(2.6472684537952984e-008))*x+(-1.8177909745548117e-006))*x+(0.00018723247026040444));
		wts[4] = (((((((((((((-1.563564093013762e-015))*x+(-9.3906364166211144e-016))*x+(1.0576030791871933e-015))*x+(5.7303698823100515e-016))*x+(-2.5608855314107615e-016))*x+(-1.0663128366394935e-016))*x+(-6.9684610006527182e-016))*x+(4.1395094184758001e-014))*x+(-2.4358086352946694e-012))*x+(1.5053281220372889e-010))*x+(-1.0336586060421509e-008))*x+(1.0646683627610294e-006));
		break;
	case 52:
		rts[0] = (((((((((((((5.9306633678109693e-012))*x+(6.2527760746888816e-013))*x+(-3.6983749396313207e-012))*x+(-4.1093054884792462e-013))*x+(7.8278124722904364e-013))*x+(2.0228263508670352e-013))*x+(-5.7541055253906848e-012))*x+(2.9812520045228535e-010))*x+(-1.5616945970494771e-008))*x+(8.1805346723116252e-007))*x+(-4.2851619234772088e-005))*x+(0.0022446714599127109));
		rts[1] = (((((((((((((-6.8212102632969618e-012))*x+(9.0949470177292824e-013))*x+(6.7738407475796212e-012))*x+(-8.4317737976865215e-013))*x+(-2.4442670110147446e-012))*x+(1.3891110484109959e-012))*x+(-5.771956986440803e-011))*x+(2.9876997912718175e-009))*x+(-1.5364539639415678e-007))*x+(7.9012806057746996e-006))*x+(-0.00040632681594333415))*x+(0.020895534476463147));
		rts[2] = (((((((((((((8.2460852960745485e-011))*x+(1.5158245029548803e-012))*x+(-5.2674901477682092e-011))*x+(-1.7810937909719842e-012))*x+(1.1714481236898184e-011))*x+(4.906297590423491e-012))*x+(-2.1306068020976454e-010))*x+(1.0474441166271237e-008))*x+(-5.175887657730508e-007))*x+(2.5576165635018966e-005))*x+(-0.0012638222490340652))*x+(0.062450591675212518));
		rts[3] = (((((((((((((1.6855968472858268e-010))*x+(-3.0316490059097604e-011))*x+(-1.0284869252548863e-010))*x+(1.7962520360015329e-011))*x+(2.1373125491663814e-011))*x+(1.0852356050842596e-011))*x+(-6.7141521971810403e-010))*x+(3.0858293994147815e-008))*x+(-1.4220988619103221e-006))*x+(6.5537813296157044e-005))*x+(-0.0030203278402549578))*x+(0.13919262481451422));
		rts[4] = (((((((((((((3.1286617740988731e-010))*x+(-2.1827872842550278e-011))*x+(-1.9387395392792919e-010))*x+(1.39455854271849e-011))*x+(4.0131453715730458e-011))*x+(6.0756140859060296e-011))*x+(-2.6039928731809896e-009))*x+(1.0581793456291659e-007))*x+(-4.3060173541276106e-006))*x+(0.00017522395339641947))*x+(-0.0071303551361458287))*x+(0.29015419043253837));
		wts[0] = (((((((((((((6.6696278130014733e-011))*x+(9.3981119183202574e-012))*x+(-3.8426151149906218e-011))*x+(-7.1243751638879368e-012))*x+(7.1717446796052773e-012))*x+(2.8125649957170631e-012))*x+(-5.2456113526962625e-011))*x+(3.0342716487533985e-009))*x+(-1.8206900452103858e-007))*x+(1.1470347350518254e-005))*x+(-0.00080292431432893788))*x+(0.084307053005965915));
		wts[1] = (((((((((((((4.0320931778599814e-011))*x+(-6.5180453627059852e-012))*x+(-2.8023805498378348e-011))*x+(3.9221959013957522e-012))*x+(7.1859555343204793e-012))*x+(-4.5889218351173134e-013))*x+(-2.1276091999311575e-011))*x+(1.1929629876542927e-009))*x+(-7.1573822891616651e-008))*x+(4.5091533346526078e-006))*x+(-0.00031564073329649862))*x+(0.033142276995252094));
		wts[2] = (((((((((((((-7.2001663890356815e-013))*x+(-7.7686005776437617e-013))*x+(7.1291121154596705e-013))*x+(6.3238303482648917e-013))*x+(-2.3388698385436629e-013))*x+(-1.2530717204602598e-013))*x+(-2.8534304548818073e-012))*x+(1.6829140858654057e-010))*x+(-1.0096342954388214e-008))*x+(6.3606946981044116e-007))*x+(-4.4524862781043111e-005))*x+(0.0046751105914673054));
		wts[3] = (((((((((((((2.5224267119483557e-013))*x+(1.2079226507921703e-013))*x+(-1.7933802591111694e-013))*x+(-7.3348734493568671e-014))*x+(4.3853809472693683e-014))*x+(1.7726560959848332e-014))*x+(-1.1856169980969017e-013))*x+(6.6731643359278313e-012))*x+(-4.0047664528119678e-010))*x+(2.5230031666056568e-008))*x+(-1.7661021982426345e-006))*x+(0.00018544073076272338));
		wts[4] = (((((((((((((2.6182759664076607e-015))*x+(8.0491169285323849e-016))*x+(-1.6289053439422217e-015))*x+(-5.5626799462989617e-016))*x+(3.3277778680821746e-016))*x+(1.4878867813742738e-016))*x+(-6.7307044992447517e-016))*x+(3.7939875127563729e-014))*x+(-2.2772492835975539e-012))*x+(1.434666581976716e-010))*x+(-1.0042665857407399e-008))*x+(1.0544799143802356e-006));
		break;
	case 53:
		rts[0] = (((((((((((((-1.4210854715202004e-012))*x+(-6.6317322004276014e-013))*x+(1.1048939541069558e-012))*x+(4.2277292777725956e-013))*x+(-3.2773783686934621e-013))*x+(-3.1826393372587905e-015))*x+(-5.0364943697071372e-012))*x+(2.7124591924406377e-010))*x+(-1.4479228468110282e-008))*x+(7.7293609804327663e-007))*x+(-4.1261198428171345e-005))*x+(0.0022026225697463794));
		rts[1] = (((((((((((((1.8189894035458565e-012))*x+(-1.5916157281026244e-012))*x+(-3.0316490059097621e-013))*x+(1.0800249583553523e-012))*x+(-2.5105843330190193e-013))*x+(7.179442225909345e-013))*x+(-5.1686210866819238e-011))*x+(2.7134745191522329e-009))*x+(-1.4225358858458806e-007))*x+(7.4577063856872778e-006))*x+(-0.0003909735237909734))*x+(0.020496958226492581));
		rts[2] = (((((((((((((7.8216544352471828e-011))*x+(-6.0632980118195212e-013))*x+(-4.9756939309493951e-011))*x+(5.1159076974727213e-013))*x+(1.1089203629429297e-011))*x+(3.5432397756570327e-012))*x+(-1.8900007484982476e-010))*x+(9.4761098227517469e-009))*x+(-4.777275658488882e-007))*x+(2.4084189189949031e-005))*x+(-0.001214181820812418))*x+(0.061211838269761273));
		rts[3] = (((((((((((((9.5800108586748437e-011))*x+(9.701276818911234e-012))*x+(-5.888978193979709e-011))*x+(-6.4422541375582414e-012))*x+(1.2107648217352104e-011))*x+(1.4021376652332645e-011))*x+(-5.8965425135208227e-010))*x+(2.7717284467598802e-008))*x+(-1.3050828562843897e-006))*x+(6.1450180164420346e-005))*x+(-0.0028933983413314325))*x+(0.13623644289127523));
		rts[4] = (((((((((((((3.8320043434699375e-010))*x+(-2.1827872842550278e-011))*x+(-2.4253192047278083e-010))*x+(1.2278178473934531e-011))*x+(5.2087519482787073e-011))*x+(5.1623298228757143e-011))*x+(-2.2525933710918853e-009))*x+(9.3721970036616156e-008))*x+(-3.9075255816959737e-006))*x+(0.00016291572949108285))*x+(-0.0067924146404161985))*x+(0.28319485651195275));
		wts[0] = (((((((((((((5.3963352305193738e-011))*x+(-2.9406995357324675e-011))*x+(-2.9065934844159831e-011))*x+(1.8341476485754047e-011))*x+(4.4148388648560894e-012))*x+(-3.2057319761709847e-012))*x+(-4.6908995206725493e-011))*x+(2.787826710222892e-009))*x+(-1.7043368221355176e-007))*x+(1.0941840315169721e-005))*x+(-0.00078051794348211036))*x+(0.083515419953330977));
		wts[1] = (((((((((((((6.6696278130014733e-011))*x+(7.8822874153653775e-012))*x+(-4.3163102721640215e-011))*x+(-5.2674901477682088e-012))*x+(1.0054179711005418e-011))*x+(1.6224059133188953e-012))*x+(-1.9454216015901693e-011))*x+(1.0956444640441987e-009))*x+(-6.6999799708256091e-008))*x+(4.3013898695098973e-006))*x+(-0.00030683247677238247))*x+(0.032831075014227884));
		wts[2] = (((((((((((((6.4043585249843691e-012))*x+(5.3053857603420807e-013))*x+(-3.68771679859492e-012))*x+(-4.05009359383257e-013))*x+(6.5044266269372498e-013))*x+(1.6164847238542279e-013))*x+(-2.6252611196042608e-012))*x+(1.545588657059227e-010))*x+(-9.4511233983638841e-009))*x+(6.0676197238008578e-007))*x+(-4.3282353901743262e-005))*x+(0.0046312118672525437));
		wts[3] = (((((((((((((1.0291027289592116e-012))*x+(-1.7171449447535753e-014))*x+(-6.6990857305881936e-013))*x+(2.7385501274087184e-015))*x+(1.5274818447134445e-013))*x+(3.7308119556674537e-015))*x+(-1.1718895529903387e-013))*x+(6.1307165941104635e-012))*x+(-3.7488332441581654e-010))*x+(2.4067534157924718e-008))*x+(-1.7168174271476292e-006))*x+(0.00018369946468150302));
		wts[4] = (((((((((((((2.581268532253489e-015))*x+(9.8994886362409785e-016))*x+(-1.4866580189121237e-015))*x+(-6.4011296263544172e-016))*x+(2.8268764643938716e-016))*x+(1.5764299587939234e-016))*x+(-6.0550206703336807e-016))*x+(3.4849948628579611e-014))*x+(-2.1317181078280179e-012))*x+(1.3685629596751195e-010))*x+(-9.7624156591745755e-009))*x+(1.0445784752460066e-006));
		break;
	case 54:
		rts[0] = (((((((((((((5.6464462735069292e-012))*x+(-1.0610771520684161e-012))*x+(-3.4769224536527564e-012))*x+(6.2409336957595453e-013))*x+(7.376321775609538e-013))*x+(-3.9449924808347221e-014))*x+(-4.6062598180185432e-012))*x+(2.4720747208532379e-010))*x+(-1.3443248189984325e-008))*x+(7.3107641704057286e-007))*x+(-3.975770381157962e-005))*x+(0.0021621200944390308));
		rts[1] = (((((((((((((2.0615213240186371e-011))*x+(-4.5474735088646412e-013))*x+(-1.3585577107733114e-011))*x+(1.9895196601282805e-013))*x+(3.1299407510232413e-012))*x+(8.485064502868529e-013))*x+(-4.6506280308259797e-011))*x+(2.4688263285573458e-009))*x+(-1.3189826641076447e-007))*x+(7.0467231555945697e-006))*x+(-0.0003764742709784921))*x+(0.020113302818162072));
		rts[2] = (((((((((((((6.0632980118195207e-011))*x+(-9.0949470177292824e-013))*x+(-3.8047195024167494e-011))*x+(1.7053025658242404e-013))*x+(8.1854523159563525e-012))*x+(3.3075764349632664e-012))*x+(-1.6777275864872837e-010))*x+(8.5896735650218635e-009))*x+(-4.4163085951195075e-007))*x+(2.2706037624400929e-005))*x+(-0.0011674096388770636))*x+(0.060021272202309864));
		rts[3] = (((((((((((((1.8553691916167736e-010))*x+(1.8189894035458565e-012))*x+(-1.1512687099942316e-010))*x+(-7.5791225147744023e-013))*x+(2.404476617812179e-011))*x+(1.0887883187630601e-011))*x+(-5.2081983170637614e-010))*x+(2.4952720186396011e-008))*x+(-1.1998587060394841e-006))*x+(5.7695531593173387e-005))*x+(-0.0027743052300347494))*x+(0.13340321678823669));
		rts[4] = (((((((((((((3.7834979593753815e-010))*x+(-8.4886172165473291e-012))*x+(-2.367717873615523e-010))*x+(3.4863963567962238e-012))*x+(4.9813782728354759e-011))*x+(4.5384733008783464e-011))*x+(-1.9541405530768921e-009))*x+(8.32477713430535e-008))*x+(-3.5540827717876295e-006))*x+(0.00015173378651820813))*x+(-0.0064779417962031408))*x+(0.27656154160186902));
		wts[0] = (((((((((((((8.7917821171383054e-011))*x+(-6.9727927135924493e-012))*x+(-5.4683368944097304e-011))*x+(3.6379788070917125e-012))*x+(1.1690796479039515e-011))*x+(1.2908193032975147e-013))*x+(-4.3324307104815794e-011))*x+(2.5646073413080708e-009))*x+(-1.5973708675232068e-007))*x+(1.0446807023144674e-005))*x+(-0.00075913464364783291))*x+(0.082745676157889053));
		wts[1] = (((((((((((((-1.8189894035458565e-012))*x+(0))*x+(3.4106051316484809e-012))*x+(1.7053025658242404e-013))*x+(-1.5939842038884915e-012))*x+(1.9066230076229352e-013))*x+(-1.636942433454654e-011))*x+(1.0081880515618498e-009))*x+(-6.2794900862472845e-008))*x+(4.1067853724420971e-006))*x+(-0.00029842640371820331))*x+(0.032528478005144718));
		wts[2] = (((((((((((((-1.3263464400855203e-012))*x+(2.2737367544323206e-013))*x+(1.6460906711775652e-012))*x+(-1.7763568394002505e-013))*x+(-6.3978452165732348e-013))*x+(9.2370555648813024e-014))*x+(-2.2464530236021574e-012))*x+(1.4220785660157276e-010))*x+(-8.857968472724317e-009))*x+(5.7931070395617068e-007))*x+(-4.2096577764336988e-005))*x+(0.0045885269762188808));
		wts[3] = (((((((((((((-3.9198274256098859e-013))*x+(-2.2500519965736505e-014))*x+(2.9080441758348264e-013))*x+(8.1416355139178094e-016))*x+(-7.6272321791748242e-014))*x+(4.9173628132355897e-015))*x+(-8.5069971900164632e-014))*x+(5.6403475640065537e-012))*x+(-3.5135600456653523e-010))*x+(2.2978665078053136e-008))*x+(-1.6697829903223087e-006))*x+(0.00018200634593461038));
		wts[4] = (((((((((((((-2.8218168542556059e-015))*x+(5.5511151231257827e-016))*x+(2.0267352610995695e-015))*x+(-3.550400714165865e-016))*x+(-5.122493864269846e-016))*x+(8.9518959374886479e-017))*x+(-4.7781015616888788e-016))*x+(3.2069171085307109e-014))*x+(-1.9979314730355234e-012))*x+(1.3066461046461862e-010))*x+(-9.4949616383496195e-009))*x+(1.0349508184518835e-006));
		break;
	case 55:
		rts[0] = (((((((((((((2.4821626235886165e-012))*x+(-1.8947806286936003e-013))*x+(-1.5170087408478139e-012))*x+(1.0539717247108151e-013))*x+(3.1441516057384433e-013))*x+(5.3882824128474262e-014))*x+(-4.0997344408211234e-012))*x+(2.2567391936660164e-010))*x+(-1.249829123383996e-008))*x+(6.9218562642921189e-007))*x+(-3.8334914168437621e-005))*x+(0.0021230802665303137));
		rts[1] = (((((((((((((2.2131037743141253e-011))*x+(7.5791225147744016e-014))*x+(-1.3471890270011498e-011))*x+(-1.7053025658242404e-013))*x+(2.7687481936785235e-012))*x+(8.2807834663375002e-013))*x+(-4.1560458778159643e-011))*x+(2.2501940681133683e-009))*x+(-1.2246831373556125e-007))*x+(6.6653918386743814e-006))*x+(-0.00036276687015438338))*x+(0.019743745795531401));
		rts[2] = (((((((((((((7.0031092036515474e-011))*x+(-1.6674069532503684e-012))*x+(-4.3523111041092001e-011))*x+(7.0106883261663212e-013))*x+(9.3033728868855779e-012))*x+(2.772893026303791e-012))*x+(-1.496307522330653e-010))*x+(7.8009550671017288e-009))*x+(-4.0887993975335934e-007))*x+(2.1431059891906246e-005))*x+(-0.0011232889137866926))*x+(0.058876135395989515));
		rts[3] = (((((((((((((1.4915713109076023e-010))*x+(-3.637978807091713e-012))*x+(-8.9357854449190199e-011))*x+(1.4400332778071365e-012))*x+(1.7820411812863313e-011))*x+(9.2607403227399719e-012))*x+(-4.5997013605377407e-010))*x+(2.2512410602359978e-008))*x+(-1.1050288300507025e-006))*x+(5.4240639793368122e-005))*x+(-0.0026624164635607171))*x+(0.13068543167544022));
		rts[4] = (((((((((((((3.0073958138624824e-010))*x+(-1.8189894035458565e-011))*x+(-1.8189894035458562e-010))*x+(9.398111918320259e-012))*x+(3.6303996845769377e-011))*x+(3.7312967530548726e-011))*x+(-1.6998432291378167e-009))*x+(7.4147591178075345e-008))*x+(-3.2397134680136239e-006))*x+(0.00014155218882289097))*x+(-0.006184812963446056))*x+(0.2702318608518392));
		wts[0] = (((((((((((((9.1555799978474767e-011))*x+(-9.0949470177292824e-013))*x+(-5.6729732023086392e-011))*x+(7.5791225147744053e-014))*x+(1.2098174314208638e-011))*x+(7.5909648937037356e-013))*x+(-3.9334905702996061e-011))*x+(2.3630749209265405e-009))*x+(-1.4988841404162123e-007))*x+(9.9825701393950004e-006))*x+(-0.00073871019015172483))*x+(0.08199683110683495));
		wts[1] = (((((((((((((3.7289282772690058e-011))*x+(-1.5158245029548803e-013))*x+(-2.290789780090563e-011))*x+(-1.1368683772161603e-013))*x+(4.8127427968817455e-012))*x+(3.2981025318197982e-013))*x+(-1.5455710785280036e-011))*x+(9.28955431097241e-010))*x+(-5.8923224628230437e-008))*x+(3.9242873862768701e-006))*x+(-0.00029039726651907457))*x+(0.032234096583615909));
		wts[2] = (((((((((((((5.5327594357853132e-012))*x+(1.8947806286936004e-014))*x+(-3.4485007442223524e-012))*x+(-4.0264088359739006e-014))*x+(7.4162898044960447e-013))*x+(5.188442268414898e-014))*x+(-2.1879905294971041e-012))*x+(1.3103959584093161e-010))*x+(-8.3118181515758529e-009))*x+(5.5356720140743959e-007))*x+(-4.0963972892679227e-005))*x+(0.004547000991086742));
		wts[3] = (((((((((((((2.1316282072803006e-013))*x+(-1.1842378929335002e-015))*x+(-1.3115434664238515e-013))*x+(-5.9211894646675022e-016))*x+(2.758904216193514e-014))*x+(1.8920050711320377e-015))*x+(-8.6528006981723138e-014))*x+(5.1977640941336389e-012))*x+(-3.2969267210689507e-010))*x+(2.195753540916778e-008))*x+(-1.6248576198413375e-006))*x+(0.00018035919580239773));
		wts[4] = (((((((((((((1.1842378929335002e-015))*x+(-3.7007434154171883e-017))*x+(-7.2395793064098746e-016))*x+(1.5612511283791264e-017))*x+(1.5048726154098802e-016))*x+(6.6136332521615763e-018))*x+(-4.9118875922645367e-016))*x+(2.9556650005807303e-014))*x+(-1.874746219178118e-012))*x+(1.248581148316627e-010))*x+(-9.2395004959083726e-009))*x+(1.0255845550459146e-006));
		break;
	case 56:
		rts[0] = (((((((((((((2.5769016550232964e-012))*x+(5.6843418860808015e-014))*x+(-1.5987211554602252e-012))*x+(-5.0922229396140509e-014))*x+(3.4061642395499798e-013))*x+(8.0306132114552994e-014))*x+(-3.6886142288731581e-012))*x+(2.0635537723023845e-010))*x+(-1.1634922525427525e-008))*x+(6.5600511495033981e-007))*x+(-3.6987155042254937e-005))*x+(0.0020854252613665947));
		rts[1] = (((((((((((((2.5011104298755527e-011))*x+(-3.7895612573872007e-013))*x+(-1.5622466283578735e-011))*x+(1.13686837721616e-013))*x+(3.3620513780382075e-012))*x+(6.7471953949886177e-013))*x+(-3.7354674908840479e-011))*x+(2.0543995763825742e-009))*x+(-1.1386622380399336e-007))*x+(6.3110857685272819e-006))*x+(-0.00034979469287828194))*x+(0.019387524058502241));
		rts[2] = (((((((((((((7.0031092036515474e-011))*x+(-4.5474735088646412e-013))*x+(-4.3598902266239747e-011))*x+(0))*x+(9.3081098384573124e-012))*x+(2.5573617297898936e-012))*x+(-1.3366633725790203e-010))*x+(7.097545440259978e-009))*x+(-3.7910948594751154e-007))*x+(2.0249778912890166e-005))*x+(-0.0010816229575530286))*x+(0.057773876317044677));
		rts[3] = (((((((((((((1.4551915228366852e-010))*x+(2.4253192047278085e-012))*x+(-9.0191557925815388e-011))*x+(-2.2737367544323206e-012))*x+(1.9014123608940281e-011))*x+(8.8202038265687098e-012))*x+(-4.0793975604932104e-010))*x+(2.0352900994187923e-008))*x+(-1.0193850531840334e-006))*x+(5.1056177711764995e-005))*x+(-0.0025571624592359171))*x+(0.1280761728857702));
		rts[4] = (((((((((((((3.3711936945716537e-010))*x+(4.850638409455617e-012))*x+(-2.0842586915629605e-010))*x+(-3.7895612573872005e-012))*x+(4.3371528590796515e-011))*x+(3.4210264251062953e-011))*x+(-1.4851485966952773e-009))*x+(6.6215144182516867e-008))*x+(-2.9593467630132744e-006))*x+(0.00013226152768800831))*x+(-0.0059111393943971141))*x+(0.26418543285216778));
		wts[0] = (((((((((((((9.5800108586748437e-011))*x+(-6.0632980118195212e-013))*x+(-5.9344529290683555e-011))*x+(-1.8947806286936008e-013))*x+(1.2657134599673249e-011))*x+(7.6264920304917417e-013))*x+(-3.5795662730227676e-011))*x+(2.180599404747833e-009))*x+(-1.4080689790067302e-007))*x+(9.5467095244476195e-006))*x+(-0.00071918545065304093))*x+(0.081267955923787882));
		wts[1] = (((((((((((((4.1836756281554699e-011))*x+(4.5474735088646412e-013))*x+(-2.6337450738841046e-011))*x+(-5.1159076974727213e-013))*x+(5.7648700628002798e-012))*x+(3.9849605097212282e-013))*x+(-1.4162448991328345e-011))*x+(8.5721466961767112e-010))*x+(-5.5353148777544562e-008))*x+(3.7529445069892087e-006))*x+(-0.00028272181942838885))*x+(0.031947565595398471));
		wts[2] = (((((((((((((5.6464462735069292e-012))*x+(-3.7895612573872008e-014))*x+(-3.5503452030146333e-012))*x+(-7.1054273576010019e-015))*x+(7.7626793881790935e-013))*x+(4.1300296516055817e-014))*x+(-1.9945989304659406e-012))*x+(1.2092175409132247e-010))*x+(-7.8082171104989114e-009))*x+(5.293972594114007e-007))*x+(-3.9881260199368812e-005))*x+(0.0045065824025272002));
		wts[3] = (((((((((((((2.1908401019269755e-013))*x+(5.9211894646675012e-016))*x+(-1.3670546176551093e-013))*x+(-1.7023419710919066e-015))*x+(2.9457917586720818e-014))*x+(1.9775847626135601e-015))*x+(-7.8916329489716221e-014))*x+(4.7963915825177672e-012))*x+(-3.0971706870532598e-010))*x+(2.0998821895886864e-008))*x+(-1.5819112490283653e-006))*x+(0.00017875597114017376));
		wts[4] = (((((((((((((1.3045120539345589e-015))*x+(9.2518585385429707e-018))*x+(-8.1821123950239405e-016))*x+(-1.445602896647339e-017))*x+(1.7853195773594641e-016))*x+(1.2757445562912769e-017))*x+(-4.5018107080671554e-016))*x+(2.7273717771349414e-014))*x+(-1.7611579225873142e-012))*x+(1.1940653936131591e-010))*x+(-8.9952926283535704e-009))*x+(1.0164680670036469e-006));
		break;
	case 57:
		rts[0] = (((((((((((((2.2926845607192563e-012))*x+(9.473903143468002e-015))*x+(-1.4364805641283358e-012))*x+(-2.0132044179869503e-014))*x+(3.1101047663166049e-013))*x+(6.583622536027177e-014))*x+(-3.3206169295733425e-012))*x+(1.889910034025277e-010))*x+(-1.0844833807886754e-008))*x+(6.2230283938554873e-007))*x+(-3.5709242071370862e-005))*x+(0.0020490826792770541));
		rts[1] = (((((((((((((2.3343697345505156e-011))*x+(-3.0316490059097606e-013))*x+(-1.4627706453514595e-011))*x+(1.1368683772161602e-013))*x+(3.1678363635971132e-012))*x+(5.8738199489501609e-013))*x+(-3.3570331699669019e-011))*x+(1.8786939411559916e-009))*x+(-1.0600630484062604e-007))*x+(5.9814526192590129e-006))*x+(-0.00033750608382258261))*x+(0.019043928603155038));
		rts[2] = (((((((((((((7.5791225147744016e-011))*x+(-6.0632980118195212e-013))*x+(-4.7862158680800349e-011))*x+(1.8947806286936003e-013))*x+(1.047813687667561e-011))*x+(2.1932085777128423e-012))*x+(-1.1981008777676528e-010))*x+(6.4689058554279191e-009))*x+(-3.5199984998087369e-007))*x+(1.9153743331677221e-005))*x+(-0.0010422329877936769))*x+(0.056712130996020578));
		rts[3] = (((((((((((((1.5158245029548803e-010))*x+(-3.0316490059097605e-012))*x+(-9.4208492858645812e-011))*x+(1.4400332778071361e-012))*x+(2.0046779051578291e-011))*x+(6.8662113032284334e-012))*x+(-3.6261157039992509e-010))*x+(1.8437410709282176e-008))*x+(-9.4187997048041561e-007))*x+(4.811619511120116e-005))*x+(-0.0024580288313847064))*x+(0.12556906717373167));
		rts[4] = (((((((((((((2.5950915490587551e-010))*x+(8.4886172165473291e-012))*x+(-1.5840366055878499e-010))*x+(-6.0632980118195202e-012))*x+(3.2173375075217336e-011))*x+(2.9932796981787156e-011))*x+(-1.2998852364868676e-009))*x+(5.9279687529093891e-008))*x+(-2.7086633962077516e-006))*x+(0.00012376644530533629))*x+(-0.0056552367324397574))*x+(0.25840366040474561));
		wts[0] = (((((((((((((1.0004441719502211e-010))*x+(-6.0632980118195212e-013))*x+(-6.24140739091672e-011))*x+(7.5791225147744003e-014))*x+(1.3481364173154969e-011))*x+(5.6132876125047905e-013))*x+(-3.2700508967309354e-011))*x+(2.0150835074635629e-009))*x+(-1.324207424916827e-007))*x+(9.1370334819225931e-006))*x+(-0.00070050590019305771))*x+(0.080558178522188578));
		wts[1] = (((((((((((((3.8805107275644936e-011))*x+(-6.0632980118195212e-013))*x+(-2.3987922759260982e-011))*x+(2.4632148173016805e-013))*x+(5.0993283669716521e-012))*x+(1.7526720815415803e-013))*x+(-1.2822779874947324e-011))*x+(7.921613735343651e-010))*x+(-5.2056440806117862e-008))*x+(3.5918951471758387e-006))*x+(-0.00027537862792274999))*x+(0.031668542211114141));
		wts[2] = (((((((((((((6.0254023992456496e-012))*x+(-3.7895612573872008e-014))*x+(-3.7492971690274617e-012))*x+(1.1842378929335002e-014))*x+(8.0735418350741384e-013))*x+(2.7533531010703879e-014))*x+(-1.8181844918530032e-012))*x+(1.1174379014692684e-010))*x+(-7.3431769293669236e-009))*x+(5.0667934034173689e-007))*x+(-3.8845416090407773e-005))*x+(0.0044672228503962411));
		wts[3] = (((((((((((((2.1789977229976404e-013))*x+(-2.9605947323337505e-015))*x+(-1.364834171605859e-013))*x+(1.0362081563168126e-015))*x+(2.9550436172106246e-014))*x+(1.1032841307212493e-015))*x+(-7.1906601043873294e-014))*x+(4.4323535004312893e-012))*x+(-2.9127099921792226e-010))*x+(2.0097703638671445e-008))*x+(-1.5408239453672498e-006))*x+(0.0001771947537172178));
		wts[4] = (((((((((((((1.2027416100105861e-015))*x+(-2.7755575615628914e-017))*x+(-7.4940054162198057e-016))*x+(1.3299546649155522e-017))*x+(1.6183524427966961e-016))*x+(4.3006686175258332e-018))*x+(-4.0846413346580973e-016))*x+(2.5204140713154983e-014))*x+(-1.6562672889477014e-012))*x+(1.1428247032041369e-010))*x+(-8.7616560574214807e-009))*x+(1.0075904466032628e-006));
		break;
	case 58:
		rts[0] = (((((((((((((2.5769016550232964e-012))*x+(6.6317322004276009e-014))*x+(-1.6200374375330282e-012))*x+(-5.3290705182007501e-014))*x+(3.537910705138832e-013))*x+(6.5688195623655091e-014))*x+(-3.0005627612202561e-012))*x+(1.7334989462399381e-010))*x+(-1.0120686191883442e-008))*x+(5.908701941836034e-007))*x+(-3.4496431057645554e-005))*x+(0.002013985080965554));
		rts[1] = (((((((((((((2.1524707941959299e-011))*x+(-1.5158245029548803e-013))*x+(-1.3263464400855202e-011))*x+(-9.4739031434680067e-015))*x+(2.793617189430127e-012))*x+(5.5126273916054426e-013))*x+(-3.0193477347969143e-011))*x+(1.7207126834506423e-009))*x+(-9.8813024979974934e-008))*x+(5.6743815490834879e-006))*x+(-0.00032585384574119965))*x+(0.018712299811620536));
		rts[2] = (((((((((((((6.6393113229423761e-011))*x+(-1.8189894035458565e-012))*x+(-4.1097791836364195e-011))*x+(9.0949470177292824e-013))*x+(8.7112539404188283e-012))*x+(1.7905676941154525e-012))*x+(-1.0730253722594321e-010))*x+(5.9059167926515475e-009))*x+(-3.2727070499449784e-007))*x+(1.8135400300258359e-005))*x+(-0.0010049562066902103))*x+(0.055688706103856803));
		rts[3] = (((((((((((((1.4066851387421289e-010))*x+(-4.850638409455617e-012))*x+(-8.6401996668428183e-011))*x+(2.5011104298755527e-012))*x+(1.8019363778876141e-011))*x+(5.7601331112285452e-012))*x+(-3.2274035296116682e-010))*x+(1.6734172270105319e-008))*x+(-8.7160288593975588e-007))*x+(4.5397673519650031e-005))*x+(-0.0023645500947021602))*x+(0.1231582307408662));
		rts[4] = (((((((((((((2.8376234695315361e-010))*x+(1.2126596023639042e-012))*x+(-1.7356190558833381e-010))*x+(-1.9705718538413444e-012))*x+(3.5565032400578886e-011))*x+(2.5129528088048879e-011))*x+(-1.1421565915270548e-009))*x+(5.3198038566885472e-008))*x+(-2.4839706551279166e-006))*x+(0.00011598357379873542))*x+(-0.0054155990333914893))*x+(0.25286953946445112));
		wts[0] = (((((((((((((8.8524150972565011e-011))*x+(-2.1221543041368323e-012))*x+(-5.4645473331523428e-011))*x+(9.8528592692067199e-013))*x+(1.1558161835030962e-011))*x+(3.2566542055671255e-013))*x+(-2.9634665092241143e-011))*x+(1.8646605740949931e-009))*x+(-1.2466598444301386e-007))*x+(8.7515537176609711e-006))*x+(-0.0006826211899039282))*x+(0.079866679218754233));
		wts[1] = (((((((((((((3.8805107275644936e-011))*x+(-1.3642420526593924e-012))*x+(-2.4215296434704214e-011))*x+(7.3896444519050419e-013))*x+(5.2272260594084701e-012))*x+(4.7961634663806763e-014))*x+(-1.1725879526617669e-011))*x+(7.3303104327256575e-010))*x+(-4.9007931638792953e-008))*x+(3.4403576817642239e-006))*x+(-0.00026834789916113248))*x+(0.031396704201845663));
		wts[2] = (((((((((((((5.7980287238024175e-012))*x+(1.8947806286936004e-014))*x+(-3.6356103313058461e-012))*x+(-3.5527136788005009e-014))*x+(7.9166303142604499e-013))*x+(3.9449924808347227e-014))*x+(-1.6600517257122267e-012))*x+(1.0339954818287347e-010))*x+(-6.9131487392265481e-009))*x+(4.8530318669451117e-007))*x+(-3.7853648551207948e-005))*x+(0.0044288768804897306));
		wts[3] = (((((((((((((2.0250467969162855e-013))*x+(-5.3290705182007514e-015))*x+(-1.2589929099249275e-013))*x+(2.5165055224836883e-015))*x+(2.6996923215468392e-014))*x+(6.4994306233264366e-016))*x+(-6.5377969242034568e-014))*x+(4.101490270099391e-012))*x+(-2.7421371819264304e-010))*x+(1.9249807208376284e-008))*x+(-1.5014849621242138e-006))*x+(0.00017567374056851653));
		wts[4] = (((((((((((((1.1749860343949572e-015))*x+(-2.3129646346357426e-017))*x+(-7.3031858338623569e-016))*x+(9.2518585385429691e-018))*x+(1.5648651356207447e-016))*x+(4.8608397399766785e-018))*x+(-3.7201912918861469e-016))*x+(2.3322392646325563e-014))*x+(-1.5592737061056663e-012))*x+(1.0946103897331413e-010))*x+(-8.5379610390119578e-009))*x+(9.9894144156423571e-007));
		break;
	case 59:
		rts[0] = (((((((((((((2.4063713984408724e-012))*x+(-3.7895612573872008e-014))*x+(-1.4956924587750107e-012))*x+(1.4210854715202002e-014))*x+(3.1930014188219497e-013))*x+(4.418687638008123e-014))*x+(-2.7083751907852616e-012))*x+(1.5923866392153485e-010))*x+(-9.4559848941184553e-009))*x+(5.6151929500071474e-007))*x+(-3.3344373871408385e-005))*x+(0.0019800695698472593));
		rts[1] = (((((((((((((2.1373125491663814e-011))*x+(-3.0316490059097606e-013))*x+(-1.3216094885137863e-011))*x+(7.5791225147744003e-014))*x+(2.8019068546806616e-012))*x+(4.8020846558453434e-013))*x+(-2.7248462745414297e-011))*x+(1.5784096252247082e-009))*x+(-9.2219666969946726e-008))*x+(5.3879747673341955e-006))*x+(-0.00031479478561341001))*x+(0.018392023225664873));
		rts[2] = (((((((((((((7.0637421837697418e-011))*x+(-1.8189894035458565e-012))*x+(-4.3864171554256849e-011))*x+(7.7686005776437627e-013))*x+(9.3744271604615879e-012))*x+(1.6176689617471612e-012))*x+(-9.6527008608404672e-011))*x+(5.4006985550358869e-009))*x+(-3.046755370633702e-007))*x+(1.7187985978874457e-005))*x+(-0.00096964411618816508))*x+(0.054701563827969507));
		rts[3] = (((((((((((((1.4915713109076023e-010))*x+(-1.2126596023639042e-012))*x+(-9.1783173653918012e-011))*x+(1.5158245029548801e-013))*x+(1.9241497284383513e-011))*x+(5.5327594357853124e-012))*x+(-2.8821419325216385e-010))*x+(1.5216234790689974e-008))*x+(-8.0775975624947094e-007))*x+(4.2880146954841575e-005))*x+(-0.0022763041900214207))*x+(0.12083822313568757));
		rts[4] = (((((((((((((3.4197000786662102e-010))*x+(-7.2759576141834259e-012))*x+(-2.1388283736693362e-010))*x+(3.0316490059097609e-012))*x+(4.5967378052106746e-011))*x+(2.0795217399912264e-011))*x+(-1.0073086068966102e-009))*x+(4.7849966359573649e-008))*x+(-2.2821009313759668e-006))*x+(0.00010883981262288511))*x+(-0.0051908765591576088))*x+(0.2475674921168477));
		wts[0] = (((((((((((((8.3067182761927441e-011))*x+(-1.2126596023639042e-012))*x+(-5.0135895435232669e-011))*x+(3.0316490059097601e-013))*x+(1.0222341491801974e-011))*x+(4.5711582667233109e-013))*x+(-2.690899355191808e-011))*x+(1.7277068664611761e-009))*x+(-1.1748546803006892e-007))*x+(8.3884633961528437e-006))*x+(-0.00066548476262993624))*x+(0.079192686752977581));
		wts[1] = (((((((((((((3.637978807091713e-011))*x+(-9.0949470177292824e-013))*x+(-2.2699471931749333e-011))*x+(3.979039320256561e-013))*x+(4.900376400958824e-012))*x+(1.1487107561454951e-013))*x+(-1.0694112262399358e-011))*x+(6.7919210996099833e-010))*x+(-4.6185167727289901e-008))*x+(3.2976218181842336e-006))*x+(-0.00026161133087689308))*x+(0.031131748374343404));
		wts[2] = (((((((((((((5.4190725980636971e-012))*x+(-2.0842586915629605e-013))*x+(-3.3656040917170072e-012))*x+(1.0658141036401503e-013))*x+(7.217929957429683e-013))*x+(4.8109664400423492e-015))*x+(-1.5103751582756786e-012))*x+(9.5809212415550363e-011))*x+(-6.5149647846679537e-009))*x+(4.651686029118543e-007))*x+(-3.6903375830339413e-005))*x+(0.004391501723809854));
		wts[3] = (((((((((((((2.0605739337042905e-013))*x+(-3.5527136788005009e-015))*x+(-1.2626936533403446e-013))*x+(1.1102230246251565e-015))*x+(2.6441811703155814e-014))*x+(9.3906364166211144e-016))*x+(-5.961261576962565e-014))*x+(3.8002442627934246e-012))*x+(-2.5841953602319617e-010))*x+(1.8451158315977427e-008))*x+(-1.4637918927661621e-006))*x+(0.00017419123523918284));
		wts[4] = (((((((((((((1.1564823173178713e-015))*x+(-4.6259292692714853e-018))*x+(-7.095019016745141e-016))*x+(-4.6259292692714853e-018))*x+(1.4904165864434066e-016))*x+(8.0411661126008251e-018))*x+(-3.3901420805453519e-016))*x+(2.1609233499808589e-014))*x+(-1.4694625358929148e-012))*x+(1.0491964609205521e-010))*x+(-8.323625254280229e-009))*x+(9.9051140525933042e-007));
		break;
	case 60:
		rts[0] = (((((((((((((2.2168933355715126e-012))*x+(0))*x+(-1.3749001936957939e-012))*x+(-1.1842378929335002e-014))*x+(2.9383902718412475e-013))*x+(4.6259292692714852e-014))*x+(-2.4508127009307637e-012))*x+(1.4648148434955507e-010))*x+(-8.8449682581042323e-009))*x+(5.3408061707315346e-007))*x+(-3.2249079425148874e-005))*x+(0.0019472774158868875));
		rts[1] = (((((((((((((2.0463630789890885e-011))*x+(-7.5791225147744016e-014))*x+(-1.2515026052521231e-011))*x+(-8.526512829121201e-014))*x+(2.6100603160254345e-012))*x+(4.68070027181966e-013))*x+(-2.46103507943e-011))*x+(1.4499946798807173e-009))*x+(-8.616718289583547e-008))*x+(5.12052286249486e-006))*x+(-0.00030428931379157949))*x+(0.018082525747000706));
		rts[2] = (((((((((((((6.6393113229423761e-011))*x+(-1.6674069532503684e-012))*x+(-4.1400956736955173e-011))*x+(7.5791225147744013e-013))*x+(8.9007320032881889e-012))*x+(1.4110194494302655e-012))*x+(-8.6913513423307138e-011))*x+(4.9464718987479728e-009))*x+(-2.8399714544398891e-007))*x+(1.630543102413886e-005))*x+(-0.00093616103678693962))*x+(0.053748808328838174));
		rts[3] = (((((((((((((1.5340143969903389e-010))*x+(-4.2443086082736646e-012))*x+(-9.5610630523879081e-011))*x+(1.8947806286936002e-012))*x+(2.0539422015038628e-011))*x+(4.5451050330787747e-012))*x+(-2.5803907159153517e-010))*x+(1.3860628496805324e-008))*x+(-7.4965651283842583e-007))*x+(4.054537771986759e-005))*x+(-0.0021929077119094758))*x+(0.11860400626775605));
		rts[4] = (((((((((((((2.9103830456733704e-010))*x+(9.701276818911234e-012))*x+(-1.8311159995694956e-010))*x+(-7.4275400644789134e-012))*x+(3.9828288815139487e-011))*x+(2.0217309308160715e-011))*x+(-8.8941239558456187e-010))*x+(4.3134020799584498e-008))*x+(-2.1003280920398968e-006))*x+(0.00010227088308674878))*x+(-0.00497985673032091))*x+(0.24248322013657528));
		wts[0] = (((((((((((((9.276845958083868e-011))*x+(-1.2126596023639042e-012))*x+(-5.7563435499711581e-011))*x+(2.6526928801710404e-013))*x+(1.2316074086508403e-011))*x+(4.4053649617126212e-013))*x+(-2.4882170398162391e-011))*x+(1.6028597708365548e-009))*x+(-1.1082804319643517e-007))*x+(8.0461178904034353e-006))*x+(-0.00064905350967149546))*x+(0.078535474670250696));
		wts[1] = (((((((((((((3.7289282772690058e-011))*x+(1.5158245029548803e-013))*x+(-2.3248958314070478e-011))*x+(-3.0316490059097606e-013))*x+(5.0188001902521746e-012))*x+(2.6704564485650429e-013))*x+(-9.8049716494112236e-012))*x+(6.3009730766339079e-010))*x+(-4.3568046221668468e-008))*x+(3.1630410313431461e-006))*x+(-0.00025515197643954674))*x+(0.030873389149180964));
		wts[2] = (((((((((((((5.0022208597511053e-012))*x+(5.6843418860808015e-014))*x+(-3.0790185216271007e-012))*x+(-6.6317322004276009e-014))*x+(6.5014660322049167e-013))*x+(4.3002638487147728e-014))*x+(-1.3757513646813397e-012))*x+(8.8882244157299325e-011))*x+(-6.1457891484262275e-009))*x+(4.461843894779452e-007))*x+(-3.5992207404939167e-005))*x+(0.0043550570959971068));
		wts[3] = (((((((((((((2.2145248597856454e-013))*x+(3.5527136788005009e-015))*x+(-1.3922196728799463e-013))*x+(-3.2566542055671257e-015))*x+(3.0475622025960547e-014))*x+(1.7902346272080649e-015))*x+(-5.5143100733771412e-014))*x+(3.5255600522310356e-012))*x+(-2.4377594364067997e-010))*x+(1.7698139459976139e-008))*x+(-1.4276499159411231e-006))*x+(0.00017274563982882127));
		wts[4] = (((((((((((((1.230497185626215e-015))*x+(-9.2518585385429707e-018))*x+(-7.6963898217504335e-016))*x+(5.7824115865893518e-019))*x+(1.6725625514209713e-016))*x+(5.8185516590055402e-018))*x+(-3.1285783064332235e-016))*x+(2.0047957525129674e-014))*x+(-1.386194072628486e-012))*x+(1.0063772129911839e-010))*x+(-8.1181095163340713e-009))*x+(9.8229125147611788e-007));
		break;
	case 61:
		rts[0] = (((((((((((((2.3874235921539366e-012))*x+(-6.6317322004276009e-014))*x+(-1.4755604145951413e-012))*x+(3.0198066269804252e-014))*x+(3.1263880373444408e-013))*x+(3.1937415675050332e-014))*x+(-2.2240635259388832e-012))*x+(1.3493310172899933e-010))*x+(-8.2825165192747693e-009))*x+(5.0840093520103033e-007))*x+(-3.1206879060904166e-005))*x+(0.0019155537162059547));
		rts[1] = (((((((((((((2.1524707941959299e-011))*x+(-6.0632980118195212e-013))*x+(-1.3206620981994394e-011))*x+(2.7474319116057206e-013))*x+(2.7758536210361245e-012))*x+(3.3454720475371385e-013))*x+(-2.2304306549851084e-011))*x+(1.3339270428976606e-009))*x+(-8.0603188905755297e-008))*x+(4.8704833429738517e-006))*x+(-0.0002943010891961192))*x+(0.017783272214891888));
		rts[2] = (((((((((((((6.2148804621150092e-011))*x+(0))*x+(-3.8331412118471534e-011))*x+(-3.979039320256561e-013))*x+(8.1238719455238116e-012))*x+(1.5181929787407473e-012))*x+(-7.8355174200813352e-011))*x+(4.5372983888588197e-009))*x+(-2.6504367429032915e-007))*x+(1.5482278800614074e-005))*x+(-0.00090438280228849444))*x+(0.052828673587703684));
		rts[3] = (((((((((((((1.2490393904348213e-010))*x+(-2.1221543041368323e-012))*x+(-7.6018598823187248e-011))*x+(5.3053857603420787e-013))*x+(1.5660361896152608e-011))*x+(4.2620721766676671e-012))*x+(-2.3083194615007111e-010))*x+(1.2647355903302088e-008))*x+(-6.9668491781138531e-007))*x+(3.8377078428764956e-005))*x+(-0.0021140117371300725))*x+(0.11645090788602344));
		rts[4] = (((((((((((((2.6678511252005893e-010))*x+(-6.063298011819521e-012))*x+(-1.6431537612030903e-010))*x+(2.197945529284576e-012))*x+(3.4466059635936589e-011))*x+(1.5721942266585149e-011))*x+(-7.8700187107945863e-010))*x+(3.8965317491109395e-008))*x+(-1.9362983534332297e-006))*x+(9.6220110826679875e-005))*x+(-0.0047814477343645079))*x+(0.23760357622736961));
		wts[0] = (((((((((((((9.398111918320258e-011))*x+(6.0632980118195212e-013))*x+(-5.8851886327223227e-011))*x+(-8.3370347662518418e-013))*x+(1.2751873631107929e-011))*x+(6.2764608325475513e-013))*x+(-2.2885841370149745e-011))*x+(1.4888517085864805e-009))*x+(-1.0464790777449846e-007))*x+(7.7230178514483168e-006))*x+(-0.00063328746365699145))*x+(0.077894358029794206));
		wts[1] = (((((((((((((3.698611787209908e-011))*x+(-3.0316490059097606e-013))*x+(-2.3002636832340308e-011))*x+(3.7895612573872001e-014))*x+(4.9548513440337648e-012))*x+(1.5987211554602252e-013))*x+(-8.9908821128877516e-012))*x+(5.8529655196556019e-010))*x+(-4.1138550316288658e-008))*x+(3.0360259044663138e-006))*x+(-0.00024895412411873695))*x+(0.030621357266596223));
		wts[2] = (((((((((((((5.3432813729159534e-012))*x+(-9.4739031434680016e-014))*x+(-3.3466562854300719e-012))*x+(3.0790185216271e-014))*x+(7.286023636273361e-013))*x+(1.902182115524435e-014))*x+(-1.2720472823228115e-012))*x+(8.2563085997596389e-011))*x+(-5.8030794157272921e-009))*x+(4.2826740191190027e-007))*x+(-3.5117926949393886e-005))*x+(0.0043195050147738718));
		wts[3] = (((((((((((((2.0842586915629605e-013))*x+(-1.1842378929335002e-015))*x+(-1.3056222769591838e-013))*x+(-7.4014868308343802e-017))*x+(2.8366198279172743e-014))*x+(9.529414294699259e-016))*x+(-5.0391404012491606e-014))*x+(3.2749011835697668e-012))*x+(-2.3018221385664081e-010))*x+(1.6987452685192708e-008))*x+(-1.3929711199218124e-006))*x+(0.00017133544775032965));
		wts[4] = (((((((((((((1.1934897514720433e-015))*x+(-1.3877787807814457e-017))*x+(-7.4882230046332176e-016))*x+(2.891205793294679e-018))*x+(1.6320856703148462e-016))*x+(4.9331198848090444e-018))*x+(-2.8680083843125409e-016))*x+(1.8622240703329341e-014))*x+(-1.3088953931089089e-012))*x+(9.6596511344837913e-011))*x+(-7.9209139287918155e-009))*x+(9.74272413241035e-007));
		break;
	case 62:
		rts[0] = (((((((((((((2.4063713984408724e-012))*x+(-7.5791225147744016e-014))*x+(-1.4980609345608778e-012))*x+(3.9671969413272258e-014))*x+(3.2152058793144528e-013))*x+(2.5313084961453569e-014))*x+(-2.0223776357279157e-012))*x+(1.2445959540752225e-010))*x+(-7.7640702290359306e-009))*x+(4.8434152490698279e-007))*x+(-3.0214395790074755e-005))*x+(0.0018848470883331468));
		rts[1] = (((((((((((((2.1676290392254789e-011))*x+(-9.0949470177292824e-013))*x+(-1.3519259785728837e-011))*x+(5.0211686660380417e-013))*x+(2.9167779302952109e-012))*x+(2.3388698385436629e-013))*x+(-2.0256426166061676e-011))*x+(1.2288309259034236e-009))*x+(-7.5481130371498243e-008))*x+(4.6364619275147496e-006))*x+(-0.0002847967046095804))*x+(0.017493762318055786));
		rts[2] = (((((((((((((6.5483618527650833e-011))*x+(-2.5769016550232964e-012))*x+(-4.0624096679190792e-011))*x+(1.4210854715202002e-012))*x+(8.6780952794166897e-012))*x+(9.1956072386286313e-013))*x+(-7.0888480270999324e-011))*x+(4.1681423497882024e-009))*x+(-2.4764529808300278e-007))*x+(1.4713614410538181e-005))*x+(-0.00087419560701280463))*x+(0.051939512481481404));
		rts[3] = (((((((((((((1.3339255626002947e-010))*x+(-3.637978807091713e-012))*x+(-8.2915600311631949e-011))*x+(2.0084674664152167e-012))*x+(1.7754094490859036e-011))*x+(3.3111291486420661e-012))*x+(-2.0761999527015482e-010))*x+(1.1559391370023301e-008))*x+(-6.4831051752959701e-007))*x+(3.6360672943158694e-005))*x+(-0.0020392981690403578))*x+(0.11437458896426339));
		rts[4] = (((((((((((((2.7284841053187847e-010))*x+(-9.701276818911234e-012))*x+(-1.6757439880166203e-010))*x+(5.0022208597511053e-012))*x+(3.4996598211970799e-011))*x+(1.2922403887690354e-011))*x+(-6.9864262523348464e-010))*x+(3.5270778890132228e-008))*x+(-1.7879733308912016e-006))*x+(9.0637396675067678e-005))*x+(-0.0045946643746656987))*x+(0.23291645050210788));
		wts[0] = (((((((((((((8.0035533756017685e-011))*x+(-2.4253192047278085e-012))*x+(-4.9112713895738125e-011))*x+(1.1747639897900322e-012))*x+(1.0298132716949718e-011))*x+(1.2316074086508405e-013))*x+(-2.0769164166267728e-011))*x+(1.3846586099930389e-009))*x+(-9.8903904732772219e-008))*x+(7.4177942794110639e-006))*x+(-0.00061814952322776962))*x+(0.077268690403473131));
		wts[1] = (((((((((((((3.4863963567962245e-011))*x+(-1.0610771520684161e-012))*x+(-2.1581551360820107e-011))*x+(5.1159076974727203e-013))*x+(4.5972115003678474e-012))*x+(4.5593158877939745e-014))*x+(-8.2219416460323665e-012))*x+(5.4432739797031593e-010))*x+(-3.888050037019012e-008))*x+(2.9160382666153692e-006))*x+(-0.00024300318885349363))*x+(0.030375398606684142));
		wts[2] = (((((((((((((5.4190725980636971e-012))*x+(-2.8421709430404007e-013))*x+(-3.3798149464322092e-012))*x+(1.5395092608135505e-013))*x+(7.2741812573440246e-013))*x+(-1.1176245114559911e-014))*x+(-1.167260732515274e-012))*x+(7.6785439118154386e-011))*x+(-5.4845547241509172e-009))*x+(4.11341724811283e-007))*x+(-3.4278477068152302e-005))*x+(0.0042848096335186383));
		wts[3] = (((((((((((((1.8118839761882555e-013))*x+(-1.0658141036401503e-014))*x+(-1.1183646601390744e-013))*x+(5.773159728050814e-015))*x+(2.3684757858670004e-014))*x+(-3.7007434154171891e-016))*x+(-4.5808553709540213e-014))*x+(3.0457257086761538e-012))*x+(-2.1754777495139435e-010))*x+(1.6316086764797906e-008))*x+(-1.3596738970284507e-006))*x+(0.00016995923712853335));
		wts[4] = (((((((((((((1.1009711660866135e-015))*x+(-6.9388939039072284e-017))*x+(-6.840592906935209e-016))*x+(3.8163916471489756e-017))*x+(1.4651185357520782e-016))*x+(-3.2706765536646056e-018))*x+(-2.6175576824683894e-016))*x+(1.731915618225522e-014))*x+(-1.2370515766881849e-012))*x+(9.2778893305366133e-011))*x+(-7.731574442255573e-009))*x+(9.6644680528173399e-007));
		break;
	case 63:
		rts[0] = (((((((((((((2.4442670110147446e-012))*x+(-2.3684757858670004e-014))*x+(-1.5359565471347498e-012))*x+(5.3290705182007498e-015))*x+(3.3528735343679728e-013))*x+(2.9846495645339623e-014))*x+(-1.8430026023826445e-012))*x+(1.1494568954069824e-010))*x+(-7.2855618404518699e-009))*x+(4.6177658592099803e-007))*x+(-2.9268516903166241e-005))*x+(0.0018551093924926724));
		rts[1] = (((((((((((((1.9554136088117957e-011))*x+(-2.2737367544323206e-013))*x+(-1.1984487476487024e-011))*x+(3.7895612573872014e-014))*x+(2.5022946677684863e-012))*x+(3.0997426847534371e-013))*x+(-1.8357870779084348e-011))*x+(1.1334998495371449e-009))*x+(-7.0759550369522043e-008))*x+(4.4171961925606549e-006))*x+(-0.00027574540697344028))*x+(0.017213527803376993));
		rts[2] = (((((((((((((6.4877288726468877e-011))*x+(-1.3642420526593924e-012))*x+(-4.043461861632143e-011))*x+(5.8738199489501619e-013))*x+(8.6733583278449552e-012))*x+(9.9535194901060688e-013))*x+(-6.4199460562501073e-011))*x+(3.8343902127498568e-009))*x+(-2.3165139494592718e-007))*x+(1.3995002980047206e-005))*x+(-0.00084549498546151937))*x+(0.051079786942694903));
		rts[3] = (((((((((((((1.4673181188603241e-010))*x+(-2.4253192047278085e-012))*x+(-9.1631591203622507e-011))*x+(1.0231815394945443e-012))*x+(1.9753088054130782e-011))*x+(3.1358619404879087e-012))*x+(-1.8706428998408833e-010))*x+(1.0581760060783077e-008))*x+(-6.0406278951097281e-007))*x+(3.448309024619197e-005))*x+(-0.0019684765262600198))*x+(0.11237101451448615));
		rts[4] = (((((((((((((2.7163575092951453e-010))*x+(-8.4886172165473291e-012))*x+(-1.6765019002680975e-010))*x+(4.16851738312592e-012))*x+(3.5299763112561771e-011))*x+(1.1316577304872529e-011))*x+(-6.2175449973741093e-010))*x+(3.1988671267413331e-008))*x+(-1.6535827490985846e-006))*x+(8.5478343571328746e-005))*x+(-0.0044186158168911848))*x+(0.22841067013915162));
		wts[0] = (((((((((((((9.4587448984384537e-011))*x+(-3.3348139065007367e-012))*x+(-5.9117155615240335e-011))*x+(1.7431981783981123e-012))*x+(1.2780295340538336e-011))*x+(-3.4342898895071475e-014))*x+(-1.9366434382087995e-011))*x+(1.2892151050418002e-009))*x+(-9.3558964205560814e-008))*x+(7.1291953441845095e-006))*x+(-0.0006036052057922629))*x+(0.076657861135604424));
		wts[1] = (((((((((((((3.7895612573872008e-011))*x+(-6.0632980118195212e-013))*x+(-2.3741601277530812e-011))*x+(2.4632148173016805e-013))*x+(5.1561717858324601e-012))*x+(8.2896652505345017e-014))*x+(-7.6293786103557669e-012))*x+(5.0679934323246323e-010))*x+(-3.6779331214857144e-008))*x+(2.8025860050277336e-006))*x+(-0.00023728561505666587))*x+(0.030135273112188801));
		wts[2] = (((((((((((((5.1916989226204651e-012))*x+(-7.5791225147744016e-014))*x+(-3.2377063992801896e-012))*x+(2.1316282072803002e-014))*x+(6.9751611893783162e-013))*x+(1.6727360237685694e-014))*x+(-1.0728177605538274e-012))*x+(7.1489379231219147e-011))*x+(-5.188160288535637e-009))*x+(3.9533794006565515e-007))*x+(-3.347194558514954e-005))*x+(0.0042509370893130559));
		wts[3] = (((((((((((((1.9303077654816053e-013))*x+(-6.5133084111342514e-015))*x+(-1.1938598258135849e-013))*x+(3.2566542055671257e-015))*x+(2.5461114698070255e-014))*x+(8.5579691481522549e-017))*x+(-4.2332746104841349e-014))*x+(2.8357186390715046e-012))*x+(-2.0579112652606305e-010))*x+(1.5681288188237408e-008))*x+(-1.3276823997867805e-006))*x+(0.00016861566477289163));
		wts[4] = (((((((((((((1.1842378929335002e-015))*x+(-4.6259292692714852e-017))*x+(-7.3783571844880192e-016))*x+(2.4286128663675296e-017))*x+(1.594499995002015e-016))*x+(-7.589415207398531e-019))*x+(-2.4233725558671837e-016))*x+(1.6124975251898217e-014))*x+(-1.1701992016176482e-012))*x+(8.9169209794037272e-011))*x+(-7.5496597618434195e-009))*x+(9.588067897538176e-007));
		break;
	case 64:
		rts[0] = (((((((((((((1.9800457569848122e-012))*x+(-4.7369515717340008e-014))*x+(-1.2404891928478414e-012))*x+(2.0724163126336251e-014))*x+(2.6852594222267118e-013))*x+(2.3425705819590803e-014))*x+(-1.6741076117969083e-012))*x+(1.0629222502167579e-010))*x+(-6.8433560810286787e-009))*x+(4.4059185903847522e-007))*x+(-2.8366369534157617e-005))*x+(0.001826295479773437));
		rts[1] = (((((((((((((2.0615213240186371e-011))*x+(2.2737367544323206e-013))*x+(-1.2884508275116483e-011))*x+(-2.3684757858670003e-013))*x+(2.7805905726078586e-012))*x+(3.4254081053101493e-013))*x+(-1.6744975776343076e-011))*x+(1.0469093369991356e-009))*x+(-6.6401446424668706e-008))*x+(4.2115412495202327e-006))*x+(-0.00026711884830814324))*x+(0.016942129948674708));
		rts[2] = (((((((((((((5.7904496012876429e-011))*x+(3.0316490059097606e-013))*x+(-3.5943988526317597e-011))*x+(-4.926429634603361e-013))*x+(7.6596506914938784e-012))*x+(1.1285787119656259e-012))*x+(-5.8154592252890325e-011))*x+(3.5321939447404325e-009))*x+(-2.1692808252945134e-007))*x+(1.3322435829118963e-005))*x+(-0.00081818490732007195))*x+(0.050248059080759647));
		rts[3] = (((((((((((((1.2914824765175581e-010))*x+(-3.3348139065007367e-012))*x+(-8.1210297745807722e-011))*x+(1.3263464400855203e-012))*x+(1.7687777168854762e-011))*x+(2.7841432862866587e-012))*x+(-1.6857522785092744e-010))*x+(9.7016947068577045e-009))*x+(-5.6352640536346433e-007))*x+(3.273258618486282e-005))*x+(-0.0019012811149686358))*x+(0.11043642741522271));
		rts[4] = (((((((((((((2.3161798405150572e-010))*x+(-6.0632980118195212e-013))*x+(-1.4316962430408844e-010))*x+(-5.3053857603420817e-013))*x+(3.0164907608802118e-011))*x+(1.0831039768769793e-011))*x+(-5.541188248988268e-010))*x+(2.906623238393043e-008))*x+(-1.5315848494457105e-006))*x+(8.0703513564363741e-005))*x+(-0.0042524949475212142))*x+(0.2240759104645717));
		wts[0] = (((((((((((((9.5800108586748437e-011))*x+(-1.2126596023639042e-012))*x+(-6.0405606442751975e-011))*x+(3.7895612573872007e-013))*x+(1.327293830399867e-011))*x+(2.5816386065950303e-013))*x+(-1.794386861320163e-011))*x+(1.2016479663164623e-009))*x+(-8.8579741005142168e-008))*x+(6.8560747118010896e-006))*x+(-0.00058962242509596444))*x+(0.076061292837348846));
		wts[1] = (((((((((((((3.5470293369144201e-011))*x+(-1.5158245029548803e-013))*x+(-2.2149985549428191e-011))*x+(-3.7895612573872001e-014))*x+(4.7772156600937405e-012))*x+(1.3441100084795227e-013))*x+(-6.9990679918419119e-012))*x+(4.7238309560289815e-010))*x+(-3.4821932989870241e-008))*x+(2.6952184792710296e-006))*x+(-0.00023178878917458026))*x+(0.029900753803514066));
		wts[2] = (((((((((((((5.2674901477682088e-012))*x+(3.7895612573872008e-014))*x+(-3.3087606728561996e-012))*x+(-4.500103993147301e-014))*x+(7.2001663890356815e-013))*x+(2.8421709430404004e-014))*x+(-9.9208604294650107e-013))*x+(6.6634281425947961e-011))*x+(-4.9120457880589639e-009))*x+(3.8019247928025579e-007))*x+(-3.2696553209291087e-005))*x+(0.0042178553639975408));
		wts[3] = (((((((((((((1.8355687340469254e-013))*x+(-4.736951571734001e-015))*x+(-1.1405691206315774e-013))*x+(2.0724163126336253e-015))*x+(2.4387899107599268e-014))*x+(3.0531133177191795e-016))*x+(-3.8925749198022906e-014))*x+(2.6431530575354852e-012))*x+(-1.9483890591415545e-010))*x+(1.5080535486827404e-008))*x+(-1.296926051676198e-006))*x+(0.00016730346066619401));
		wts[4] = (((((((((((((1.1102230246251565e-015))*x+(-4.6259292692714853e-018))*x+(-6.9388939039072284e-016))*x+(-1.1564823173178711e-018))*x+(1.4976446009266434e-016))*x+(4.2825985813177417e-018))*x+(-2.2248732081212952e-016))*x+(1.5029689370953579e-014))*x+(-1.1079211363580277e-012))*x+(8.5753122867100937e-011))*x+(-7.3747685651308305e-009))*x+(9.5134514490166739e-007));
		break;
	case 65:
		rts[0] = (((((((((((((1.8758328224066645e-012))*x+(-6.1580370432542012e-014))*x+(-1.1735797518970987e-012))*x+(2.8421709430404004e-014))*x+(2.5416705777085252e-013))*x+(1.9410399213863151e-014))*x+(-1.5271534037353263e-012))*x+(9.8408686292443066e-011))*x+(-6.4341970857154096e-009))*x+(4.2068340965789304e-007))*x+(-2.7505298820712232e-005))*x+(0.0017983629634081779));
		rts[1] = (((((((((((((1.7735146684572101e-011))*x+(-1.6674069532503684e-012))*x+(-1.1112888387287967e-011))*x+(9.4739031434680011e-013))*x+(2.4099241121196733e-012))*x+(4.9737991503207013e-014))*x+(-1.5235923633838408e-011))*x+(9.6816813825266012e-010))*x+(-6.2373759826076875e-008))*x+(4.0184571738858628e-006))*x+(-0.00025889086348245466))*x+(0.016679157270833626));
		rts[2] = (((((((((((((5.8510825814058379e-011))*x+(-1.2126596023639042e-012))*x+(-3.666400516522117e-011))*x+(5.3053857603420807e-013))*x+(7.920183027939249e-012))*x+(7.815970093361101e-013))*x+(-5.287866441013496e-011))*x+(3.2581752111108622e-009))*x+(-2.0335613156822563e-007))*x+(1.2692283449022844e-005))*x+(-0.00079217697313351638))*x+(0.049442983156797043));
		rts[3] = (((((((((((((1.2672292844702798e-010))*x+(-3.9411437076826888e-012))*x+(-8.151346264639868e-011))*x+(1.9705718538413444e-012))*x+(1.8398319904614859e-011))*x+(2.2512362344665844e-012))*x+(-1.5248617183753291e-010))*x+(8.9080513336151982e-009))*x+(-5.263339798907325e-007))*x+(3.1098588956090141e-005))*x+(-0.0018374685333273025))*x+(0.10856732489749865));
		rts[4] = (((((((((((((2.5465851649641991e-010))*x+(-2.4253192047278085e-012))*x+(-1.6173847446528575e-010))*x+(3.0316490059097601e-013))*x+(3.5697667044587433e-011))*x+(9.4075858214637248e-012))*x+(-4.9599968576785614e-010))*x+(2.6458483404212526e-008))*x+(-1.4206331767629976e-006))*x+(7.6277793393179444e-005))*x+(-0.0040955691065868872))*x+(0.21990261597065203));
		wts[0] = (((((((((((((9.1555799978474767e-011))*x+(-2.4253192047278085e-012))*x+(-5.6957105698529624e-011))*x+(1.0231815394945443e-012))*x+(1.2178702490928116e-011))*x+(1.2789769243681798e-013))*x+(-1.6419606415259597e-011))*x+(1.1212746287014852e-009))*x+(-8.393612274670835e-008))*x+(6.5973811934257514e-006))*x+(-0.00057617129078104702))*x+(0.075478439092318064));
		wts[1] = (((((((((((((3.3196556614711881e-011))*x+(-6.8212102632969618e-013))*x+(-2.058679153075597e-011))*x+(2.463214817301681e-013))*x+(4.3722063007104834e-012))*x+(8.200847408564488e-014))*x+(-6.4154237477964671e-012))*x+(4.4078566722542217e-010))*x+(-3.2996460274751595e-008))*x+(2.5935224536345609e-006))*x+(-0.00022650096089135431))*x+(0.029671625876765705));
		wts[2] = (((((((((((((4.850638409455617e-012))*x+(3.7895612573872008e-014))*x+(-3.0458598606249625e-012))*x+(-5.447494307494101e-014))*x+(6.6287716056952673e-013))*x+(3.1974423109204508e-014))*x+(-9.1177065897340981e-013))*x+(6.2176236381716876e-011))*x+(-4.6545410141892365e-009))*x+(3.6584705074190388e-007))*x+(-3.1950642419391254e-005))*x+(0.0041855341569394218));
		wts[3] = (((((((((((((1.9303077654816053e-013))*x+(-4.1448326252672506e-015))*x+(-1.20570220474292e-013))*x+(1.4802973661668749e-015))*x+(2.5942211342074487e-014))*x+(4.5565403302324126e-016))*x+(-3.6078489732786296e-014))*x+(2.4663243091323692e-012))*x+(-1.8462483413828401e-010))*x+(1.4511516487328565e-008))*x+(-1.2673391062432631e-006))*x+(0.00016602142291784251));
		wts[4] = (((((((((((((1.1194748831636994e-015))*x+(-4.6259292692714853e-018))*x+(-7.0603245472256039e-016))*x+(-2.0238440553062747e-018))*x+(1.5475179008609766e-016))*x+(4.4994390158148426e-018))*x+(-2.0630334463325739e-016))*x+(1.4024243192526513e-014))*x+(-1.0498403707796653e-012))*x+(8.2517484699931798e-011))*x+(-7.206526995125199e-009))*x+(9.4405503636106531e-007));
		break;
	case 66:
		rts[0] = (((((((((((((2.2547889481453845e-012))*x+(-1.8947806286936004e-014))*x+(-1.4341120883424687e-012))*x+(-1.7763568394002505e-015))*x+(3.184119634624949e-013))*x+(2.4794980883295157e-014))*x+(-1.4027899212602315e-012))*x+(9.1215576758507666e-011))*x+(-6.0551649721495475e-009))*x+(4.0195655542311221e-007))*x+(-2.6682848349804254e-005))*x+(0.0017712720107256152));
		rts[1] = (((((((((((((1.9099388737231493e-011))*x+(3.7895612573872007e-013))*x+(-1.2012909185917428e-011))*x+(-3.0316490059097601e-013))*x+(2.6183499812759692e-012))*x+(2.9457917586720817e-013))*x+(-1.3928413977737364e-011))*x+(8.9638244974802684e-010))*x+(-5.8646875878790951e-008))*x+(3.836997952622277e-006))*x+(-0.00025103727157682723))*x+(0.016424223444116186));
		rts[2] = (((((((((((((5.184119800105691e-011))*x+(0))*x+(-3.2760757070112355e-011))*x+(-1.3263464400855202e-013))*x+(7.1812185827487456e-012))*x+(8.1475567033824815e-013))*x+(-4.808857016295557e-011))*x+(3.0092447052728253e-009))*x+(-1.9082917255182816e-007))*x+(1.2101254314602258e-005))*x+(-0.00076738969805916998))*x+(0.048663298317761283));
		rts[3] = (((((((((((((1.1338367282102505e-010))*x+(-1.5158245029548803e-012))*x+(-7.1584812152044222e-011))*x+(3.0316490059097601e-013))*x+(1.5660361896152608e-011))*x+(2.3743969753316679e-012))*x+(-1.3770066568478492e-010))*x+(8.1909941052060731e-009))*x+(-4.92159929726954e-007))*x+(2.9571564818471154e-005))*x+(-0.0017768154641837068))*x+(0.1067604373788729));
		rts[4] = (((((((((((((2.4738255888223648e-010))*x+(-4.850638409455617e-012))*x+(-1.5491726420198879e-010))*x+(1.4400332778071361e-012))*x+(3.3461825902728989e-011))*x+(8.1854523159563541e-012))*x+(-4.4403355066909472e-010))*x+(2.412649043511313e-008))*x+(-1.3195490583909712e-006))*x+(7.2169851191516976e-005))*x+(-0.0039471719954745303))*x+(0.21588192999894945));
		wts[0] = (((((((((((((8.6705161569019154e-011))*x+(-1.2126596023639042e-012))*x+(-5.4304412818358579e-011))*x+(3.7895612573872007e-013))*x+(1.1719218188469917e-011))*x+(2.1553129651389705e-013))*x+(-1.5165794546116256e-011))*x+(1.0473642693871929e-009))*x+(-7.9600846053518026e-008))*x+(6.3521495592133714e-006))*x+(-0.000563223927463726))*x+(0.074908782352671732));
		wts[1] = (((((((((((((3.637978807091713e-011))*x+(-3.7895612573872007e-013))*x+(-2.2964741219766438e-011))*x+(7.5791225147744003e-014))*x+(5.0495903754684451e-012))*x+(1.0569323194431489e-013))*x+(-6.020073328727448e-012))*x+(4.1173068658177192e-010))*x+(-3.1292198017969966e-008))*x+(2.4971184819586509e-006))*x+(-0.00022141117200517985))*x+(0.029447685876677867));
		wts[2] = (((((((((((((5.1538033100465928e-012))*x+(-3.7895612573872008e-014))*x+(-3.2590226813529926e-012))*x+(-2.3684757858670017e-015))*x+(7.1883240101063462e-013))*x+(1.8355687340469256e-014))*x+(-8.5020879225794488e-013))*x+(5.8079180353942661e-011))*x+(-4.4141349811455122e-009))*x+(3.5224812902634456e-007))*x+(-3.1232667431323278e-005))*x+(0.0041539447683644386));
		wts[3] = (((((((((((((1.8947806286936003e-013))*x+(2.9605947323337505e-015))*x+(-1.1812772982011666e-013))*x+(-2.9605947323337505e-015))*x+(2.5405603546838997e-014))*x+(1.3854658161468097e-015))*x+(-3.3333289832053005e-014))*x+(2.3036760577836248e-012))*x+(-1.7508901533486163e-010))*x+(1.3972108079793856e-008))*x+(-1.2388602491441083e-006))*x+(0.00016476841313613317));
		wts[4] = (((((((((((((1.1287267417022424e-015))*x+(-4.6259292692714853e-018))*x+(-7.1123662515049091e-016))*x+(-2.0238440553062747e-018))*x+(1.5569143196891844e-016))*x+(4.2464585089015588e-018))*x+(-1.9095059011995744e-016))*x+(1.3099875007810631e-014))*x+(-9.9561642290758152e-013))*x+(7.9450222549085056e-011))*x+(-7.0445863973284044e-009))*x+(9.3692999084439309e-007));
		break;
	case 67:
		rts[0] = (((((((((((((1.8758328224066645e-012))*x+(-1.8947806286936004e-014))*x+(-1.1735797518970987e-012))*x+(3.5527136788005009e-015))*x+(2.532788793511524e-013))*x+(2.01320441798695e-014))*x+(-1.2778713272728244e-012))*x+(8.4645346287715029e-011))*x+(-5.7036373237243088e-009))*x+(3.8432491930555596e-007))*x+(-2.5896742619477401e-005))*x+(0.0017449851536280247));
		rts[1] = (((((((((((((1.8796223836640515e-011))*x+(-5.3053857603420807e-013))*x+(-1.1652900866465641e-011))*x+(3.0316490059097601e-013))*x+(2.4833468614815497e-012))*x+(1.2641739507065117e-013))*x+(-1.2717308687607934e-011))*x+(8.3092551358040124e-010))*x+(-5.5194236801373954e-008))*x+(3.6663017269726594e-006))*x+(-0.00024353569801886134))*x+(0.016176965406507295));
		rts[2] = (((((((((((((5.305385760342081e-011))*x+(-2.4253192047278085e-012))*x+(-3.298813074555558e-011))*x+(1.1747639897900322e-012))*x+(7.0343730840249918e-012))*x+(5.068538181755382e-013))*x+(-4.3785049660035228e-011))*x+(2.7828130910734217e-009))*x+(-1.7925212854319472e-007))*x+(1.1546358719980814e-005))*x+(-0.00074374787284225182))*x+(0.047907822007363383));
		rts[3] = (((((((((((((1.1641532182693481e-010))*x+(-9.0949470177292824e-013))*x+(-7.3214323492720723e-011))*x+(0))*x+(1.6001422409317456e-011))*x+(2.1778134851047071e-012))*x+(-1.2489032030771341e-010))*x+(7.5421264789099496e-009))*x+(-4.6071496817567947e-007))*x+(2.8142901083721045e-005))*x+(-0.0017191167186234799))*x+(0.10501270937646923));
		rts[4] = (((((((((((((2.6921043172478676e-010))*x+(-3.0316490059097605e-012))*x+(-1.6931759698006013e-010))*x+(4.5474735088646392e-013))*x+(3.6834535421803594e-011))*x+(7.3825390245474409e-012))*x+(-3.9890994211570308e-010))*x+(2.2036849678386261e-008))*x+(-1.2272978134146111e-006))*x+(6.8351669774470894e-005))*x+(-0.0038066965925650439))*x+(0.21200563199886785));
		wts[0] = (((((((((((((8.4886172165473298e-011))*x+(9.0949470177292824e-013))*x+(-5.2599110252534339e-011))*x+(-1.0989727646422882e-012))*x+(1.1207627418722645e-011))*x+(5.6014452335754561e-013))*x+(-1.3988810110276971e-011))*x+(9.7929027849848649e-010))*x+(-7.5549264992128912e-008))*x+(6.1194923489799038e-006))*x+(-0.00055075431116516122))*x+(0.074351832007291785));
		wts[1] = (((((((((((((3.2741809263825417e-011))*x+(0))*x+(-2.0387839564743142e-011))*x+(-1.9895196601282805e-013))*x+(4.3769432522822171e-012))*x+(1.6697754290362354e-013))*x+(-5.503449547935209e-012))*x+(3.8497760534994541e-010))*x+(-2.969946757043947e-008))*x+(2.4056576912132957e-006))*x+(-0.00021650919212736045))*x+(0.029228740937185443));
		wts[2] = (((((((((((((4.9264296346033608e-012))*x+(3.7895612573872008e-014))*x+(-3.0695446184836324e-012))*x+(-5.2106467289074012e-014))*x+(6.6110080373012648e-013))*x+(2.8421709430404004e-014))*x+(-7.8048678631148505e-013))*x+(5.4305338004212438e-011))*x+(-4.1894614247658018e-009))*x+(3.3934650154702578e-007))*x+(-3.0541185127642631e-005))*x+(0.0041230599922304784));
		wts[3] = (((((((((((((1.6697754290362354e-013))*x+(-1.1842378929335002e-015))*x+(-1.0325074129013956e-013))*x+(-3.7007434154171891e-016))*x+(2.1908401019269757e-014))*x+(7.5402647089125218e-016))*x+(-3.0527952850819177e-014))*x+(2.1540824679533439e-012))*x+(-1.6617721660894833e-010))*x+(1.3460358208193435e-008))*x+(-1.2114322383634714e-006))*x+(0.00016354335217903693));
		wts[4] = (((((((((((((9.9920072216264089e-016))*x+(-4.6259292692714853e-018))*x+(-6.1409211049578971e-016))*x+(-2.8912057932946782e-018))*x+(1.2916461881543975e-016))*x+(4.3187386537339255e-018))*x+(-1.738111607765824e-016))*x+(1.224887342885413e-014))*x+(-9.4494093957351818e-013))*x+(7.654023639817623e-011))*x+(-6.8886212739126191e-009))*x+(9.2996387197810485e-007));
		break;
	case 68:
		rts[0] = (((((((((((((1.8379372098327922e-012))*x+(-4.2632564145606011e-014))*x+(-1.1593688971818967e-012))*x+(1.8947806286936007e-014))*x+(2.5313084961453564e-013))*x+(1.4821477378745837e-014))*x+(-1.1719560507235844e-012))*x+(7.8634892578903034e-011))*x+(-5.3772527486862596e-009))*x+(3.6770959217078948e-007))*x+(-2.5144871282629308e-005))*x+(0.0017194671156978484));
		rts[1] = (((((((((((((1.8189894035458565e-011))*x+(6.0632980118195212e-013))*x+(-1.1728692091613388e-011))*x+(-4.8316906031686813e-013))*x+(2.6538771180639742e-012))*x+(3.0434913848390955e-013))*x+(-1.1683617036813605e-011))*x+(7.7108741614040355e-010))*x+(-5.1991974170384481e-008))*x+(3.5055821979111204e-006))*x+(-0.00023636541504580062))*x+(0.015937041634569892));
		rts[2] = (((((((((((((4.9719043696920075e-011))*x+(-3.0316490059097606e-013))*x+(-3.0922819860279554e-011))*x+(-5.6843418860808015e-014))*x+(6.5985735394254626e-012))*x+(6.7856831265089568e-013))*x+(-3.9936054463396431e-011))*x+(2.5764927968907614e-009))*x+(-1.6853984709704523e-007))*x+(1.1024876984099447e-005))*x+(-0.00072118199264535848))*x+(0.047175443981367159));
		rts[3] = (((((((((((((1.2854191785057384e-010))*x+(-4.850638409455617e-012))*x+(-8.1096610908086093e-011))*x+(2.3874235921539366e-012))*x+(1.7810937909719844e-011))*x+(1.4684549872375405e-012))*x+(-1.1359505928491369e-010))*x+(6.9540172139189354e-009))*x+(-4.3174171234413211e-007))*x+(2.6804803961444357e-005))*x+(-0.0016641834982981734))*x+(0.10332128226459592));
		rts[4] = (((((((((((((2.2919266484677792e-010))*x+(1.8189894035458565e-012))*x+(-1.4423070145615688e-010))*x+(-2.4253192047278085e-012))*x+(3.1510201855174578e-011))*x+(7.1835870585346121e-012))*x+(-3.5841699978315467e-010))*x+(2.0160612438739161e-008))*x+(-1.1429692603666846e-006))*x+(6.4798144651795342e-005))*x+(-0.003673588935753664))*x+(0.20826608142637748));
		wts[0] = (((((((((((((9.0949470177292824e-011))*x+(-2.7284841053187847e-012))*x+(-5.7373957436842225e-011))*x+(1.2884508275116484e-012))*x+(1.257186947138204e-011))*x+(-1.0658141036401503e-014))*x+(-1.3145928789981552e-011))*x+(9.1663136340495533e-010))*x+(-7.1759001426160055e-008))*x+(5.8985925687436245e-006))*x+(-0.00053873812120925355))*x+(0.073807122605644357));
		wts[1] = (((((((((((((3.1832314562052488e-011))*x+(-7.5791225147744013e-013))*x+(-1.9952040020143613e-011))*x+(3.3158661002138002e-013))*x+(4.3272052607790101e-012))*x+(2.9013828376870749e-014))*x+(-5.1066558389341781e-012))*x+(3.6033798167522946e-010))*x+(-2.820946539786965e-008))*x+(2.3188189105354433e-006))*x+(-0.00021178546046136165))*x+(0.029014608083199552));
		wts[2] = (((((((((((((5.1538033100465928e-012))*x+(-1.8947806286936004e-014))*x+(-3.2495487782095247e-012))*x+(-7.1054273576010019e-015))*x+(7.1172697365303362e-013))*x+(1.5617137213060534e-014))*x+(-7.3015667586181132e-013))*x+(5.0828915150920765e-011))*x+(-3.9792787814851841e-009))*x+(3.2709686335116034e-007))*x+(-2.9874846844787337e-005))*x+(0.0040928540177347303));
		wts[3] = (((((((((((((1.8710958708349304e-013))*x+(-4.736951571734001e-015))*x+(-1.1797970008349995e-013))*x+(1.9243865760169379e-015))*x+(2.5886700190843229e-014))*x+(2.1741867565575979e-016))*x+(-2.8778484225296573e-014))*x+(2.0161823599540436e-012))*x+(-1.5784019573855437e-010))*x+(1.2974469840060896e-008))*x+(-1.1850015784489405e-006))*x+(0.00016234521624742848));
		wts[4] = (((((((((((((1.0362081563168126e-015))*x+(-2.3129646346357426e-017))*x+(-6.4994306233264366e-016))*x+(1.0119220276531373e-017))*x+(1.4123540300244503e-016))*x+(9.5771191902886251e-019))*x+(-1.628562013254268e-016))*x+(1.1464791970239771e-014))*x+(-8.9753380542892478e-013))*x+(7.3777307654011623e-011))*x+(-6.7383274312977977e-009))*x+(9.2315085808748235e-007));
		break;
	case 69:
		rts[0] = (((((((((((((2.0179413695586845e-012))*x+(-3.7895612573872008e-014))*x+(-1.2736478538499796e-012))*x+(1.5395092608135503e-014))*x+(2.7933211299568939e-013))*x+(1.4358884451818692e-014))*x+(-1.0786024851050513e-012))*x+(7.3128947342127036e-011))*x+(-5.0738839364102926e-009))*x+(3.5203839007039622e-007))*x+(-2.4425274968824983e-005))*x+(0.0016946846542556567));
		rts[1] = (((((((((((((1.7280399333685637e-011))*x+(3.0316490059097606e-013))*x+(-1.0610771520684162e-011))*x+(-3.0316490059097606e-013))*x+(2.2251830008220472e-012))*x+(2.5105843330190208e-013))*x+(-1.0649703341414352e-011))*x+(7.1636718779188868e-010))*x+(-4.9018622313989901e-008))*x+(3.3541209988931695e-006))*x+(-0.00022950719836720089))*x+(0.015704130569572889));
		rts[2] = (((((((((((((5.1538033100465931e-011))*x+(0))*x+(-3.2249166300365076e-011))*x+(-3.2211270687791205e-013))*x+(6.9727927135924493e-012))*x+(6.9870035683076505e-013))*x+(-3.655994026037964e-011))*x+(2.3882639569687094e-009))*x+(-1.586159600423335e-007))*x+(1.0534331416928165e-005))*x+(-0.00069962774561770958))*x+(0.046465120863557759));
		rts[3] = (((((((((((((1.0853303441156943e-010))*x+(-3.637978807091713e-012))*x+(-6.6734173742588597e-011))*x+(1.8947806286936006e-012))*x+(1.4040324458619576e-011))*x+(1.3073986337985841e-012))*x+(-1.0291900665038156e-010))*x+(6.4200629997420338e-009))*x+(-4.0501066569942346e-007))*x+(2.5550209141800284e-005))*x+(-0.0016118418490242592))*x+(0.10168347867227734));
		rts[4] = (((((((((((((2.5829649530351162e-010))*x+(-8.4886172165473291e-012))*x+(-1.6727123390107104e-010))*x+(4.3200998334214083e-012))*x+(3.8104038443028308e-011))*x+(4.8837970704577547e-012))*x+(-3.2380883160006607e-010))*x+(1.8473045315658965e-008))*x+(-1.0657606885344782e-006))*x+(6.1486736761151572e-005))*x+(-0.0035473426527161205))*x+(0.20465616747721777));
		wts[0] = (((((((((((((8.0035533756017685e-011))*x+(-1.8189894035458565e-012))*x+(-4.9567461246624589e-011))*x+(7.5791225147744023e-013))*x+(1.052550639239295e-011))*x+(8.7633604077078989e-014))*x+(-1.1988040190165823e-011))*x+(8.5874596322810238e-010))*x+(-6.8209776974785072e-008))*x+(5.6886971876909022e-006))*x+(-0.00052715260591885971))*x+(0.07327421222271524));
		wts[1] = (((((((((((((3.3348139065007367e-011))*x+(-3.7895612573872007e-013))*x+(-2.0880482528203476e-011))*x+(9.4739031434679991e-014))*x+(4.5285257025777046e-012))*x+(7.3718808835110382e-014))*x+(-4.7622646566954537e-012))*x+(3.3758288756994637e-010))*x+(-2.6814210934977819e-008))*x+(2.2363061121047816e-006))*x+(-0.00020723103300610986))*x+(0.028805113587840735));
		wts[2] = (((((((((((((4.6990559591601287e-012))*x+(-1.8947806286936003e-013))*x+(-2.9653316839054846e-012))*x+(9.4739031434680016e-014))*x+(6.4896236532755814e-013))*x+(-6.6613381477509392e-015))*x+(-6.7312821983023241e-013))*x+(4.7621554847646991e-011))*x+(-3.7824619293173401e-009))*x+(3.1545745605235842e-007))*x+(-2.9232390925499275e-005))*x+(0.0040633023386438434));
		wts[3] = (((((((((((((1.7881992183295853e-013))*x+(-4.1448326252672506e-015))*x+(-1.1168843627729074e-013))*x+(1.7763568394002501e-015))*x+(2.4091839634365894e-014))*x+(1.457167719820518e-016))*x+(-2.6508598556980918e-014))*x+(1.8888973140248249e-012))*x+(-1.5003335797044229e-010))*x+(1.2512786604175499e-008))*x+(-1.1595182250981593e-006))*x+(0.0001611730332886186));
		wts[4] = (((((((((((((1.1379786002407855e-015))*x+(-6.9388939039072284e-018))*x+(-7.1759727789573923e-016))*x+(-2.8912057932946759e-019))*x+(1.5728159515523052e-016))*x+(3.099011209687733e-018))*x+(-1.5287928258403416e-016))*x+(1.0740717713740694e-014))*x+(-8.5314130093064138e-013))*x+(7.1152017649136851e-011))*x+(-6.5934203003318002e-009))*x+(9.1648542174588078e-007));
		break;
	default:
		double fr = 1/X;
		double fw = sqrt(fr);
		for(unsigned int i = 0 ; i < 5 ; i++){
			double DUM = fr*hermite_roots[5][i]*hermite_roots[5][i];
			rts[i] = DUM/(1.0-DUM);
			wts[i] = fw*hermite_weights[5][i];
		}
		break;
	}
}
#endif
