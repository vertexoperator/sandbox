/*
incomplete gamma function

gammap(a,x) = \dfrac{1}{\Gamma(a)} \int_{0}^x t^{a-1} e^{-x} dx
*/

#include <cmath>
#define EPS 1.0e-9

double gammap_sr(double a, double x, double ldenum)
{
  const int itmax = 200;
  int n;
  double sum, del, ap;

  if (x <= 0)
     return 0; /* invalid arguments */

  ap = a;
  sum = del = 1/a;
  for (n=1; fabs(del)>fabs(sum)*EPS || n<=itmax; n++) {
     ++ap;
     sum += del *= x/ap;
  }
  return sum * exp(-x+a*log(x)-ldenum);
}

double gammaq_cf(double a, double x, double ldenum)
{
  /* modified Lentz's method */
  const int itmax = 200;
  const double fpmin = 1.0e-80;
  int n;
  double an, b, c, d, del, cf;
  b = x+1-a;
  c = 1/fpmin;
  d = 1/b;
  cf = del = d;
  for (n=1; fabs(del-1) > EPS || n<=itmax; n++) {
     an = -n*(n-a);
     b += 2;
     d = an*d + b;
     if (fabs(d) < fpmin) d = fpmin;
     c = b + an/c;
     if (fabs(c) < fpmin) c = fpmin;
     d = 1/d;
     del = d*c;
     cf *= del;
  }
  return cf * exp(-x+a*log(x)-ldenum);
}

double gammap (double a, double x)
{
  /** Incomplete Gammafunction **/
  if (x < 0 || a <= 0) return 0; /* invalid arguments */

  if (x < a+1)
     return gammap_sr(a,x,lgamma(a));
  else
     return 1-gammaq_cf(a,x,lgamma(a));
}

