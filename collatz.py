#-*- coding:utf-8 -*-
"""
An analytic approach to the Collatz 3n + 1 Problem
http://preprint.math.uni-hamburg.de/public/papers/hbam/hbam2011-09.pdf
にある、いくつかのアルゴリズムの実装&NOTE

NOTE:
論文にあるannihilation algorithmは、微妙に間違ってる気がするので、独断で修正してある
2*l=12から始めると、(12,12,6)->(6,6,3)->(8,3,4)
と辿るけど、while 2*l>8だと、(6,6,3)で終了してしまうとか諸々


読んだ限り、TABLE4.8までは問題なさげ

Annihilation algorithmが任意の2*l>8に対して、(8,3,4)で停止することが言えるなら、Collatz予想は正しい

それを示すために、ALGORITHM4.14でannihilation algorithmを"逆走"していけるという主張っぽい;
(8,3,4)<-(6,6,3)<-...
       <-(10,10,3)<-...
       <-(16,16,3)<-...
とか、そんな感じ。なのだけど、(8,3,4)から辿って、ちゃんと全部の2*l>8が出てくることを示せていないと思われる

#ちなみに、ALGORITHM4.14も修正しないと、そのままでは間違ってると思われる

"""


def alg_forward(j):
  assert(j%3!=2)
  k=j
  ret = [k]
  while True:
    if k%2==0:break
    k = (3*k+1)/2
    ret.append(k)
  return ret

def alg_backward(m):
  assert(m >=5 and m%3==2)
  k = m
  ret = [k]
  while True:
    if k%3!=2:break
    k = (2*k-1)/3
    ret.append(k)
  return ret

def alg_annihilation(in_b):
  assert(in_b>8 and in_b%2==0)
  ret = []
  twoell = in_b
  while True:
    if twoell%3==2:
       j = alg_backward(twoell)[-1]
       j2dash = twoell/2
    elif twoell%6==0:
       j,j2dash = twoell,twoell/2
    else:
       j = twoell
       j2dash = alg_backward(twoell/2)[-1]
    ret.append( (twoell , j , j2dash) )
    if twoell==8:break
    twoell = alg_forward(j2dash)[-1]
  return ret

if __name__=="__main__":
  for n in xrange(10,1000000,2):
    assert(alg_annihilation(n)[-1]==(8,3,4)),n

