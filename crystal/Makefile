FC=gfortran
CC=g++
LDFLAGS=-lgfortran

all:
	$(FC) -fopenmp -fPIC -O2 -c eri.f90
	$(CC) -fopenmp -c  -Wall $(LDFLAGS) -O2 -shared -fPIC crys.cpp molint.cpp
	$(CC) -fopenmp -shared eri.o crys.o molint.o -o libhf.so
clean:
	rm *.mod
	rm *.o
	rm *.so
	rm *.pyc
