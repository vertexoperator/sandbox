	module molint
	TYPE GaussBasis
	  integer(8) :: nx,ny,nz
	  real(8) :: x,y,z
	  integer(8) :: length
   	  real(8),allocatable :: norms      !これは互換性のあるやり方か?
	  real(8),allocatable :: exponents  !これは互換性のあるやり方か?
	END TYPE GaussBasis
	end module molint

	real(8) function computeFock(basis , Nbasis , P , F , Nthread)
		use molint
		use omp_lib
		external computeERI  ! defined by C/C++
		real(8) :: computeERI
		integer :: Nbasis,Nthread,I,J,K,L,L_H
		TYPE(GaussBasis) :: basis(Nbasis)
		real(8) :: IJKL,C1,C2
		real(8) :: P(Nbasis,Nbasis),F(Nbasis,Nbasis)
		real(8) :: starttime,endtime
		call omp_set_num_threads(Nthread)
!$omp parallel
                starttime = omp_get_wtime()
!$omp  do private(J,K,L,L_H,IJKL,C1,C2) reduction(+:F)
		DO I=1,Nbasis
		    DO J=1,I
		       DO K=1,I
		           L_H = K
		           IF(K.eq.I) L_H = J
		           DO L=1,L_H
		                IJKL  = computeERI(basis(I)%x , &
				                   basis(I)%y , &
				                   basis(I)%z , &
				                   basis(I)%nx , &
				                   basis(I)%ny , &
				                   basis(I)%nz , &
				                   basis(I)%exponents , &
				                   basis(I)%norms , &
				                   basis(I)%length , &
				                   basis(J)%x , basis(J)%y , basis(J)%z , &
				                   basis(J)%nx , basis(J)%ny , basis(J)%nz , &
				                   basis(J)%exponents , &
				                   basis(J)%norms , &
				                   basis(J)%length , &
				                   basis(K)%x , basis(K)%y , basis(K)%z , &
				                   basis(K)%nx , basis(K)%ny , basis(K)%nz , &
				                   basis(K)%exponents , &
				                   basis(K)%norms , &
				                   basis(K)%length , &
				                   basis(L)%x , basis(L)%y , basis(L)%z , &
				                   basis(L)%nx , basis(L)%ny , basis(L)%nz , &
				                   basis(L)%exponents , &
				                   basis(L)%norms , &
				                   basis(L)%length)
!!                              (IJ|KL)=(IJ|LK)=(JI|KL)=(JI|LK)=
!!                              (KL|IJ)=(KL|JI)=(LK|IJ)=(LK|JI)
!!				F[i,j] += 2.0*P[k,l]*(ij|kl)
!!				F[i,l] += -P[k,j]*(ij|kl)
		                IF(I.eq.K .and. J.eq.L) IJKL = IJKL*0.5
		                C1 = 1.0
		                C2 = 1.0
		                IF (I.ne.J) THEN
		                   C2 = 2.0
		                   F(J,L) = F(J,L) - P(I,K)*IJKL
		                   F(K,I) = F(K,I) - P(J,L)*IJKL
		                END IF
		                IF (K.ne.L) THEN
		                   C1 = 2.0
		                   F(I,K) = F(I,K) - P(J,L)*IJKL
		                   F(L,J) = F(L,J) - P(I,K)*IJKL
 		                END IF
		                IF (I.ne.J .and. K.ne.L) THEN
		                   F(J,K) = F(J,K) - P(I,L)*IJKL
		                   F(L,I) = F(L,I) - P(J,K)*IJKL
		                END IF
		                F(I,J) = F(I,J) + C1*2.0*P(K,L)*IJKL
                                F(I,L) = F(I,L) - P(J,K)*IJKL
		                F(K,L) = F(K,L) + C2*2.0*P(I,J)*IJKL
		                F(K,J) = F(K,J) - P(I,L)*IJKL
		           END DO
		       END DO
		    END DO
		END DO
!$omp end do
                endtime = omp_get_wtime()
!$omp end parallel
	DO I=1,Nbasis
	   DO J=I+1,Nbasis
	      F(I,J)=F(J,I)
	   END DO
	END DO
	computeFock = endtime-starttime
	END 


