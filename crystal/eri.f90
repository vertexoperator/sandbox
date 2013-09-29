	module molint
	TYPE GaussBasis
	  integer(8) :: nx,ny,nz
	  real(8) :: x,y,z
	  integer(8) :: length
   	  real(8),allocatable :: norms      !これは互換性のあるやり方か?
	  real(8),allocatable :: exponents  !これは互換性のあるやり方か?
	END TYPE GaussBasis
	end module molint

	real(8) function computeFock(basis , Nbasis , P , F)
		use molint
		use omp_lib
		external computeERI  ! defined by C/C++
		real(8) :: computeERI
		integer :: Nbasis
		TYPE(GaussBasis) :: basis(Nbasis)
		real(8) :: IJKL
		real(8) :: P(Nbasis,Nbasis),F(Nbasis,Nbasis)
		real(8) :: starttime,endtime
!$omp parallel
                starttime = omp_get_wtime()
!$omp  do private(J,K,L,IJKL) reduction(+:F)
		DO I=1,Nbasis
		    DO J=I,Nbasis
		       DO K=1,Nbasis
		           DO L=K,Nbasis
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
!!				 F[i,j] += 2.0*P[k,l]*(ij|kl)
!!				 F[i,l] += -P[k,j]*(ij|kl)
		                F(J,I) = F(J,I) + 2.0*P(L,K)*IJKL
		                F(L,I) = F(L,I)-P(J,K)*IJKL 
		                IF (I.ne.J .and. K.ne.L) THEN
		                       F(I,J) = F(I,J) + 2.0*P(L,K)*IJKL
		                       F(L,J) = F(L,J) - P(I,K)*IJKL
		                       F(J,I) = F(J,I) + 2.0*P(K,L)*IJKL
		                       F(K,I) = F(K,I) - P(J,L)*IJKL
		                       F(I,J) = F(I,J) + 2.0*P(K,L)*IJKL
		                       F(K,J) = F(K,J) - P(I,L)*IJKL
		                ELSE IF (I.ne.J) THEN
		                       F(I,J) = F(I,J) + 2.0*P(L,K)*IJKL
		                       F(L,J) = F(L,J) - P(I,K)*IJKL
		                ELSE IF (K.ne.L) THEN
		                       F(J,I) = F(J,I) + 2.0*P(K,L)*IJKL
		                       F(K,I) = F(K,I) - P(J,L)*IJKL
		                END IF
		           END DO
		       END DO
		    END DO
		END DO
!$omp end do
                endtime = omp_get_wtime()
!$omp end parallel
	computeFock = endtime-starttime
	END 


