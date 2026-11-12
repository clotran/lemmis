! complex: literal constants (R718), COMPLEX declarations (R704), the
! arithmetic, mixed with integer and real, == and /=, and the intrinsics
! REAL, AIMAG, CMPLX, CONJG, ABS, KIND; list-directed output writes a
! complex as (re,im) (13.10.4p8), each part compared as a real
program cplx
  use iso_fortran_env, only: real64
  implicit none
  complex :: a, b, c(3)
  complex(real64) :: z
  integer :: i
  real :: r
  a = (1.5, -2)
  b = (0.5e0, 4)
  z = (0.1_real64, -3)
  print *, a, b, z
  print *, a + b, a - b, a * b, a / (2.0, 0.0), -a
  print *, a + 1, 2 * a, a - 0.5, z + a, (2, 3) ** 2, a ** 1
  print *, a == (1.5, -2.0), a /= b, (1.0, 0.0) == 1.0
  print *, real(a), aimag(a), real(z), aimag(z), real(a, real64), kind(z)
  print *, conjg(a), abs((3.0, -4.0)), cmplx(1, 2), cmplx(1.5_real64, kind=real64), cmplx(a)
  r = a
  i = (7.9, 1.0)
  z = 2
  print *, r, i, z
  do i = 1, 3
    c(i) = cmplx(i, -i)
  end do
  print *, c, c(2) * c(3)
  print *, (1.0, -0.0), (-0.0, 0)
end program cplx
