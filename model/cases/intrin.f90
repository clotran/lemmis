! intrin: EXP and LOG, correctly rounded (fintr.lisp): the model's value is
! the true value rounded to nearest, which gfortran's and flang's libm give
! for these arguments
program intrin
  use iso_fortran_env, only: real32, real64
  implicit none
  real(real64) :: x
  real(real32) :: s
  x = 710.0_real64
  print *, exp(1.0_real64), log(2.0_real64), exp(0.0_real64), log(1.0_real64)
  print *, exp(x), exp(-x), log(1.0e-300_real64), exp(-1.5_real64)
  s = 2.5
  print *, exp(s), log(s), exp(-s), log(0.1)
  print *, dexp(0.5d0), dlog(10.0d0), alog(3.0)
end program intrin
