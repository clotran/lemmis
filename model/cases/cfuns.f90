! cfuns: EXP, LOG, SIN, COS of a complex (16.9.74, .120, .180, .55), each
! part correctly rounded, and ABS (16.9.2), the modulus correctly rounded; arguments where gfortran's and flang's libm agree
! with the correctly rounded value (both are an ulp off elsewhere)
program cfuns
  use iso_fortran_env, only: real64
  implicit none
  complex(real64) :: z, w
  complex :: a, b
  z = (1, 1)
  w = (0.5_real64, -2)
  a = (1, 1)
  b = (-3, 0.25)
  print *, exp(z)
  print *, exp(w)
  print *, log(z), log(w)
  print *, sin(z), sin((0.0_real64, 1.0_real64))
  print *, cos(w)
  print *, abs(z), abs(w), abs(b)
  print *, exp(a), log((0.5, -2.0)), sin(b)
  print *, cos((10.0, 3.0)), cexp(a), clog(a)
end program cfuns
