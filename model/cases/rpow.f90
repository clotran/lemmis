! rpow: a real to a real power (10.1.5.2.1), the true value correctly rounded
! (fcplx fl-pow); exact, irrational and integer-valued powers, both kinds and
! mixed; arguments where gfortran, flang and the exactly rounded value agree
program rpow
  use iso_fortran_env, only: real64
  implicit none
  real :: x, y
  real(real64) :: a, b
  x = 10.0
  y = 5.0
  print *, x ** y, 2.0 ** 0.5, 1.5 ** 2.5, 0.7 ** (-3.3)
  x = 0.875
  y = 100.0
  print *, x ** y, 100.0 ** (-1.5), 1234.5 ** 0.25, 3.0 ** 3.0, 1.0 ** 123.4
  a = 2
  b = 0.5_real64
  print *, a ** b, 10.0_real64 ** 0.3_real64, 2.5_real64 ** 3.0_real64, 4.0_real64 ** b
  a = 1.0001_real64
  b = 10000
  print *, a ** b, 0.1_real64 ** 0.1_real64, 123456.789_real64 ** (-2.75_real64)
  print *, 9.0_real64 ** 1.5_real64, 1.1_real64 ** 100.5_real64, 3.0_real64 ** 36.0_real64
  print *, 16.0_real64 ** 0.75_real64, 1.7_real64 ** (-0.4_real64), 2.5 ** 1.5_real64
  print *, 7.0_real64 ** (-0.0625_real64), 3.0_real64 ** 0.1
end program rpow
