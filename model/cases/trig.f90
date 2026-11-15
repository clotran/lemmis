! trig: SIN, COS, TAN, ATAN, ATAN2, correctly rounded (ftrig.lisp): the
! model's value is the true value rounded to nearest; sin(1d22) checks the
! range reduction by an exact rational pi. (not here: flang's
! atan2(-2d0, 0.5d0), one ulp off the true -1.32581766366803255...)
program trig
  use iso_fortran_env, only: real32, real64
  implicit none
  real(real64) :: x, big
  real(real32) :: s
  x = 1.0_real64
  big = 1.0e22_real64
  print *, sin(x), cos(x), atan2(x, -x), sin(big)
  print *, cos(big), sin(-0.5_real64), cos(3.0_real64), atan(0.25_real64)
  print *, atan2(-1.0_real64, 3.0_real64), atan2(0.0_real64, -1.0_real64), atan(1.0e10_real64), tan(0.5_real64)
  s = 2.5
  print *, sin(s), cos(s), atan(s), atan2(s, -s)
  print *, dsin(0.75d0), dcos(0.75d0), datan(3.0d0), datan2(1.0d0, 2.0d0)
end program trig
