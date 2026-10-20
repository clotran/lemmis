! reals: binary64 and binary32 arithmetic, rounding, signed zeros,
! infinities and NaN, conversions, and the intrinsics clotran's compiler
! writes (sqrt, abs, sign, merge, min, max, real, floor, int, nint)
program reals
  use iso_fortran_env, only: int64, real32, real64
  implicit none
  real(real64) :: x, y, z, zero, nzero, inf, nan
  real(real32) :: s, t
  integer(int64) :: i
  x = 0.1_real64
  y = 0.2_real64
  print *, x + y, x * 3.0_real64, 1.0_real64 / 3.0_real64
  s = 0.1
  t = s * 3.0
  print *, s, t, real(s, real64)
  zero = 0.0_real64
  nzero = -zero
  inf = 1.0_real64 / zero
  nan = zero / zero
  print *, nzero, inf, -inf
  print *, nan /= nan, nan == nan, inf > huge(x), nzero == zero
  print *, sign(1.0_real64, nzero), sign(2.0_real64, -0.5_real64), abs(nzero)
  print *, sqrt(2.0_real64), sqrt(nzero), sqrt(2.0)
  i = 9007199254740993_int64
  print *, real(i, real64), real(i)
  print *, floor(-2.5_real64, int64), int(-2.5_real64), nint(-2.5_real64), nint(2.5_real64), ceiling(2.1d0)
  z = huge(x)
  print *, z * 2.0_real64, tiny(x) / 4.0_real64, epsilon(s)
  print *, merge(x, y, x < y), min(x, y), max(x, y, 0.5_real64)
  print *, mod(-7.5_real64, 2.0_real64), modulo(-7.5_real64, 2.0_real64)
  z = 1.0d300
  print *, z * z, -z * z, z / 1.0d-300
  print *, x ** 2, 2.0_real64 ** (-1), 1.5d0 + 2
  print *, max(nan, 1.0_real64)
end program reals
