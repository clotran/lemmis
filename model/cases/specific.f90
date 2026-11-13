! specific: FORTRAN 77's specific intrinsic names (16.8, Tables 16.2, 16.3),
! each its generic on arguments of one type and kind; DIM, AINT, ANINT, DPROD
program specific
  integer :: i, j
  real :: x, y
  double precision :: d, e
  i = -7
  j = 3
  x = -2.75
  y = 1.5
  d = 2.25d0
  e = -0.5d0
  print *, iabs(i), isign(j, i), idim(j, i), idim(i, j), dim(j, i), max0(i, j, 2), min0(i, j)
  print *, amax0(i, j), amin0(i, j), max1(x, y), min1(x, y), amax1(x, y, 0.5), amin1(x, y)
  print *, abs(x), amod(x, y), dim(y, x), dim(x, y), aint(x), anint(x), aint(-0.25), anint(-0.25)
  print *, float(i), ifix(x), sngl(d), idint(-d), idnint(-d), dint(e), dnint(-d), dnint(e)
  print *, dabs(e), dsign(d, e), dmod(d, 1.0d0), ddim(d, e), dmax1(d, e, 1.0d0), dmin1(d, e)
  print *, dsqrt(d), dprod(x, y), dprod(y, y), anint(2.5), aint(1.0d0 / 3.0d0) + 1
end program
