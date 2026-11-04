! DOUBLE PRECISION (R704, 7.4.3.2p2): a real of the kind of 1.0d0
program dprec
  implicit none
  double precision :: x, y
  real :: r
  x = 1.0d0 / 3.0d0
  r = 1.0 / 3.0
  y = r
  print *, x, kind(x), kind(1.0d0) == kind(x)
  print *, x + r, kind(x + r), y
  print *, sqrt(2.0d0), dble(r) == y
end program dprec
