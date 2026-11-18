! comlayout: a COMMON block is one storage sequence (F77 17.1.2, 15.9.4): a
! unit may lay it out with other shapes, blank common may be shorter or
! longer in another unit, and an EQUIVALENCE extends a block that another
! unit then names
program comlayout
  integer :: a, b, c, d(3), x, y(3), p, q
  logical :: l
  common /b7/ a, b, c, d
  common p, l, q
  common /b9/ x
  equivalence (x, y)
  a = 41
  c = 43
  d(1) = 141
  d(2) = 142
  p = 1
  l = .true.
  q = 3
  x = 5
  y(2) = 15
  y(3) = 20
  call s
  print *, a, b, c, d
  print *, p, l, q
  print *, x, y
end program comlayout
subroutine s
  integer :: g(5), h, r, t(4), x1, x2, x3
  common /b7/ g, h
  common r
  common /b9/ x1, x2, x3
  g(1) = g(1) + 1
  g(2) = 43
  g(5) = g(5) + 1
  h = 144
  r = r + 10
  x2 = x2 + 1
  x3 = x3 + 1
  call u
end subroutine s
subroutine u
  integer :: t(2), m, n
  common t, m, n
  m = m + 1
  n = 7
end subroutine u
