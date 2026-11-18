! equivsub: R870 EQUIVALENCE (8.10.1) in subprograms: a complex over two
! local reals, an array element over a local integer, a COMMON member over a
! local (the local takes the member's value, 19.6.5), a SAVE'd pair kept
! across calls, an EQUIVALENCE in a function, and a BLOCK DATA local over a
! COMMON real seen through another unit's integer (SAVE /b/, DATA implied-DO)
program equivsub
  integer :: k, f
  common /blk/ k
  k = 4
  call s(1.5)
  call s(2.5)
  print *, f(3)
  call t
end program equivsub
block data bd
  real :: x
  integer :: nb, w(3)
  common /cx/ x, w
  save /cx/
  equivalence (nb, x)
  data nb /34/, (w(i), i = 1, 3) /3*5/
end
subroutine t
  real :: x
  integer :: nt, w(3)
  common /cx/ x, w
  equivalence (nt, x)
  print *, nt, w
end subroutine t
subroutine s(v)
  real :: v, r(2)
  complex :: c
  integer :: a(3), j, m, n, p, q
  integer :: k
  common /blk/ k
  save p, q
  equivalence (c, r), (a(2), j), (m, k), (p, q)
  c = (0.5, -1.0)
  print *, r(1), r(2), v
  a = [7, 8, 9]
  print *, j
  print *, m
  m = m + 1
  print *, k
  if (v < 2.0) q = 10
  p = p + 1
  print *, q
end subroutine s
integer function f(i)
  integer :: i, t(2), u
  equivalence (t(2), u)
  t = [i, 2 * i]
  f = u
end function f
