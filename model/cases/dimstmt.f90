! dimstmt: R851 DIMENSION statements (8.6.6): an entity's array-spec given
! apart from its type, before or after its type declaration, with and
! without ::, lower bounds; and an implicitly typed array (8.7)
program dimstmt
  integer :: a, n
  real(8) b
  dimension a(3), b(0:1, 2)
  dimension :: m(2)
  dimension x(4), k(4)
  integer :: m
  a = [1, 2, 3]
  b = 0.5d0
  b(1, 2) = 2.0d0
  m = 7
  do n = 1, 4
    x(n) = n / 2.0
    k(n) = n * n
  end do
  print *, a, sum(b), m, size(b), lbound(b, 1)
  print *, x, k
end program dimstmt
