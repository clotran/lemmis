! parstmt: PARAMETER ( named-constant-def-list ) (R855, 8.6.11): each
! constant typed by its earlier declaration or implicitly, its value
! converted as by assignment
program parstmt
  integer :: k
  double precision :: d
  character(5) :: c
  parameter (k = 3, d = 0.5d0 * k, c = 'abc')
  parameter (ipn = k + 4, rpn = 7, lpn = 2.9)
  real :: a(k)
  a = rpn
  print *, k, d, c, ipn, rpn, lpn, a
end program
