! blockdata: BLOCK DATA (F77 16.2.5) giving a COMMON block its initial values, read by a
! subroutine; DATA in a subroutine (8.6.7), saved between calls
program blockdata
  implicit none
  call s1
  call s1
end program blockdata

subroutine s1
  implicit none
  integer :: n, k
  real :: x
  character(len=3) :: c
  common /blk/ n, x, c
  data k /10/
  print *, n, x, c, k
  n = n + 1
  k = k + 1
end subroutine s1

block data bd
  implicit none
  integer :: n
  real :: x
  character(len=3) :: c
  common /blk/ n, x, c
  data n, x, c /5, 2.5, 'abc'/
end
