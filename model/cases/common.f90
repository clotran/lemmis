! common: COMMON blocks (R873, 8.10.2) shared by a main program and external
! subprograms, each object of the same type, kind and bounds in every unit
program cblocks
  integer :: n, ia(3)
  real :: x
  common /blk/ n, x, ia
  common k, m
  n = 2
  x = 1.5
  ia = [1, 2, 3]
  k = 10
  call bump
  print *, n, x, ia, k, m, iget()
end program
subroutine bump
  common /blk/ i, y, ja(3) // l, j
  i = i + 1
  y = y * 2
  ja(2) = 7
  l = l + 5
  j = 4
end subroutine
integer function iget()
  common k
  iget = k * 3
end function
