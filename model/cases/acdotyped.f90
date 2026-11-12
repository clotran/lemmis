! not gfortran: gfortran 16 rejects R783's integer-type-spec :: (Fortran 2008)
! ac-implied-do-control with an integer-type-spec (R783): the variable a
! construct entity of that type and kind, not declared outside
program acdotyped
  implicit none
  integer :: i, n
  i = 1
  n = 3
  print *, [(m * 2, integer :: m = 1, 3)]
  print *, [(m + i, integer(8) :: m = 1, 2)], [(-m, integer(kind=8) :: m = n, 1, -1)]
  print *, huge([(m, integer(8) :: m = 1, 2)]), huge([(m, integer :: m = 1, 2)])
  print *, [((10 * m + i, integer :: m = 1, 2), i = 1, 2)]
end program acdotyped
