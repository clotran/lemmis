! ac-implied-do (R782, R783, R784) in array constructors (R777): the
! values for each value of the do-variable, a construct entity (19.4)
program acdo
  implicit none
  integer :: i, j, n
  integer :: a(5), b(6)
  real :: r(4)
  i = 42
  n = 3
  a = [(i * i, i = 1, 5)]
  print *, a
  print *, i                                   ! not changed by the implied-do
  b = [0, (j, -j, j = 1, 2), 9]
  print *, b
  print *, [((10 * i + j, j = 1, 2), i = 1, n)]
  print *, [(i, i = 10, 1, -3)]
  print *, size([(i, i = 1, 7)]), sum([(i, i = 1, 100)])
  r = [(real(i) / 2.0, i = 1, 4)]
  print *, r
  print *, [(a(i), i = 5, 1, -2)], [1, (n + i, i = 1, 2)]
end program acdo
