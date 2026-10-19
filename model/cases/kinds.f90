! integer kinds, the result kind of mixed operands (10.1.9.3), division
! toward zero (10.1.5.2.2), negative powers (10.1.5.2.1p5)
program kinds
  use iso_fortran_env, only: int8, int16, int32, int64
  implicit none
  integer(int8) :: a
  integer(int16) :: b
  integer(int64) :: c
  integer :: i
  a = 100_int8
  b = 30000_int16
  c = 9000000000_int64
  i = -7
  print *, a, b, c, kind(a), kind(b), kind(c), kind(i)
  print *, kind(a + b), kind(b * c), a + b, b * 2
  print *, i / 2, -i / 2, i / (-2), mod(i, 3), modulo(i, 3), mod(7, -3), modulo(7, -3)
  print *, 2 ** 10, 2 ** (-3), (-1) ** (-3), 1 ** (-5), (-2) ** 3
  print *, huge(a), huge(b), huge(i), huge(c)
  print *, -2 ** 2, 2 ** 3 ** 2, 10 - 3 - 2, 100 / 10 / 5
  print *, abs(-5), max(3, 9, 4), min(3, -9, 4), int(c / 1000000_int64)
end program kinds
