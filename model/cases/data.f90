! data: R840 DATA statements (8.6.7) in a main program: scalars, whole
! arrays in array element order, array elements, a repeat r * c, a
! signed constant, sets with and without a comma between them, values
! converted as in intrinsic assignment (a character's to its length)
program datas
  integer :: i, j, k(3), m(2, 2)
  real :: x, y(4)
  logical :: l
  character(len=3) :: c, cs(2)
  data i, j /1, -2/, k /3*7/
  data m /1, 2, 3, 4/, x /2/
  data y(2), y(4) /1.5, -0.5/
  data l /.true./ c /'abcde'/
  data cs /2*'xy'/
  y(1) = 0.0
  y(3) = m(2, 1)
  print *, i, j, k, m
  print *, x, y, l, c, '|', cs(1), '|', cs(2), '|'
end program datas
