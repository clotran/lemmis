! WRITE to an internal file (12.2.5, 12.8): a CHARACTER scalar takes one record,
! blank-filled; a CHARACTER array a record per element
program intwrite
  implicit none
  character(len=12) :: s
  character(len=4) :: a(3)
  integer :: i
  i = 42
  s = ' '
  write (s, '(a2, i5)') 'AB', i
  print *, s, '|'
  a = ' '
  write (unit=a, fmt='(a1/a3)') 'X', 'yz'
  print *, a(1), '|', a(2), '|', a(3), '|'
end program intwrite
