! DO loop iteration counts (11.1.7.4.1), the DO variable after the loop,
! EXIT and CYCLE, DO WHILE, IF constructs
program loops
  implicit none
  integer :: i, j, s, n
  s = 0
  do i = 10, 1, -3
    s = s + i
  end do
  print *, s, i
  do i = 5, 1
    s = s + 1000
  end do
  print *, s, i
  n = 0
  do i = 1, 20
    if (mod(i, 2) == 0) cycle
    if (i > 11) exit
    n = n + i
  end do
  print *, n, i
  j = 1
  do while (j < 100)
    j = j * 3
  end do
  print *, j
  n = 0
  do
    n = n + 1
    if (n >= 7) exit
  end do
  print *, n
  do i = 1, 4
    if (i == 1) then
      print *, 'one'
    else if (i == 2) then
      print *, 'two'
    else if (i == 3) then
      print *, 'three', .true.
    else
      print *, 'many', .false., i > 3
    end if
  end do
end program loops
