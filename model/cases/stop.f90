! STOP with a stop-code (R1162, R1163): an integer or a character scalar
program stopcode
  implicit none
  integer :: i
  character(len=4) :: w
  w = 'done'
  do i = 1, 5
    print *, i
    if (i == 7) stop w
    if (i == 3) stop 2 - 2
  end do
  print *, 'not reached'
end program stopcode
