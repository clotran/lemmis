! seqfile: sequential files on units not connected by OPEN (F77 12.3.2: a READ or WRITE connects
! the unit's default file, which the run starts without); formatted and unformatted records
! written, REWIND, BACKSPACE, ENDFILE (12.10.4), READ back, END= at the end of the file
program seqfile
  implicit none
  integer :: i, j, k(3)
  real :: r
  character(len=4) :: c
  do i = 1, 3
    write (10, '(i3, f6.2, a4)') i, 0.5 * i, 'ab'
  end do
  rewind 10
  read (10, '(i3, f6.2, a4)') i, r, c
  print *, i, r, c
  read (10, '(i3)') i
  backspace 10
  backspace 10
  read (10, '(i3)') j
  print *, i, j
  read (10, *)
  read (10, '(i3)') i
  read (10, '(i3)', end=10) i
  print *, 'not at the end'
10 print *, 'end', i
  backspace 10
  backspace 10
  read (10, '(i3)') i
  print *, 'last', i
  k = [4, 5, 6]
  write (11) k, 2.5, 'wxyz'
  write (11) 7
  endfile 11
  rewind 11
  k = 0
  read (11) k(1), k(2)
  read (11) j
  print *, k, j
  backspace (11)
  backspace (unit=11)
  read (11) k, r, c
  print *, k, r, c
  read (11)
  read (11, end=20) j
  stop 1
20 print *, 'end 11'
end program
