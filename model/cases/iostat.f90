! iostat: IOSTAT= on READ and WRITE (F77 12.7): zero when no error or end of file occurs (a nonzero
! value is the processor's); with a unit and format positional or keyword, with ERR= and END= beside it
program iostat
  implicit none
  integer :: i, j, ios, k
  ios = 9
  write (21, '(i3)', iostat=ios) 42
  k = ios
  rewind 21
  ios = 9
  read (unit=21, fmt='(i3)', iostat=ios, end=80, err=90) i
  print *, k, ios, i
  ios = 9
  write (*, '(a, i2)', iostat=ios) 'ok', 7
  print *, ios
  ios = 9
  write (21, '(2i4)', iostat=ios) 5, 6
  rewind (21)
  read (21, '(i3)') i
  read (21, *, iostat=j) i, k
  print *, ios, j, i, k
  close (21, status='DELETE')
  stop
80 print *, 'end'
  stop
90 print *, 'err'
end program
