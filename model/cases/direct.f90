! direct: formatted direct access to a named file (F77 12.2.4.2, 12.10.1-3): OPEN FILE= a variable,
! ACCESS='DIRECT', RECL=, STATUS='NEW' then 'OLD' after CLOSE; WRITE and READ with REC= (records in any
! order, blank-filled to RECL, a slash the next record); INQUIRE RECL= NEXTREC=; ERR= and IOSTAT= not taken
program direct
  implicit none
  character(len=12) :: fn
  character(len=10) :: c
  integer :: i, j, n, r, ios
  real :: x
  fn = 'dfile  '
  open (file=fn, unit=12, access='DIRECT', recl=20, form='FORMATTED', status='NEW', iostat=ios)
  inquire (unit=12, recl=r, nextrec=n)
  print *, ios, r, n
  do i = 3, 1, -1
    write (unit=12, rec=i, fmt='(i4, f8.2)', err=90) i, 1.5 * i
  end do
  write (12, '(a3 / a4)', rec=4) 'abc', 'defg'
  inquire (12, nextrec=n)
  print *, n
  read (12, rec=2, fmt='(i4, f8.2, a8)') j, x, c
  print *, j, x, '[', c, ']'
  close (unit=12)
  open (12, file=fn, access='direct', recl=20, form='formatted', status='old')
  inquire (unit=12, nextrec=n)
  print *, n
  j = 3
  read (12, rec=j, fmt='(i4)', err=90) i
  read (12, '(a20 / a5)', rec=4) fn, c
  inquire (unit=12, nextrec=n, recl=r)
  print *, i, '[', fn, '][', c, ']', n, r
  close (12, status='delete', err=90)
  write (13, '(i3)') 7
  rewind (unit=13, iostat=ios, err=90)
  read (13, '(i3)') i
  print *, ios, i
  close (13, status='delete', iostat=ios)
  print *, ios
  stop
90 print *, 'err'
end program
