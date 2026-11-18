! seqnamed: a named sequential file (F77 12.10.1-3) on the empty file system: OPEN FILE= STATUS='NEW', WRITE,
! ENDFILE, REWIND, CLOSE (KEEP), INQUIRE by file (EXIST= OPENED= NUMBER=), OPEN STATUS='OLD' reads the records
! back; INQUIRE by unit (OPENED= NUMBER= ACCESS= FORM= BLANK=); CLOSE STATUS='DELETE' then EXIST= false
program seqnamed
  implicit none
  character(len=8) :: fn
  character(len=10) :: acc, frm, blk
  logical :: ex, op
  integer :: i, j, n, ios
  fn = 'sfile'
  inquire (file=fn, exist=ex, opened=op, iostat=ios)
  print *, ios, ex, op
  open (file=fn, unit=14, access='SEQUENTIAL', form='FORMATTED', status='NEW', blank='NULL')
  inquire (file=fn, exist=ex, opened=op, number=n)
  print *, ex, op, n
  inquire (unit=14, opened=op, number=n, access=acc, form=frm, blank=blk)
  print *, op, n, ' ', acc, frm, blk
  do i = 1, 3
    write (14, '(i4)') 10 * i
  end do
  endfile 14
  rewind 14
  close (unit=14, status='KEEP')
  inquire (file=fn, exist=ex, opened=op)
  print *, ex, op
  inquire (14, opened=op)
  print *, op
  open (15, file=fn, status='OLD')
  read (15, '(i4)') i
  read (15, '(i4)') j
  print *, i, j
  close (15, status='DELETE')
  inquire (file=fn, exist=ex)
  print *, ex
end program
