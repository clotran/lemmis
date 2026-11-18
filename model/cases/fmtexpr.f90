! fmtexpr: F77 12.2.4 a format that is a character expression or an array
! element (FMT= or the second positional control item), and DATA in a
! subroutine with an assumed-length dummy
program fmtexpr
  character(len=6) :: a
  character(len=12) :: c(3)
  integer :: j(2), i
  a = 'I3,I2'
  j = [5, 7]
  write (6, '(1X,' // a // ')') j
  c(2) = '(1X,I4,I3)'
  i = 2
  write (6, c(i)) j
  write (6, fmt=c(i)) j(2), j(1)
  write (6, fmt='(1X,' // a(1:2) // ')') 42
  call s('(1X,A,I2)')
end program fmtexpr
subroutine s(f)
  character(len=*) :: f
  character(len=3) :: t
  data t /'n ='/
  write (6, f) t, 9
end subroutine s
