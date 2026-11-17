! fmtvar: a CHARACTER variable as the format (F77 12.2.4): FMT= and positional, a scalar, an array
program fmtvar
  character(len=12) :: f
  character(len=6) :: fa(2)
  character(len=20) :: u
  integer :: n
  u = " "
  f = '(I3, 1X, I4)'
  fa(1) = '(I2,'
  fa(2) = '1X,I2)'
  write (*, f) 7, 8
  write (unit=*, fmt=fa) 5, 6
  write (u, fmt=f) 12, 345
  read (u, f) n, n
  print *, n
end program fmtvar
