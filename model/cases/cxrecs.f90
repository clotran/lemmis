! cxrecs: list-directed input of a complex whose end of record falls between the real part and the
! comma, or the comma and the imaginary part (F77 13.6, F2008 10.10.3.1); records of an internal file
program cxrecs
  implicit none
  character(len=12) :: c(4)
  complex :: z, w
  integer :: i
  c(1) = '(1.5    ,'
  c(2) = '  2.25)  7'
  c(3) = '(3.0'
  c(4) = ', -4.0)'
  read (c, *) z, i, w
  print *, real(z), aimag(z), i, real(w), aimag(w)
end program
