! READ from * (12.6, 13.7, 13.10.3), its records ioread.in: list-directed
! (separators, null values, r*c, a slash), formatted (I F L B O Z, BZ, kP,
! an implied point, T TL X, a slash), a nonadvancing READ
program ioread
  implicit none
  integer :: n, m, a(5), j(4), i1, i2
  real(8) :: x, y, z(5)
  real :: s
  logical :: l1, l2
  a = 0
  j = 0
  z = 9
  read *, n, x, l1
  print *, n, x, l1
  read (*, *) a
  print *, a
  read (unit=*, fmt=*) m, j(2)
  print *, m, j
  read (*, '(i6, f6.0, f5.2)') i1, x, y
  print *, i1, x, y
  read (*, '(bz, i5, bn, i6, 1x, 2l1)') i1, i2, l1, l2
  print *, i1, i2, l1, l2
  read *, z(1:5)
  print *, z
  read *, x, s
  write (*, '(f6.2, 1x, f6.2)') x, s
  read *
  read (*, '(b5, o4, z3)') i1, i2, n
  print *, i1, i2, n
  read (*, '(f6.2, i3)') x, n
  print *, x, n
  read '(2p, f6.0)', x
  print *, x
  read (*, '(t6, i2, tl4, i3)') i1, i2
  print *, i1, i2
  read (*, 10) i1, i2
10 format (i2 / i2)
  print *, i1, i2
  read (*, '(i2)', advance='no') i1
  read (*, '(i3)') i2
  print *, i1, i2
  read *, l1, l2, n
  print *, l1, l2, n
end program ioread
