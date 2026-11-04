! Formatted output (13.7, 13.8): character-literal formats, FMT= and UNIT=,
! PRINT with a format, ES EN G B O Z T TL TR P S SP SS : and ADVANCE='NO'
program iofmt
  implicit none
  integer :: i, k(3)
  real(8) :: d
  real :: r
  logical :: b
  d = 1234.5d0
  r = -0.00125
  b = .false.
  k = [1, 2, 3]
  write (*, '(es12.4, 1x, en12.4, 1x, es10.2)') d, d, 0.000123d0
  write (*, '(en12.3, 1x, en12.3, 1x, en12.3)') 999.95d0, 0.0123d0, -45678.0d0
  write (*, '(g12.4, 1x, g12.4, 1x, g12.4, 1x, g12.4)') d, 0.001d0, 0.5d0, 0.0d0
  write (*, '(g12.4e3, g10.3, g8.2)') 1.0d10, 99.96d0, 7.0d0
  write (*, '(g6.2, g5.0, 1x, g4.1, g3.0)') 42, 7, .true., b
  write (unit=*, fmt='(b10, 1x, o6, 1x, z6, 1x, b0, 1x, z0.4, 1x, b8.6)') 10, 64, 255, 5, 171, 3
  write (*, fmt='(z9, 1x, o12)') -1, -8
  write (fmt='(i3, t10, i3, tl5, i1, tr2, i2)', unit=6) 1, 2, 3, 4
  write (*, '(2p, f10.3, 1x, e12.4, -1p, e12.4, 0p, f8.2, 1p, e12.4)') d, d, d, d, d
  write (*, '(sp, i4, f8.2, e11.3, ss, i4, s, i4)') 5, 1.5d0, 2.0d0, 5, 5
  write (*, '(3(i2, :, ","))') 1, 2
  write (*, '(a, 3(i2, :, " and"))') 'k:', k
  write (*, '(i2, (i3, i4))') 1, 2, 3, 4, 5, 6, 7
  write (*, '(i2, 3i3)') 1, 2, 3, 4, 5, 6
  write (*, '("[", 2(i1, 1x), "]")') (1), 2, 3
  write (*, '(e12.4, f6.3, f4.2, f3.2)') r, r, 0.25d0, 0.5d0
  write (*, '(e10.3e1, e12.3e4, d11.3)') 1.5d5, 2.5d-120, -6.0d-3
  write (*, '(a)', advance='no') 'abc'
  write (*, '(i3)') 7
  write (*, '(a, 2x)', advance='NO') 'x='
  write (*, '(i2, t1, a)', advance='no') 9, '<'
  write (*, '(a)') '>'
  print '(i4, f6.1)', 3, 2.5d0
  print 10, 4, d
10 format (i5, f10.2)
  print '(a, l2)', 'b is', b
  i = 3
  write (*, 20, advance='no') i
20 format ('i=', i0)
  write (*, '(a)', advance='yes') ';'
  write (*, '(f8.3)', advance='no') 1.5d0
end program iofmt
