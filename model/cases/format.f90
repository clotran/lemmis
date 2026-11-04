! FORMAT and WRITE in free form: E, L, A, X, /, reversion, and GO TO
program fmt
  implicit none
  integer :: i
  real(8) :: d
  logical :: b
  d = 1234.5d0
  b = .true.
  write (*, 200) d, b, 'abc'
200 format (e12.4, 1x, l2, 1x, a5)
  write (*, 210) 7, 8
210 format (i3 / i3)
  write (*, 230) 1, 2, 3, 4, 5
230 format (3i4)
  i = 0
300 i = i + 1
  if (i < 3) go to 300
  write (*, 240) 'i=', i
240 format (a, i0)
  write (*, 220)
220 format ('no items')
  ! ties round to even, the processor's I/O rounding (13.7.2.3.8)
  write (*, 250) 0.125d0, 0.375d0, 2.5d0, 3.5d0, -2.5d0, 1235.5d0
250 format (2f6.2, 3f5.0, e12.4)
  write (*, 260) 42, -7, 1.5d0
260 format (i0, 1x, i0, 1x, f0.2)
end program fmt
