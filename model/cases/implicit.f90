! implicit: R863 IMPLICIT statements (8.7): a type for each name by its
! first letter, single letters and ranges, LOGICAL, DOUBLE PRECISION,
! CHARACTER * length, INTEGER over a letter 8.7 makes real; the rest real
! or integer as 8.7p3, and a DIMENSION'd name typed the same way
program impl
  implicit logical (l), double precision (d), character*5 (c, s-t)
  implicit integer (a-b)
  dimension cs(2)
  lflag = .true.
  d1 = 1.0d0 / 3.0d0
  cname = 'abcdefgh'
  tname = 'xy'
  cs(2) = 'qrstuvw'
  a1 = 7 / 2
  b2 = a1 * 2
  x = 2.5
  i = 3
  print *, lflag, cname, '|', tname, '|', cs(2), '|', a1, b2, x, i
  print *, d1, len(cname)
end program impl
