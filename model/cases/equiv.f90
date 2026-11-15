! equiv: R870 EQUIVALENCE (8.10.1) in a main program: storage association
! (19.5.3): two reals one variable, a complex over two reals (each way), an
! array element over another array's, a complex at a real array's element,
! sets sharing a variable, and DATA through an associate
program equiv
  real :: x, y, r(2), s(4)
  complex :: c, d
  integer :: a(4), b(2), p, q, t, i1, i2
  equivalence (x, y), (c, r)
  equivalence (a(3), b(1)), (d, s(3))
  equivalence (p, q), (q, t)
  equivalence (i1, i2)
  data i1 /5/
  x = 1.5
  print *, y
  y = -2.0
  print *, x
  c = (1.5, -2.0)
  print *, r(1), r(2)
  r(2) = 3.0
  print *, c
  a = [1, 2, 3, 4]
  print *, b
  b(2) = 9
  print *, a
  s = [1.0, 2.0, 3.0, 4.0]
  print *, d
  d = (0.5, 0.25)
  print *, s
  t = 7
  print *, p, q
  print *, i2
end program equiv
