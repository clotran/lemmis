! charequiv: character EQUIVALENCE of different lengths (F77 17.1.2: a
! character storage unit per character), and internal WRITE (12.2.5) to an
! array element, a substring, and a variable not yet defined
program charequiv
  character(len=6) :: s
  character(len=1) :: e(6)
  character(len=3) :: t(2)
  character(len=8) :: w, u(2)
  equivalence (s, e), (t, e)
  s = 'abcdef'
  print *, e(2), e(5), t(2)
  e(4) = 'X'
  print *, s, t(1), t(2)
  t(1) = 'pqr'
  print *, s
  write (w, '(I4)') 42
  print *, w
  w = 'zzzzzzzz'
  write (w(3:6), '(I4)') -7
  print *, w
  u(2) = 'old'
  write (u(1), '(A,I2)') 'n=', 5
  print *, u(1), u(2)
end program charequiv
