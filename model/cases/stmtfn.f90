! stmtfn: statement functions (R1544, 15.6.4), typed by declaration or
! implicitly; the value as by assignment to the function's type; ICHAR
program stmtfn
  logical :: neg, l
  real :: r
  character :: c
  dimension ia(3)
  sq(x) = x * x
  neg(l) = .not. l
  ihyp(i, j) = sqrt(float(i**2) + float(j**2))
  r(x, y) = sq(x) + y
  k = 3
  ia = [1, 2, 3]
  c = 'A'
  print *, sq(1.5), neg(.true.), ihyp(k, 4), r(2.0, 0.25), sq(float(ia(2)))
  ia(1) = 7
  print *, ia, ichar(c), iachar('a'), ichar(c) < ichar('B')
end program
