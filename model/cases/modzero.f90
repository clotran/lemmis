! modzero: a zero result of real MOD takes the sign of A (gfortran, flang and
! flang-new agree; 16.9.145 gives the value only). MODULO's zero sign stays
! processor dependent (16.9.146), so no MODULO zero is printed here.
program z
  real :: a, p
  real(8) :: x, y, zz
  a = 4.0
  p = 2.0
  print *, mod(a, p), mod(-a, p), mod(a, -p), mod(-a, -p)
  zz = 0.0d0
  x = 0.5d0
  y = mod(zz, 100.0d0)
  print *, y, mod(-zz, 3.0d0), mod(x - x, 100.0d0), mod(-6.0d0, 3.0d0), mod(6.0d0, -3.0d0)
  print *, mod(-0.0, 2.0), mod(7.5, 2.5), mod(-7.5, 2.5)
  x = 6.0d0
  print *, modulo(x, -3.0d0) + 1.0d0, modulo(-x, 3.0d0) + 1.0d0
end program
