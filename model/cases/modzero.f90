! modzero: a zero result of real MOD and MODULO, its sign processor dependent
! (16.9.145, 16.9.146 give its value only; gfortran and flang differ on MOD's)
program z
  real(8) :: x, y, zz
  x = 0.5d0
  zz = 0.0d0
  y = mod(zz, 100.0d0)
  print *, y, mod(x - x, 100.0d0), mod(zz, 3.0d0), mod(-zz, 3.0d0)
  print *, modulo(zz, 3.0d0), modulo(-zz,3.0d0), modulo(-zz,-3.0d0), modulo(zz, -3.0d0)
  x = 6.0d0
  print *, mod(x, 3.0d0), mod(-x, 3.0d0), modulo(x, -3.0d0), modulo(-x, 3.0d0), modulo(-x, -3.0d0)
end program
