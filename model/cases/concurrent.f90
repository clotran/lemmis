! concurrent: DO CONCURRENT as clotran's compiler writes it, two indices
! with an integer-type-spec, a pure function, and a temporary each
! iteration defines before it refers to it
module sq
  use iso_fortran_env, only: int64, real64
  implicit none
contains
  pure function twice(x) result(r)
    real(real64), intent(in) :: x
    real(real64) :: r
    r = x + x
  end function twice
end module sq

program concurrent
  use iso_fortran_env, only: int64, real64
  use sq
  implicit none
  integer(int64) :: k, n
  real(real64) :: a(0:4), t
  integer :: m(3, 2), i
  n = 5_int64
  do concurrent (k = 0:n - 1)
    a(k) = twice(real(k, real64)) + 0.5_real64
  end do
  print *, a
  do concurrent (integer :: i2 = 1:3, j = 1:2)
    m(i2, j) = 10 * i2 + j
  end do
  print *, m
  do concurrent (k = 0:4:2)
    t = a(k) * 2.0_real64
    a(k) = t
  end do
  print *, a
  i = 0
  print *, i
end program concurrent
