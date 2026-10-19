! arrays: bounds (8.5.8), element order (9.5.3.2), sections (9.5.3.3),
! whole-array assignment and elemental operations (10.1.10), constructors
program arrays
  implicit none
  integer :: a(5), b(0:4), m(2, 3), i, j
  integer, dimension(3) :: c
  a = [1, 2, 3, 4, 5]
  b = a * 10
  print *, a, b(0), b(4), size(a), lbound(b, 1), ubound(b, 1)
  do j = 1, 3
    do i = 1, 2
      m(i, j) = 10 * i + j
    end do
  end do
  print *, m
  print *, m(2, :), m(:, 3)
  print *, a(2:4), a(5:1:-2), a(::2), size(a(3:2))
  c = a(1:3) + a(3:5)
  print *, c, sum(c), product(c), maxval(a), minval(b)
  a(2:4) = 0
  print *, a, any(a == 0), all(a > 0), count(a > 0)
  print *, size(m), size(m, 2), shape_sum(m)
contains
  integer function shape_sum(x)
    integer, intent(in) :: x(:, :)
    shape_sum = size(x, 1) * 100 + size(x, 2)
  end function shape_sum
end program arrays
