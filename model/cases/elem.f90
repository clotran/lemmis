! elemental and pure procedures (15.8, 15.9): an elemental function on
! arrays element by element, on scalars as itself; a pure function's result
module ops
  implicit none
contains
  elemental integer function clamp(x, lo, hi)
    integer, intent(in) :: x, lo, hi
    clamp = max(lo, min(x, hi))
  end function clamp
  pure integer function dot(a, b)
    integer, intent(in) :: a(:), b(:)
    dot = sum(a * b)
  end function dot
end module ops

program elem
  use ops
  implicit none
  integer :: v(6), w(6)
  v = [-5, 0, 3, 8, 12, 20]
  w = clamp(v, 0, 10)
  print *, w
  print *, clamp(15, 0, 10), clamp(v(1), 0, 10)
  print *, dot(v, w), dot([1, 2, 3], [4, 5, 6])
  print *, clamp(v, v - 1, 10)
end program elem
