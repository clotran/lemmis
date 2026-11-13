module m3
  implicit none
  type point
    integer :: x, y
  end type point
  type :: box
    type(point) :: lo, hi
    real(8) :: w(2)
    integer :: n = 7
    character(len=4) :: tag = 'none'
  end type
end module m3
program t3
  use m3
  implicit none
  type(point) :: p, ps(2)
  type(box) :: b
  p%x = 3
  p%y = -4
  ps(1) = point(1, 2)
  ps(2) = p
  b%lo = p
  b%hi = point(5, 6)
  b%w = 1.5d0
  print *, p, ps
  print *, b, 'end'
  write (*, '(2i4)') ps
end program t3
