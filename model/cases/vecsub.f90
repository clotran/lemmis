! vector subscripts (R921, R925): a rank-one integer array as a
! section-subscript, its elements' values the indices, in order
program vecsub
  implicit none
  integer :: a(6), b(3, 4), v(3), w(2), i, j
  a = [(10 * i, i = 1, 6)]
  v = [5, 1, 3]
  print *, a(v)
  print *, a([6, 6, 2]), size(a(v)), sum(a(v))
  a(v) = [-1, -2, -3]
  print *, a
  do i = 1, 3
    do j = 1, 4
      b(i, j) = 10 * i + j
    end do
  end do
  w = [4, 2]
  print *, b(2, w), b(v(2:3), 1)
  print *, b([3, 1], w)
  b([1, 2], w) = 0
  print *, b(1, :), b(2, :)
  print *, a(v(3:1:-1)) + 1
end program vecsub
