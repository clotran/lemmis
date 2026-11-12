! ALLOCATABLE (R802), deferred shape (R822), ALLOCATE (R927, R932, R934),
! DEALLOCATE (R941) and ALLOCATED (16.9.11): an array whose bounds are
! given at run time
module stats
  implicit none
contains
  real function mean(x)
    real, intent(in) :: x(:)
    mean = sum(x) / real(size(x))
  end function mean
  subroutine squares(n)
    integer, intent(in) :: n
    integer, allocatable :: s(:)      ! a local: unallocated at each call
    integer :: i
    print *, allocated(s)
    allocate(s(n))
    do i = 1, n
      s(i) = i * i
    end do
    print *, s, sum(s)
  end subroutine squares
end module stats

program alloc
  use stats
  implicit none
  real, allocatable :: a(:)
  integer, allocatable :: m(:, :), v(:)
  integer :: i, j, n
  n = 5
  print *, allocated(a), allocated(m)
  allocate(a(n), m(0:1, -1:n - 3))
  print *, allocated(a), size(a), lbound(m), ubound(m), size(m)
  do i = 1, n
    a(i) = real(i) / 2.0
  end do
  do j = -1, n - 3
    do i = 0, 1
      m(i, j) = 10 * i + j
    end do
  end do
  print *, a, mean(a)
  print *, m
  print *, sum(m(1, :))
  deallocate(a)
  print *, allocated(a)
  allocate(a(2:3))
  a = 7.5
  print *, lbound(a), a
  if (.not. allocated(v)) allocate(v(0))
  print *, size(v), allocated(v)
  deallocate(a, m, v)
  print *, allocated(a), allocated(m), allocated(v)
  call squares(3)
  call squares(4)
end program alloc
