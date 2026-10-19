! host association (19.5.1.4), explicit-shape dummies (8.5.8.2, 15.5.2.12),
! array-valued functions, recursion, logical kinds, STOP
program hosts
  implicit none
  integer :: n, acc(6)
  logical(1) :: flag
  n = 0
  call add(3)
  call add(4)
  print *, n, fib(15)
  acc = 0
  call setv(acc, 6)
  print *, acc, total(acc, size(acc))
  print *, evens(5)
  flag = .true._1
  print *, flag, kind(flag), .not. flag, flag .eqv. .false.
  if (n == 7) stop
  print *, 'not reached'
contains
  subroutine add(k)
    integer, intent(in) :: k
    n = n + k
  end subroutine add
  recursive function fib(k) result(f)
    integer, intent(in) :: k
    integer :: f
    if (k < 2) then
      f = k
    else
      f = fib(k - 1) + fib(k - 2)
    end if
  end function fib
  subroutine setv(v, m)
    integer, intent(in) :: m
    integer, intent(inout) :: v(m)
    integer :: i
    do i = 1, m
      v(i) = i * i
    end do
  end subroutine setv
  integer function total(v, m)
    integer, intent(in) :: m
    integer, intent(in) :: v(m)
    total = sum(v)
  end function total
  function evens(m) result(r)
    integer, intent(in) :: m
    integer :: r(m)
    integer :: i
    do i = 1, m
      r(i) = 2 * i
    end do
  end function evens
end program hosts
