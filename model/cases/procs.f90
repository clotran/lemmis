! modules and use association (14.2), procedures and their arguments:
! intent (8.5.10), value, recursion, pure, internal procedures and host
! association (19.5.1.4), keyword arguments (15.5.2.1)
module counters
  implicit none
  integer :: total = 0
contains
  subroutine bump(n)
    integer, intent(in) :: n
    total = total + n
  end subroutine bump
  pure integer function sq(x)
    integer, intent(in) :: x
    sq = x * x
  end function sq
  recursive integer function fact(n) result(r)
    integer, intent(in) :: n
    if (n <= 1) then
      r = 1
    else
      r = n * fact(n - 1)
    end if
  end function fact
  subroutine swap(x, y)
    integer, intent(inout) :: x, y
    integer :: t
    t = x
    x = y
    y = t
  end subroutine swap
  subroutine fill(v, k)
    integer, intent(out) :: v(:)
    integer, value :: k
    integer :: i
    do i = 1, size(v)
      v(i) = k * i
    end do
    k = 0
  end subroutine fill
end module counters

program procs
  use counters
  implicit none
  integer :: p, q, w(4), k
  call bump(5)
  call bump(n=7)
  print *, total, sq(9), fact(10)
  p = 1
  q = 2
  call swap(p, q)
  print *, p, q
  k = 3
  call fill(w, k)
  print *, w, k
  call swap(w(1), w(4))
  print *, w
  call twice()
  print *, total
contains
  subroutine twice()
    total = total * 2
  end subroutine twice
end program procs
