! userename: USE with a rename-list and an ONLY list with renames (14.2.2, R1409, R1411,
! R1412): a renamed entity is reached by its local name; a rename-list keeps the rest
module ur_m
  implicit none
  integer :: n = 3, m = 4
  real(8), parameter :: half = 0.5d0
contains
  integer function twice(i)
    integer, intent(in) :: i
    twice = 2 * i
  end function
  subroutine bump(i)
    integer, intent(inout) :: i
    i = i + n
  end subroutine
end module

program userename
  use ur_m, cnt => n, dbl => twice
  implicit none
  integer :: k
  k = 1
  call bump(k)
  print *, cnt, m, dbl(k), k, half
  call sub2
contains
  subroutine sub2
    use ur_m, only: up => bump, m, h => half
    integer :: j
    j = m
    call up(j)
    print *, j, h
  end subroutine
end program
