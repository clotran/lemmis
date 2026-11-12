! SAVE (R802's attribute, R859 save-stmt): a procedure's local keeps its
! value from one call to the next (8.5.16)
module counters
  implicit none
contains
  integer function bump()
    integer, save :: n
    integer :: k = 0                  ! initialized: saved too (8.5.16)
    if (k == 0) n = 0
    k = 1
    n = n + 1
    bump = n
  end function bump
  subroutine tally(x)
    integer, intent(in) :: x
    integer :: total, calls
    real :: avg
    save total, calls
    if (x == 0) then
      total = 0
      calls = 0
    end if
    total = total + x
    calls = calls + 1
    avg = real(total) / real(calls)
    print *, calls, total, avg
  end subroutine tally
  subroutine each()
    integer :: m
    logical :: first = .true.
    save
    if (first) m = 10
    first = .false.
    m = m * 2
    print *, m
  end subroutine each
end module counters

program saving
  use counters
  implicit none
  integer :: i
  do i = 1, 3
    print *, bump()
  end do
  call tally(0)
  call tally(4)
  call tally(5)
  call each()
  call each()
end program saving
