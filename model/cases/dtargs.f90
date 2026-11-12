! derived-type dummy arguments (15.5.2.4): a structure and an array of
! structures by reference, INTENT(IN), INTENT(OUT) default-initialized
! (7.5.4.6), VALUE, an element of an array of structures copied back; a
! function of a derived type; a section of an array component assigned
module bodies
  implicit none
  type body
    real(8) :: m = 1.0d0
    integer :: v(3) = 0
  end type body
contains
  subroutine push(b, dv)
    type(body), intent(inout) :: b
    integer, intent(in) :: dv
    b%v = b%v + dv
  end subroutine push
  subroutine reset(b)
    type(body), intent(out) :: b
    b%v(1) = -1
  end subroutine reset
  real(8) function total(bs)
    type(body), intent(in) :: bs(:)
    integer :: i
    total = 0
    do i = 1, size(bs)
      total = total + bs(i)%m * sum(bs(i)%v)
    end do
  end function total
  function heavy(m) result(b)
    real(8), intent(in) :: m
    type(body) :: b
    b%m = m
    b%v(2:3) = [7, 8]
  end function heavy
  integer function first(b)
    type(body), value :: b
    b%v(1) = 99
    first = b%v(1)
  end function first
end module bodies
program dtargs
  use bodies
  implicit none
  type(body) :: a, bs(2)
  a%v(2:3) = 5
  print *, a%v(1), a%v(2), a%v(3)
  call push(a, 2)
  print *, a%v(1), a%v(2), a%v(3), a%m
  bs(1) = a
  call push(bs(2), 1)
  print *, bs(2)%v(3), total(bs)
  call reset(a)
  print *, a%v(1), a%v(2), a%m
  bs(2) = heavy(2.5d0)
  print *, bs(2)%m, bs(2)%v(1), bs(2)%v(3), first(bs(2)), bs(2)%v(1)
end program dtargs
