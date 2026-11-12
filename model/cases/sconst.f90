! structure constructors (R756, 7.5.10): components in declaration order,
! by keyword, from default initialization; each value converted as in
! intrinsic assignment; arrays of structures (an element's component
! read and assigned, R911's first part-ref an array element, a whole
! element assigned)
module geo
  implicit none
  type pt
    integer :: x, y
  end type pt
  type rec
    real(8) :: w
    integer :: n = 5
    character(len=3) :: tag = 'abc'
    integer :: c(2) = 0
    type(pt) :: p
  end type rec
end module geo
program sconst
  use geo
  implicit none
  type(pt) :: p, ps(3)
  type(rec) :: r, rs(2)
  integer :: i
  p = pt(3, -4)
  print *, p%x, p%y
  p = pt(y=7, x=2)
  print *, p%x, p%y
  r = rec(1, p=pt(1, 2))
  print *, r%w, r%n, r%tag, r%c(1), r%c(2), r%p%x, r%p%y
  r = rec(2.5d0, 9, 'xy', [4, 5], p)
  print *, r%w, r%n, r%tag // '|', r%c(1) + r%c(2), r%p%y
  do i = 1, 3
    ps(i) = pt(i, i * i)
  end do
  ps(2)%y = ps(2)%y + 100
  print *, ps(1)%x, ps(2)%y, ps(3)%x + ps(3)%y, size(ps)
  rs(1) = r
  rs(2)%w = 0.5d0
  rs(2)%p = ps(3)
  rs(2)%c(2) = rs(1)%n
  print *, rs(1)%tag, rs(2)%n, rs(2)%c(2), rs(2)%p%y, rs(2)%w + rs(1)%w
  ps = pt(0, 1)
  p = ps(2)
  print *, p%x, p%y, ps(3)%y
end program sconst
