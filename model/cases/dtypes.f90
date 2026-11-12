! derived types (7.5): a type's definition among the declarations (R726,
! R727 TYPE [::] name, R737 components, END TYPE [name]); TYPE(t)
! declarations (R703, R754); default initialization (7.5.4.6); a
! component of a derived type; R911 data-refs read (R913), with
! subscripts on an array component and a section of one; R1033 with a
! structure component the variable; a whole structure assigned; a type
! of the host's (host association) and one local to a procedure
module shapes
  implicit none
  type point
    integer :: x, y
  end type point
  type :: box
    type(point) :: lo, hi
    real(8) :: w(3)
    integer :: n = 7
    character(len=4) :: tag = 'none'
  end type
end module shapes
program dtypes
  use shapes
  implicit none
  type(point) :: p, q
  type(box) :: b
  integer :: i
  p%x = 3
  p%y = -4
  q = p
  q%y = q%y * 2
  print *, p%x, p%y, q%x, q%y
  print *, b%n, b%tag, len(b%tag)
  b%lo = p
  b%hi%x = 10
  b%hi%y = b%lo%y + 1
  do i = 1, 3
    b%w(i) = i * 0.5d0
  end do
  print *, b%lo%x, b%hi%x, b%hi%y
  print *, b%w(2), b%w(1) + b%w(3), sum(b%w(2:3))
  b%tag = 'ab'
  b%n = b%n + size(b%w)
  print *, b%tag // '|', b%n
  call show(5)
contains
  subroutine show(k)
    integer, intent(in) :: k
    type(point) :: r
    type pair
      type(point) :: a
      integer :: c(2) = 0
    end type pair
    type(pair) :: z
    r%x = k
    r%y = p%x
    z%a = r
    z%c(2) = z%a%x * 3
    print *, r%x + r%y, z%c(1), z%c(2), z%a%y
  end subroutine show
end program dtypes
