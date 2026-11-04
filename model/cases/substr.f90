! substrings (9.4.1, R908-R910): of a scalar, of an array element, of a
! named constant; the bounds omitted; zero length; assignment to a
! substring (10.2.1.3p10: fit to its length) and a string built one
! character at a time; CHARACTER*(n), CHARACTER*(*), the comma after
! CHARACTER*n (R722, C725), DOUBLEPRECISION written as one word
program substr
  implicit none
  character(len=10) :: s
  character*(6) :: t
  character*4, u
  character(3) :: w(3)
  character(len=*), parameter :: abc = 'abcdefgh'
  doubleprecision :: x
  integer :: i, n
  s = 'hello world'
  print *, s(1:5), '|', s(7:), '|', s(:4), '|', s(:), '|'
  print *, len(s(2:4)), len(s(5:4)), s(3:3) // s(3:3)
  print *, abc(2:3), abc(len(abc):), len(abc(4:3))
  s(1:1) = 'J'
  s(7:10) = 'WORLD!!'
  print *, s
  t = s(1:6)
  t(2:3) = 'x'
  print *, t // '|'
  u = 'four'
  print *, u, len(u)
  w(1) = 'abc'
  w(2) = 'def'
  w(3) = 'ghi'
  w(2)(2:2) = 'Z'
  print *, w(2)(1:2), w(3)(3:), w
  n = 5
  do i = 1, n
    s(i:i) = abc(n - i + 1:n - i + 1)
  end do
  print *, s(1:n)
  print *, s(2:3) == 'dc', s(1:2) < s(2:3)
  x = 1.5d0
  print *, x
  call show(s(1:3))
contains
  subroutine show(v)
    character*(*), intent(in) :: v
    print *, v, len(v)
  end subroutine show
end program substr
