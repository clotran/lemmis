! character (7.4.4): declared lengths (R721-R723), assignment padding and
! truncating (10.2.1.3p10), concatenation (10.1.5.3), the relations
! (10.1.5.5: the shorter padded with blanks), LEN, LEN_TRIM, TRIM, an
! assumed length (8.5.13), and the A edit descriptor (13.7.4)
program chars
  implicit none
  character(len=5) :: a
  character(3) :: b
  character*8 :: c
  character :: d
  character(len=*), parameter :: hello = 'hello'
  character(len=2+2) :: e
  integer :: n
  a = 'ab'
  b = 'xyzw'
  c = a // b
  d = 'q'
  e = "it's"
  print *, a // '|'
  print *, b, len(b)
  print *, c // '|', len(c), len(d), len(e), e
  print *, len(a // b), len_trim(a), len(trim(a)), len_trim('   ')
  print *, trim(a) // b // trim('  ') // d
  print *, a == 'ab', 'ab' == 'ab   ', 'abc' < 'abd', 'b' > 'abc', a /= b
  print *, 'abc' .lt. 'abcd', 'abc ' .le. 'abc', d >= 'q', 'a' // 'b' == 'ab'
  print *, hello, len(hello)
  print *, 'x', b, 'y', 1, a, d
  n = 3
  call show(hello // ' world', n)
  call show(b, len(a))
  write (*, '(a)') a // '|'
  write (*, '(a3, "|", a8, "|", a, "|", a)') hello, b, d, c
  if (a // 'x' < b) then
    print *, 'less'
  else
    print *, 'not less'
  end if
contains
  subroutine show(s, k)
    character(len=*), intent(in) :: s
    integer, intent(in) :: k
    print *, s, len(s), k
  end subroutine show
end program chars
