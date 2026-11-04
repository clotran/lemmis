! a character dummy shorter than its actual (15.5.2.4p2): it is the
! actual's leftmost characters, and what it defines is defined there
program chardummy
  implicit none
  character(len=8) :: s
  character(3) :: t(2)
  s = 'abcdefgh'
  call show(s)
  call upd(s)
  print *, s
  t(1) = 'xyz'
  t(2) = 'pqr'
  call upd(t(2))
  print *, t
contains
  subroutine show(c)
    character(len=3), intent(in) :: c
    print *, c, len(c)
  end subroutine show
  subroutine upd(c)
    character(len=2), intent(inout) :: c
    print *, c
    c = 'XY'
  end subroutine upd
end program chardummy
