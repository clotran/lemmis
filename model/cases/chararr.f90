! character arrays: element assignment padding and truncating, an
! elemental concatenation and relation, a constructor of one length
program chararr
  implicit none
  character(len=3) :: w(3)
  character(len=2), parameter :: p(2) = ['ab', 'cd']
  integer :: i
  w(1) = 'one'
  w(2) = 'tw'
  w(3) = 'three'
  do i = 1, 3
    print *, w(i) // '|', len(w(i))
  end do
  print *, w(1) < w(2), w // '!'
  print *, w == 'tw', p, p(2) // w(3)
  w = 'z'
  print *, w // '|'
end program chararr
