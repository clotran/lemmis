! BLOCK construct (R1107, R1108, R1109, R1110): declarations of its own,
! elaborated each time the block runs, hiding the outer names
program blocks
  implicit none
  integer :: i, x, s
  x = 1
  s = 0
  block
    integer :: x                      ! hides the outer x
    real :: h(3)
    x = 40
    h = [1.5, 2.5, 3.5]
    print *, x + 2, sum(h)
  end block
  print *, x
  do i = 1, 4
    block
      integer, parameter :: k = 10
      integer :: t
      t = k * i
      if (i == 3) exit
      s = s + t
    end block
  end do
  print *, i, s
  block
    print *, 'no declarations'
    block
      character(len=5) :: w
      w = 'inner'
      print *, w, x
    end block
  endblock
end program blocks
