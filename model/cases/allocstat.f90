! allocstat: ALLOCATE and DEALLOCATE with STAT=, ERRMSG=, SOURCE= and MOLD= (9.7.1, 9.7.3, 9.7.4):
! STAT= is zero after a successful statement (a failure's nonzero value is the processor's);
! SOURCE= gives each allocated object the source's value, MOLD= only its type
program allocstat
  implicit none
  integer, allocatable :: a(:), b(:,:)
  real(8), allocatable :: r(:)
  integer :: ist, k
  character(len=20) :: msg
  ist = 7
  msg = 'unchanged'
  allocate (a(3), b(2, 0:1), stat=ist, errmsg=msg)
  print *, ist, trim(msg), size(a), size(b), lbound(b, 2)
  a = [1, 2, 3]
  b = 4
  deallocate (a, stat=ist)
  print *, ist, allocated(a), allocated(b)
  ist = 9
  allocate (a(2:4), source=5)
  print *, a, lbound(a, 1)
  allocate (r(2), source=[1.5d0, 2.5d0], stat=ist)
  print *, ist, r
  deallocate (r)
  allocate (r(3), mold=1.0d0)
  r = 0.5d0
  print *, sum(r)
  k = 1
  deallocate (a, b, r, errmsg=msg, stat=ist)
  print *, ist, trim(msg), allocated(a), allocated(b), allocated(r), k
end program
