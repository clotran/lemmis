! select: SELECT CASE on integers and logicals -- single values, the
! three range forms, a list, DEFAULT anywhere, and no match at all
program selects
  use iso_fortran_env, only: int64
  implicit none
  integer(int64) :: n
  integer :: k
  logical :: b
  do n = -3_int64, 12_int64, 3_int64
    select case (n)
    case (1_int64)
      print *, n, "one"
    case default
      print *, n, "other"
    case (:-1_int64)
      print *, n, "negative"
    case (6_int64:9_int64, 11_int64)
      print *, n, "six to nine, or eleven"
    case (12_int64:)
      print *, n, "twelve on"
    end select
  end do
  do k = 1, 3
    select case (k)
    case (2)
      print *, k, "two"
    end select
  end do
  b = .false.
  select case (b)
  case (.true.)
    print *, "yes"
  case (.false.)
    print *, "no"
  end select
end program selects
