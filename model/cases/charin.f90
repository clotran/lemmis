! character input (12.6.4.5): list-directed, delimited and not
! (13.10.3.1), r*c, padding and truncating to the item's length; A
! editing (13.7.4: w, no w); a character array; SELECT CASE on a
! character expression (11.1.9: case values and ranges)
program charin
  implicit none
  character(len=5) :: a, b
  character(3) :: c(3)
  character(len=8) :: d
  character :: g
  integer :: n, i
  read *, a, n, b
  print *, a, '|', n, '|', b, '|'
  read *, c
  print *, c
  read (*, '(a, a3, a8)') d, a, b
  print *, d, '|', a, '|', b, '|'
  read *, a, b
  print *, a, '|', b, '|'
  do i = 1, 5
    read (*, '(a)') g
    select case (g)
    case ('a', 'e', 'i', 'o', 'u')
      print *, g, ' vowel'
    case ('0':'9')
      print *, g, ' digit'
    case ('A':'Z')
      print *, g, ' upper'
    case default
      print *, g, ' consonant'
    end select
  end do
  select case (trim(d))
  case ('abc')
    print *, 'abc'
  case ('abcdefgh')
    print *, 'whole'
  case default
    print *, 'other'
  end select
end program charin
