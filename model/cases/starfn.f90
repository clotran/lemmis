! starfn: a CHARACTER*(*) function (F77 8.4.1) takes the length its caller
! declares, whether the header or a type statement in the function says (*)
program starfn
  character(len=4) :: cg
  character(len=2) :: ch
  character(len=6) :: s
  external cg, ch
  s = 'abcdef'
  print *, '[', cg(s), ']', len(cg(s))
  print *, '[', ch(s), ']'
end program starfn
character(len=*) function cg(s)
  character(len=*) :: s
  cg = s(2:3)
end function cg
function ch(s)
  character(len=*) :: ch
  character(len=*) :: s
  ch = s(4:6)
end function ch
