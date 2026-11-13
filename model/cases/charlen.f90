! charlen: R803's entity-decl * char-length (7.4.4.2): an entity's own
! length overriding its type's, after an array-spec too, beside
! CHARACTER * char-length and an initialization
program charlen
  character a*3, b*5, c(2)*4
  character*6 d, e*2
  character(len=4) :: f*7 = 'abcdefg', g
  a = 'abcdef'
  b = 'xy'
  c(1) = 'pqrstu'
  c(2) = 'z'
  d = 'longer string'
  e = 'mn'
  g = 'hijklm'
  print *, a, '|', b, '|', c(1), c(2), '|', d, '|', e, '|', f, '|', g
  print *, len(a), len(b), len(c(1)), len(d), len(e), len(f), len(g)
end program charlen
