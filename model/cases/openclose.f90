! openclose: OPEN (R1204) of a scratch file and CLOSE (R1208), connecting and
! disconnecting units (12.5.6, 12.5.7); CLOSE of a unit that is not connected has
! no effect; a closed unit can be opened again; the spellings are case blind
program oc
  integer :: u
  u = 10
  open (unit=u, status='scratch')
  open (11, STATUS='Scratch  ', access='sequential', form='formatted')
  close (u)
  close (unit=11, status='delete')
  close (12)
  open (unit=10, status='scratch', form='FORMATTED')
  close (10, status='DELETE')
  print *, 'ok', u
end program
