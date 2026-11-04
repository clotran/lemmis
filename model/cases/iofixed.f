C     READ, PRINT AND WRITE IN FIXED FORM
      PROGRAM IOFIX
      INTEGER I, J
      READ (5, 100) I, J
  100 FORMAT (2I4)
      PRINT 200, I + J
  200 FORMAT (' SUM =', I6)
      READ *, I
      PRINT *, I
      WRITE (6, '(1X, A, I3)') 'I =', I
      WRITE (UNIT = 6, FMT = 200) J
      END
