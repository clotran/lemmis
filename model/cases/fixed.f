C     FIXED FORM: LABELS, GO TO, LABEL DO, FORMAT
      PROGRAM FIXED
      IMPLICIT NONE
      INTEGER :: I, N, S
      REAL :: X
      S = 0
      N = 1
   10 CONTINUE
      S = S + N
      N = N + 1
      IF (N .LE. 5) GO TO 10
      WRITE (*, 100) S, N
  100 FORMAT (' SUM ', I4, ' NEXT', I3)
      DO 20 I = 1, 3
         WRITE (*, 110) I, I * I
   20 CONTINUE
  110 FORMAT (I2, 2X, I5.3)
      X = 2.5
      WRITE (*, 120) X, -X
  120 FORMAT (F8.3, 1X, F6.1)
      WRITE (*, 130) 1, 2, 3, 4
  130 FORMAT (2(I3, '|'))
      N = -2
      IF (N .LT. 0) GO TO 40
      IF (N .EQ. 0) GO TO 50
      GO TO 60
   40 WRITE (*, 140) 'NEG'
      GOTO 70
   50 WRITE (*, 140) 'ZERO'
      GO TO 70
   60 WRITE (*, 140) 'POS'
  140 FORMAT (A)
   70 PRINT *, 'DONE',
     &  N
      END
