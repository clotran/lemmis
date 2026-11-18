C     NOPROG: A MAIN PROGRAM WITH NO PROGRAM STATEMENT (F77 3.5, 14.1),
C     FIRST AND AFTER THE OTHER UNITS
      INTEGER I, F
      I = 2
      CALL S(I)
      PRINT *, I, F(I)
      END
      SUBROUTINE S(K)
      INTEGER K
      K = K * 3
      END
      INTEGER FUNCTION F(K)
      INTEGER K
      F = K + 1
      END
