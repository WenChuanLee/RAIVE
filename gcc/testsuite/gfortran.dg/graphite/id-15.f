      SUBROUTINE ORDORB(IORBTP)
      LOGICAL MASWRK
      DIMENSION IORBTP(12,12)
      DIMENSION NSYMTP(12,8)
      IF (MASWRK) WRITE(IW) K,NORB
      DO 420 I = 1,NTPS
         DO 400 J = 1,8
            NSYMTP(I,J) = 0
  400    CONTINUE
         DO 410 J=1,NORB
            IORBTP(I,J) = 0
  410    CONTINUE
  420 CONTINUE
      CALL RDRSYM(ICODE,NSYMTP,NSYM)
 9055 FORMAT(I5)
      END
