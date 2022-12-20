# Dice Program 2#
CONTEXT ctxDiceProgram2
SETS 
    STATES : { s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34 }
CONSTANTS 
END

MACHINE DiceProgram2
  SEES ctxDiceProgram2

  VARIABLES

    st 
    diceSum 

  INVARIANTS

    st : STATES
    diceSum : Nat 

  INITIALISATION

    st := s0
    diceSum := 0

  EVENT State0Trans 
  WEIGHT 1
  WHERE 
    st = s0
  THEN
    st := {s1 @ 0.5 , s2 @ 0.5 }
  END

  EVENT State1Trans 
  WEIGHT 1
  WHERE 
    st = s1
  THEN
    st := {s3 @ 0.5 , s4 @ 0.5 }
  END

  EVENT State2Trans 
  WEIGHT 1
  WHERE 
    st = s2
  THEN
    st := {s5 @ 0.5 , s6 @ 0.5 }
  END

  EVENT State3Trans1
  WEIGHT 1
  WHERE 
    st = s3
  THEN
    st := s7
  END

  EVENT State3Trans2
  WEIGHT 1
  WHERE 
    st = s3
  THEN
    st := s34
    diceSum := 6
  END

  EVENT State4Trans1
  WEIGHT 1
  WHERE 
    st = s4
  THEN
    st := s8
  END

  EVENT State4Trans2
  WEIGHT 1
  WHERE 
    st = s4
  THEN
    st := s34
    diceSum := 7
  END

  EVENT State5Trans1
  WEIGHT 1
  WHERE 
    st = s5
  THEN
    st := s9
  END

  EVENT State5Trans2
  WEIGHT 1
  WHERE 
    st = s5
  THEN
    st := s34
    diceSum := 8
  END

  EVENT State6Trans 
  WEIGHT 1
  WHERE 
    st = s6
  THEN
    st := {s10 @ 0.5 , s11 @ 0.5 }
  END

  EVENT State7Trans1
  WEIGHT 1
  WHERE 
    st = s7
  THEN
    st := s12
  END

  EVENT State7Trans2
  WEIGHT 1
  WHERE 
    st = s7
  THEN
    st := s34
    diceSum := 4
  END

  EVENT State8Trans1
  WEIGHT 1
  WHERE 
    st = s8
  THEN
    st := s13
  END

  EVENT State8Trans2
  WEIGHT 1
  WHERE 
    st = s8
  THEN
    st := s34
    diceSum := 5
  END

  EVENT State9Trans1
  WEIGHT 1
  WHERE 
    st = s9
  THEN
    st := s14
  END

  EVENT State9Trans2
  WEIGHT 1
  WHERE 
    st = s9
  THEN
    st := s34
    diceSum := 9
  END

  EVENT State10Trans1
  WEIGHT 1
  WHERE 
    st = s10
  THEN
    st := s15
  END

  EVENT State10Trans2
  WEIGHT 1
  WHERE 
    st = s10
  THEN
    st := s34
    diceSum := 10
  END

  EVENT State11Trans 
  WEIGHT 1
  WHERE 
    st = s11
  THEN
    st := {s16 @ 0.5 , s17 @ 0.5 }
  END

  EVENT State12Trans1
  WEIGHT 1
  WHERE 
    st = s12
  THEN
    st := s18
  END

  EVENT State12Trans2
  WEIGHT 1
  WHERE 
    st = s12
  THEN
    st := s34
    diceSum := 3
  END

  EVENT State13Trans1
  WEIGHT 1
  WHERE 
    st = s13
  THEN
    st := s19
  END

  EVENT State13Trans2
  WEIGHT 1
  WHERE 
    st = s13
  THEN
    st := s34
    diceSum := 5
  END

  EVENT State14Trans1
  WEIGHT 1
  WHERE 
    st = s14
  THEN
    st := s20
  END

  EVENT State14Trans2
  WEIGHT 1
  WHERE 
    st = s14
  THEN
    st := s34
    diceSum := 7
  END

  EVENT State15Trans1
  WEIGHT 1
  WHERE 
    st = s15
  THEN
    st := s21
  END

  EVENT State15Trans2
  WEIGHT 1
  WHERE 
    st = s15
  THEN
    st := s34
    diceSum := 9
  END

  EVENT State16Trans1
  WEIGHT 1
  WHERE 
    st = s16
  THEN
    st := s22
  END

  EVENT State16Trans2
  WEIGHT 1
  WHERE 
    st = s16
  THEN
    st := s34
    diceSum := 11
  END

  EVENT State17Trans 
  WEIGHT 1
  WHERE 
    st = s17
  THEN
    st := {s23 @ 0.5 , s24 @ 0.5 }
  END

  EVENT State18Trans1
  WEIGHT 1
  WHERE 
    st = s18
  THEN
    st := s25
  END

  EVENT State18Trans2
  WEIGHT 1
  WHERE 
    st = s18
  THEN
    st := s34
    diceSum := 2
  END

  EVENT State19Trans1
  WEIGHT 1
  WHERE 
    st = s19
  THEN
    st := s26
  END

  EVENT State19Trans2
  WEIGHT 1
  WHERE 
    st = s19
  THEN
    st := s34
    diceSum := 3
  END

  EVENT State20Trans1
  WEIGHT 1
  WHERE 
    st = s20
  THEN
    st := s27
  END

  EVENT State20Trans2
  WEIGHT 1
  WHERE 
    st = s20
  THEN
    st := s34
    diceSum := 4
  END

  EVENT State21Trans 
  WEIGHT 1
  WHERE 
    st = s21
  THEN
    st := s34
    diceSum := {5 @ 0.5 , 9 @ 0.5 }
  END

  EVENT State22Trans1
  WEIGHT 1
  WHERE 
    st = s22
  THEN
    st := s28
  END

  EVENT State22Trans2
  WEIGHT 1
  WHERE 
    st = s22
  THEN
    st := s34
    diceSum := 10
  END

  EVENT State23Trans1
  WEIGHT 1
  WHERE 
    st = s23
  THEN
    st := s29
  END

  EVENT State23Trans2
  WEIGHT 1
  WHERE 
    st = s23
  THEN
    st := s34
    diceSum := 11
  END

  EVENT State24Trans1
  WEIGHT 1
  WHERE 
    st = s24
  THEN
    st := s30
  END

  EVENT State24Trans2
  WEIGHT 1
  WHERE 
    st = s24
  THEN
    st := s34
    diceSum := 12
  END

  EVENT State25Trans1
  WEIGHT 1
  WHERE 
    st = s25
  THEN
    st := s1
  END

  EVENT State25Trans2
  WEIGHT 1
  WHERE 
    st = s25
  THEN
    st := s34
    diceSum := 2
  END

  EVENT State26Trans1
  WEIGHT 1
  WHERE 
    st = s26
  THEN
    st := s31
  END

  EVENT State26Trans2
  WEIGHT 1
  WHERE 
    st = s26
  THEN
    st := s34
    diceSum := 3
  END

  EVENT State27Trans1
  WEIGHT 1
  WHERE 
    st = s27
  THEN
    st := s32
  END

  EVENT State27Trans2
  WEIGHT 1
  WHERE 
    st = s27
  THEN
    st := s34
    diceSum := 6
  END

  EVENT State28Trans 
  WEIGHT 1
  WHERE 
    st = s28
  THEN
    st := s34
    diceSum := {7 @ 0.5 , 8 @ 0.5 }
  END

  EVENT State29Trans1
  WEIGHT 1
  WHERE 
    st = s29
  THEN
    st := s33
  END

  EVENT State29Trans2
  WEIGHT 1
  WHERE 
    st = s29
  THEN
    st := s34
    diceSum := 11
  END

  EVENT State30Trans1
  WEIGHT 1
  WHERE 
    st = s30
  THEN
    st := s2
  END

  EVENT State30Trans2
  WEIGHT 1
  WHERE 
    st = s30
  THEN
    st := s34
    diceSum := 12
  END

  EVENT State31Trans 
  WEIGHT 1
  WHERE 
    st = s31
  THEN
    st := s34
    diceSum := {2 @ 0.5 , 4 @ 0.5 }
  END

  EVENT State32Trans 
  WEIGHT 1
  WHERE 
    st = s32
  THEN
    st := s34
    diceSum := {6 @ 0.5 , 8 @ 0.5 }
  END

  EVENT State33Trans 
  WEIGHT 1
  WHERE 
    st = s33
  THEN
    st := s34
    diceSum := {10 @ 0.5 , 12 @ 0.5 }
  END

END

PROPERTIES
 diceSum = 2 ;
 diceSum = 3 ;
 diceSum = 4 ;
 diceSum = 5 ;
 diceSum = 6 ;
 diceSum = 7 ;
 diceSum = 8 ;
 diceSum = 9 ;
 diceSum = 10 ;
 diceSum = 11 ;
 diceSum = 12 
