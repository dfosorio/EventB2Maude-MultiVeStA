# Dice Program 1#
CONTEXT ctxDiceProgram1
SETS 
    STATES : { s0, s1, s2, s3, s4, s5, s6, s7 }
CONSTANTS 
END

MACHINE DiceProgram1
  SEES ctxDiceProgram1

  VARIABLES

    st 
    dice 

  INVARIANTS

    st : STATES
    dice : Nat 

  INITIALISATION

    st := s0
    dice := 0

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
    st := s1
  END

  EVENT State3Trans2 
  WEIGHT 1
  WHERE 
    st = s3
  THEN
    st := s7
    dice := 1
  END

  EVENT State4Trans 
  WEIGHT 1
  WHERE 
    st = s4
  THEN
    st := s7
    dice := {2 @ 0.5 , 3 @ 0.5 }
  END

  EVENT State5Trans 
  WEIGHT 1
  WHERE 
    st = s5
  THEN
    st := s7
    dice := {4 @ 0.5 , 5 @ 0.5 }
  END

  EVENT State6Trans1 
  WEIGHT 1
  WHERE 
    st = s6
  THEN
    st := s2
  END

  EVENT State6Trans2 
  WEIGHT 1
  WHERE 
    st = s6
  THEN
    st := s7
    dice := 6
  END

END

PROPERTIES
 dice = 1 ;
 dice = 2 ;
 dice = 3 ;
 dice = 4 ;
 dice = 5 ;
 dice = 6
