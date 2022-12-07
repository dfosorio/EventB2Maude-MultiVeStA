# Emergency Brake system #
CONTEXT ctxBrakeSystem
SETS 
    SPEDAL : { up, down }
    SBRAKE : { applied, released } 
CONSTANTS 
    MAXWEAR : Nat := 10
END

MACHINE BrakeSystem
  SEES ctxBrakeSystem

  VARIABLES

    pedal 
    brake 
    wear 

  INVARIANTS

    pedal : SPEDAL
    brake : SBRAKE
    wear  : Nat 

  INITIALISATION

    pedal := up
    brake := released
    wear  := 0


  EVENT PushPedal
  WEIGHT MAXWEAR
  WHERE 
    pedal = up
  THEN
    pedal := {down @ 0.9 , up @ 0.1 }
  END

  EVENT ReleasePedal
  WEIGHT MAXWEAR
  WHERE 
    pedal = down
  THEN
    pedal := up
  END

  EVENT ApplyBrake
  WEIGHT MAXWEAR - wear
  WHERE
    pedal = down /\ brake = released
  THEN
    brake := applied
    wear  := wear + 1
  END

  EVENT ApplyBrakeFailure
  WEIGHT wear
  WHERE
    pedal = down /\ brake = released
  THEN
    brake := released 
  END

  EVENT ReleaseBrake
  WEIGHT MAXWEAR - wear
  WHERE
    pedal = up /\ brake = applied
  THEN
    brake := released 
  END
END

PROPERTIES
 brake = applied ;
 wear
