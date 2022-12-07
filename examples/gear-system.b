# Gear system modeled in Aouadhi, M.A., Delahaye, B., Lanoix, A.: A Fully
# Probabilistic Extension of Event-B. Research report, LINA-University of
# Nantes (Jan 2016).

CONTEXT ctxGearSystem
SETS 
    SUD : { up, down }
    SER : { extended, retracted } 
    SOC : { open , closed } 
CONSTANTS 
    FCMD : Nat := 9
END

MACHINE GearSystem
  SEES ctxGearSystem

  VARIABLES
    handle gear door cmd

  INVARIANTS

    handle : SUD
    gear : SER
    door : SOC
    cmd  : Nat 

  INITIALISATION

    handle := up
    door   := closed
    gear   := retracted
    cmd    := 0


  # Interface with the pilot#
  EVENT pcmd
  WEIGHT FCMD - cmd
  ANY
    cc <: {up, down}
  WHERE 
    cmd <= FCMD
  THEN
    handle := cc
    cmd    := cmd + 1
  END

  EVENT extend
  WEIGHT FCMD + cmd
  WHERE
    handle = down /\ door = open /\ gear = retracted
  THEN
    gear := {extended @ 0.9 , retracted @ 0.1 }
    cmd  := 0
  END

  EVENT retract
  WEIGHT FCMD + cmd
  WHERE
    handle = up /\ door = open /\ gear = extended
  THEN
    gear := {extended @ 0.1 , retracted @ 0.9 }
    cmd  := 0
  END

  EVENT open
  WEIGHT FCMD + cmd
  WHERE
     door = closed /\
        ( (handle = down /\ gear = retracted) \/ (handle = up /\ gear = extended) ) 
  THEN
    door := {open @ 0.9 , closed @ 0.1 }
    cmd := 0
  END

  EVENT close
  WEIGHT FCMD + cmd
  WHERE
     door = open /\
        ( (handle = down /\ gear = extended) \/ (handle = up /\ gear = retracted) ) 
  THEN
    door := {open @ 0.1 , closed @ 0.9 }
    cmd := 0
  END
END

PROPERTIES
 door = open ;
 gear = extended ;
 cmd
