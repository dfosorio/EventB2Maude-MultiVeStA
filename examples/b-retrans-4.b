# Bounded re-transmission protocol (Chapter 6, Abrial's book)
# 4th refinement of the model  #
# The content of the file is irrelevant. Hence, D always take the value D2
CONTEXT ctxBRTP
SETS 
    STATE : {working, success, failure }
    DATA  : { D1 , D2 } 
CONSTANTS 
    N : Nat := 100 # Size of the file #
END


MACHINE BRTP
  SEES ctxBRTP

  VARIABLES
    fileR # File at the receiver #
    counterR # Counter for R #
    counterS # Counter for S #
    stateR   # R's State #
    stateS   # S's State #
    W        # Activation bit when true the sender is enabled #
    D

  INVARIANTS
    fileR :  POW ( Nat ** STATE )
    counterR : Nat 
    counterS : Nat 
    stateR   : STATE 
    stateS   : STATE 
    W        : Bool
    D        : DATA

  INITIALISATION

    fileR    := emptyrel
    counterR := 0
    counterS := 0
    stateR   := working 
    stateS   := working 
    W        := True
    D        := D1

  
  EVENT SND-snd-data
  WEIGHT 1
  WHERE 
    W = True /\
    stateS = working
  THEN
    D := D2
    W := False
  END

  EVENT RCV-current-data
  WEIGHT 1
  WHERE 
    stateR = working /\
    W = False /\
    counterR = counterS  /\
   (counterR + 1) < N 
  THEN
    counterR    := counterR + 1
    fileR := fileR <+ { counterR  |-> D }
  END

  EVENT RCV-success
  WEIGHT 1
  WHERE 
    stateR = working /\
    W = False /\
    N = (counterR + 1) /\
    counterR = counterS
  THEN
    stateR := success 
    fileR := fileR <+ { counterR  |-> D }
    counterR    := counterR + 1
  END

  EVENT SND-rcv-current-ack
  WEIGHT 1
  WHERE
    stateS = working /\
    W = False /\
    (counterS + 1) < N /\
    counterR  = (counterS + 1)
  THEN
    W := True 
    counterS := counterS + 1
  END

  EVENT SND-success
  WEIGHT 1
  WHERE
    stateS = working /\
    W = False /\
    (counterS + 1) = N /\
    counterR  = (counterS + 1)
  THEN
    stateS := success
  END

  EVENT SND-time-out
  WEIGHT 1 
  WHERE 
   stateS = working /\ 
   W = False  
  THEN 
    W := True 
  END 
END

PROPERTIES
 stateS = success /\ stateR = success ; # both agents end in success
 stateS = failure /\ stateR = failure   # both fail 
