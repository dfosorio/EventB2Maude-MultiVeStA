# P2P Protocol model in Aouadhi, M.A., Delahaye, B., Lanoix, A.: Introducing
# probabilistic reasoning within Event-B. Softw. Syst. Model. 18(3)
# (2019)
# Here the file is a function 0.. N*K-1 -> {emp, ok, download}. Consistently, 
# i -> S represents that the block i/N of the client i mod N is currently in
# state S

CONTEXT ctxP2P
SETS 
    STATE : { emp, ok, sending }
CONSTANTS 
    N : Nat := 5 # Number of clients #
    K : Nat := 10 # Number of blocks #
END

MACHINE P2P
  SEES ctxP2P
  VARIABLES
    file
    n
    done

  INVARIANTS
    file :  POW ( Nat ** STATE )
    n    : Nat 
    done : Bool

  INITIALISATION
    file    := {0 .. (N * K - 1) } ** { emp }
    n       := 0
    done    := False

  # Sending a block (not sent yet) to a client which is not currently receiving a block #
  EVENT sent
  WEIGHT N * K  - card(file |> {sending})
  ANY
   block <: { x . dom(file |> {emp}) || ((x mod N) /: { y . dom(file |> {sending}) | y mod N  })  }
  WHERE 
    True
  THEN
    file := file <+ { block |-> sending }
    n    := n + 1

  END

  # Receiving one block #
  EVENT receive
  WEIGHT 1 + card( file |> {ok})
  ANY
    block <: dom(file |> { sending })
  WHERE 
    True
  THEN
    file := file <+ { block |-> ok }
  END

  # Failing: from sending to emp #
  EVENT fail
  WEIGHT N * K - card( file |> {ok})
  ANY
    block <: dom(file |> { sending })
  WHERE
    True
  THEN
    file := { file @ 0.6 , (file <+ { block |-> emp }) @ 0.4 }
  END

  # Executed when all the blocks have been copied #
  EVENT finish
  WEIGHT 1
  WHERE
    (done = False) /\ (card( file |> {ok}) = N * K)
  THEN
    done := True 
  END
END

PROPERTIES
 n
