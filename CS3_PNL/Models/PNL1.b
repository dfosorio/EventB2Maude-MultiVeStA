# PNL #
CONTEXT ctxPNL
SETS 
    AGENTS : { a, b, c } # nodes of the graph #
CONSTANTS 
END

MACHINE PNL
  SEES ctxPNL

  VARIABLES
    AgentsComb # set of all possible edges #
    Rpositive # relation that represents positive edges in graph #
    Rnegative # relation that represents negative edges in graph # 

  INVARIANTS
    Rpositive :  POW ( AGENTS ** AGENTS )
    Rnegative :  POW ( AGENTS ** AGENTS )
    AgentsComb :  POW ( AGENTS ** AGENTS ) 

  INITIALISATION
    AgentsComb := { a |-> b, a |-> c, 
                    b |-> c }
    Rpositive := emptyrel # intial configuration of the graph's positive edges #
    Rnegative := emptyrel # intial configuration of the graph's negative edges #

  
  EVENT addPositiveEdge 
  WEIGHT 1
  ANY 
    edge <: (AgentsComb \ Rpositive) \ Rnegative
  WHERE
    True 
  THEN
    Rpositive := Rpositive \s/ edge
  END

  EVENT addNegativeEdge 
  WEIGHT 1
  ANY 
    edge <: (AgentsComb \ Rpositive) \ Rnegative
  WHERE
    True 
  THEN
    Rnegative := Rnegative \s/ edge
  END


END
