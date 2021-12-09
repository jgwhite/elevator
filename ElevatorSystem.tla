---- MODULE ElevatorSystem ----

EXTENDS Sequences, Naturals, FiniteSets

----

VARIABLES externalRequests, internalRequests, elevatorState, elevatorFloor

vars == <<externalRequests, internalRequests, elevatorState, elevatorFloor>>

----

Elevator      == {"1"}
ElevatorState == {"IDLE", "ASCENDING", "DESCENDING"}
Direction     == {"UP", "DOWN"}
Floor         == 1..2

----

TypeOK ==
  /\ externalRequests \in SUBSET (Floor \X Direction)
  /\ internalRequests \in [ Elevator -> SUBSET Floor ]
  /\ elevatorState    \in [ Elevator -> ElevatorState ]
  /\ elevatorFloor    \in [ Elevator -> Floor ]

----

Min(s) == CHOOSE v \in s : \A w \in s : v <= w
Max(s) == CHOOSE v \in s : \A w \in s : v >= w

----

Init ==
  /\ externalRequests = {}
  /\ internalRequests = [ e \in Elevator |-> {} ]
  /\ elevatorState    = [ e \in Elevator |-> "IDLE" ]
  /\ elevatorFloor    = [ e \in Elevator |-> 1 ]

----

Summon ==
  \E f \in Floor, d \in Direction :
    /\ f = Max(Floor) => d = "DOWN"
    /\ f = Min(Floor) => d = "UP"
    /\ externalRequests' = externalRequests \union {<<f, d>>}
    /\ UNCHANGED <<internalRequests, elevatorState, elevatorFloor>>

Accept ==
  \E e \in Elevator, r \in externalRequests :
    /\ \/ elevatorState[e] = "IDLE"
       \/ elevatorState[e] = "ASCENDING" /\ r[2] = "UP" /\ elevatorFloor[e] <= r[1]
       \/ elevatorState[e] = "DESCENDING" /\ r[2] = "DOWN" /\ elevatorFloor[e] >= r[1]
    /\ externalRequests' = externalRequests \ {r}
    /\ internalRequests' = [internalRequests EXCEPT ![e] = @ \union {r[1]}]
    /\ UNCHANGED <<elevatorState, elevatorFloor>>

Ascend ==
  \E e \in Elevator :
    \E r \in internalRequests[e] :
      /\ elevatorState[e] \in {"IDLE", "ASCENDING"}
      /\ elevatorFloor[e] < r
      /\ elevatorState' = [elevatorState EXCEPT ![e] = "ASCENDING"]
      /\ elevatorFloor' = [elevatorFloor EXCEPT ![e] = @ + 1]
      /\ UNCHANGED <<internalRequests, externalRequests>>

Descend ==
  \E e \in Elevator :
    \E r \in internalRequests[e] :
      /\ elevatorState[e] \in {"IDLE", "DESCENDING"}
      /\ elevatorFloor[e] > r
      /\ elevatorState' = [elevatorState EXCEPT ![e] = "DESCENDING"]
      /\ elevatorFloor' = [elevatorFloor EXCEPT ![e] = @ - 1]
      /\ UNCHANGED <<internalRequests, externalRequests>>

Deposit ==
  \E e \in Elevator :
    \E r \in internalRequests[e] :
      /\ elevatorFloor[e] = r
      /\ internalRequests' = [internalRequests EXCEPT ![e] = @ \ {r}]
      /\ UNCHANGED <<externalRequests, elevatorFloor, elevatorState>>

Request ==
  \E e \in Elevator, f \in Floor :
    /\ internalRequests' = [internalRequests EXCEPT ![e] = @ \union {f}]
    /\ UNCHANGED <<externalRequests, elevatorFloor, elevatorState>>

Stop ==
  \E e \in Elevator :
    /\ internalRequests[e] = {}
    /\ elevatorState' = [elevatorState EXCEPT ![e] = "IDLE"]
    /\ UNCHANGED <<externalRequests, internalRequests, elevatorFloor>>

----

Next ==
  \/ Summon
  \/ Accept
  \/ Ascend
  \/ Descend
  \/ Deposit
  \/ Request
  \/ Stop

Spec == Init /\ [][Next]_vars

----

Constraint ==
  /\ Cardinality(externalRequests) < 2
  /\ \A e \in Elevator : Cardinality(internalRequests[e]) < 2

====