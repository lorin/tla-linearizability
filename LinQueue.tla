----------------------------- MODULE LinQueue -------------------------------

EXTENDS Naturals, Sequences

opInvocations == {"E", "D"}
opResponse == "Ok"

values == {"x", "y"} 

Processes == {"A", "B"}

\* Process subhistory
H|P == SelectSeq(H, LAMBDA e : e.proc = P)

PossibleResponses(e) ==
    CASE e.op = "E" -> {[op|->"Ok", proc|->e.proc]}
      [] e.op = "D" -> [op:{"Ok"}, proc:{e.proc}, val:values]

IsLegalSequentialHistory(H) == FALSE \* TODO, this will be defined elsewhere

IsInvocation(e) == e.op \in opInvocations

Matches(H, i, j) ==
    /\ H[i].proc = H[j].proc
    /\ H[i].op \in opInvocations
    /\ H[j].op = opResponse
    /\ ~\E k \in (i+1)..(j-1) : H[k].proc = H[i].proc

=============================================================================
