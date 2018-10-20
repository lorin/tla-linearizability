-------------------------- MODULE Linearizability --------------------------

EXTENDS Sequences

CONSTANT PossibleResponses(_)

Collect(S) == {} \* TODO 

InvocationsWithoutResponses(H) == {} \* TODO

\* Return a set with all of the possible sequences that could
\* by appended to H to extend it by completing operations
Extensions(H) == 
    LET R == { PossibleResponses(inv) : inv \in InvocationsWithoutResponses(H)}
    IN {} \* TODO

ExtendedHistories(H) == {H} \union {H \o ext: ext \in Extensions(H)}

\* Returns a set of functions on 1..N->1..N that represent permutations
\* for reordering a sequence of events
Orderings(N) == {} \* TODO

IsLegalSequentialHistory(S) == FALSE \* TODO

RespectsPrecedenceOrdering(H, S) == FALSE \* TODO

\* Composition
f ** g == [x \in DOMAIN(g) |-> f[g[x]]]


(***************************************************************************

Herlihy & Wing 1990, p469:

A history H is linearizable if it can be extended (by appending zero or more
response events) to some history H’ such that:

Ll: complete(H’) is equivalent to some legal sequential history S, and
L2: <_H ⊆ <_S
***************************************************************************)

IsLinearizableHistory(H) == 
    \E Hp \in ExtendedHistories(H) : 
        /\ \E f \in Orderings(Len(Hp)) :
            LET S == Hp ** f
            IN /\ IsLegalSequentialHistory(S)
               /\ RespectsPrecedenceOrdering(H, S)
                
        

=============================================================================
\* Modification History
\* Last modified Sat Oct 20 13:38:18 PDT 2018 by lhochstein
\* Created Sat Oct 20 09:56:44 PDT 2018 by lhochstein
