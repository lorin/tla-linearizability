-------------------------- MODULE Linearizability --------------------------

EXTENDS Sequences

Extensions(H) == {} \* TODO

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
    \E Hp \in Extensions(H) : 
        /\ \E f \in Orderings(Len(Hp)) :
            LET S == Hp ** f
            IN /\ IsLegalSequentialHistory(S)
               /\ RespectsPrecedenceOrdering(H, S)
                
        

=============================================================================
\* Modification History
\* Last modified Sat Oct 20 13:38:18 PDT 2018 by lhochstein
\* Created Sat Oct 20 09:56:44 PDT 2018 by lhochstein
