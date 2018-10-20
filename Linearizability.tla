-------------------------- MODULE Linearizability --------------------------

EXTENDS Naturals, Sequences

CONSTANT PossibleResponses(_) \* Argument is a history
CONSTANT IsInvocation(_) \* Argument is event
CONSTANT Matches(_, _, _) \* Arguments are sequence, index, index

\* Transpose a set of sets
\* Collect({{"a","b"}, {"x","y"}}) => {{"x", "a"}, {"x", "b"}, {"a", "y"}, {"b", "y"}} 
RECURSIVE Collect(_)

Collect(S) == 
    IF S = {} THEN {{}} ELSE
    LET s == CHOOSE s \in S : TRUE
        R == Collect(S \ {s})
        er == {<<e,r>> \in s \X R : TRUE }
    IN {{e} \union r : <<e,r>> \in er }

\* Given a history, return the invocations that don't have an associated response
InvocationsWithoutResponses(H) ==
    LET N == Len(H)
        inds == {i \in 1..N : IsInvocation(H[i]) /\ ~\E j \in i+1..N : Matches(H,i,j) }
    IN {H[i] : i \in inds }

\* Return a set with all of the possible sets of events that could
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
