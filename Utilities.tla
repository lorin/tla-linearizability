----------------------------- MODULE Utilities -----------------------------
EXTENDS Naturals, Sequences, FiniteSets

\* Returns a set of functions on 1..N->1..N that represent permutations
\* for reordering a sequence of events
Orderings(N) == LET S == 1..N
                    Range(f) == { f[x] : x \in DOMAIN f }
                    Onto(f) == DOMAIN f = Range(f)
                IN {f \in [S->S] : Onto(f)}

\* Composition
f ** g == [x \in DOMAIN(g) |-> f[g[x]]]

\* Given a set, return a sequence made of its elements
RECURSIVE ToSeq(_)
ToSeq(S) == IF S = {} THEN << >>
            ELSE LET e == CHOOSE e \in S : TRUE
                     T == S \ {e}
                 IN Append(ToSeq(T), e)

\* Given a set, return a set of sequences that are permutations 
Perms(S) == LET fs == Orderings(Cardinality(S))
                s == ToSeq(S)
            IN {s**f: f \in fs}


=============================================================================
\* Modification History
\* Created Mon Oct 22 19:21:10 PDT 2018 by lhochstein
