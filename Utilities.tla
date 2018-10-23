----------------------------- MODULE Utilities -----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Composition
f ** g == [x \in DOMAIN(g) |-> f[g[x]]]

\* Given a set, return a sequence made of its elements
RECURSIVE ToSeq(_)
ToSeq(S) == IF S = {} THEN << >>
            ELSE LET e == CHOOSE e \in S : TRUE
                     T == S \ {e}
                 IN Append(ToSeq(T), e)

\* Returns a set of functions on 1..N->1..N that represent permutations
\* for reordering a sequence of events
\*
\* This is a simple implementation that filters down from a larger set.
OrderingsSimple(N) == LET S == 1..N
                    Range(f) == { f[x] : x \in DOMAIN f }
                    Onto(f) == DOMAIN f = Range(f)
                IN {f \in [S->S] : Onto(f)}

\* Returns a set of functions on 1..N->1..N that represent permutations
\* for reordering a sequence of events
\*
\* This constructs the set rather than filtering down.
\*
RECURSIVE Orderings(_)
Orderings(N) == 
    CASE N=0 -> {}
      [] N=1 -> {[x \in {1}|->1]}
      [] OTHER -> LET fs == Orderings(N-1)
                      Helper(n, fp) == LET f == Append(fp,n) IN {[f EXCEPT ![x]=f[n], ![n]=f[x]] : x \in 1..n }
                  IN UNION({Helper(N,f): f \in fs})

\* Given a set, return a set of sequences that are permutations 
Perms(S) == LET fs == Orderings(Cardinality(S))
                s == ToSeq(S)
            IN {s**f: f \in fs}


=============================================================================
\* Modification History
\* Last modified Mon Oct 22 20:09:54 PDT 2018 by lhochstein
\* Created Mon Oct 22 19:21:10 PDT 2018 by lhochstein
