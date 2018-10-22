-------------------------- MODULE LinQueuePlusCal --------------------------
EXTENDS LinQueue

CONSTANT H

f ** g == [x \in DOMAIN(g) |-> f[g[x]]]

(*
--algorithm FindLinearization
variables
    linearizable = FALSE,
    completeHp, f, S;

begin

A: with Hp \in L!ExtendedHistories(H) do
    completeHp := L!Complete(Hp);
   end with;
B: with x \in L!Orderings(Len(completeHp)) do
    f := x;
   end with;
C: S := completeHp ** f;
D: linearizable := /\ L!IsSequential(S)
                   /\ IsLegal(S)
                   /\ L!AreEquivalent(S, completeHp)
                   /\ L!RespectsPrecedenceOrdering(H, S)
end algorithm
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES linearizable, completeHp, f, S, pc

vars == << linearizable, completeHp, f, S, pc >>

Init == (* Global variables *)
        /\ linearizable = FALSE
        /\ completeHp = defaultInitValue
        /\ f = defaultInitValue
        /\ S = defaultInitValue
        /\ pc = "A"

A == /\ pc = "A"
     /\ \E Hp \in L!ExtendedHistories(H):
          completeHp' = L!Complete(Hp)
     /\ pc' = "B"
     /\ UNCHANGED << linearizable, f, S >>

B == /\ pc = "B"
     /\ \E x \in L!Orderings(Len(completeHp)):
          f' = x
     /\ pc' = "C"
     /\ UNCHANGED << linearizable, completeHp, S >>

C == /\ pc = "C"
     /\ S' = completeHp ** f
     /\ pc' = "D"
     /\ UNCHANGED << linearizable, completeHp, f >>

D == /\ pc = "D"
     /\ linearizable' = (/\ L!IsSequential(S)
                         /\ IsLegal(S)
                         /\ L!AreEquivalent(S, completeHp)
                         /\ L!RespectsPrecedenceOrdering(H, S))
     /\ pc' = "Done"
     /\ UNCHANGED << completeHp, f, S >>

Next == A \/ B \/ C \/ D
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION



=============================================================================
\* Modification History
\* Last modified Sun Oct 21 19:50:03 PDT 2018 by lhochstein
\* Created Sun Oct 21 19:33:05 PDT 2018 by lhochstein
