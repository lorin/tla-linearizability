-------------------------- MODULE LinQueuePlusCal --------------------------
EXTENDS LinQueue, Utilities

CONSTANT H

(*
--algorithm FindLinearization
variables
    linearizable = FALSE,
    completeHp, f, S;

begin

with Hp \in L!ExtendedHistories(H) do
 completeHp := L!Complete(Hp);
end with;
with x \in L!Orderings(Len(completeHp)) do
 f := x;
end with;
S := completeHp ** f;
linearizable := /\ L!IsSequential(S)
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
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ \E Hp \in L!ExtendedHistories(H):
              completeHp' = L!Complete(Hp)
         /\ \E x \in L!Orderings(Len(completeHp')):
              f' = x
         /\ S' = completeHp' ** f'
         /\ linearizable' = (/\ L!IsSequential(S')
                             /\ IsLegal(S')
                             /\ L!AreEquivalent(S', completeHp')
                             /\ L!RespectsPrecedenceOrdering(H, S'))
         /\ pc' = "Done"

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION



=============================================================================
\* Modification History
\* Last modified Mon Oct 22 19:40:16 PDT 2018 by lhochstein
\* Created Sun Oct 21 19:33:05 PDT 2018 by lhochstein
