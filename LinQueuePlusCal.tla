-------------------------- MODULE LinQueuePlusCal --------------------------
EXTENDS LinQueue

CONSTANT H

f ** g == [x \in DOMAIN(g) |-> f[g[x]]]

(*
--algorithm FindLinearization
variables
    linearizable = FALSE,
    Hp, completeHp, f, S;

begin

Hp: with x \in L!ExtendedHistories(H) do
    Hp := x;
    end with;
CHp: completeHp := L!Complete(Hp);
Ord: with x \in L!Orderings(Len(completeHp)) do
    f := x;
    end with;
Sq: S := completeHp ** f;
Chk: linearizable := /\ L!IsSequential(S)
                     /\ IsLegal(S)
                     /\ L!AreEquivalent(S, completeHp)
                     /\ L!RespectsPrecedenceOrdering(H, S)
end algorithm
*)
\* BEGIN TRANSLATION
\* Label Hp at line 16 col 5 changed to Hp_
CONSTANT defaultInitValue
VARIABLES linearizable, Hp, completeHp, f, S, pc

vars == << linearizable, Hp, completeHp, f, S, pc >>

Init == (* Global variables *)
        /\ linearizable = FALSE
        /\ Hp = defaultInitValue
        /\ completeHp = defaultInitValue
        /\ f = defaultInitValue
        /\ S = defaultInitValue
        /\ pc = "Hp_"

Hp_ == /\ pc = "Hp_"
       /\ \E x \in L!ExtendedHistories(H):
            Hp' = x
       /\ pc' = "CHp"
       /\ UNCHANGED << linearizable, completeHp, f, S >>

CHp == /\ pc = "CHp"
       /\ completeHp' = L!Complete(Hp)
       /\ pc' = "Ord"
       /\ UNCHANGED << linearizable, Hp, f, S >>

Ord == /\ pc = "Ord"
       /\ \E x \in L!Orderings(Len(completeHp)):
            f' = x
       /\ pc' = "Sq"
       /\ UNCHANGED << linearizable, Hp, completeHp, S >>

Sq == /\ pc = "Sq"
      /\ S' = completeHp ** f
      /\ pc' = "Chk"
      /\ UNCHANGED << linearizable, Hp, completeHp, f >>

Chk == /\ pc = "Chk"
       /\ linearizable' = (/\ L!IsSequential(S)
                           /\ IsLegal(S)
                           /\ L!AreEquivalent(S, completeHp)
                           /\ L!RespectsPrecedenceOrdering(H, S))
       /\ pc' = "Done"
       /\ UNCHANGED << Hp, completeHp, f, S >>

Next == Hp_ \/ CHp \/ Ord \/ Sq \/ Chk
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION



=============================================================================
\* Modification History
\* Last modified Sun Oct 21 19:50:03 PDT 2018 by lhochstein
\* Created Sun Oct 21 19:33:05 PDT 2018 by lhochstein
