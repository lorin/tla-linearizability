------------------------------- MODULE Queue -------------------------------
(*** A specification for an abstract, sequential queue ***)

EXTENDS Naturals, Sequences, TLC

CONSTANT Values

CONSTANT Nmax \* Bound the max size of the queue so TLC can check it

VARIABLE items, H

Enq(val, q, qp) == qp = Append(q, val)

Deq(val, q, qp) == /\ q /= << >>
                   /\ val = Head(q)
                   /\ qp = Tail(q)
                   
                   
LOCAL SequenceOf(S) == UNION {[1..n -> S] : n \in Nat}
                   
Init == /\ items = << >>
        /\ H = << >>

Next == \/ \E v \in Values : /\ Enq(v, items, items')
                             /\ H' = Append(H, [op|->"E", val|->v])
                             /\ Len(H') <= Nmax
        \/ \E v \in Values : /\ Deq(v, items, items')
                             /\ H' = Append(H, [op|->"D", val|->v])
        
Spec == Init /\ [] [Next]_<<items,H>>

IsFIFO == LET FilterByOp(op) == SelectSeq(H, LAMBDA e: e.op = op)
              ToVal(S) == [i \in DOMAIN(S) |-> S[i].val]
              enqs == ToVal(FilterByOp("E"))
              deqs == ToVal(FilterByOp("D"))
          IN /\ Len(enqs) >= Len(deqs)
             /\ SubSeq(enqs,1, Len(deqs)) = deqs

            

THEOREM Spec => IsFIFO
              
RECURSIVE IsValidHelper(_, _)

IsValidHelper(h, q) == \/ h = << >>
                       \/ LET first == Head(h)
                              rest == Tail(h)
                          IN \/ /\ first.op = "E" 
                                /\ IsValidHelper(rest, Append(q, first.val))
                             \/ /\ first.op = "D"
                                /\ Len(q)>0
                                /\ first.val = Head(q)
                                /\ IsValidHelper(rest, Tail(q))


IsValid(h) == /\ IsValidHelper(h, << >>)
                 

=============================================================================
\* Modification History
\* Last modified Sun Oct 21 11:19:29 PDT 2018 by lhochstein
\* Created Fri Apr 20 23:43:41 PDT 2018 by lhochstein
